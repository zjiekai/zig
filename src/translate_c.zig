//! This is the userland implementation of translate-c which is used by both stage1
//! and stage2.

const std = @import("std");
const assert = std.debug.assert;
const clang = @import("clang.zig");
const ctok = std.c.tokenizer;
const CToken = std.c.Token;
const mem = std.mem;
const math = std.math;
const ast = @import("translate_c/ast.zig");
const Node = ast.Node;
const Tag = Node.Tag;

const CallingConvention = std.builtin.CallingConvention;

pub const ClangErrMsg = clang.Stage2ErrorMsg;

pub const Error = std.mem.Allocator.Error;
const TypeError = Error || error{UnsupportedType};
const TransError = TypeError || error{UnsupportedTranslation};

const SymbolTable = std.StringArrayHashMap(Node);
const AliasList = std.ArrayList(struct {
    alias: []const u8,
    name: []const u8,
});

const Scope = struct {
    id: Id,
    parent: ?*Scope,

    const Id = enum {
        @"switch",
        block,
        root,
        condition,
        loop,
    };

    /// Represents an in-progress Node.Switch. This struct is stack-allocated.
    /// When it is deinitialized, it produces an Node.Switch which is allocated
    /// into the main arena.
    const Switch = struct {
        base: Scope,
        pending_block: Block,
        cases: std.ArrayList(Node),
        switch_label: ?[]const u8,
        default_label: ?[]const u8,
    };

    /// Used for the scope of condition expressions, for example `if (cond)`.
    /// The block is lazily initialised because it is only needed for rare
    /// cases of comma operators being used.
    const Condition = struct {
        base: Scope,
        block: ?Block = null,

        fn getBlockScope(self: *Condition, c: *Context) !*Block {
            if (self.block) |*b| return b;
            self.block = try Block.init(c, &self.base, true);
            return &self.block.?;
        }

        fn deinit(self: *Condition) void {
            if (self.block) |*b| b.deinit();
        }
    };

    /// Represents an in-progress Node.Block. This struct is stack-allocated.
    /// When it is deinitialized, it produces an Node.Block which is allocated
    /// into the main arena.
    const Block = struct {
        base: Scope,
        statements: std.ArrayList(Node),
        variables: AliasList,
        mangle_count: u32 = 0,
        label: ?[]const u8 = null,

        /// When the block corresponds to a function, keep track of the return type
        /// so that the return expression can be cast, if necessary
        return_type: ?clang.QualType = null,

        fn init(c: *Context, parent: *Scope, labeled: bool) !Block {
            var blk = Block{
                .base = .{
                    .id = .block,
                    .parent = parent,
                },
                .statements = std.ArrayList(Node).init(c.gpa),
                .variables = AliasList.init(c.gpa),
            };
            if (labeled) {
                blk.label = try blk.makeMangledName(c, "blk");
            }
            return blk;
        }

        fn deinit(self: *Block) void {
            self.statements.deinit();
            self.variables.deinit();
            self.* = undefined;
        }

        fn complete(self: *Block, c: *Context) !Node {
            // We reserve 1 extra statement if the parent is a Loop. This is in case of
            // do while, we want to put `if (cond) break;` at the end.
            const alloc_len = self.statements.items.len + @boolToInt(self.base.parent.?.id == .loop);
            var stmts = try c.arena.alloc(Node, alloc_len);
            stmts.len -= 1;
            mem.copy(Node, stmts, self.statements.items);
            return Tag.block.create(c.arena, .{
                .label = self.label,
                .stmts = stmts,
            });
        }

        /// Given the desired name, return a name that does not shadow anything from outer scopes.
        /// Inserts the returned name into the scope.
        fn makeMangledName(scope: *Block, c: *Context, name: []const u8) ![]const u8 {
            const name_copy = try c.arena.dupe(u8, name);
            var proposed_name = name_copy;
            while (scope.contains(proposed_name)) {
                scope.mangle_count += 1;
                proposed_name = try std.fmt.allocPrint(c.arena, "{s}_{d}", .{ name, scope.mangle_count });
            }
            try scope.variables.append(.{ .name = name_copy, .alias = proposed_name });
            return proposed_name;
        }

        fn getAlias(scope: *Block, name: []const u8) []const u8 {
            for (scope.variables.items) |p| {
                if (mem.eql(u8, p.name, name))
                    return p.alias;
            }
            return scope.base.parent.?.getAlias(name);
        }

        fn localContains(scope: *Block, name: []const u8) bool {
            for (scope.variables.items) |p| {
                if (mem.eql(u8, p.alias, name))
                    return true;
            }
            return false;
        }

        fn contains(scope: *Block, name: []const u8) bool {
            if (scope.localContains(name))
                return true;
            return scope.base.parent.?.contains(name);
        }
    };

    const Root = struct {
        base: Scope,
        sym_table: SymbolTable,
        macro_table: SymbolTable,
        context: *Context,
        nodes: std.ArrayList(Node),

        fn init(c: *Context) Root {
            return .{
                .base = .{
                    .id = .root,
                    .parent = null,
                },
                .sym_table = SymbolTable.init(c.gpa),
                .macro_table = SymbolTable.init(c.gpa),
                .context = c,
                .nodes = std.ArrayList(Node).init(c.gpa),
            };
        }

        fn deinit(scope: *Root) void {
            scope.sym_table.deinit();
            scope.macro_table.deinit();
            scope.nodes.deinit();
        }

        /// Check if the global scope contains this name, without looking into the "future", e.g.
        /// ignore the preprocessed decl and macro names.
        fn containsNow(scope: *Root, name: []const u8) bool {
            return isZigPrimitiveType(name) or
                scope.sym_table.contains(name) or
                scope.macro_table.contains(name);
        }

        /// Check if the global scope contains the name, includes all decls that haven't been translated yet.
        fn contains(scope: *Root, name: []const u8) bool {
            return scope.containsNow(name) or scope.context.global_names.contains(name);
        }
    };

    fn findBlockScope(inner: *Scope, c: *Context) !*Scope.Block {
        var scope = inner;
        while (true) {
            switch (scope.id) {
                .root => unreachable,
                .block => return @fieldParentPtr(Block, "base", scope),
                .condition => return @fieldParentPtr(Condition, "base", scope).getBlockScope(c),
                else => scope = scope.parent.?,
            }
        }
    }

    fn findBlockReturnType(inner: *Scope, c: *Context) clang.QualType {
        var scope = inner;
        while (true) {
            switch (scope.id) {
                .root => unreachable,
                .block => {
                    const block = @fieldParentPtr(Block, "base", scope);
                    if (block.return_type) |qt| return qt;
                    scope = scope.parent.?;
                },
                else => scope = scope.parent.?,
            }
        }
    }

    fn getAlias(scope: *Scope, name: []const u8) []const u8 {
        return switch (scope.id) {
            .root => return name,
            .block => @fieldParentPtr(Block, "base", scope).getAlias(name),
            .@"switch", .loop, .condition => scope.parent.?.getAlias(name),
        };
    }

    fn contains(scope: *Scope, name: []const u8) bool {
        return switch (scope.id) {
            .root => @fieldParentPtr(Root, "base", scope).contains(name),
            .block => @fieldParentPtr(Block, "base", scope).contains(name),
            .@"switch", .loop, .condition => scope.parent.?.contains(name),
        };
    }

    fn getBreakableScope(inner: *Scope) *Scope {
        var scope = inner;
        while (true) {
            switch (scope.id) {
                .root => unreachable,
                .@"switch" => return scope,
                .loop => return scope,
                else => scope = scope.parent.?,
            }
        }
    }

    fn getSwitch(inner: *Scope) *Scope.Switch {
        var scope = inner;
        while (true) {
            switch (scope.id) {
                .root => unreachable,
                .@"switch" => return @fieldParentPtr(Switch, "base", scope),
                else => scope = scope.parent.?,
            }
        }
    }

    /// Appends a node to the first block scope if inside a function, or to the root tree if not.
    fn appendNode(inner: *Scope, node: Node) !void {
        var scope = inner;
        while (true) {
            switch (scope.id) {
                .root => {
                    const root = @fieldParentPtr(Root, "base", scope);
                    return root.nodes.append(node);
                },
                .block => {
                    const block = @fieldParentPtr(Block, "base", scope);
                    return block.statements.append(node);
                },
                else => scope = scope.parent.?,
            }
        }
    }
};

pub const Context = struct {
    gpa: *mem.Allocator,
    arena: *mem.Allocator,
    source_manager: *clang.SourceManager,
    decl_table: std.AutoArrayHashMapUnmanaged(usize, []const u8) = .{},
    alias_list: AliasList,
    global_scope: *Scope.Root,
    clang_context: *clang.ASTContext,
    mangle_count: u32 = 0,
    opaque_demotes: std.AutoHashMapUnmanaged(usize, void) = .{},

    /// This one is different than the root scope's name table. This contains
    /// a list of names that we found by visiting all the top level decls without
    /// translating them. The other maps are updated as we translate; this one is updated
    /// up front in a pre-processing step.
    global_names: std.StringArrayHashMapUnmanaged(void) = .{},

    fn getMangle(c: *Context) u32 {
        c.mangle_count += 1;
        return c.mangle_count;
    }

    /// Convert a null-terminated C string to a slice allocated in the arena
    fn str(c: *Context, s: [*:0]const u8) ![]u8 {
        return mem.dupe(c.arena, u8, mem.spanZ(s));
    }

    /// Convert a clang source location to a file:line:column string
    fn locStr(c: *Context, loc: clang.SourceLocation) ![]u8 {
        const spelling_loc = c.source_manager.getSpellingLoc(loc);
        const filename_c = c.source_manager.getFilename(spelling_loc);
        const filename = if (filename_c) |s| try c.str(s) else @as([]const u8, "(no file)");

        const line = c.source_manager.getSpellingLineNumber(spelling_loc);
        const column = c.source_manager.getSpellingColumnNumber(spelling_loc);
        return std.fmt.allocPrint(c.arena, "{s}:{d}:{d}", .{ filename, line, column });
    }
};

pub fn translate(
    gpa: *mem.Allocator,
    args_begin: [*]?[*]const u8,
    args_end: [*]?[*]const u8,
    errors: *[]ClangErrMsg,
    resources_path: [*:0]const u8,
) !std.zig.ast.Tree {
    const ast_unit = clang.LoadFromCommandLine(
        args_begin,
        args_end,
        &errors.ptr,
        &errors.len,
        resources_path,
    ) orelse {
        if (errors.len == 0) return error.ASTUnitFailure;
        return error.SemanticAnalyzeFail;
    };
    defer ast_unit.delete();

    // For memory that has the same lifetime as the Tree that we return
    // from this function.
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();

    var context = Context{
        .gpa = gpa,
        .arena = &arena.allocator,
        .source_manager = ast_unit.getSourceManager(),
        .alias_list = AliasList.init(gpa),
        .global_scope = try arena.allocator.create(Scope.Root),
        .clang_context = ast_unit.getASTContext(),
    };
    context.global_scope.* = Scope.Root.init(&context);
    defer {
        context.decl_table.deinit(gpa);
        context.alias_list.deinit();
        context.global_names.deinit(gpa);
        context.opaque_demotes.deinit(gpa);
        context.global_scope.deinit();
    }

    try context.global_scope.nodes.append(Tag.usingnamespace_builtins.init());

    try prepopulateGlobalNameTable(ast_unit, &context);

    if (!ast_unit.visitLocalTopLevelDecls(&context, declVisitorC)) {
        return error.OutOfMemory;
    }

    try transPreprocessorEntities(&context, ast_unit);

    try addMacros(&context);
    for (context.alias_list.items) |alias| {
        if (!context.global_scope.sym_table.contains(alias.alias)) {
            const node = try Tag.alias.create(context.arena, .{ .actual = alias.alias, .mangled = alias.name });
            try addTopLevelDecl(&context, alias.alias, node);
        }
    }

    return ast.render(gpa, context.global_scope.nodes.items);
}

fn prepopulateGlobalNameTable(ast_unit: *clang.ASTUnit, c: *Context) !void {
    if (!ast_unit.visitLocalTopLevelDecls(c, declVisitorNamesOnlyC)) {
        return error.OutOfMemory;
    }

    // TODO if we see #undef, delete it from the table
    var it = ast_unit.getLocalPreprocessingEntities_begin();
    const it_end = ast_unit.getLocalPreprocessingEntities_end();

    while (it.I != it_end.I) : (it.I += 1) {
        const entity = it.deref();
        switch (entity.getKind()) {
            .MacroDefinitionKind => {
                const macro = @ptrCast(*clang.MacroDefinitionRecord, entity);
                const raw_name = macro.getName_getNameStart();
                const name = try c.str(raw_name);
                _ = try c.global_names.put(c.gpa, name, {});
            },
            else => {},
        }
    }
}

fn declVisitorNamesOnlyC(context: ?*c_void, decl: *const clang.Decl) callconv(.C) bool {
    const c = @ptrCast(*Context, @alignCast(@alignOf(Context), context));
    declVisitorNamesOnly(c, decl) catch return false;
    return true;
}

fn declVisitorC(context: ?*c_void, decl: *const clang.Decl) callconv(.C) bool {
    const c = @ptrCast(*Context, @alignCast(@alignOf(Context), context));
    declVisitor(c, decl) catch return false;
    return true;
}

fn declVisitorNamesOnly(c: *Context, decl: *const clang.Decl) Error!void {
    if (decl.castToNamedDecl()) |named_decl| {
        const decl_name = try c.str(named_decl.getName_bytes_begin());
        _ = try c.global_names.put(c.gpa, decl_name, {});
    }
}

fn declVisitor(c: *Context, decl: *const clang.Decl) Error!void {
    switch (decl.getKind()) {
        .Function => {
            return visitFnDecl(c, @ptrCast(*const clang.FunctionDecl, decl));
        },
        .Typedef => {
            _ = try transTypeDef(c, @ptrCast(*const clang.TypedefNameDecl, decl), true);
        },
        .Enum => {
            _ = try transEnumDecl(c, @ptrCast(*const clang.EnumDecl, decl));
        },
        .Record => {
            _ = try transRecordDecl(c, @ptrCast(*const clang.RecordDecl, decl));
        },
        .Var => {
            return visitVarDecl(c, @ptrCast(*const clang.VarDecl, decl), null);
        },
        .Empty => {
            // Do nothing
        },
        else => {
            const decl_name = try c.str(decl.getDeclKindName());
            try warn(c, &c.global_scope.base, decl.getLocation(), "ignoring {s} declaration", .{decl_name});
        },
    }
}

fn visitFnDecl(c: *Context, fn_decl: *const clang.FunctionDecl) Error!void {
    const fn_name = try c.str(@ptrCast(*const clang.NamedDecl, fn_decl).getName_bytes_begin());
    if (c.global_scope.sym_table.contains(fn_name))
        return; // Avoid processing this decl twice

    // Skip this declaration if a proper definition exists
    if (!fn_decl.isThisDeclarationADefinition()) {
        if (fn_decl.getDefinition()) |def|
            return visitFnDecl(c, def);
    }

    const fn_decl_loc = fn_decl.getLocation();
    const has_body = fn_decl.hasBody();
    const storage_class = fn_decl.getStorageClass();
    var decl_ctx = FnDeclContext{
        .fn_name = fn_name,
        .has_body = has_body,
        .storage_class = storage_class,
        .is_export = switch (storage_class) {
            .None => has_body and !fn_decl.isInlineSpecified(),
            .Extern, .Static => false,
            .PrivateExtern => return failDecl(c, fn_decl_loc, fn_name, "unsupported storage class: private extern", .{}),
            .Auto => unreachable, // Not legal on functions
            .Register => unreachable, // Not legal on functions
        },
    };

    var fn_qt = fn_decl.getType();

    const fn_type = while (true) {
        const fn_type = fn_qt.getTypePtr();

        switch (fn_type.getTypeClass()) {
            .Attributed => {
                const attr_type = @ptrCast(*const clang.AttributedType, fn_type);
                fn_qt = attr_type.getEquivalentType();
            },
            .Paren => {
                const paren_type = @ptrCast(*const clang.ParenType, fn_type);
                fn_qt = paren_type.getInnerType();
            },
            else => break fn_type,
        }
    } else unreachable;
    const fn_ty = @ptrCast(*const clang.FunctionType, fn_type);
    const return_qt = fn_ty.getReturnType();

    const proto_node = switch (fn_type.getTypeClass()) {
        .FunctionProto => blk: {
            const fn_proto_type = @ptrCast(*const clang.FunctionProtoType, fn_type);
            if (has_body and fn_proto_type.isVariadic()) {
                decl_ctx.has_body = false;
                decl_ctx.storage_class = .Extern;
                decl_ctx.is_export = false;
                try warn(c, &c.global_scope.base, fn_decl_loc, "TODO unable to translate variadic function, demoted to declaration", .{});
            }
            break :blk transFnProto(c, fn_decl, fn_proto_type, fn_decl_loc, decl_ctx, true) catch |err| switch (err) {
                error.UnsupportedType => {
                    return failDecl(c, fn_decl_loc, fn_name, "unable to resolve prototype of function", .{});
                },
                error.OutOfMemory => |e| return e,
            };
        },
        .FunctionNoProto => blk: {
            const fn_no_proto_type = @ptrCast(*const clang.FunctionType, fn_type);
            break :blk transFnNoProto(c, fn_no_proto_type, fn_decl_loc, decl_ctx, true) catch |err| switch (err) {
                error.UnsupportedType => {
                    return failDecl(c, fn_decl_loc, fn_name, "unable to resolve prototype of function", .{});
                },
                error.OutOfMemory => |e| return e,
            };
        },
        else => return failDecl(c, fn_decl_loc, fn_name, "unable to resolve function type {}", .{fn_type.getTypeClass()}),
    };

    if (!decl_ctx.has_body) {
        return addTopLevelDecl(c, fn_name, Node.initPayload(&proto_node.base));
    }

    // actual function definition with body
    const body_stmt = fn_decl.getBody();
    var block_scope = try Scope.Block.init(c, &c.global_scope.base, false);
    block_scope.return_type = return_qt;
    defer block_scope.deinit();

    var scope = &block_scope.base;

    var param_id: c_uint = 0;
    for (proto_node.data.params) |*param, i| {
        const param_name = param.name orelse
            return failDecl(c, fn_decl_loc, fn_name, "function {s} parameter has no name", .{fn_name});

        const c_param = fn_decl.getParamDecl(param_id);
        const qual_type = c_param.getOriginalType();
        const is_const = qual_type.isConstQualified();

        const mangled_param_name = try block_scope.makeMangledName(c, param_name);
        param.name = mangled_param_name;

        if (!is_const) {
            const bare_arg_name = try std.fmt.allocPrint(c.arena, "arg_{s}", .{mangled_param_name});
            const arg_name = try block_scope.makeMangledName(c, bare_arg_name);
            param.name = arg_name;

            const redecl_node = try Tag.arg_redecl.create(c.arena, .{ .actual = mangled_param_name, .mangled = arg_name });
            try block_scope.statements.append(redecl_node);
        }

        param_id += 1;
    }

    const casted_body = @ptrCast(*const clang.CompoundStmt, body_stmt);
    transCompoundStmtInline(c, &block_scope.base, casted_body, &block_scope) catch |err| switch (err) {
        error.OutOfMemory => |e| return e,
        error.UnsupportedTranslation,
        error.UnsupportedType,
        => return failDecl(c, fn_decl_loc, fn_name, "unable to translate function", .{}),
    };
    // add return statement if the function didn't have one
    blk: {
        if (fn_ty.getNoReturnAttr()) break :blk;
        if (isCVoid(return_qt)) break :blk;

        if (block_scope.statements.items.len > 0) {
            var last = block_scope.statements.items[block_scope.statements.items.len - 1];
            while (true) {
                switch (last.tag()) {
                    .block => {
                        const block = last.castTag(.block).?;
                        if (block.data.stmts.len == 0) break;

                        last = block.data.stmts[block.data.stmts.len - 1];
                    },
                    // no extra return needed
                    .@"return", .return_void => break :blk,
                    else => break,
                }
            }
        }

        const rhs = transZeroInitExpr(c, scope, fn_decl_loc, return_qt.getTypePtr()) catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            error.UnsupportedTranslation,
            error.UnsupportedType,
            => return failDecl(c, fn_decl_loc, fn_name, "unable to create a return value for function", .{}),
        };
        const ret = try Tag.@"return".create(c.arena, rhs);
        try block_scope.statements.append(ret);
    }

    proto_node.data.body = try block_scope.complete(c);
    return addTopLevelDecl(c, fn_name, Node.initPayload(&proto_node.base));
}

fn transQualTypeMaybeInitialized(c: *Context, qt: clang.QualType, decl_init: ?*const clang.Expr, loc: clang.SourceLocation) TransError!Node {
    return if (decl_init) |init_expr|
        transQualTypeInitialized(c, qt, init_expr, loc)
    else
        transQualType(c, qt, loc);
}

/// if mangled_name is not null, this var decl was declared in a block scope.
fn visitVarDecl(c: *Context, var_decl: *const clang.VarDecl, mangled_name: ?[]const u8) Error!void {
    const var_name = mangled_name orelse try c.str(@ptrCast(*const clang.NamedDecl, var_decl).getName_bytes_begin());
    if (c.global_scope.sym_table.contains(var_name))
        return; // Avoid processing this decl twice

    const is_pub = mangled_name == null;
    const is_thread_local = var_decl.getTLSKind() != .None;
    const scope = &c.global_scope.base;

    // TODO https://github.com/ziglang/zig/issues/3756
    // TODO https://github.com/ziglang/zig/issues/1802
    const checked_name = if (isZigPrimitiveType(var_name)) try std.fmt.allocPrint(c.arena, "{s}_{d}", .{ var_name, c.getMangle() }) else var_name;
    const var_decl_loc = var_decl.getLocation();

    const qual_type = var_decl.getTypeSourceInfo_getType();
    const storage_class = var_decl.getStorageClass();
    const is_const = qual_type.isConstQualified();
    const has_init = var_decl.hasInit();
    const decl_init = var_decl.getInit();

    // In C extern variables with initializers behave like Zig exports.
    // extern int foo = 2;
    // does the same as:
    // extern int foo;
    // int foo = 2;
    const is_extern = storage_class == .Extern and !has_init;
    const is_export = !is_extern and storage_class != .Static;

    const type_node = transQualTypeMaybeInitialized(c, qual_type, decl_init, var_decl_loc) catch |err| switch (err) {
        error.UnsupportedTranslation, error.UnsupportedType => {
            return failDecl(c, var_decl_loc, checked_name, "unable to resolve variable type", .{});
        },
        error.OutOfMemory => |e| return e,
    };

    var init_node: ?Node = null;

    // If the initialization expression is not present, initialize with undefined.
    // If it is an integer literal, we can skip the @as since it will be redundant
    // with the variable type.
    if (has_init) {
        if (decl_init) |expr| {
            const node_or_error = if (expr.getStmtClass() == .StringLiteralClass)
                transStringLiteralAsArray(c, scope, @ptrCast(*const clang.StringLiteral, expr), zigArraySize(c, type_node) catch 0)
            else
                transExprCoercing(c, scope, expr, .used);
            init_node = node_or_error catch |err| switch (err) {
                error.UnsupportedTranslation,
                error.UnsupportedType,
                => {
                    return failDecl(c, var_decl_loc, checked_name, "unable to translate initializer", .{});
                },
                error.OutOfMemory => |e| return e,
            };
            if (!qualTypeIsBoolean(qual_type) and isBoolRes(init_node.?)) {
                init_node = try Tag.bool_to_int.create(c.arena, init_node.?);
            }
        } else {
            init_node = Tag.undefined_literal.init();
        }
    } else if (storage_class != .Extern) {
        // The C language specification states that variables with static or threadlocal
        // storage without an initializer are initialized to a zero value.

        // @import("std").mem.zeroes(T)
        init_node = try Tag.std_mem_zeroes.create(c.arena, type_node);
    }

    const linksection_string = blk: {
        var str_len: usize = undefined;
        if (var_decl.getSectionAttribute(&str_len)) |str_ptr| {
            break :blk str_ptr[0..str_len];
        }
        break :blk null;
    };

    const alignment = blk: {
        const alignment = var_decl.getAlignedAttribute(c.clang_context);
        if (alignment != 0) {
            // Clang reports the alignment in bits
            break :blk alignment / 8;
        }
        break :blk null;
    };

    const node = try Tag.var_decl.create(c.arena, .{
        .is_pub = is_pub,
        .is_const = is_const,
        .is_extern = is_extern,
        .is_export = is_export,
        .linksection_string = linksection_string,
        .alignment = alignment,
        .name = checked_name,
        .type = type_node,
        .init = init_node,
    });
    return addTopLevelDecl(c, checked_name, node);
}

fn transTypeDefAsBuiltin(c: *Context, typedef_decl: *const clang.TypedefNameDecl, builtin_name: []const u8) !Node {
    _ = try c.decl_table.put(c.gpa, @ptrToInt(typedef_decl.getCanonicalDecl()), builtin_name);
    return Tag.identifier.create(c.arena, builtin_name);
}

const builtin_typedef_map = std.ComptimeStringMap([]const u8, .{
    .{ "uint8_t", "u8" },
    .{ "int8_t", "i8" },
    .{ "uint16_t", "u16" },
    .{ "int16_t", "i16" },
    .{ "uint32_t", "u32" },
    .{ "int32_t", "i32" },
    .{ "uint64_t", "u64" },
    .{ "int64_t", "i64" },
    .{ "intptr_t", "isize" },
    .{ "uintptr_t", "usize" },
    .{ "ssize_t", "isize" },
    .{ "size_t", "usize" },
});

fn transTypeDef(c: *Context, typedef_decl: *const clang.TypedefNameDecl, top_level_visit: bool) Error!?Node {
    if (c.decl_table.get(@ptrToInt(typedef_decl.getCanonicalDecl()))) |name|
        return try Tag.identifier.create(c.arena, name); // Avoid processing this decl twice

    const typedef_name = try c.str(@ptrCast(*const clang.NamedDecl, typedef_decl).getName_bytes_begin());

    // TODO https://github.com/ziglang/zig/issues/3756
    // TODO https://github.com/ziglang/zig/issues/1802
    const checked_name = if (isZigPrimitiveType(typedef_name)) try std.fmt.allocPrint(c.arena, "{s}_{d}", .{ typedef_name, c.getMangle() }) else typedef_name;
    if (builtin_typedef_map.get(checked_name)) |builtin| {
        _ = try c.decl_table.put(c.gpa, @ptrToInt(typedef_decl.getCanonicalDecl()), builtin);
        return try Tag.identifier.create(c.arena, builtin);
    }

    if (!top_level_visit) {
        return try Tag.identifier.create(c.arena, checked_name);
    }

    _ = try c.decl_table.put(c.gpa, @ptrToInt(typedef_decl.getCanonicalDecl()), checked_name);
    const node = (try transCreateNodeTypedef(c, typedef_decl, true, checked_name)) orelse return null;
    try addTopLevelDecl(c, checked_name, node);
    return try Tag.identifier.create(c.arena, checked_name);
}

fn transCreateNodeTypedef(
    c: *Context,
    typedef_decl: *const clang.TypedefNameDecl,
    toplevel: bool,
    checked_name: []const u8,
) Error!?Node {
    const child_qt = typedef_decl.getUnderlyingType();
    const typedef_loc = typedef_decl.getLocation();
    const init_node = transQualType(c, child_qt, typedef_loc) catch |err| switch (err) {
        error.UnsupportedType => {
            try failDecl(c, typedef_loc, checked_name, "unable to resolve typedef child type", .{});
            return null;
        },
        error.OutOfMemory => |e| return e,
    };

    const payload = try c.arena.create(ast.Payload.SimpleVarDecl);
    payload.* = .{
        .base = .{ .tag = ([2]Tag{ .typedef, .pub_typedef })[@boolToInt(toplevel)] },
        .data = .{
            .name = checked_name,
            .init = init_node,
        },
    };
    return Node.initPayload(&payload.base);
}

fn transRecordDecl(c: *Context, record_decl: *const clang.RecordDecl) Error!?Node {
    if (c.decl_table.get(@ptrToInt(record_decl.getCanonicalDecl()))) |name|
        return try Tag.identifier.create(c.arena, name); // Avoid processing this decl twice
    const record_loc = record_decl.getLocation();

    var bare_name = try c.str(@ptrCast(*const clang.NamedDecl, record_decl).getName_bytes_begin());
    var is_unnamed = false;
    // Record declarations such as `struct {...} x` have no name but they're not
    // anonymous hence here isAnonymousStructOrUnion is not needed
    if (bare_name.len == 0) {
        bare_name = try std.fmt.allocPrint(c.arena, "unnamed_{d}", .{c.getMangle()});
        is_unnamed = true;
    }

    var container_kind_name: []const u8 = undefined;
    var is_union = false;
    if (record_decl.isUnion()) {
        container_kind_name = "union";
        is_union = true;
    } else if (record_decl.isStruct()) {
        container_kind_name = "struct";
    } else {
        try warn(c, &c.global_scope.base, record_loc, "record {s} is not a struct or union", .{bare_name});
        return null;
    }

    const name = try std.fmt.allocPrint(c.arena, "{s}_{s}", .{ container_kind_name, bare_name });
    _ = try c.decl_table.put(c.gpa, @ptrToInt(record_decl.getCanonicalDecl()), name);

    const is_pub = !is_unnamed;
    const init_node = blk: {
        const record_def = record_decl.getDefinition() orelse {
            _ = try c.opaque_demotes.put(c.gpa, @ptrToInt(record_decl.getCanonicalDecl()), {});
            break :blk Tag.opaque_literal.init();
        };

        const is_packed = record_decl.getPackedAttribute();
        var fields = std.ArrayList(ast.Payload.Record.Field).init(c.gpa);
        defer fields.deinit();

        var unnamed_field_count: u32 = 0;
        var it = record_def.field_begin();
        const end_it = record_def.field_end();
        while (it.neq(end_it)) : (it = it.next()) {
            const field_decl = it.deref();
            const field_loc = field_decl.getLocation();
            const field_qt = field_decl.getType();

            if (field_decl.isBitField()) {
                _ = try c.opaque_demotes.put(c.gpa, @ptrToInt(record_decl.getCanonicalDecl()), {});
                try warn(c, &c.global_scope.base, field_loc, "{s} demoted to opaque type - has bitfield", .{container_kind_name});
                break :blk Tag.opaque_literal.init();
            }

            if (qualTypeCanon(field_qt).isIncompleteOrZeroLengthArrayType(c.clang_context)) {
                _ = try c.opaque_demotes.put(c.gpa, @ptrToInt(record_decl.getCanonicalDecl()), {});
                try warn(c, &c.global_scope.base, field_loc, "{s} demoted to opaque type - has variable length array", .{container_kind_name});
                break :blk Tag.opaque_literal.init();
            }

            var is_anon = false;
            var field_name = try c.str(@ptrCast(*const clang.NamedDecl, field_decl).getName_bytes_begin());
            if (field_decl.isAnonymousStructOrUnion() or field_name.len == 0) {
                // Context.getMangle() is not used here because doing so causes unpredictable field names for anonymous fields.
                field_name = try std.fmt.allocPrint(c.arena, "unnamed_{d}", .{unnamed_field_count});
                unnamed_field_count += 1;
                is_anon = true;
            }
            const field_type = transQualType(c, field_qt, field_loc) catch |err| switch (err) {
                error.UnsupportedType => {
                    _ = try c.opaque_demotes.put(c.gpa, @ptrToInt(record_decl.getCanonicalDecl()), {});
                    try warn(c, &c.global_scope.base, record_loc, "{s} demoted to opaque type - unable to translate type of field {s}", .{ container_kind_name, field_name });
                    break :blk Tag.opaque_literal.init();
                },
                else => |e| return e,
            };

            const alignment = blk_2: {
                const alignment = field_decl.getAlignedAttribute(c.clang_context);
                if (alignment != 0) {
                    // Clang reports the alignment in bits
                    break :blk_2 alignment / 8;
                }
                break :blk_2 null;
            };

            if (is_anon) {
                _ = try c.decl_table.put(c.gpa, @ptrToInt(field_decl.getCanonicalDecl()), field_name);
            }

            try fields.append(.{
                .name = field_name,
                .type = field_type,
                .alignment = alignment,
            });
        }

        const record_payload = try c.arena.create(ast.Payload.Record);
        record_payload.* = .{
            .base = .{ .tag = ([2]Tag{ .@"struct", .@"union" })[@boolToInt(is_union)] },
            .data = .{
                .is_packed = is_packed,
                .fields = try c.arena.dupe(ast.Payload.Record.Field, fields.items),
            },
        };
        break :blk Node.initPayload(&record_payload.base);
    };

    const payload = try c.arena.create(ast.Payload.SimpleVarDecl);
    payload.* = .{
        .base = .{ .tag = ([2]Tag{ .var_simple, .pub_var_simple })[@boolToInt(is_pub)] },
        .data = .{
            .name = name,
            .init = init_node,
        },
    };

    try addTopLevelDecl(c, name, Node.initPayload(&payload.base));
    if (!is_unnamed)
        try c.alias_list.append(.{ .alias = bare_name, .name = name });
    return try Tag.identifier.create(c.arena, name);
}

fn transEnumDecl(c: *Context, enum_decl: *const clang.EnumDecl) Error!?Node {
    if (c.decl_table.get(@ptrToInt(enum_decl.getCanonicalDecl()))) |name|
        return try Tag.identifier.create(c.arena, name); // Avoid processing this decl twice
    const enum_loc = enum_decl.getLocation();

    var bare_name = try c.str(@ptrCast(*const clang.NamedDecl, enum_decl).getName_bytes_begin());
    var is_unnamed = false;
    if (bare_name.len == 0) {
        bare_name = try std.fmt.allocPrint(c.arena, "unnamed_{d}", .{c.getMangle()});
        is_unnamed = true;
    }

    const name = try std.fmt.allocPrint(c.arena, "enum_{s}", .{bare_name});
    _ = try c.decl_table.put(c.gpa, @ptrToInt(enum_decl.getCanonicalDecl()), name);

    const is_pub = !is_unnamed;

    const init_node = if (enum_decl.getDefinition()) |enum_def| blk: {
        var pure_enum = true;
        var it = enum_def.enumerator_begin();
        var end_it = enum_def.enumerator_end();
        while (it.neq(end_it)) : (it = it.next()) {
            const enum_const = it.deref();
            if (enum_const.getInitExpr()) |_| {
                pure_enum = false;
                break;
            }
        }

        var fields = std.ArrayList(ast.Payload.Enum.Field).init(c.gpa);
        defer fields.deinit();

        const int_type = enum_decl.getIntegerType();
        // The underlying type may be null in case of forward-declared enum
        // types, while that's not ISO-C compliant many compilers allow this and
        // default to the usual integer type used for all the enums.

        // default to c_int since msvc and gcc default to different types
        const init_arg_expr = if (int_type.ptr != null and
            !isCBuiltinType(int_type, .UInt) and
            !isCBuiltinType(int_type, .Int))
            transQualType(c, int_type, enum_loc) catch |err| switch (err) {
                error.UnsupportedType => {
                    try failDecl(c, enum_loc, name, "unable to translate enum tag type", .{});
                    return null;
                },
                else => |e| return e,
            }
        else
            try Tag.type.create(c.arena, "c_int");

        it = enum_def.enumerator_begin();
        end_it = enum_def.enumerator_end();
        while (it.neq(end_it)) : (it = it.next()) {
            const enum_const = it.deref();
            const enum_val_name = try c.str(@ptrCast(*const clang.NamedDecl, enum_const).getName_bytes_begin());

            const field_name = if (!is_unnamed and mem.startsWith(u8, enum_val_name, bare_name))
                enum_val_name[bare_name.len..]
            else
                enum_val_name;

            const int_node = if (!pure_enum)
                try transCreateNodeAPInt(c, enum_const.getInitVal())
            else
                null;

            try fields.append(.{
                .name = field_name,
                .value = int_node,
            });

            // In C each enum value is in the global namespace. So we put them there too.
            // At this point we can rely on the enum emitting successfully.
            try addTopLevelDecl(c, field_name, try Tag.enum_redecl.create(c.arena, .{
                .enum_val_name = enum_val_name,
                .field_name = field_name,
                .enum_name = name,
            }));
        }

        break :blk try Tag.@"enum".create(c.arena, try c.arena.dupe(ast.Payload.Enum.Field, fields.items));
    } else blk: {
        _ = try c.opaque_demotes.put(c.gpa, @ptrToInt(enum_decl.getCanonicalDecl()), {});
        break :blk Tag.opaque_literal.init();
    };

    const payload = try c.arena.create(ast.Payload.SimpleVarDecl);
    payload.* = .{
        .base = .{ .tag = ([2]Tag{ .var_simple, .pub_var_simple })[@boolToInt(is_pub)] },
        .data = .{
            .name = name,
            .init = init_node,
        },
    };

    try addTopLevelDecl(c, name, Node.initPayload(&payload.base));
    if (!is_unnamed)
        try c.alias_list.append(.{ .alias = bare_name, .name = name });
    return try Tag.identifier.create(c.arena, name);
}

const ResultUsed = enum {
    used,
    unused,
};

fn transStmt(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.Stmt,
    result_used: ResultUsed,
) TransError!Node {
    const sc = stmt.getStmtClass();
    switch (sc) {
        .BinaryOperatorClass => return transBinaryOperator(c, scope, @ptrCast(*const clang.BinaryOperator, stmt), result_used),
        .CompoundStmtClass => return transCompoundStmt(c, scope, @ptrCast(*const clang.CompoundStmt, stmt)),
        .CStyleCastExprClass => return transCStyleCastExprClass(c, scope, @ptrCast(*const clang.CStyleCastExpr, stmt), result_used),
        .DeclStmtClass => return transDeclStmt(c, scope, @ptrCast(*const clang.DeclStmt, stmt)),
        .DeclRefExprClass => return transDeclRefExpr(c, scope, @ptrCast(*const clang.DeclRefExpr, stmt)),
        .ImplicitCastExprClass => return transImplicitCastExpr(c, scope, @ptrCast(*const clang.ImplicitCastExpr, stmt), result_used),
        .IntegerLiteralClass => return transIntegerLiteral(c, scope, @ptrCast(*const clang.IntegerLiteral, stmt), result_used, .with_as),
        .ReturnStmtClass => return transReturnStmt(c, scope, @ptrCast(*const clang.ReturnStmt, stmt)),
        .StringLiteralClass => return transStringLiteral(c, scope, @ptrCast(*const clang.StringLiteral, stmt), result_used),
        .ParenExprClass => {
            const expr = try transExpr(c, scope, @ptrCast(*const clang.ParenExpr, stmt).getSubExpr(), .used);
            return maybeSuppressResult(c, scope, result_used, expr);
        },
        .InitListExprClass => return transInitListExpr(c, scope, @ptrCast(*const clang.InitListExpr, stmt), result_used),
        .ImplicitValueInitExprClass => return transImplicitValueInitExpr(c, scope, @ptrCast(*const clang.Expr, stmt), result_used),
        .IfStmtClass => return transIfStmt(c, scope, @ptrCast(*const clang.IfStmt, stmt)),
        .WhileStmtClass => return transWhileLoop(c, scope, @ptrCast(*const clang.WhileStmt, stmt)),
        .DoStmtClass => return transDoWhileLoop(c, scope, @ptrCast(*const clang.DoStmt, stmt)),
        .NullStmtClass => {
            return Tag.empty_block.init();
        },
        .ContinueStmtClass => return Tag.@"continue".init(),
        .BreakStmtClass => return transBreak(c, scope),
        .ForStmtClass => return transForLoop(c, scope, @ptrCast(*const clang.ForStmt, stmt)),
        .FloatingLiteralClass => return transFloatingLiteral(c, scope, @ptrCast(*const clang.FloatingLiteral, stmt), result_used),
        .ConditionalOperatorClass => {
            return transConditionalOperator(c, scope, @ptrCast(*const clang.ConditionalOperator, stmt), result_used);
        },
        .BinaryConditionalOperatorClass => {
            return transBinaryConditionalOperator(c, scope, @ptrCast(*const clang.BinaryConditionalOperator, stmt), result_used);
        },
        .SwitchStmtClass => return transSwitch(c, scope, @ptrCast(*const clang.SwitchStmt, stmt)),
        .CaseStmtClass => return transCase(c, scope, @ptrCast(*const clang.CaseStmt, stmt)),
        .DefaultStmtClass => return transDefault(c, scope, @ptrCast(*const clang.DefaultStmt, stmt)),
        .ConstantExprClass => return transConstantExpr(c, scope, @ptrCast(*const clang.Expr, stmt), result_used),
        .PredefinedExprClass => return transPredefinedExpr(c, scope, @ptrCast(*const clang.PredefinedExpr, stmt), result_used),
        .CharacterLiteralClass => return transCharLiteral(c, scope, @ptrCast(*const clang.CharacterLiteral, stmt), result_used, .with_as),
        .StmtExprClass => return transStmtExpr(c, scope, @ptrCast(*const clang.StmtExpr, stmt), result_used),
        .MemberExprClass => return transMemberExpr(c, scope, @ptrCast(*const clang.MemberExpr, stmt), result_used),
        .ArraySubscriptExprClass => return transArrayAccess(c, scope, @ptrCast(*const clang.ArraySubscriptExpr, stmt), result_used),
        .CallExprClass => return transCallExpr(c, scope, @ptrCast(*const clang.CallExpr, stmt), result_used),
        .UnaryExprOrTypeTraitExprClass => return transUnaryExprOrTypeTraitExpr(c, scope, @ptrCast(*const clang.UnaryExprOrTypeTraitExpr, stmt), result_used),
        .UnaryOperatorClass => return transUnaryOperator(c, scope, @ptrCast(*const clang.UnaryOperator, stmt), result_used),
        .CompoundAssignOperatorClass => return transCompoundAssignOperator(c, scope, @ptrCast(*const clang.CompoundAssignOperator, stmt), result_used),
        .OpaqueValueExprClass => {
            const source_expr = @ptrCast(*const clang.OpaqueValueExpr, stmt).getSourceExpr().?;
            const expr = try transExpr(c, scope, source_expr, .used);
            return maybeSuppressResult(c, scope, result_used, expr);
        },
        else => {
            return fail(
                c,
                error.UnsupportedTranslation,
                stmt.getBeginLoc(),
                "TODO implement translation of stmt class {s}",
                .{@tagName(sc)},
            );
        },
    }
}

fn transBinaryOperator(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.BinaryOperator,
    result_used: ResultUsed,
) TransError!Node {
    const op = stmt.getOpcode();
    const qt = stmt.getType();
    switch (op) {
        .Assign => return try transCreateNodeAssign(c, scope, result_used, stmt.getLHS(), stmt.getRHS()),
        .Comma => {
            var block_scope = try Scope.Block.init(c, scope, true);
            defer block_scope.deinit();

            const lhs = try transExpr(c, &block_scope.base, stmt.getLHS(), .unused);
            try block_scope.statements.append(lhs);

            const rhs = try transExpr(c, &block_scope.base, stmt.getRHS(), .used);
            const break_node = try Tag.break_val.create(c.arena, .{
                .label = block_scope.label,
                .val = rhs,
            });
            try block_scope.statements.append(break_node);
            const block_node = try block_scope.complete(c);
            return maybeSuppressResult(c, scope, result_used, block_node);
        },
        .Div => {
            if (cIsSignedInteger(qt)) {
                // signed integer division uses @divTrunc
                const lhs = try transExpr(c, scope, stmt.getLHS(), .used);
                const rhs = try transExpr(c, scope, stmt.getRHS(), .used);
                const div_trunc = try Tag.div_trunc.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
                return maybeSuppressResult(c, scope, result_used, div_trunc);
            }
        },
        .Rem => {
            if (cIsSignedInteger(qt)) {
                // signed integer division uses @rem
                const lhs = try transExpr(c, scope, stmt.getLHS(), .used);
                const rhs = try transExpr(c, scope, stmt.getRHS(), .used);
                const rem = try Tag.rem.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
                return maybeSuppressResult(c, scope, result_used, rem);
            }
        },
        .Shl => {
            return transCreateNodeShiftOp(c, scope, stmt, .shl, result_used);
        },
        .Shr => {
            return transCreateNodeShiftOp(c, scope, stmt, .shr, result_used);
        },
        .LAnd => {
            return transCreateNodeBoolInfixOp(c, scope, stmt, .@"and", result_used);
        },
        .LOr => {
            return transCreateNodeBoolInfixOp(c, scope, stmt, .@"or", result_used);
        },
        else => {},
    }
    var op_id: Tag = undefined;
    switch (op) {
        .Add => {
            if (cIsUnsignedInteger(qt)) {
                op_id = .add_wrap;
            } else {
                op_id = .add;
            }
        },
        .Sub => {
            if (cIsUnsignedInteger(qt)) {
                op_id = .sub_wrap;
            } else {
                op_id = .sub;
            }
        },
        .Mul => {
            if (cIsUnsignedInteger(qt)) {
                op_id = .mul_wrap;
            } else {
                op_id = .mul;
            }
        },
        .Div => {
            // unsigned/float division uses the operator
            op_id = .div;
        },
        .Rem => {
            // unsigned/float division uses the operator
            op_id = .mod;
        },
        .LT => {
            op_id = .less_than;
        },
        .GT => {
            op_id = .greater_than;
        },
        .LE => {
            op_id = .less_than_equal;
        },
        .GE => {
            op_id = .greater_than_equal;
        },
        .EQ => {
            op_id = .equal;
        },
        .NE => {
            op_id = .not_equal;
        },
        .And => {
            op_id = .bit_and;
        },
        .Xor => {
            op_id = .bit_xor;
        },
        .Or => {
            op_id = .bit_or;
        },
        else => unreachable,
    }

    const lhs_uncasted = try transExpr(c, scope, stmt.getLHS(), .used);
    const rhs_uncasted = try transExpr(c, scope, stmt.getRHS(), .used);

    const lhs = if (isBoolRes(lhs_uncasted))
        try Tag.bool_to_int.create(c.arena, lhs_uncasted)
    else
        lhs_uncasted;

    const rhs = if (isBoolRes(rhs_uncasted))
        try Tag.bool_to_int.create(c.arena, rhs_uncasted)
    else
        rhs_uncasted;

    return transCreateNodeInfixOp(c, scope, op_id, lhs, rhs, result_used);
}

fn transCompoundStmtInline(
    c: *Context,
    parent_scope: *Scope,
    stmt: *const clang.CompoundStmt,
    block: *Scope.Block,
) TransError!void {
    var it = stmt.body_begin();
    const end_it = stmt.body_end();
    while (it != end_it) : (it += 1) {
        const result = try transStmt(c, parent_scope, it[0], .unused);
        try block.statements.append(result);
    }
}

fn transCompoundStmt(c: *Context, scope: *Scope, stmt: *const clang.CompoundStmt) TransError!Node {
    var block_scope = try Scope.Block.init(c, scope, false);
    defer block_scope.deinit();
    try transCompoundStmtInline(c, &block_scope.base, stmt, &block_scope);
    return try block_scope.complete(c);
}

fn transCStyleCastExprClass(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.CStyleCastExpr,
    result_used: ResultUsed,
) TransError!Node {
    const sub_expr = stmt.getSubExpr();
    const cast_node = (try transCCast(
        c,
        scope,
        stmt.getBeginLoc(),
        stmt.getType(),
        sub_expr.getType(),
        try transExpr(c, scope, sub_expr, .used),
    ));
    return maybeSuppressResult(c, scope, result_used, cast_node);
}

fn transDeclStmtOne(
    c: *Context,
    scope: *Scope,
    decl: *const clang.Decl,
    block_scope: *Scope.Block,
) TransError!Node {
    switch (decl.getKind()) {
        .Var => {
            const var_decl = @ptrCast(*const clang.VarDecl, decl);
            const decl_init = var_decl.getInit();

            const qual_type = var_decl.getTypeSourceInfo_getType();
            const name = try c.str(@ptrCast(*const clang.NamedDecl, var_decl).getName_bytes_begin());
            const mangled_name = try block_scope.makeMangledName(c, name);

            switch (var_decl.getStorageClass()) {
                .Extern, .Static => {
                    // This is actually a global variable, put it in the global scope and reference it.
                    // `_ = mangled_name;`
                    try visitVarDecl(c, var_decl, mangled_name);
                    return try maybeSuppressResult(c, scope, .unused, try Tag.identifier.create(c.arena, mangled_name));
                },
                else => {},
            }

            const is_const = qual_type.isConstQualified();

            const loc = decl.getLocation();
            const type_node = try transQualTypeMaybeInitialized(c, qual_type, decl_init, loc);

            var init_node = if (decl_init) |expr|
                if (expr.getStmtClass() == .StringLiteralClass)
                    try transStringLiteralAsArray(c, scope, @ptrCast(*const clang.StringLiteral, expr), try zigArraySize(c, type_node))
                else
                    try transExprCoercing(c, scope, expr, .used)
            else
                Tag.undefined_literal.init();
            if (!qualTypeIsBoolean(qual_type) and isBoolRes(init_node)) {
                init_node = try Tag.bool_to_int.create(c.arena, init_node);
            }
            return Tag.var_decl.create(c.arena, .{
                .is_pub = false,
                .is_const = is_const,
                .is_extern = false,
                .is_export = false,
                .linksection_string = null,
                .alignment = null,
                .name = mangled_name,
                .type = type_node,
                .init = init_node,
            });
        },
        .Typedef => {
            const typedef_decl = @ptrCast(*const clang.TypedefNameDecl, decl);
            const name = try c.str(@ptrCast(*const clang.NamedDecl, typedef_decl).getName_bytes_begin());

            const underlying_qual = typedef_decl.getUnderlyingType();
            const underlying_type = underlying_qual.getTypePtr();

            const mangled_name = try block_scope.makeMangledName(c, name);
            const node = (try transCreateNodeTypedef(c, typedef_decl, false, mangled_name)) orelse
                return error.UnsupportedTranslation;
            return node;
        },
        else => |kind| return fail(
            c,
            error.UnsupportedTranslation,
            decl.getLocation(),
            "TODO implement translation of DeclStmt kind {s}",
            .{@tagName(kind)},
        ),
    }
}

fn transDeclStmt(c: *Context, scope: *Scope, stmt: *const clang.DeclStmt) TransError!Node {
    const block_scope = scope.findBlockScope(c) catch unreachable;

    var it = stmt.decl_begin();
    const end_it = stmt.decl_end();
    assert(it != end_it);
    while (true) : (it += 1) {
        const node = try transDeclStmtOne(c, scope, it[0], block_scope);

        if (it + 1 == end_it) {
            return node;
        } else {
            try block_scope.statements.append(node);
        }
    }
    unreachable;
}

fn transDeclRefExpr(
    c: *Context,
    scope: *Scope,
    expr: *const clang.DeclRefExpr,
) TransError!Node {
    const value_decl = expr.getDecl();
    const name = try c.str(@ptrCast(*const clang.NamedDecl, value_decl).getName_bytes_begin());
    const mangled_name = scope.getAlias(name);
    return Tag.identifier.create(c.arena, mangled_name);
}

fn transImplicitCastExpr(
    c: *Context,
    scope: *Scope,
    expr: *const clang.ImplicitCastExpr,
    result_used: ResultUsed,
) TransError!Node {
    const sub_expr = expr.getSubExpr();
    const dest_type = getExprQualType(c, @ptrCast(*const clang.Expr, expr));
    const src_type = getExprQualType(c, sub_expr);
    switch (expr.getCastKind()) {
        .BitCast, .FloatingCast, .FloatingToIntegral, .IntegralToFloating, .IntegralCast, .PointerToIntegral, .IntegralToPointer => {
            const sub_expr_node = try transExpr(c, scope, sub_expr, .used);
            const casted = try transCCast(c, scope, expr.getBeginLoc(), dest_type, src_type, sub_expr_node);
            return maybeSuppressResult(c, scope, result_used, casted);
        },
        .LValueToRValue, .NoOp, .FunctionToPointerDecay => {
            const sub_expr_node = try transExpr(c, scope, sub_expr, .used);
            return maybeSuppressResult(c, scope, result_used, sub_expr_node);
        },
        .ArrayToPointerDecay => {
            if (exprIsNarrowStringLiteral(sub_expr)) {
                const sub_expr_node = try transExpr(c, scope, sub_expr, .used);
                return maybeSuppressResult(c, scope, result_used, sub_expr_node);
            }

            const addr = try Tag.address_of.create(c.arena, try transExpr(c, scope, sub_expr, .used));
            return maybeSuppressResult(c, scope, result_used, addr);
        },
        .NullToPointer => {
            return Tag.null_literal.init();
        },
        .PointerToBoolean => {
            // @ptrToInt(val) != 0
            const ptr_to_int = try Tag.ptr_to_int.create(c.arena, try transExpr(c, scope, sub_expr, .used));

            const ne = try Tag.not_equal.create(c.arena, .{ .lhs = ptr_to_int, .rhs = Tag.zero_literal.init() });
            return maybeSuppressResult(c, scope, result_used, ne);
        },
        .IntegralToBoolean => {
            const sub_expr_node = try transExpr(c, scope, sub_expr, .used);

            // The expression is already a boolean one, return it as-is
            if (isBoolRes(sub_expr_node))
                return maybeSuppressResult(c, scope, result_used, sub_expr_node);

            // val != 0
            const ne = try Tag.not_equal.create(c.arena, .{ .lhs = sub_expr_node, .rhs = Tag.zero_literal.init() });
            return maybeSuppressResult(c, scope, result_used, ne);
        },
        .BuiltinFnToFnPtr => {
            return transExpr(c, scope, sub_expr, result_used);
        },
        else => |kind| return fail(
            c,
            error.UnsupportedTranslation,
            @ptrCast(*const clang.Stmt, expr).getBeginLoc(),
            "TODO implement translation of CastKind {s}",
            .{@tagName(kind)},
        ),
    }
}

fn transBoolExpr(
    c: *Context,
    scope: *Scope,
    expr: *const clang.Expr,
    used: ResultUsed,
) TransError!Node {
    if (@ptrCast(*const clang.Stmt, expr).getStmtClass() == .IntegerLiteralClass) {
        var is_zero: bool = undefined;
        if (!(@ptrCast(*const clang.IntegerLiteral, expr).isZero(&is_zero, c.clang_context))) {
            return fail(c, error.UnsupportedTranslation, expr.getBeginLoc(), "invalid integer literal", .{});
        }
        return Node{ .tag_if_small_enough = @enumToInt(([2]Tag{ .true_literal, .false_literal })[@boolToInt(is_zero)]) };
    }

    var res = try transExpr(c, scope, expr, used);
    if (isBoolRes(res)) {
        return maybeSuppressResult(c, scope, used, res);
    }

    const ty = getExprQualType(c, expr).getTypePtr();
    const node = try finishBoolExpr(c, scope, expr.getBeginLoc(), ty, res, used);

    return maybeSuppressResult(c, scope, used, node);
}

fn exprIsBooleanType(expr: *const clang.Expr) bool {
    return qualTypeIsBoolean(expr.getType());
}

fn exprIsNarrowStringLiteral(expr: *const clang.Expr) bool {
    switch (expr.getStmtClass()) {
        .StringLiteralClass => {
            const string_lit = @ptrCast(*const clang.StringLiteral, expr);
            return string_lit.getCharByteWidth() == 1;
        },
        .PredefinedExprClass => return true,
        .UnaryOperatorClass => {
            const op_expr = @ptrCast(*const clang.UnaryOperator, expr).getSubExpr();
            return exprIsNarrowStringLiteral(op_expr);
        },
        .ParenExprClass => {
            const op_expr = @ptrCast(*const clang.ParenExpr, expr).getSubExpr();
            return exprIsNarrowStringLiteral(op_expr);
        },
        else => return false,
    }
}

fn isBoolRes(res: Node) bool {
    switch (res.tag()) {
        .@"or",
        .@"and",
        .equal,
        .not_equal,
        .less_than,
        .less_than_equal,
        .greater_than,
        .greater_than_equal,
        .not,
        .false_literal,
        .true_literal,
        => return true,
        else => return false,
    }
}

fn finishBoolExpr(
    c: *Context,
    scope: *Scope,
    loc: clang.SourceLocation,
    ty: *const clang.Type,
    node: Node,
    used: ResultUsed,
) TransError!Node {
    switch (ty.getTypeClass()) {
        .Builtin => {
            const builtin_ty = @ptrCast(*const clang.BuiltinType, ty);

            switch (builtin_ty.getKind()) {
                .Bool => return node,
                .Char_U,
                .UChar,
                .Char_S,
                .SChar,
                .UShort,
                .UInt,
                .ULong,
                .ULongLong,
                .Short,
                .Int,
                .Long,
                .LongLong,
                .UInt128,
                .Int128,
                .Float,
                .Double,
                .Float128,
                .LongDouble,
                .WChar_U,
                .Char8,
                .Char16,
                .Char32,
                .WChar_S,
                .Float16,
                => {
                    // node != 0
                    return Tag.not_equal.create(c.arena, .{ .lhs = node, .rhs = Tag.zero_literal.init() });
                },
                .NullPtr => {
                    // node == null
                    return Tag.equal.create(c.arena, .{ .lhs = node, .rhs = Tag.null_literal.init() });
                },
                else => {},
            }
        },
        .Pointer => {
            // node == null
            return Tag.equal.create(c.arena, .{ .lhs = node, .rhs = Tag.null_literal.init() });
        },
        .Typedef => {
            const typedef_ty = @ptrCast(*const clang.TypedefType, ty);
            const typedef_decl = typedef_ty.getDecl();
            const underlying_type = typedef_decl.getUnderlyingType();
            return finishBoolExpr(c, scope, loc, underlying_type.getTypePtr(), node, used);
        },
        .Enum => {
            // node != 0
            return Tag.not_equal.create(c.arena, .{ .lhs = node, .rhs = Tag.zero_literal.init() });
        },
        .Elaborated => {
            const elaborated_ty = @ptrCast(*const clang.ElaboratedType, ty);
            const named_type = elaborated_ty.getNamedType();
            return finishBoolExpr(c, scope, loc, named_type.getTypePtr(), node, used);
        },
        else => {},
    }
    return fail(c, error.UnsupportedType, loc, "unsupported bool expression type", .{});
}

const SuppressCast = enum {
    with_as,
    no_as,
};
fn transIntegerLiteral(
    c: *Context,
    scope: *Scope,
    expr: *const clang.IntegerLiteral,
    result_used: ResultUsed,
    suppress_as: SuppressCast,
) TransError!Node {
    var eval_result: clang.ExprEvalResult = undefined;
    if (!expr.EvaluateAsInt(&eval_result, c.clang_context)) {
        const loc = expr.getBeginLoc();
        return fail(c, error.UnsupportedTranslation, loc, "invalid integer literal", .{});
    }

    if (suppress_as == .no_as) {
        const int_lit_node = try transCreateNodeAPInt(c, eval_result.Val.getInt());
        return maybeSuppressResult(c, scope, result_used, int_lit_node);
    }

    // Integer literals in C have types, and this can matter for several reasons.
    // For example, this is valid C:
    //     unsigned char y = 256;
    // How this gets evaluated is the 256 is an integer, which gets truncated to signed char, then bit-casted
    // to unsigned char, resulting in 0. In order for this to work, we have to emit this zig code:
    //     var y = @bitCast(u8, @truncate(i8, @as(c_int, 256)));
    // Ideally in translate-c we could flatten this out to simply:
    //     var y: u8 = 0;
    // But the first step is to be correct, and the next step is to make the output more elegant.

    // @as(T, x)
    const expr_base = @ptrCast(*const clang.Expr, expr);
    const ty_node = try transQualType(c, expr_base.getType(), expr_base.getBeginLoc());
    const rhs = try transCreateNodeAPInt(c, eval_result.Val.getInt());
    const as = try Tag.as.create(c.arena, .{ .lhs = ty_node, .rhs = rhs });
    return maybeSuppressResult(c, scope, result_used, as);
}

fn transReturnStmt(
    c: *Context,
    scope: *Scope,
    expr: *const clang.ReturnStmt,
) TransError!Node {
    const val_expr = expr.getRetValue() orelse
        return Tag.return_void.init();

    var rhs = try transExprCoercing(c, scope, val_expr, .used);
    const return_qt = scope.findBlockReturnType(c);
    if (isBoolRes(rhs) and !qualTypeIsBoolean(return_qt)) {
        rhs = try Tag.bool_to_int.create(c.arena, rhs);
    }
    return Tag.@"return".create(c.arena, rhs);
}

fn transStringLiteral(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.StringLiteral,
    result_used: ResultUsed,
) TransError!Node {
    const kind = stmt.getKind();
    switch (kind) {
        .Ascii, .UTF8 => {
            var len: usize = undefined;
            const bytes_ptr = stmt.getString_bytes_begin_size(&len);

            const str = try std.fmt.allocPrint(c.arena, "\"{}\"", .{std.zig.fmtEscapes(bytes_ptr[0..len])});
            const node = try Tag.string_literal.create(c.arena, str);
            return maybeSuppressResult(c, scope, result_used, node);
        },
        .UTF16, .UTF32, .Wide => {
            const str_type = @tagName(stmt.getKind());
            const name = try std.fmt.allocPrint(c.arena, "zig.{s}_string_{d}", .{ str_type, c.getMangle() });
            const lit_array = try transStringLiteralAsArray(c, scope, stmt, stmt.getLength() + 1);

            const decl = try Tag.var_simple.create(c.arena, .{ .name = name, .init = lit_array });
            try scope.appendNode(decl);
            const node = try Tag.identifier.create(c.arena, name);
            return maybeSuppressResult(c, scope, result_used, node);
        },
    }
}

/// Parse the size of an array back out from an ast Node.
fn zigArraySize(c: *Context, node: Node) TransError!usize {
    if (node.castTag(.array_type)) |array| {
        return array.data.len;
    }
    return error.UnsupportedTranslation;
}

/// Translate a string literal to an array of integers. Used when an
/// array is initialized from a string literal. `array_size` is the
/// size of the array being initialized. If the string literal is larger
/// than the array, truncate the string. If the array is larger than the
/// string literal, pad the array with 0's
fn transStringLiteralAsArray(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.StringLiteral,
    array_size: usize,
) TransError!Node {
    if (array_size == 0) return error.UnsupportedType;

    const str_length = stmt.getLength();

    const expr_base = @ptrCast(*const clang.Expr, stmt);
    const ty = expr_base.getType().getTypePtr();
    const const_arr_ty = @ptrCast(*const clang.ConstantArrayType, ty);

    const arr_type = try transQualType(c, const_arr_ty.getElementType(), expr_base.getBeginLoc());
    const init_list = try c.arena.alloc(Node, array_size);

    var i: c_uint = 0;
    const kind = stmt.getKind();
    const narrow = kind == .Ascii or kind == .UTF8;
    while (i < str_length and i < array_size) : (i += 1) {
        const code_unit = stmt.getCodeUnit(i);
        init_list[i] = try transCreateCharLitNode(c, narrow, code_unit);
    }
    while (i < array_size) : (i += 1) {
        init_list[i] = try transCreateNodeNumber(c, 0);
    }

    return Tag.array_init.create(c.arena, init_list);
}

fn cIsEnum(qt: clang.QualType) bool {
    return qt.getCanonicalType().getTypeClass() == .Enum;
}

/// Get the underlying int type of an enum. The C compiler chooses a signed int
/// type that is large enough to hold all of the enum's values. It is not required
/// to be the smallest possible type that can hold all the values.
fn cIntTypeForEnum(enum_qt: clang.QualType) clang.QualType {
    assert(cIsEnum(enum_qt));
    const ty = enum_qt.getCanonicalType().getTypePtr();
    const enum_ty = @ptrCast(*const clang.EnumType, ty);
    const enum_decl = enum_ty.getDecl();
    return enum_decl.getIntegerType();
}

fn transCCast(
    c: *Context,
    scope: *Scope,
    loc: clang.SourceLocation,
    dst_type: clang.QualType,
    src_type: clang.QualType,
    expr: Node,
) !Node {
    if (qualTypeCanon(dst_type).isVoidType()) return expr;
    if (dst_type.eq(src_type)) return expr;
    if (qualTypeIsPtr(dst_type) and qualTypeIsPtr(src_type))
        return transCPtrCast(c, loc, dst_type, src_type, expr);

    const dst_node = try transQualType(c, dst_type, loc);
    if (cIsInteger(dst_type) and (cIsInteger(src_type) or cIsEnum(src_type))) {
        // 1. If src_type is an enum, determine the underlying signed int type
        // 2. Extend or truncate without changing signed-ness.
        // 3. Bit-cast to correct signed-ness
        const src_type_is_signed = cIsSignedInteger(src_type) or cIsEnum(src_type);
        const src_int_type = if (cIsInteger(src_type)) src_type else cIntTypeForEnum(src_type);
        var src_int_expr = if (cIsInteger(src_type)) expr else try Tag.enum_to_int.create(c.arena, expr);

        if (isBoolRes(src_int_expr)) {
            src_int_expr = try Tag.bool_to_int.create(c.arena, src_int_expr);
        }

        switch (cIntTypeCmp(dst_type, src_int_type)) {
            .lt => {
                // @truncate(SameSignSmallerInt, src_int_expr)
                const ty_node = try transQualTypeIntWidthOf(c, dst_type, src_type_is_signed);
                src_int_expr = try Tag.truncate.create(c.arena, .{ .lhs = ty_node, .rhs = src_int_expr });
            },
            .gt => {
                // @as(SameSignBiggerInt, src_int_expr)
                const ty_node = try transQualTypeIntWidthOf(c, dst_type, src_type_is_signed);
                src_int_expr = try Tag.as.create(c.arena, .{ .lhs = ty_node, .rhs = src_int_expr });
            },
            .eq => {
                // src_int_expr = src_int_expr
            },
        }
        // @bitCast(dest_type, intermediate_value)
        return Tag.bit_cast.create(c.arena, .{ .lhs = dst_node, .rhs = src_int_expr });
    }
    if (cIsInteger(dst_type) and qualTypeIsPtr(src_type)) {
        // @intCast(dest_type, @ptrToInt(val))
        const ptr_to_int = try Tag.ptr_to_int.create(c.arena, expr);
        return Tag.int_cast.create(c.arena, .{ .lhs = dst_node, .rhs = ptr_to_int });
    }
    if (cIsInteger(src_type) and qualTypeIsPtr(dst_type)) {
        // @intToPtr(dest_type, val)
        return Tag.int_to_ptr.create(c.arena, .{ .lhs = dst_node, .rhs = expr });
    }
    if (cIsFloating(src_type) and cIsFloating(dst_type)) {
        // @floatCast(dest_type, val)
        return Tag.float_cast.create(c.arena, .{ .lhs = dst_node, .rhs = expr });
    }
    if (cIsFloating(src_type) and !cIsFloating(dst_type)) {
        // @floatToInt(dest_type, val)
        return Tag.float_to_int.create(c.arena, .{ .lhs = dst_node, .rhs = expr });
    }
    if (!cIsFloating(src_type) and cIsFloating(dst_type)) {
        // @intToFloat(dest_type, val)
        return Tag.int_to_float.create(c.arena, .{ .lhs = dst_node, .rhs = expr });
    }
    if (qualTypeIsBoolean(src_type) and !qualTypeIsBoolean(dst_type)) {
        // @boolToInt returns either a comptime_int or a u1
        // TODO: if dst_type is 1 bit & signed (bitfield) we need @bitCast
        // instead of @as
        const bool_to_int = try Tag.bool_to_int.create(c.arena, expr);
        return Tag.as.create(c.arena, .{ .lhs = dst_node, .rhs = bool_to_int });
    }
    if (cIsEnum(dst_type)) {
        // @intToEnum(dest_type, val)
        return Tag.int_to_enum.create(c.arena, .{ .lhs = dst_node, .rhs = expr });
    }
    if (cIsEnum(src_type) and !cIsEnum(dst_type)) {
        // @enumToInt(val)
        return Tag.enum_to_int.create(c.arena, expr);
    }
    // @as(dest_type, val)
    return Tag.as.create(c.arena, .{ .lhs = dst_node, .rhs = expr });
}

fn transExpr(c: *Context, scope: *Scope, expr: *const clang.Expr, used: ResultUsed) TransError!Node {
    return transStmt(c, scope, @ptrCast(*const clang.Stmt, expr), used);
}

/// Same as `transExpr` but with the knowledge that the operand will be type coerced, and therefore
/// an `@as` would be redundant. This is used to prevent redundant `@as` in integer literals.
fn transExprCoercing(c: *Context, scope: *Scope, expr: *const clang.Expr, used: ResultUsed) TransError!Node {
    switch (@ptrCast(*const clang.Stmt, expr).getStmtClass()) {
        .IntegerLiteralClass => {
            return transIntegerLiteral(c, scope, @ptrCast(*const clang.IntegerLiteral, expr), .used, .no_as);
        },
        .CharacterLiteralClass => {
            return transCharLiteral(c, scope, @ptrCast(*const clang.CharacterLiteral, expr), .used, .no_as);
        },
        .UnaryOperatorClass => {
            const un_expr = @ptrCast(*const clang.UnaryOperator, expr);
            if (un_expr.getOpcode() == .Extension) {
                return transExprCoercing(c, scope, un_expr.getSubExpr(), used);
            }
        },
        else => {},
    }
    return transExpr(c, scope, expr, .used);
}

fn transInitListExprRecord(
    c: *Context,
    scope: *Scope,
    loc: clang.SourceLocation,
    expr: *const clang.InitListExpr,
    ty: *const clang.Type,
) TransError!Node {
    var is_union_type = false;
    // Unions and Structs are both represented as RecordDecl
    const record_ty = ty.getAsRecordType() orelse
        blk: {
        is_union_type = true;
        break :blk ty.getAsUnionType();
    } orelse unreachable;
    const record_decl = record_ty.getDecl();
    const record_def = record_decl.getDefinition() orelse
        unreachable;

    const ty_node = try transType(c, ty, loc);
    const init_count = expr.getNumInits();
    var field_inits = std.ArrayList(ast.Payload.ContainerInit.Initializer).init(c.gpa);
    defer field_inits.deinit();

    var init_i: c_uint = 0;
    var it = record_def.field_begin();
    const end_it = record_def.field_end();
    while (it.neq(end_it)) : (it = it.next()) {
        const field_decl = it.deref();

        // The initializer for a union type has a single entry only
        if (is_union_type and field_decl != expr.getInitializedFieldInUnion()) {
            continue;
        }

        assert(init_i < init_count);
        const elem_expr = expr.getInit(init_i);
        init_i += 1;

        // Generate the field assignment expression:
        //     .field_name = expr
        var raw_name = try c.str(@ptrCast(*const clang.NamedDecl, field_decl).getName_bytes_begin());
        if (field_decl.isAnonymousStructOrUnion()) {
            const name = c.decl_table.get(@ptrToInt(field_decl.getCanonicalDecl())).?;
            raw_name = try mem.dupe(c.arena, u8, name);
        }

        try field_inits.append(.{
            .name = raw_name,
            .value = try transExpr(c, scope, elem_expr, .used),
        });
    }

    return Tag.container_init.create(c.arena, try c.arena.dupe(ast.Payload.ContainerInit.Initializer, field_inits.items));
}

fn transInitListExprArray(
    c: *Context,
    scope: *Scope,
    loc: clang.SourceLocation,
    expr: *const clang.InitListExpr,
    ty: *const clang.Type,
) TransError!Node {
    const arr_type = ty.getAsArrayTypeUnsafe();
    const child_qt = arr_type.getElementType();
    const init_count = expr.getNumInits();
    assert(@ptrCast(*const clang.Type, arr_type).isConstantArrayType());
    const const_arr_ty = @ptrCast(*const clang.ConstantArrayType, arr_type);
    const size_ap_int = const_arr_ty.getSize();
    const all_count = size_ap_int.getLimitedValue(math.maxInt(usize));
    const leftover_count = all_count - init_count;

    if (all_count == 0) {
        return Tag.empty_array.create(c.arena, try transQualType(c, child_qt, loc));
    }

    const ty_node = try transType(c, ty, loc);
    const init_node = if (init_count != 0) blk: {
        const init_list = try c.arena.alloc(Node, init_count);

        for (init_list) |*init, i| {
            const elem_expr = expr.getInit(@intCast(c_uint, i));
            init.* = try transExpr(c, scope, elem_expr, .used);
        }
        const init_node = try Tag.array_init.create(c.arena, init_list);
        if (leftover_count == 0) {
            return init_node;
        }
        break :blk init_node;
    } else null;

    const filler_val_expr = expr.getArrayFiller();
    const filler_node = try Tag.array_filler.create(c.arena, .{
        .type = ty_node,
        .filler = try transExpr(c, scope, filler_val_expr, .used),
        .count = leftover_count,
    });

    if (init_node) |some| {
        return Tag.array_cat.create(c.arena, .{ .lhs = some, .rhs = filler_node });
    } else {
        return filler_node;
    }
}

fn transInitListExpr(
    c: *Context,
    scope: *Scope,
    expr: *const clang.InitListExpr,
    used: ResultUsed,
) TransError!Node {
    const qt = getExprQualType(c, @ptrCast(*const clang.Expr, expr));
    var qual_type = qt.getTypePtr();
    const source_loc = @ptrCast(*const clang.Expr, expr).getBeginLoc();

    if (qual_type.isRecordType()) {
        return maybeSuppressResult(c, scope, used, try transInitListExprRecord(
            c,
            scope,
            source_loc,
            expr,
            qual_type,
        ));
    } else if (qual_type.isArrayType()) {
        return maybeSuppressResult(c, scope, used, try transInitListExprArray(
            c,
            scope,
            source_loc,
            expr,
            qual_type,
        ));
    } else {
        const type_name = c.str(qual_type.getTypeClassName());
        return fail(c, error.UnsupportedType, source_loc, "unsupported initlist type: '{s}'", .{type_name});
    }
}

fn transZeroInitExpr(
    c: *Context,
    scope: *Scope,
    source_loc: clang.SourceLocation,
    ty: *const clang.Type,
) TransError!Node {
    switch (ty.getTypeClass()) {
        .Builtin => {
            const builtin_ty = @ptrCast(*const clang.BuiltinType, ty);
            switch (builtin_ty.getKind()) {
                .Bool => return Tag.false_literal.init(),
                .Char_U,
                .UChar,
                .Char_S,
                .Char8,
                .SChar,
                .UShort,
                .UInt,
                .ULong,
                .ULongLong,
                .Short,
                .Int,
                .Long,
                .LongLong,
                .UInt128,
                .Int128,
                .Float,
                .Double,
                .Float128,
                .Float16,
                .LongDouble,
                => return Tag.zero_literal.init(),
                else => return fail(c, error.UnsupportedType, source_loc, "unsupported builtin type", .{}),
            }
        },
        .Pointer => return Tag.null_literal.init(),
        .Typedef => {
            const typedef_ty = @ptrCast(*const clang.TypedefType, ty);
            const typedef_decl = typedef_ty.getDecl();
            return transZeroInitExpr(
                c,
                scope,
                source_loc,
                typedef_decl.getUnderlyingType().getTypePtr(),
            );
        },
        else => {},
    }

    return fail(c, error.UnsupportedType, source_loc, "type does not have an implicit init value", .{});
}

fn transImplicitValueInitExpr(
    c: *Context,
    scope: *Scope,
    expr: *const clang.Expr,
    used: ResultUsed,
) TransError!Node {
    const source_loc = expr.getBeginLoc();
    const qt = getExprQualType(c, expr);
    const ty = qt.getTypePtr();
    return transZeroInitExpr(c, scope, source_loc, ty);
}

fn transIfStmt(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.IfStmt,
) TransError!Node {
    // if (c) t
    // if (c) t else e
    var cond_scope = Scope.Condition{
        .base = .{
            .parent = scope,
            .id = .condition,
        },
    };
    defer cond_scope.deinit();
    const cond_expr = @ptrCast(*const clang.Expr, stmt.getCond());
    const cond = try transBoolExpr(c, &cond_scope.base, cond_expr, .used);

    const then_body = try transStmt(c, scope, stmt.getThen(), .unused);
    const else_body = if (stmt.getElse()) |expr|
        try transStmt(c, scope, expr, .unused)
    else
        null;
    return Tag.@"if".create(c.arena, .{ .cond = cond, .then = then_body, .@"else" = else_body });
}

fn transWhileLoop(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.WhileStmt,
) TransError!Node {
    var cond_scope = Scope.Condition{
        .base = .{
            .parent = scope,
            .id = .condition,
        },
    };
    defer cond_scope.deinit();
    const cond_expr = @ptrCast(*const clang.Expr, stmt.getCond());
    const cond = try transBoolExpr(c, &cond_scope.base, cond_expr, .used);

    var loop_scope = Scope{
        .parent = scope,
        .id = .loop,
    };
    const body = try transStmt(c, &loop_scope, stmt.getBody(), .unused);
    return Tag.@"while".create(c.arena, .{ .cond = cond, .body = body, .cont_expr = null });
}

fn transDoWhileLoop(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.DoStmt,
) TransError!Node {
    var loop_scope = Scope{
        .parent = scope,
        .id = .loop,
    };

    // if (!cond) break;
    var cond_scope = Scope.Condition{
        .base = .{
            .parent = scope,
            .id = .condition,
        },
    };
    defer cond_scope.deinit();
    const cond = try transBoolExpr(c, &cond_scope.base, @ptrCast(*const clang.Expr, stmt.getCond()), .used);
    const if_not_break = try Tag.if_not_break.create(c.arena, cond);

    const body_node = if (stmt.getBody().getStmtClass() == .CompoundStmtClass) blk: {
        // there's already a block in C, so we'll append our condition to it.
        // c: do {
        // c:   a;
        // c:   b;
        // c: } while(c);
        // zig: while (true) {
        // zig:   a;
        // zig:   b;
        // zig:   if (!cond) break;
        // zig: }
        const node = try transStmt(c, &loop_scope, stmt.getBody(), .unused);
        const block = node.castTag(.block).?;
        block.data.stmts.len += 1; // This is safe since we reserve one extra space in Scope.Block.complete.
        block.data.stmts[block.data.stmts.len - 1] = if_not_break;
        break :blk node;
    } else blk: {
        // the C statement is without a block, so we need to create a block to contain it.
        // c: do
        // c:   a;
        // c: while(c);
        // zig: while (true) {
        // zig:   a;
        // zig:   if (!cond) break;
        // zig: }
        const statements = try c.arena.alloc(Node, 2);
        statements[0] = try transStmt(c, &loop_scope, stmt.getBody(), .unused);
        statements[1] = if_not_break;
        break :blk try Tag.block.create(c.arena, .{ .label = null, .stmts = statements });
    };
    return Tag.while_true.create(c.arena, body_node);
}

fn transForLoop(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.ForStmt,
) TransError!Node {
    var loop_scope = Scope{
        .parent = scope,
        .id = .loop,
    };

    var block_scope: ?Scope.Block = null;
    defer if (block_scope) |*bs| bs.deinit();

    if (stmt.getInit()) |init| {
        block_scope = try Scope.Block.init(c, scope, false);
        loop_scope.parent = &block_scope.?.base;
        const init_node = try transStmt(c, &block_scope.?.base, init, .unused);
        try block_scope.?.statements.append(init_node);
    }
    var cond_scope = Scope.Condition{
        .base = .{
            .parent = &loop_scope,
            .id = .condition,
        },
    };
    defer cond_scope.deinit();

    const cond = if (stmt.getCond()) |cond|
        try transBoolExpr(c, &cond_scope.base, cond, .used)
    else
        Tag.true_literal.init();

    const cont_expr = if (stmt.getInc()) |incr|
        try transExpr(c, &cond_scope.base, incr, .unused)
    else
        null;

    const body = try transStmt(c, &loop_scope, stmt.getBody(), .unused);
    const while_node = try Tag.@"while".create(c.arena, .{ .cond = cond, .body = body, .cont_expr = cont_expr });
    if (block_scope) |*bs| {
        try bs.statements.append(while_node);
        return try bs.complete(c);
    } else {
        return while_node;
    }
}

fn transSwitch(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.SwitchStmt,
) TransError!Node {
    var cond_scope = Scope.Condition{
        .base = .{
            .parent = scope,
            .id = .condition,
        },
    };
    defer cond_scope.deinit();
    const switch_expr = try transExpr(c, &cond_scope.base, stmt.getCond(), .used);
    const switch_node = try c.arena.create(ast.Payload.Switch);
    switch_node.* = .{
        .base = .{ .tag = .@"switch" },
        .data = .{
            .cond = switch_expr,
            .cases = undefined, // set later
        },
    };

    var switch_scope = Scope.Switch{
        .base = .{
            .id = .@"switch",
            .parent = scope,
        },
        .cases = std.ArrayList(Node).init(c.gpa),
        .pending_block = undefined,
        .default_label = null,
        .switch_label = null,
    };
    defer switch_scope.cases.deinit();

    // tmp block that all statements will go before being picked up by a case or default
    var block_scope = try Scope.Block.init(c, &switch_scope.base, false);
    defer block_scope.deinit();

    // Note that we do not defer a deinit here; the switch_scope.pending_block field
    // has its own memory management. This resource is freed inside `transCase` and
    // then the final pending_block is freed at the bottom of this function with
    // pending_block.deinit().
    switch_scope.pending_block = try Scope.Block.init(c, scope, false);
    try switch_scope.pending_block.statements.append(Node.initPayload(&switch_node.base));

    const last = try transStmt(c, &block_scope.base, stmt.getBody(), .unused);

    // take all pending statements
    const last_block_stmts = last.castTag(.block).?.data.stmts;
    try switch_scope.pending_block.statements.ensureCapacity(
        switch_scope.pending_block.statements.items.len + last_block_stmts.len,
    );
    for (last_block_stmts) |n| {
        switch_scope.pending_block.statements.appendAssumeCapacity(n);
    }

    if (switch_scope.default_label == null) {
        switch_scope.switch_label = try block_scope.makeMangledName(c, "switch");
    }
    if (switch_scope.switch_label) |l| {
        switch_scope.pending_block.label = l;
    }
    if (switch_scope.default_label == null) {
        const else_prong = try Tag.switch_else.create(
            c.arena,
            try Tag.@"break".create(c.arena, switch_scope.switch_label.?),
        );
        try switch_scope.cases.append(else_prong);
    }

    switch_node.data.cases = try c.arena.dupe(Node, switch_scope.cases.items);
    const result_node = try switch_scope.pending_block.complete(c);
    switch_scope.pending_block.deinit();
    return result_node;
}

fn transCase(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.CaseStmt,
) TransError!Node {
    const block_scope = scope.findBlockScope(c) catch unreachable;
    const switch_scope = scope.getSwitch();
    const label = try block_scope.makeMangledName(c, "case");

    const expr = if (stmt.getRHS()) |rhs| blk: {
        const lhs_node = try transExpr(c, scope, stmt.getLHS(), .used);
        const rhs_node = try transExpr(c, scope, rhs, .used);

        break :blk try Tag.ellipsis3.create(c.arena, .{ .lhs = lhs_node, .rhs = rhs_node });
    } else
        try transExpr(c, scope, stmt.getLHS(), .used);

    const switch_prong = try Tag.switch_prong.create(c.arena, .{
        .lhs = expr,
        .rhs = try Tag.@"break".create(c.arena, label),
    });
    try switch_scope.cases.append(switch_prong);

    switch_scope.pending_block.label = label;

    // take all pending statements
    try switch_scope.pending_block.statements.appendSlice(block_scope.statements.items);
    block_scope.statements.shrinkAndFree(0);

    const pending_node = try switch_scope.pending_block.complete(c);
    switch_scope.pending_block.deinit();
    switch_scope.pending_block = try Scope.Block.init(c, scope, false);

    try switch_scope.pending_block.statements.append(pending_node);

    return transStmt(c, scope, stmt.getSubStmt(), .unused);
}

fn transDefault(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.DefaultStmt,
) TransError!Node {
    const block_scope = scope.findBlockScope(c) catch unreachable;
    const switch_scope = scope.getSwitch();
    switch_scope.default_label = try block_scope.makeMangledName(c, "default");

    const else_prong = try Tag.switch_else.create(
        c.arena,
        try Tag.@"break".create(c.arena, switch_scope.default_label.?),
    );
    try switch_scope.cases.append(else_prong);
    switch_scope.pending_block.label = switch_scope.default_label.?;

    // take all pending statements
    try switch_scope.pending_block.statements.appendSlice(block_scope.statements.items);
    block_scope.statements.shrinkAndFree(0);

    const pending_node = try switch_scope.pending_block.complete(c);
    switch_scope.pending_block.deinit();
    switch_scope.pending_block = try Scope.Block.init(c, scope, false);
    try switch_scope.pending_block.statements.append(pending_node);

    return transStmt(c, scope, stmt.getSubStmt(), .unused);
}

fn transConstantExpr(c: *Context, scope: *Scope, expr: *const clang.Expr, used: ResultUsed) TransError!Node {
    var result: clang.ExprEvalResult = undefined;
    if (!expr.EvaluateAsConstantExpr(&result, .EvaluateForCodeGen, c.clang_context))
        return fail(c, error.UnsupportedTranslation, expr.getBeginLoc(), "invalid constant expression", .{});

    switch (result.Val.getKind()) {
        .Int => {
            // See comment in `transIntegerLiteral` for why this code is here.
            // @as(T, x)
            const expr_base = @ptrCast(*const clang.Expr, expr);
            const as_node = try Tag.as.create(c.arena, .{
                .lhs = try transQualType(c, expr_base.getType(), expr_base.getBeginLoc()),
                .rhs = try transCreateNodeAPInt(c, result.Val.getInt()),
            });
            return maybeSuppressResult(c, scope, used, as_node);
        },
        else => {
            return fail(c, error.UnsupportedTranslation, expr.getBeginLoc(), "unsupported constant expression kind", .{});
        },
    }
}

fn transPredefinedExpr(c: *Context, scope: *Scope, expr: *const clang.PredefinedExpr, used: ResultUsed) TransError!Node {
    return transStringLiteral(c, scope, expr.getFunctionName(), used);
}

fn transCreateCharLitNode(c: *Context, narrow: bool, val: u32) TransError!Node {
    return Tag.char_literal.create(c.arena, if (narrow)
        try std.fmt.allocPrint(c.arena, "'{s}'", .{std.zig.fmtEscapes(&.{@intCast(u8, val)})})
    else
        try std.fmt.allocPrint(c.arena, "'\\u{{{x}}}'", .{val}));
}

fn transCharLiteral(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.CharacterLiteral,
    result_used: ResultUsed,
    suppress_as: SuppressCast,
) TransError!Node {
    const kind = stmt.getKind();
    const val = stmt.getValue();
    const narrow = kind == .Ascii or kind == .UTF8;
    // C has a somewhat obscure feature called multi-character character constant
    // e.g. 'abcd'
    const int_lit_node = if (kind == .Ascii and val > 255)
        try transCreateNodeNumber(c, val)
    else
        try transCreateCharLitNode(c, narrow, val);

    if (suppress_as == .no_as) {
        return maybeSuppressResult(c, scope, result_used, int_lit_node);
    }
    // See comment in `transIntegerLiteral` for why this code is here.
    // @as(T, x)
    const expr_base = @ptrCast(*const clang.Expr, stmt);
    const as_node = try Tag.as.create(c.arena, .{
        .lhs = try transQualType(c, expr_base.getType(), expr_base.getBeginLoc()),
        .rhs = int_lit_node,
    });
    return maybeSuppressResult(c, scope, result_used, as_node);
}

fn transStmtExpr(c: *Context, scope: *Scope, stmt: *const clang.StmtExpr, used: ResultUsed) TransError!Node {
    const comp = stmt.getSubStmt();
    if (used == .unused) {
        return transCompoundStmt(c, scope, comp);
    }
    var block_scope = try Scope.Block.init(c, scope, true);
    defer block_scope.deinit();

    var it = comp.body_begin();
    const end_it = comp.body_end();
    while (it != end_it - 1) : (it += 1) {
        const result = try transStmt(c, &block_scope.base, it[0], .unused);
        try block_scope.statements.append(result);
    }
    const break_node = try Tag.break_val.create(c.arena, .{
        .label = block_scope.label,
        .val = try transStmt(c, &block_scope.base, it[0], .used),
    });
    try block_scope.statements.append(break_node);
    const res = try block_scope.complete(c);
    return maybeSuppressResult(c, scope, used, res);
}

fn transMemberExpr(c: *Context, scope: *Scope, stmt: *const clang.MemberExpr, result_used: ResultUsed) TransError!Node {
    var container_node = try transExpr(c, scope, stmt.getBase(), .used);

    if (stmt.isArrow()) {
        container_node = try Tag.deref.create(c.arena, container_node);
    }

    const member_decl = stmt.getMemberDecl();
    const name = blk: {
        const decl_kind = @ptrCast(*const clang.Decl, member_decl).getKind();
        // If we're referring to a anonymous struct/enum find the bogus name
        // we've assigned to it during the RecordDecl translation
        if (decl_kind == .Field) {
            const field_decl = @ptrCast(*const clang.FieldDecl, member_decl);
            if (field_decl.isAnonymousStructOrUnion()) {
                const name = c.decl_table.get(@ptrToInt(field_decl.getCanonicalDecl())).?;
                break :blk try mem.dupe(c.arena, u8, name);
            }
        }
        const decl = @ptrCast(*const clang.NamedDecl, member_decl);
        break :blk try c.str(decl.getName_bytes_begin());
    };
    const ident = try Tag.identifier.create(c.arena, name);

    const node = try Tag.field_access.create(c.arena, .{ .lhs = container_node, .rhs = ident });
    return maybeSuppressResult(c, scope, result_used, node);
}

fn transArrayAccess(c: *Context, scope: *Scope, stmt: *const clang.ArraySubscriptExpr, result_used: ResultUsed) TransError!Node {
    var base_stmt = stmt.getBase();

    // Unwrap the base statement if it's an array decayed to a bare pointer type
    // so that we index the array itself
    if (@ptrCast(*const clang.Stmt, base_stmt).getStmtClass() == .ImplicitCastExprClass) {
        const implicit_cast = @ptrCast(*const clang.ImplicitCastExpr, base_stmt);

        if (implicit_cast.getCastKind() == .ArrayToPointerDecay) {
            base_stmt = implicit_cast.getSubExpr();
        }
    }

    const container_node = try transExpr(c, scope, base_stmt, .used);

    // cast if the index is long long or signed
    const subscr_expr = stmt.getIdx();
    const qt = getExprQualType(c, subscr_expr);
    const is_longlong = cIsLongLongInteger(qt);
    const is_signed = cIsSignedInteger(qt);

    const rhs = if (is_longlong or is_signed) blk: {
        // check if long long first so that signed long long doesn't just become unsigned long long
        var typeid_node = if (is_longlong) try Tag.identifier.create(c.arena, "usize") else try transQualTypeIntWidthOf(c, qt, false);
        break :blk try Tag.int_cast.create(c.arena, .{ .lhs = typeid_node, .rhs = try transExpr(c, scope, subscr_expr, .used) });
    } else
        try transExpr(c, scope, subscr_expr, .used);

    const node = try Tag.array_access.create(c.arena, .{
        .lhs = container_node,
        .rhs = rhs,
    });
    return maybeSuppressResult(c, scope, result_used, node);
}

/// Check if an expression is ultimately a reference to a function declaration
/// (which means it should not be unwrapped with `.?` in translated code)
fn cIsFunctionDeclRef(expr: *const clang.Expr) bool {
    switch (expr.getStmtClass()) {
        .ParenExprClass => {
            const op_expr = @ptrCast(*const clang.ParenExpr, expr).getSubExpr();
            return cIsFunctionDeclRef(op_expr);
        },
        .DeclRefExprClass => {
            const decl_ref = @ptrCast(*const clang.DeclRefExpr, expr);
            const value_decl = decl_ref.getDecl();
            const qt = value_decl.getType();
            return qualTypeChildIsFnProto(qt);
        },
        .ImplicitCastExprClass => {
            const implicit_cast = @ptrCast(*const clang.ImplicitCastExpr, expr);
            const cast_kind = implicit_cast.getCastKind();
            if (cast_kind == .BuiltinFnToFnPtr) return true;
            if (cast_kind == .FunctionToPointerDecay) {
                return cIsFunctionDeclRef(implicit_cast.getSubExpr());
            }
            return false;
        },
        .UnaryOperatorClass => {
            const un_op = @ptrCast(*const clang.UnaryOperator, expr);
            const opcode = un_op.getOpcode();
            return (opcode == .AddrOf or opcode == .Deref) and cIsFunctionDeclRef(un_op.getSubExpr());
        },
        else => return false,
    }
}

fn transCallExpr(c: *Context, scope: *Scope, stmt: *const clang.CallExpr, result_used: ResultUsed) TransError!Node {
    const callee = stmt.getCallee();
    var raw_fn_expr = try transExpr(c, scope, callee, .used);

    var is_ptr = false;
    const fn_ty = qualTypeGetFnProto(callee.getType(), &is_ptr);

    const fn_expr = if (is_ptr and fn_ty != null and !cIsFunctionDeclRef(callee))
        try Tag.unwrap.create(c.arena, raw_fn_expr)
    else
        raw_fn_expr;

    const num_args = stmt.getNumArgs();
    const args = try c.arena.alloc(Node, num_args);

    const c_args = stmt.getArgs();
    var i: usize = 0;
    while (i < num_args) : (i += 1) {
        var arg = try transExpr(c, scope, c_args[i], .used);

        // In C the result type of a boolean expression is int. If this result is passed as
        // an argument to a function whose parameter is also int, there is no cast. Therefore
        // in Zig we'll need to cast it from bool to u1 (which will safely coerce to c_int).
        if (fn_ty) |ty| {
            switch (ty) {
                .Proto => |fn_proto| {
                    const param_count = fn_proto.getNumParams();
                    if (i < param_count) {
                        const param_qt = fn_proto.getParamType(@intCast(c_uint, i));
                        if (isBoolRes(arg) and cIsNativeInt(param_qt)) {
                            arg = try Tag.bool_to_int.create(c.arena, arg);
                        }
                    }
                },
                else => {},
            }
        }
        args[i] = arg;
    }
    const node = try Tag.call.create(c.arena, .{ .lhs = fn_expr, .args = args });
    if (fn_ty) |ty| {
        const canon = ty.getReturnType().getCanonicalType();
        const ret_ty = canon.getTypePtr();
        if (ret_ty.isVoidType()) {
            return node;
        }
    }

    return maybeSuppressResult(c, scope, result_used, node);
}

const ClangFunctionType = union(enum) {
    Proto: *const clang.FunctionProtoType,
    NoProto: *const clang.FunctionType,

    fn getReturnType(self: @This()) clang.QualType {
        switch (@as(std.meta.Tag(@This()), self)) {
            .Proto => return self.Proto.getReturnType(),
            .NoProto => return self.NoProto.getReturnType(),
        }
    }
};

fn qualTypeGetFnProto(qt: clang.QualType, is_ptr: *bool) ?ClangFunctionType {
    const canon = qt.getCanonicalType();
    var ty = canon.getTypePtr();
    is_ptr.* = false;

    if (ty.getTypeClass() == .Pointer) {
        is_ptr.* = true;
        const child_qt = ty.getPointeeType();
        ty = child_qt.getTypePtr();
    }
    if (ty.getTypeClass() == .FunctionProto) {
        return ClangFunctionType{ .Proto = @ptrCast(*const clang.FunctionProtoType, ty) };
    }
    if (ty.getTypeClass() == .FunctionNoProto) {
        return ClangFunctionType{ .NoProto = @ptrCast(*const clang.FunctionType, ty) };
    }
    return null;
}

fn transUnaryExprOrTypeTraitExpr(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.UnaryExprOrTypeTraitExpr,
    result_used: ResultUsed,
) TransError!Node {
    const loc = stmt.getBeginLoc();
    const type_node = try transQualType(c, stmt.getTypeOfArgument(), loc);

    const kind = stmt.getKind();
    switch (kind) {
        .SizeOf => return Tag.sizeof.create(c.arena, type_node),
        .AlignOf => return Tag.alignof.create(c.arena, type_node),
        .PreferredAlignOf,
        .VecStep,
        .OpenMPRequiredSimdAlign,
        => return fail(
            c,
            error.UnsupportedTranslation,
            loc,
            "Unsupported type trait kind {}",
            .{kind},
        ),
    }
}

fn qualTypeHasWrappingOverflow(qt: clang.QualType) bool {
    if (cIsUnsignedInteger(qt)) {
        // unsigned integer overflow wraps around.
        return true;
    } else {
        // float, signed integer, and pointer overflow is undefined behavior.
        return false;
    }
}

fn transUnaryOperator(c: *Context, scope: *Scope, stmt: *const clang.UnaryOperator, used: ResultUsed) TransError!Node {
    const op_expr = stmt.getSubExpr();
    switch (stmt.getOpcode()) {
        .PostInc => if (qualTypeHasWrappingOverflow(stmt.getType()))
            return transCreatePostCrement(c, scope, stmt, .add_wrap_assign, used)
        else
            return transCreatePostCrement(c, scope, stmt, .add_assign, used),
        .PostDec => if (qualTypeHasWrappingOverflow(stmt.getType()))
            return transCreatePostCrement(c, scope, stmt, .sub_wrap_assign, used)
        else
            return transCreatePostCrement(c, scope, stmt, .sub_assign, used),
        .PreInc => if (qualTypeHasWrappingOverflow(stmt.getType()))
            return transCreatePreCrement(c, scope, stmt, .add_wrap_assign, used)
        else
            return transCreatePreCrement(c, scope, stmt, .add_assign, used),
        .PreDec => if (qualTypeHasWrappingOverflow(stmt.getType()))
            return transCreatePreCrement(c, scope, stmt, .sub_wrap_assign, used)
        else
            return transCreatePreCrement(c, scope, stmt, .sub_assign, used),
        .AddrOf => {
            if (cIsFunctionDeclRef(op_expr)) {
                return transExpr(c, scope, op_expr, used);
            }
            return Tag.address_of.create(c.arena, try transExpr(c, scope, op_expr, used));
        },
        .Deref => {
            const node = try transExpr(c, scope, op_expr, used);
            var is_ptr = false;
            const fn_ty = qualTypeGetFnProto(op_expr.getType(), &is_ptr);
            if (fn_ty != null and is_ptr)
                return node;
            const unwrapped = try Tag.unwrap.create(c.arena, node);
            return Tag.deref.create(c.arena, unwrapped);
        },
        .Plus => return transExpr(c, scope, op_expr, used),
        .Minus => {
            if (!qualTypeHasWrappingOverflow(op_expr.getType())) {
                return Tag.negate.create(c.arena, try transExpr(c, scope, op_expr, .used));
            } else if (cIsUnsignedInteger(op_expr.getType())) {
                // use -% x for unsigned integers
                return Tag.negate_wrap.create(c.arena, try transExpr(c, scope, op_expr, .used));
            } else
                return fail(c, error.UnsupportedTranslation, stmt.getBeginLoc(), "C negation with non float non integer", .{});
        },
        .Not => {
            return Tag.bit_not.create(c.arena, try transExpr(c, scope, op_expr, .used));
        },
        .LNot => {
            return Tag.not.create(c.arena, try transExpr(c, scope, op_expr, .used));
        },
        .Extension => {
            return transExpr(c, scope, stmt.getSubExpr(), used);
        },
        else => return fail(c, error.UnsupportedTranslation, stmt.getBeginLoc(), "unsupported C translation {}", .{stmt.getOpcode()}),
    }
}

fn transCreatePreCrement(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.UnaryOperator,
    op: Tag,
    used: ResultUsed,
) TransError!Node {
    const op_expr = stmt.getSubExpr();

    if (used == .unused) {
        // common case
        // c: ++expr
        // zig: expr += 1
        const lhs = try transExpr(c, scope, op_expr, .used);
        const rhs = Tag.one_literal.init();
        return transCreateNodeInfixOp(c, scope, op, lhs, rhs, .used);
    }
    // worst case
    // c: ++expr
    // zig: (blk: {
    // zig:     const _ref = &expr;
    // zig:     _ref.* += 1;
    // zig:     break :blk _ref.*
    // zig: })
    var block_scope = try Scope.Block.init(c, scope, true);
    defer block_scope.deinit();
    const ref = try block_scope.makeMangledName(c, "ref");

    const expr = try transExpr(c, scope, op_expr, .used);
    const addr_of = try Tag.address_of.create(c.arena, expr);
    const ref_decl = try Tag.var_simple.create(c.arena, .{ .name = ref, .init = addr_of });
    try block_scope.statements.append(ref_decl);

    const lhs_node = try Tag.identifier.create(c.arena, ref);
    const ref_node = try Tag.deref.create(c.arena, lhs_node);
    const node = try transCreateNodeInfixOp(c, scope, op, ref_node, Tag.one_literal.init(), .used);
    try block_scope.statements.append(node);

    const break_node = try Tag.break_val.create(c.arena, .{
        .label = block_scope.label,
        .val = ref_node,
    });
    try block_scope.statements.append(break_node);
    return block_scope.complete(c);
}

fn transCreatePostCrement(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.UnaryOperator,
    op: Tag,
    used: ResultUsed,
) TransError!Node {
    const op_expr = stmt.getSubExpr();

    if (used == .unused) {
        // common case
        // c: expr++
        // zig: expr += 1
        const lhs = try transExpr(c, scope, op_expr, .used);
        const rhs = Tag.one_literal.init();
        return transCreateNodeInfixOp(c, scope, op, lhs, rhs, .used);
    }
    // worst case
    // c: expr++
    // zig: (blk: {
    // zig:     const _ref = &expr;
    // zig:     const _tmp = _ref.*;
    // zig:     _ref.* += 1;
    // zig:     break :blk _tmp
    // zig: })
    var block_scope = try Scope.Block.init(c, scope, true);
    defer block_scope.deinit();
    const ref = try block_scope.makeMangledName(c, "ref");

    const expr = try transExpr(c, scope, op_expr, .used);
    const addr_of = try Tag.address_of.create(c.arena, expr);
    const ref_decl = try Tag.var_simple.create(c.arena, .{ .name = ref, .init = addr_of });
    try block_scope.statements.append(ref_decl);

    const lhs_node = try Tag.identifier.create(c.arena, ref);
    const ref_node = try Tag.deref.create(c.arena, lhs_node);

    const tmp = try block_scope.makeMangledName(c, "tmp");
    const tmp_decl = try Tag.var_simple.create(c.arena, .{ .name = tmp, .init = ref_node });
    try block_scope.statements.append(tmp_decl);

    const node = try transCreateNodeInfixOp(c, scope, op, ref_node, Tag.one_literal.init(), .used);
    try block_scope.statements.append(node);

    const break_node = try Tag.break_val.create(c.arena, .{
        .label = block_scope.label,
        .val = try Tag.identifier.create(c.arena, tmp),
    });
    try block_scope.statements.append(break_node);
    return block_scope.complete(c);
}

fn transCompoundAssignOperator(c: *Context, scope: *Scope, stmt: *const clang.CompoundAssignOperator, used: ResultUsed) TransError!Node {
    switch (stmt.getOpcode()) {
        .MulAssign => if (qualTypeHasWrappingOverflow(stmt.getType()))
            return transCreateCompoundAssign(c, scope, stmt, .mul_wrap_assign, used)
        else
            return transCreateCompoundAssign(c, scope, stmt, .mul_assign, used),
        .AddAssign => if (qualTypeHasWrappingOverflow(stmt.getType()))
            return transCreateCompoundAssign(c, scope, stmt, .add_wrap_assign, used)
        else
            return transCreateCompoundAssign(c, scope, stmt, .add_assign, used),
        .SubAssign => if (qualTypeHasWrappingOverflow(stmt.getType()))
            return transCreateCompoundAssign(c, scope, stmt, .sub_wrap_assign, used)
        else
            return transCreateCompoundAssign(c, scope, stmt, .sub_assign, used),
        .DivAssign => return transCreateCompoundAssign(c, scope, stmt, .div_assign, used),
        .RemAssign => return transCreateCompoundAssign(c, scope, stmt, .mod_assign, used),
        .ShlAssign => return transCreateCompoundAssign(c, scope, stmt, .shl_assign, used),
        .ShrAssign => return transCreateCompoundAssign(c, scope, stmt, .shr_assign, used),
        .AndAssign => return transCreateCompoundAssign(c, scope, stmt, .bit_and_assign, used),
        .XorAssign => return transCreateCompoundAssign(c, scope, stmt, .bit_xor_assign, used),
        .OrAssign => return transCreateCompoundAssign(c, scope, stmt, .bit_or_assign, used),
        else => return fail(
            c,
            error.UnsupportedTranslation,
            stmt.getBeginLoc(),
            "unsupported C translation {}",
            .{stmt.getOpcode()},
        ),
    }
}

fn transCreateCompoundAssign(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.CompoundAssignOperator,
    op: Tag,
    used: ResultUsed,
) TransError!Node {
    const is_shift = op == .shl_assign or op == .shr_assign;
    const is_div = op == .div_assign;
    const is_mod = op == .mod_assign;
    const lhs = stmt.getLHS();
    const rhs = stmt.getRHS();
    const loc = stmt.getBeginLoc();
    const lhs_qt = getExprQualType(c, lhs);
    const rhs_qt = getExprQualType(c, rhs);
    const is_signed = cIsSignedInteger(lhs_qt);
    const requires_int_cast = blk: {
        const are_integers = cIsInteger(lhs_qt) and cIsInteger(rhs_qt);
        const are_same_sign = cIsSignedInteger(lhs_qt) == cIsSignedInteger(rhs_qt);
        break :blk are_integers and !are_same_sign;
    };
    if (used == .unused) {
        // common case
        // c: lhs += rhs
        // zig: lhs += rhs
        if ((is_mod or is_div) and is_signed) {
            const lhs_node = try transExpr(c, scope, lhs, .used);
            const rhs_node = try transExpr(c, scope, rhs, .used);
            const builtin = if (is_mod)
                try Tag.rem.create(c.arena, .{ .lhs = lhs_node, .rhs = rhs_node })
            else
                try Tag.div_trunc.create(c.arena, .{ .lhs = lhs_node, .rhs = rhs_node });

            return transCreateNodeInfixOp(c, scope, .assign, lhs_node, builtin, .used);
        }

        const lhs_node = try transExpr(c, scope, lhs, .used);
        var rhs_node = if (is_shift or requires_int_cast)
            try transExprCoercing(c, scope, rhs, .used)
        else
            try transExpr(c, scope, rhs, .used);

        if (is_shift or requires_int_cast) {
            // @intCast(rhs)
            const cast_to_type = if (is_shift)
                try qualTypeToLog2IntRef(c, getExprQualType(c, rhs), loc)
            else
                try transQualType(c, getExprQualType(c, lhs), loc);

            rhs_node = try Tag.int_cast.create(c.arena, .{ .lhs = cast_to_type, .rhs = rhs_node });
        }

        return transCreateNodeInfixOp(c, scope, op, lhs_node, rhs_node, .used);
    }
    // worst case
    // c:   lhs += rhs
    // zig: (blk: {
    // zig:     const _ref = &lhs;
    // zig:     _ref.* += rhs;
    // zig:     break :blk _ref.*
    // zig: })
    var block_scope = try Scope.Block.init(c, scope, true);
    defer block_scope.deinit();
    const ref = try block_scope.makeMangledName(c, "ref");

    const expr = try transExpr(c, scope, lhs, .used);
    const addr_of = try Tag.address_of.create(c.arena, expr);
    const ref_decl = try Tag.var_simple.create(c.arena, .{ .name = ref, .init = addr_of });
    try block_scope.statements.append(ref_decl);

    const lhs_node = try Tag.identifier.create(c.arena, ref);
    const ref_node = try Tag.deref.create(c.arena, lhs_node);

    if ((is_mod or is_div) and is_signed) {
        const rhs_node = try transExpr(c, scope, rhs, .used);
        const builtin = if (is_mod)
            try Tag.rem.create(c.arena, .{ .lhs = lhs_node, .rhs = rhs_node })
        else
            try Tag.div_trunc.create(c.arena, .{ .lhs = lhs_node, .rhs = rhs_node });

        const assign = try transCreateNodeInfixOp(c, scope, .assign, lhs_node, builtin, .used);
        try block_scope.statements.append(assign);
    } else {
        var rhs_node = try transExpr(c, scope, rhs, .used);

        if (is_shift or requires_int_cast) {
            // @intCast(rhs)
            const cast_to_type = if (is_shift)
                try qualTypeToLog2IntRef(c, getExprQualType(c, rhs), loc)
            else
                try transQualType(c, getExprQualType(c, lhs), loc);

            rhs_node = try Tag.int_cast.create(c.arena, .{ .lhs = cast_to_type, .rhs = rhs_node });
        }

        const assign = try transCreateNodeInfixOp(c, scope, op, ref_node, rhs_node, .used);
        try block_scope.statements.append(assign);
    }

    const break_node = try Tag.break_val.create(c.arena, .{
        .label = block_scope.label,
        .val = ref_node,
    });
    try block_scope.statements.append(break_node);
    return block_scope.complete(c);
}

fn transCPtrCast(
    c: *Context,
    loc: clang.SourceLocation,
    dst_type: clang.QualType,
    src_type: clang.QualType,
    expr: Node,
) !Node {
    const ty = dst_type.getTypePtr();
    const child_type = ty.getPointeeType();
    const src_ty = src_type.getTypePtr();
    const src_child_type = src_ty.getPointeeType();
    const dst_type_node = try transType(c, ty, loc);

    if ((src_child_type.isConstQualified() and
        !child_type.isConstQualified()) or
        (src_child_type.isVolatileQualified() and
        !child_type.isVolatileQualified()))
    {
        // Casting away const or volatile requires us to use @intToPtr
        const ptr_to_int = try Tag.ptr_to_int.create(c.arena, expr);
        const int_to_ptr = try Tag.int_to_ptr.create(c.arena, .{ .lhs = dst_type_node, .rhs = ptr_to_int });
        return int_to_ptr;
    } else {
        // Implicit downcasting from higher to lower alignment values is forbidden,
        // use @alignCast to side-step this problem
        const rhs = if (qualTypeCanon(child_type).isVoidType())
            // void has 1-byte alignment, so @alignCast is not needed
            expr
        else if (typeIsOpaque(c, qualTypeCanon(child_type), loc))
            // For opaque types a ptrCast is enough
            expr
        else blk: {
            const child_type_node = try transQualType(c, child_type, loc);
            const alignof = try Tag.alignof.create(c.arena, child_type_node);
            const align_cast = try Tag.align_cast.create(c.arena, .{ .lhs = alignof, .rhs = expr });
            break :blk align_cast;
        };
        return Tag.ptr_cast.create(c.arena, .{ .lhs = dst_type_node, .rhs = rhs });
    }
}

fn transBreak(c: *Context, scope: *Scope) TransError!Node {
    const break_scope = scope.getBreakableScope();
    const label_text: ?[]const u8 = if (break_scope.id == .@"switch") blk: {
        const swtch = @fieldParentPtr(Scope.Switch, "base", break_scope);
        const block_scope = try scope.findBlockScope(c);
        swtch.switch_label = try block_scope.makeMangledName(c, "switch");
        break :blk swtch.switch_label;
    } else
        null;

    return Tag.@"break".create(c.arena, label_text);
}

fn transFloatingLiteral(c: *Context, scope: *Scope, stmt: *const clang.FloatingLiteral, used: ResultUsed) TransError!Node {
    // TODO use something more accurate
    const dbl = stmt.getValueAsApproximateDouble();
    const node = try transCreateNodeNumber(c, dbl);
    return maybeSuppressResult(c, scope, used, node);
}

fn transBinaryConditionalOperator(c: *Context, scope: *Scope, stmt: *const clang.BinaryConditionalOperator, used: ResultUsed) TransError!Node {
    // GNU extension of the ternary operator where the middle expression is
    // omitted, the conditition itself is returned if it evaluates to true
    const qt = @ptrCast(*const clang.Expr, stmt).getType();
    const res_is_bool = qualTypeIsBoolean(qt);
    const casted_stmt = @ptrCast(*const clang.AbstractConditionalOperator, stmt);
    const cond_expr = casted_stmt.getCond();
    const true_expr = casted_stmt.getTrueExpr();
    const false_expr = casted_stmt.getFalseExpr();

    // c:   (cond_expr)?:(false_expr)
    // zig: (blk: {
    //          const _cond_temp = (cond_expr);
    //          break :blk if (_cond_temp) _cond_temp else (false_expr);
    //      })
    var block_scope = try Scope.Block.init(c, scope, true);
    defer block_scope.deinit();

    const mangled_name = try block_scope.makeMangledName(c, "cond_temp");
    const init_node = try transExpr(c, &block_scope.base, cond_expr, .used);
    const ref_decl = try Tag.var_simple.create(c.arena, .{ .name = mangled_name, .init = init_node });
    try block_scope.statements.append(ref_decl);

    var cond_scope = Scope.Condition{
        .base = .{
            .parent = &block_scope.base,
            .id = .condition,
        },
    };
    defer cond_scope.deinit();
    const cond_node = try transBoolExpr(c, &cond_scope.base, cond_expr, .used);
    var then_body = try Tag.identifier.create(c.arena, mangled_name);
    if (!res_is_bool and isBoolRes(init_node)) {
        then_body = try Tag.bool_to_int.create(c.arena, then_body);
    }

    var else_body = try transExpr(c, &block_scope.base, false_expr, .used);
    if (!res_is_bool and isBoolRes(else_body)) {
        else_body = try Tag.bool_to_int.create(c.arena, else_body);
    }
    const if_node = try Tag.@"if".create(c.arena, .{
        .cond = cond_node,
        .then = then_body,
        .@"else" = else_body,
    });
    const break_node = try Tag.break_val.create(c.arena, .{
        .label = block_scope.label,
        .val = if_node,
    });
    try block_scope.statements.append(break_node);
    const res = try block_scope.complete(c);
    return maybeSuppressResult(c, scope, used, res);
}

fn transConditionalOperator(c: *Context, scope: *Scope, stmt: *const clang.ConditionalOperator, used: ResultUsed) TransError!Node {
    var cond_scope = Scope.Condition{
        .base = .{
            .parent = scope,
            .id = .condition,
        },
    };
    defer cond_scope.deinit();

    const qt = @ptrCast(*const clang.Expr, stmt).getType();
    const res_is_bool = qualTypeIsBoolean(qt);
    const casted_stmt = @ptrCast(*const clang.AbstractConditionalOperator, stmt);
    const cond_expr = casted_stmt.getCond();
    const true_expr = casted_stmt.getTrueExpr();
    const false_expr = casted_stmt.getFalseExpr();

    const cond = try transBoolExpr(c, &cond_scope.base, cond_expr, .used);

    var then_body = try transExpr(c, scope, true_expr, .used);
    if (!res_is_bool and isBoolRes(then_body)) {
        then_body = try Tag.bool_to_int.create(c.arena, then_body);
    }

    var else_body = try transExpr(c, scope, false_expr, .used);
    if (!res_is_bool and isBoolRes(else_body)) {
        else_body = try Tag.bool_to_int.create(c.arena, else_body);
    }

    const if_node = try Tag.@"if".create(c.arena, .{
        .cond = cond,
        .then = then_body,
        .@"else" = else_body,
    });
    return maybeSuppressResult(c, scope, used, if_node);
}

fn maybeSuppressResult(
    c: *Context,
    scope: *Scope,
    used: ResultUsed,
    result: Node,
) TransError!Node {
    if (used == .used) return result;
    return Tag.ignore.create(c.arena, result);
}

fn addTopLevelDecl(c: *Context, name: []const u8, decl_node: Node) !void {
    _ = try c.global_scope.sym_table.put(name, decl_node);
}

/// Translate a qual type for a variable with an initializer. The initializer
/// only matters for incomplete arrays, since the size of the array is determined
/// by the size of the initializer
fn transQualTypeInitialized(
    c: *Context,
    qt: clang.QualType,
    decl_init: *const clang.Expr,
    source_loc: clang.SourceLocation,
) TypeError!Node {
    const ty = qt.getTypePtr();
    if (ty.getTypeClass() == .IncompleteArray) {
        const incomplete_array_ty = @ptrCast(*const clang.IncompleteArrayType, ty);
        const elem_ty = try transType(c, incomplete_array_ty.getElementType().getTypePtr(), source_loc);

        switch (decl_init.getStmtClass()) {
            .StringLiteralClass => {
                const string_lit = @ptrCast(*const clang.StringLiteral, decl_init);
                const string_lit_size = string_lit.getLength() + 1; // +1 for null terminator
                const array_size = @intCast(usize, string_lit_size);
                return Tag.array_type.create(c.arena, .{ .len = array_size, .elem_type = elem_ty });
            },
            .InitListExprClass => {
                const init_expr = @ptrCast(*const clang.InitListExpr, decl_init);
                const size = init_expr.getNumInits();
                return Tag.array_type.create(c.arena, .{ .len = size, .elem_type = elem_ty });
            },
            else => {},
        }
    }
    return transQualType(c, qt, source_loc);
}

fn transQualType(c: *Context, qt: clang.QualType, source_loc: clang.SourceLocation) TypeError!Node {
    return transType(c, qt.getTypePtr(), source_loc);
}

/// Produces a Zig AST node by translating a Clang QualType, respecting the width, but modifying the signed-ness.
/// Asserts the type is an integer.
fn transQualTypeIntWidthOf(c: *Context, ty: clang.QualType, is_signed: bool) TypeError!Node {
    return transTypeIntWidthOf(c, qualTypeCanon(ty), is_signed);
}

/// Produces a Zig AST node by translating a Clang Type, respecting the width, but modifying the signed-ness.
/// Asserts the type is an integer.
fn transTypeIntWidthOf(c: *Context, ty: *const clang.Type, is_signed: bool) TypeError!Node {
    assert(ty.getTypeClass() == .Builtin);
    const builtin_ty = @ptrCast(*const clang.BuiltinType, ty);
    return Tag.type.create(c.arena, switch (builtin_ty.getKind()) {
        .Char_U, .Char_S, .UChar, .SChar, .Char8 => if (is_signed) "i8" else "u8",
        .UShort, .Short => if (is_signed) "c_short" else "c_ushort",
        .UInt, .Int => if (is_signed) "c_int" else "c_uint",
        .ULong, .Long => if (is_signed) "c_long" else "c_ulong",
        .ULongLong, .LongLong => if (is_signed) "c_longlong" else "c_ulonglong",
        .UInt128, .Int128 => if (is_signed) "i128" else "u128",
        .Char16 => if (is_signed) "i16" else "u16",
        .Char32 => if (is_signed) "i32" else "u32",
        else => unreachable, // only call this function when it has already been determined the type is int
    });
}

fn isCBuiltinType(qt: clang.QualType, kind: clang.BuiltinTypeKind) bool {
    const c_type = qualTypeCanon(qt);
    if (c_type.getTypeClass() != .Builtin)
        return false;
    const builtin_ty = @ptrCast(*const clang.BuiltinType, c_type);
    return builtin_ty.getKind() == kind;
}

fn qualTypeIsPtr(qt: clang.QualType) bool {
    return qualTypeCanon(qt).getTypeClass() == .Pointer;
}

fn qualTypeIsBoolean(qt: clang.QualType) bool {
    return qualTypeCanon(qt).isBooleanType();
}

fn qualTypeIntBitWidth(c: *Context, qt: clang.QualType, source_loc: clang.SourceLocation) !u32 {
    const ty = qt.getTypePtr();

    switch (ty.getTypeClass()) {
        .Builtin => {
            const builtin_ty = @ptrCast(*const clang.BuiltinType, ty);

            switch (builtin_ty.getKind()) {
                .Char_U,
                .UChar,
                .Char_S,
                .SChar,
                => return 8,
                .UInt128,
                .Int128,
                => return 128,
                else => return 0,
            }

            unreachable;
        },
        .Typedef => {
            const typedef_ty = @ptrCast(*const clang.TypedefType, ty);
            const typedef_decl = typedef_ty.getDecl();
            const type_name = try c.str(@ptrCast(*const clang.NamedDecl, typedef_decl).getName_bytes_begin());

            if (mem.eql(u8, type_name, "uint8_t") or mem.eql(u8, type_name, "int8_t")) {
                return 8;
            } else if (mem.eql(u8, type_name, "uint16_t") or mem.eql(u8, type_name, "int16_t")) {
                return 16;
            } else if (mem.eql(u8, type_name, "uint32_t") or mem.eql(u8, type_name, "int32_t")) {
                return 32;
            } else if (mem.eql(u8, type_name, "uint64_t") or mem.eql(u8, type_name, "int64_t")) {
                return 64;
            } else {
                return 0;
            }
        },
        else => return 0,
    }

    unreachable;
}

fn qualTypeToLog2IntRef(c: *Context, qt: clang.QualType, source_loc: clang.SourceLocation) !Node {
    const int_bit_width = try qualTypeIntBitWidth(c, qt, source_loc);

    if (int_bit_width != 0) {
        // we can perform the log2 now.
        const cast_bit_width = math.log2_int(u64, int_bit_width);
        return Tag.log2_int_type.create(c.arena, cast_bit_width);
    }

    const zig_type = try transQualType(c, qt, source_loc);
    return Tag.std_math_Log2Int.create(c.arena, zig_type);
}

fn qualTypeChildIsFnProto(qt: clang.QualType) bool {
    const ty = qualTypeCanon(qt);

    switch (ty.getTypeClass()) {
        .FunctionProto, .FunctionNoProto => return true,
        else => return false,
    }
}

fn qualTypeCanon(qt: clang.QualType) *const clang.Type {
    const canon = qt.getCanonicalType();
    return canon.getTypePtr();
}

fn getExprQualType(c: *Context, expr: *const clang.Expr) clang.QualType {
    blk: {
        // If this is a C `char *`, turn it into a `const char *`
        if (expr.getStmtClass() != .ImplicitCastExprClass) break :blk;
        const cast_expr = @ptrCast(*const clang.ImplicitCastExpr, expr);
        if (cast_expr.getCastKind() != .ArrayToPointerDecay) break :blk;
        const sub_expr = cast_expr.getSubExpr();
        if (sub_expr.getStmtClass() != .StringLiteralClass) break :blk;
        const array_qt = sub_expr.getType();
        const array_type = @ptrCast(*const clang.ArrayType, array_qt.getTypePtr());
        var pointee_qt = array_type.getElementType();
        pointee_qt.addConst();
        return c.clang_context.getPointerType(pointee_qt);
    }
    return expr.getType();
}

fn typeIsOpaque(c: *Context, ty: *const clang.Type, loc: clang.SourceLocation) bool {
    switch (ty.getTypeClass()) {
        .Builtin => {
            const builtin_ty = @ptrCast(*const clang.BuiltinType, ty);
            return builtin_ty.getKind() == .Void;
        },
        .Record => {
            const record_ty = @ptrCast(*const clang.RecordType, ty);
            const record_decl = record_ty.getDecl();
            const record_def = record_decl.getDefinition() orelse
                return true;
            var it = record_def.field_begin();
            const end_it = record_def.field_end();
            while (it.neq(end_it)) : (it = it.next()) {
                const field_decl = it.deref();

                if (field_decl.isBitField()) {
                    return true;
                }
            }
            return false;
        },
        .Elaborated => {
            const elaborated_ty = @ptrCast(*const clang.ElaboratedType, ty);
            const qt = elaborated_ty.getNamedType();
            return typeIsOpaque(c, qt.getTypePtr(), loc);
        },
        .Typedef => {
            const typedef_ty = @ptrCast(*const clang.TypedefType, ty);
            const typedef_decl = typedef_ty.getDecl();
            const underlying_type = typedef_decl.getUnderlyingType();
            return typeIsOpaque(c, underlying_type.getTypePtr(), loc);
        },
        else => return false,
    }
}

fn cIsInteger(qt: clang.QualType) bool {
    return cIsSignedInteger(qt) or cIsUnsignedInteger(qt);
}

fn cIsUnsignedInteger(qt: clang.QualType) bool {
    const c_type = qualTypeCanon(qt);
    if (c_type.getTypeClass() != .Builtin) return false;
    const builtin_ty = @ptrCast(*const clang.BuiltinType, c_type);
    return switch (builtin_ty.getKind()) {
        .Char_U,
        .UChar,
        .Char_S,
        .UShort,
        .UInt,
        .ULong,
        .ULongLong,
        .UInt128,
        .WChar_U,
        => true,
        else => false,
    };
}

fn cIntTypeToIndex(qt: clang.QualType) u8 {
    const c_type = qualTypeCanon(qt);
    assert(c_type.getTypeClass() == .Builtin);
    const builtin_ty = @ptrCast(*const clang.BuiltinType, c_type);
    return switch (builtin_ty.getKind()) {
        .Bool, .Char_U, .Char_S, .UChar, .SChar, .Char8 => 1,
        .WChar_U, .WChar_S => 2,
        .UShort, .Short, .Char16 => 3,
        .UInt, .Int, .Char32 => 4,
        .ULong, .Long => 5,
        .ULongLong, .LongLong => 6,
        .UInt128, .Int128 => 7,
        else => unreachable,
    };
}

fn cIntTypeCmp(a: clang.QualType, b: clang.QualType) math.Order {
    const a_index = cIntTypeToIndex(a);
    const b_index = cIntTypeToIndex(b);
    return math.order(a_index, b_index);
}

fn cIsSignedInteger(qt: clang.QualType) bool {
    const c_type = qualTypeCanon(qt);
    if (c_type.getTypeClass() != .Builtin) return false;
    const builtin_ty = @ptrCast(*const clang.BuiltinType, c_type);
    return switch (builtin_ty.getKind()) {
        .SChar,
        .Short,
        .Int,
        .Long,
        .LongLong,
        .Int128,
        .WChar_S,
        => true,
        else => false,
    };
}

fn cIsNativeInt(qt: clang.QualType) bool {
    const c_type = qualTypeCanon(qt);
    if (c_type.getTypeClass() != .Builtin) return false;
    const builtin_ty = @ptrCast(*const clang.BuiltinType, c_type);
    return builtin_ty.getKind() == .Int;
}

fn cIsFloating(qt: clang.QualType) bool {
    const c_type = qualTypeCanon(qt);
    if (c_type.getTypeClass() != .Builtin) return false;
    const builtin_ty = @ptrCast(*const clang.BuiltinType, c_type);
    return switch (builtin_ty.getKind()) {
        .Float,
        .Double,
        .Float128,
        .LongDouble,
        => true,
        else => false,
    };
}

fn cIsLongLongInteger(qt: clang.QualType) bool {
    const c_type = qualTypeCanon(qt);
    if (c_type.getTypeClass() != .Builtin) return false;
    const builtin_ty = @ptrCast(*const clang.BuiltinType, c_type);
    return switch (builtin_ty.getKind()) {
        .LongLong, .ULongLong, .Int128, .UInt128 => true,
        else => false,
    };
}
fn transCreateNodeAssign(
    c: *Context,
    scope: *Scope,
    result_used: ResultUsed,
    lhs: *const clang.Expr,
    rhs: *const clang.Expr,
) !Node {
    // common case
    // c:   lhs = rhs
    // zig: lhs = rhs
    if (result_used == .unused) {
        const lhs_node = try transExpr(c, scope, lhs, .used);
        var rhs_node = try transExprCoercing(c, scope, rhs, .used);
        if (!exprIsBooleanType(lhs) and isBoolRes(rhs_node)) {
            rhs_node = try Tag.bool_to_int.create(c.arena, rhs_node);
        }
        return transCreateNodeInfixOp(c, scope, .assign, lhs_node, rhs_node, .used);
    }

    // worst case
    // c:   lhs = rhs
    // zig: (blk: {
    // zig:     const _tmp = rhs;
    // zig:     lhs = _tmp;
    // zig:     break :blk _tmp
    // zig: })
    var block_scope = try Scope.Block.init(c, scope, true);
    defer block_scope.deinit();

    const tmp = try block_scope.makeMangledName(c, "tmp");
    const rhs_node = try transExpr(c, scope, rhs, .used);
    const tmp_decl = try Tag.var_simple.create(c.arena, .{ .name = tmp, .init = rhs_node });
    try block_scope.statements.append(tmp_decl);

    const lhs_node = try transExpr(c, &block_scope.base, lhs, .used);
    const tmp_ident = try Tag.identifier.create(c.arena, tmp);
    const assign = try transCreateNodeInfixOp(c, &block_scope.base, .assign, lhs_node, tmp_ident, .used);
    try block_scope.statements.append(assign);

    const break_node = try Tag.break_val.create(c.arena, .{
        .label = block_scope.label,
        .val = tmp_ident,
    });
    try block_scope.statements.append(break_node);
    return block_scope.complete(c);
}

fn transCreateNodeInfixOp(
    c: *Context,
    scope: *Scope,
    op: Tag,
    lhs: Node,
    rhs: Node,
    used: ResultUsed,
) !Node {
    const payload = try c.arena.create(ast.Payload.BinOp);
    payload.* = .{
        .base = .{ .tag = op },
        .data = .{
            .lhs = lhs,
            .rhs = rhs,
        },
    };
    return maybeSuppressResult(c, scope, used, Node.initPayload(&payload.base));
}

fn transCreateNodeBoolInfixOp(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.BinaryOperator,
    op: Tag,
    used: ResultUsed,
) !Node {
    std.debug.assert(op == .@"and" or op == .@"or");

    const lhs = try transBoolExpr(c, scope, stmt.getLHS(), .used);
    const rhs = try transBoolExpr(c, scope, stmt.getRHS(), .used);

    return transCreateNodeInfixOp(c, scope, op, lhs, rhs, used);
}

fn transCreateNodeAPInt(c: *Context, int: *const clang.APSInt) !Node {
    const num_limbs = math.cast(usize, int.getNumWords()) catch |err| switch (err) {
        error.Overflow => return error.OutOfMemory,
    };
    var aps_int = int;
    const is_negative = int.isSigned() and int.isNegative();
    if (is_negative) aps_int = aps_int.negate();
    defer if (is_negative) {
        aps_int.free();
    };

    const limbs = try c.arena.alloc(math.big.Limb, num_limbs);
    defer c.arena.free(limbs);

    const data = aps_int.getRawData();
    switch (@sizeOf(math.big.Limb)) {
        8 => {
            var i: usize = 0;
            while (i < num_limbs) : (i += 1) {
                limbs[i] = data[i];
            }
        },
        4 => {
            var limb_i: usize = 0;
            var data_i: usize = 0;
            while (limb_i < num_limbs) : ({
                limb_i += 2;
                data_i += 1;
            }) {
                limbs[limb_i] = @truncate(u32, data[data_i]);
                limbs[limb_i + 1] = @truncate(u32, data[data_i] >> 32);
            }
        },
        else => @compileError("unimplemented"),
    }

    const big: math.big.int.Const = .{ .limbs = limbs, .positive = !is_negative };
    const str = big.toStringAlloc(c.arena, 10, false) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
    };
    return Tag.number_literal.create(c.arena, str);
}

fn transCreateNodeNumber(c: *Context, int: anytype) !Node {
    const fmt_s = if (comptime std.meta.trait.isNumber(@TypeOf(int))) "{d}" else "{s}";
    const str = try std.fmt.allocPrint(c.arena, fmt_s, .{int});
    return Tag.number_literal.create(c.arena, str);
}

fn transCreateNodeMacroFn(c: *Context, name: []const u8, ref: Node, proto_alias: *ast.Payload.Func) !Node {
    const scope = &c.global_scope.base;

    var fn_params = std.ArrayList(ast.Payload.Param).init(c.gpa);
    defer fn_params.deinit();

    for (proto_alias.data.params) |param, i| {
        const param_name = param.name orelse
            try std.fmt.allocPrint(c.arena, "arg_{d}", .{c.getMangle()});

        try fn_params.append(.{
            .name = param_name,
            .type = param.type,
            .is_noalias = param.is_noalias,
        });
    }

    const init = if (ref.castTag(.var_decl)) |v|
        v.data.init.?
    else if (ref.castTag(.var_simple) orelse ref.castTag(.pub_var_simple)) |v|
        v.data.init
    else
        unreachable;

    const unwrap_expr = try Tag.unwrap.create(c.arena, init);
    const args = try c.arena.alloc(Node, fn_params.items.len);
    for (fn_params.items) |param, i| {
        args[i] = try Tag.identifier.create(c.arena, param.name.?);
    }
    const call_expr = try Tag.call.create(c.arena, .{
        .lhs = unwrap_expr,
        .args = args,
    });
    const return_expr = try Tag.@"return".create(c.arena, call_expr);
    const block = try Tag.block_single.create(c.arena, return_expr);

    return Tag.pub_inline_fn.create(c.arena, .{
        .name = name,
        .params = try c.arena.dupe(ast.Payload.Param, fn_params.items),
        .return_type = proto_alias.data.return_type,
        .body = block,
    });
}

fn transCreateNodeShiftOp(
    c: *Context,
    scope: *Scope,
    stmt: *const clang.BinaryOperator,
    op: Tag,
    used: ResultUsed,
) !Node {
    std.debug.assert(op == .shl or op == .shr);

    const lhs_expr = stmt.getLHS();
    const rhs_expr = stmt.getRHS();
    const rhs_location = rhs_expr.getBeginLoc();
    // lhs >> @as(u5, rh)

    const lhs = try transExpr(c, scope, lhs_expr, .used);

    const rhs_type = try qualTypeToLog2IntRef(c, stmt.getType(), rhs_location);
    const rhs = try transExprCoercing(c, scope, rhs_expr, .used);
    const rhs_casted = try Tag.int_cast.create(c.arena, .{ .lhs = rhs_type, .rhs = rhs_type });

    return transCreateNodeInfixOp(c, scope, op, lhs, rhs_casted, used);
}

fn transType(c: *Context, ty: *const clang.Type, source_loc: clang.SourceLocation) TypeError!Node {
    switch (ty.getTypeClass()) {
        .Builtin => {
            const builtin_ty = @ptrCast(*const clang.BuiltinType, ty);
            return Tag.type.create(c.arena, switch (builtin_ty.getKind()) {
                .Void => "c_void",
                .Bool => "bool",
                .Char_U, .UChar, .Char_S, .Char8 => "u8",
                .SChar => "i8",
                .UShort => "c_ushort",
                .UInt => "c_uint",
                .ULong => "c_ulong",
                .ULongLong => "c_ulonglong",
                .Short => "c_short",
                .Int => "c_int",
                .Long => "c_long",
                .LongLong => "c_longlong",
                .UInt128 => "u128",
                .Int128 => "i128",
                .Float => "f32",
                .Double => "f64",
                .Float128 => "f128",
                .Float16 => "f16",
                .LongDouble => "c_longdouble",
                else => return fail(c, error.UnsupportedType, source_loc, "unsupported builtin type", .{}),
            });
        },
        .FunctionProto => {
            const fn_proto_ty = @ptrCast(*const clang.FunctionProtoType, ty);
            const fn_proto = try transFnProto(c, null, fn_proto_ty, source_loc, null, false);
            return Node.initPayload(&fn_proto.base);
        },
        .FunctionNoProto => {
            const fn_no_proto_ty = @ptrCast(*const clang.FunctionType, ty);
            const fn_proto = try transFnNoProto(c, fn_no_proto_ty, source_loc, null, false);
            return Node.initPayload(&fn_proto.base);
        },
        .Paren => {
            const paren_ty = @ptrCast(*const clang.ParenType, ty);
            return transQualType(c, paren_ty.getInnerType(), source_loc);
        },
        .Pointer => {
            const child_qt = ty.getPointeeType();
            if (qualTypeChildIsFnProto(child_qt)) {
                return Tag.optional_type.create(c.arena, try transQualType(c, child_qt, source_loc));
            }
            const is_const = child_qt.isConstQualified();
            const is_volatile = child_qt.isVolatileQualified();
            const elem_type = try transQualType(c, child_qt, source_loc);
            if (typeIsOpaque(c, child_qt.getTypePtr(), source_loc) or qualTypeWasDemotedToOpaque(c, child_qt)) {
                return Tag.single_pointer.create(c.arena, .{ .is_const = is_const, .is_volatile = is_volatile, .elem_type = elem_type });
            }

            return Tag.c_pointer.create(c.arena, .{ .is_const = is_const, .is_volatile = is_volatile, .elem_type = elem_type });
        },
        .ConstantArray => {
            const const_arr_ty = @ptrCast(*const clang.ConstantArrayType, ty);

            const size_ap_int = const_arr_ty.getSize();
            const size = size_ap_int.getLimitedValue(math.maxInt(usize));
            const elem_type = try transType(c, const_arr_ty.getElementType().getTypePtr(), source_loc);

            return Tag.array_type.create(c.arena, .{ .len = size, .elem_type = elem_type });
        },
        .IncompleteArray => {
            const incomplete_array_ty = @ptrCast(*const clang.IncompleteArrayType, ty);

            const child_qt = incomplete_array_ty.getElementType();
            const is_const = child_qt.isConstQualified();
            const is_volatile = child_qt.isVolatileQualified();
            const elem_type = try transQualType(c, child_qt, source_loc);

            return Tag.c_pointer.create(c.arena, .{ .is_const = is_const, .is_volatile = is_volatile, .elem_type = elem_type });
        },
        .Typedef => {
            const typedef_ty = @ptrCast(*const clang.TypedefType, ty);

            const typedef_decl = typedef_ty.getDecl();
            return (try transTypeDef(c, typedef_decl, false)) orelse
                fail(c, error.UnsupportedType, source_loc, "unable to translate typedef declaration", .{});
        },
        .Record => {
            const record_ty = @ptrCast(*const clang.RecordType, ty);

            const record_decl = record_ty.getDecl();
            return (try transRecordDecl(c, record_decl)) orelse
                fail(c, error.UnsupportedType, source_loc, "unable to resolve record declaration", .{});
        },
        .Enum => {
            const enum_ty = @ptrCast(*const clang.EnumType, ty);

            const enum_decl = enum_ty.getDecl();
            return (try transEnumDecl(c, enum_decl)) orelse
                fail(c, error.UnsupportedType, source_loc, "unable to translate enum declaration", .{});
        },
        .Elaborated => {
            const elaborated_ty = @ptrCast(*const clang.ElaboratedType, ty);
            return transQualType(c, elaborated_ty.getNamedType(), source_loc);
        },
        .Decayed => {
            const decayed_ty = @ptrCast(*const clang.DecayedType, ty);
            return transQualType(c, decayed_ty.getDecayedType(), source_loc);
        },
        .Attributed => {
            const attributed_ty = @ptrCast(*const clang.AttributedType, ty);
            return transQualType(c, attributed_ty.getEquivalentType(), source_loc);
        },
        .MacroQualified => {
            const macroqualified_ty = @ptrCast(*const clang.MacroQualifiedType, ty);
            return transQualType(c, macroqualified_ty.getModifiedType(), source_loc);
        },
        else => {
            const type_name = c.str(ty.getTypeClassName());
            return fail(c, error.UnsupportedType, source_loc, "unsupported type: '{s}'", .{type_name});
        },
    }
}

fn qualTypeWasDemotedToOpaque(c: *Context, qt: clang.QualType) bool {
    const ty = qt.getTypePtr();
    switch (qt.getTypeClass()) {
        .Typedef => {
            const typedef_ty = @ptrCast(*const clang.TypedefType, ty);

            const typedef_decl = typedef_ty.getDecl();
            const underlying_type = typedef_decl.getUnderlyingType();
            return qualTypeWasDemotedToOpaque(c, underlying_type);
        },
        .Record => {
            const record_ty = @ptrCast(*const clang.RecordType, ty);

            const record_decl = record_ty.getDecl();
            const canonical = @ptrToInt(record_decl.getCanonicalDecl());
            return c.opaque_demotes.contains(canonical);
        },
        .Enum => {
            const enum_ty = @ptrCast(*const clang.EnumType, ty);

            const enum_decl = enum_ty.getDecl();
            const canonical = @ptrToInt(enum_decl.getCanonicalDecl());
            return c.opaque_demotes.contains(canonical);
        },
        .Elaborated => {
            const elaborated_ty = @ptrCast(*const clang.ElaboratedType, ty);
            return qualTypeWasDemotedToOpaque(c, elaborated_ty.getNamedType());
        },
        .Decayed => {
            const decayed_ty = @ptrCast(*const clang.DecayedType, ty);
            return qualTypeWasDemotedToOpaque(c, decayed_ty.getDecayedType());
        },
        .Attributed => {
            const attributed_ty = @ptrCast(*const clang.AttributedType, ty);
            return qualTypeWasDemotedToOpaque(c, attributed_ty.getEquivalentType());
        },
        .MacroQualified => {
            const macroqualified_ty = @ptrCast(*const clang.MacroQualifiedType, ty);
            return qualTypeWasDemotedToOpaque(c, macroqualified_ty.getModifiedType());
        },
        else => return false,
    }
}

fn isCVoid(qt: clang.QualType) bool {
    const ty = qt.getTypePtr();
    if (ty.getTypeClass() == .Builtin) {
        const builtin_ty = @ptrCast(*const clang.BuiltinType, ty);
        return builtin_ty.getKind() == .Void;
    }
    return false;
}

const FnDeclContext = struct {
    fn_name: []const u8,
    has_body: bool,
    storage_class: clang.StorageClass,
    is_export: bool,
};

fn transCC(
    c: *Context,
    fn_ty: *const clang.FunctionType,
    source_loc: clang.SourceLocation,
) !CallingConvention {
    const clang_cc = fn_ty.getCallConv();
    switch (clang_cc) {
        .C => return CallingConvention.C,
        .X86StdCall => return CallingConvention.Stdcall,
        .X86FastCall => return CallingConvention.Fastcall,
        .X86VectorCall, .AArch64VectorCall => return CallingConvention.Vectorcall,
        .X86ThisCall => return CallingConvention.Thiscall,
        .AAPCS => return CallingConvention.AAPCS,
        .AAPCS_VFP => return CallingConvention.AAPCSVFP,
        else => return fail(
            c,
            error.UnsupportedType,
            source_loc,
            "unsupported calling convention: {s}",
            .{@tagName(clang_cc)},
        ),
    }
}

fn transFnProto(
    c: *Context,
    fn_decl: ?*const clang.FunctionDecl,
    fn_proto_ty: *const clang.FunctionProtoType,
    source_loc: clang.SourceLocation,
    fn_decl_context: ?FnDeclContext,
    is_pub: bool,
) !*ast.Payload.Func {
    const fn_ty = @ptrCast(*const clang.FunctionType, fn_proto_ty);
    const cc = try transCC(c, fn_ty, source_loc);
    const is_var_args = fn_proto_ty.isVariadic();
    return finishTransFnProto(c, fn_decl, fn_proto_ty, fn_ty, source_loc, fn_decl_context, is_var_args, cc, is_pub);
}

fn transFnNoProto(
    c: *Context,
    fn_ty: *const clang.FunctionType,
    source_loc: clang.SourceLocation,
    fn_decl_context: ?FnDeclContext,
    is_pub: bool,
) !*ast.Payload.Func {
    const cc = try transCC(c, fn_ty, source_loc);
    const is_var_args = if (fn_decl_context) |ctx| (!ctx.is_export and ctx.storage_class != .Static) else true;
    return finishTransFnProto(c, null, null, fn_ty, source_loc, fn_decl_context, is_var_args, cc, is_pub);
}

fn finishTransFnProto(
    c: *Context,
    fn_decl: ?*const clang.FunctionDecl,
    fn_proto_ty: ?*const clang.FunctionProtoType,
    fn_ty: *const clang.FunctionType,
    source_loc: clang.SourceLocation,
    fn_decl_context: ?FnDeclContext,
    is_var_args: bool,
    cc: CallingConvention,
    is_pub: bool,
) !*ast.Payload.Func {
    const is_export = if (fn_decl_context) |ctx| ctx.is_export else false;
    const is_extern = if (fn_decl_context) |ctx| !ctx.has_body else false;

    // TODO check for always_inline attribute
    // TODO check for align attribute

    var fn_params = std.ArrayList(ast.Payload.Param).init(c.gpa);
    defer fn_params.deinit();
    const param_count: usize = if (fn_proto_ty != null) fn_proto_ty.?.getNumParams() else 0;
    try fn_params.ensureCapacity(param_count);

    var i: usize = 0;
    while (i < param_count) : (i += 1) {
        const param_qt = fn_proto_ty.?.getParamType(@intCast(c_uint, i));
        const is_noalias = param_qt.isRestrictQualified();

        const param_name: ?[]const u8 =
            if (fn_decl) |decl|
        blk: {
            const param = decl.getParamDecl(@intCast(c_uint, i));
            const param_name: []const u8 = try c.str(@ptrCast(*const clang.NamedDecl, param).getName_bytes_begin());
            if (param_name.len < 1)
                break :blk null;

            break :blk param_name;
        } else null;
        const type_node = try transQualType(c, param_qt, source_loc);

        fn_params.addOneAssumeCapacity().* = .{
            .is_noalias = is_noalias,
            .name = param_name,
            .type = type_node,
        };
    }

    const linksection_string = blk: {
        if (fn_decl) |decl| {
            var str_len: usize = undefined;
            if (decl.getSectionAttribute(&str_len)) |str_ptr| {
                break :blk str_ptr[0..str_len];
            }
        }
        break :blk null;
    };

    const alignment = blk: {
        if (fn_decl) |decl| {
            const alignment = decl.getAlignedAttribute(c.clang_context);
            if (alignment != 0) {
                // Clang reports the alignment in bits
                break :blk alignment / 8;
            }
        }
        break :blk null;
    };

    const explicit_callconv = if ((is_export or is_extern) and cc == .C) null else cc;

    const return_type_node = blk: {
        if (fn_ty.getNoReturnAttr()) {
            break :blk Tag.noreturn_type.init();
        } else {
            const return_qt = fn_ty.getReturnType();
            if (isCVoid(return_qt)) {
                // convert primitive c_void to actual void (only for return type)
                break :blk Tag.void_type.init();
            } else {
                break :blk transQualType(c, return_qt, source_loc) catch |err| switch (err) {
                    error.UnsupportedType => {
                        try warn(c, &c.global_scope.base, source_loc, "unsupported function proto return type", .{});
                        return err;
                    },
                    error.OutOfMemory => |e| return e,
                };
            }
        }
    };
    const name: ?[]const u8 = if (fn_decl_context) |ctx| ctx.fn_name else null;
    const payload = try c.arena.create(ast.Payload.Func);
    payload.* = .{
        .base = .{ .tag = .func },
        .data = .{
            .is_pub = is_pub,
            .is_extern = is_extern,
            .is_export = is_export,
            .is_var_args = is_var_args,
            .name = name,
            .linksection_string = linksection_string,
            .explicit_callconv = explicit_callconv,
            .params = try c.arena.dupe(ast.Payload.Param, fn_params.items),
            .return_type = return_type_node,
            .body = null,
            .alignment = alignment,
        },
    };
    return payload;
}

fn warn(c: *Context, scope: *Scope, loc: clang.SourceLocation, comptime format: []const u8, args: anytype) !void {
    const args_prefix = .{c.locStr(loc)};
    const value = try std.fmt.allocPrint(c.arena, "// {s}: warning: " ++ format, args_prefix ++ args);
    try scope.appendNode(try Tag.warning.create(c.arena, value));
}

fn fail(
    c: *Context,
    err: anytype,
    source_loc: clang.SourceLocation,
    comptime format: []const u8,
    args: anytype,
) (@TypeOf(err) || error{OutOfMemory}) {
    try warn(c, &c.global_scope.base, source_loc, format, args);
    return err;
}

pub fn failDecl(c: *Context, loc: clang.SourceLocation, name: []const u8, comptime format: []const u8, args: anytype) Error!void {
    // location
    // pub const name = @compileError(msg);
    const location_comment = try std.fmt.allocPrint(c.arena, "// {s}", .{c.locStr(loc)});
    try c.global_scope.nodes.append(try Tag.warning.create(c.arena, location_comment));
    const fail_msg = try std.fmt.allocPrint(c.arena, format, args);
    try c.global_scope.nodes.append(try Tag.fail_decl.create(c.arena, fail_msg));
}

pub fn freeErrors(errors: []ClangErrMsg) void {
    errors.ptr.delete(errors.len);
}

fn isZigPrimitiveType(name: []const u8) bool {
    if (name.len > 1 and (name[0] == 'u' or name[0] == 'i')) {
        for (name[1..]) |c| {
            switch (c) {
                '0'...'9' => {},
                else => return false,
            }
        }
        return true;
    }
    return @import("astgen.zig").simple_types.has(name);
}

const MacroCtx = struct {
    source: []const u8,
    list: []const CToken,
    i: usize = 0,
    loc: clang.SourceLocation,
    name: []const u8,

    fn peek(self: *MacroCtx) ?CToken.Id {
        if (self.i >= self.list.len) return null;
        return self.list[self.i + 1].id;
    }

    fn next(self: *MacroCtx) ?CToken.Id {
        if (self.i >= self.list.len) return null;
        self.i += 1;
        return self.list[self.i].id;
    }

    fn slice(self: *MacroCtx) []const u8 {
        const tok = self.list[self.i];
        return self.source[tok.start..tok.end];
    }

    fn fail(self: *MacroCtx, c: *Context, comptime fmt: []const u8, args: anytype) !void {
        return failDecl(c, self.loc, self.name, fmt, args);
    }
};

fn transPreprocessorEntities(c: *Context, unit: *clang.ASTUnit) Error!void {
    // TODO if we see #undef, delete it from the table
    var it = unit.getLocalPreprocessingEntities_begin();
    const it_end = unit.getLocalPreprocessingEntities_end();
    var tok_list = std.ArrayList(CToken).init(c.gpa);
    defer tok_list.deinit();
    const scope = c.global_scope;

    while (it.I != it_end.I) : (it.I += 1) {
        const entity = it.deref();
        tok_list.items.len = 0;
        switch (entity.getKind()) {
            .MacroDefinitionKind => {
                const macro = @ptrCast(*clang.MacroDefinitionRecord, entity);
                const raw_name = macro.getName_getNameStart();
                const begin_loc = macro.getSourceRange_getBegin();

                const name = try c.str(raw_name);
                // TODO https://github.com/ziglang/zig/issues/3756
                // TODO https://github.com/ziglang/zig/issues/1802
                const mangled_name = if (isZigPrimitiveType(name)) try std.fmt.allocPrint(c.arena, "{s}_{d}", .{ name, c.getMangle() }) else name;
                if (scope.containsNow(mangled_name)) {
                    continue;
                }

                const begin_c = c.source_manager.getCharacterData(begin_loc);
                const slice = begin_c[0..mem.len(begin_c)];

                var tokenizer = std.c.Tokenizer{
                    .buffer = slice,
                };
                while (true) {
                    const tok = tokenizer.next();
                    switch (tok.id) {
                        .Nl, .Eof => {
                            try tok_list.append(tok);
                            break;
                        },
                        .LineComment, .MultiLineComment => continue,
                        else => {},
                    }
                    try tok_list.append(tok);
                }

                var macro_ctx = MacroCtx{
                    .source = slice,
                    .list = tok_list.items,
                    .name = mangled_name,
                    .loc = begin_loc,
                };
                assert(mem.eql(u8, macro_ctx.slice(), name));

                var macro_fn = false;
                switch (macro_ctx.peek().?) {
                    .Identifier => {
                        // if it equals itself, ignore. for example, from stdio.h:
                        // #define stdin stdin
                        const tok = macro_ctx.list[1];
                        if (mem.eql(u8, name, slice[tok.start..tok.end])) {
                            continue;
                        }
                    },
                    .Nl, .Eof => {
                        // this means it is a macro without a value
                        // we don't care about such things
                        continue;
                    },
                    .LParen => {
                        // if the name is immediately followed by a '(' then it is a function
                        macro_fn = macro_ctx.list[0].end == macro_ctx.list[1].start;
                    },
                    else => {},
                }

                (if (macro_fn)
                    transMacroFnDefine(c, &macro_ctx)
                else
                    transMacroDefine(c, &macro_ctx)) catch |err| switch (err) {
                    error.ParseError => continue,
                    error.OutOfMemory => |e| return e,
                };
            },
            else => {},
        }
    }
}

fn transMacroDefine(c: *Context, m: *MacroCtx) ParseError!void {
    const scope = &c.global_scope.base;

    const init_node = try parseCExpr(c, m, scope);
    const last = m.next().?;
    if (last != .Eof and last != .Nl)
        return m.fail(c, "unable to translate C expr: unexpected token .{s}", .{@tagName(last)});

    const var_decl = try Tag.pub_var_simple.create(c.arena, .{ .name = m.name, .init = init_node });
    _ = try c.global_scope.macro_table.put(m.name, var_decl);
}

fn transMacroFnDefine(c: *Context, m: *MacroCtx) ParseError!void {
    var block_scope = try Scope.Block.init(c, &c.global_scope.base, false);
    defer block_scope.deinit();
    const scope = &block_scope.base;

    if (m.next().? != .LParen) {
        return m.fail(c, "unable to translate C expr: expected '('", .{});
    }

    var fn_params = std.ArrayList(ast.Payload.Param).init(c.gpa);
    defer fn_params.deinit();

    while (true) {
        if (m.peek().? != .Identifier) break;
        _ = m.next();

        const mangled_name = try block_scope.makeMangledName(c, m.slice());
        try fn_params.append(.{
            .is_noalias = false,
            .name = mangled_name,
            .type = Tag.@"anytype".init(),
        });

        if (m.peek().? != .Comma) break;
        _ = m.next();
    }

    if (m.next().? != .RParen) {
        return m.fail(c, "unable to translate C expr: expected ')'", .{});
    }

    const expr = try parseCExpr(c, m, scope);
    const last = m.next().?;
    if (last != .Eof and last != .Nl)
        return m.fail(c, "unable to translate C expr: unexpected token .{s}", .{@tagName(last)});

    const typeof_arg = if (expr.castTag(.block)) |some| blk: {
        const stmts = some.data.stmts;
        const blk_last = stmts[stmts.len - 1];
        const br = blk_last.castTag(.break_val).?;
        break :blk br.data.val;
    } else expr;
    const typeof = try Tag.typeof.create(c.arena, typeof_arg);
    const return_expr = try Tag.@"return".create(c.arena, expr);
    try block_scope.statements.append(return_expr);

    const fn_decl = try Tag.pub_inline_fn.create(c.arena, .{
        .name = m.name,
        .params = try c.arena.dupe(ast.Payload.Param, fn_params.items),
        .return_type = typeof,
        .body = try block_scope.complete(c),
    });
    _ = try c.global_scope.macro_table.put(m.name, fn_decl);
}

const ParseError = Error || error{ParseError};

fn parseCExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    // TODO parseCAssignExpr here
    const node = try parseCCondExpr(c, m, scope);
    if (m.next().? != .Comma) {
        m.i -= 1;
        return node;
    }
    var block_scope = try Scope.Block.init(c, scope, true);
    defer block_scope.deinit();

    var last = node;
    while (true) {
        // suppress result
        const ignore = try Tag.ignore.create(c.arena, last);
        try block_scope.statements.append(ignore);

        last = try parseCCondExpr(c, m, scope);
        if (m.next().? != .Comma) {
            m.i -= 1;
            break;
        }
    }

    const break_node = try Tag.break_val.create(c.arena, .{
        .label = block_scope.label,
        .val = last,
    });
    try block_scope.statements.append(break_node);
    return try block_scope.complete(c);
}

fn parseCNumLit(c: *Context, m: *MacroCtx) ParseError!Node {
    var lit_bytes = m.slice();

    switch (m.list[m.i].id) {
        .IntegerLiteral => |suffix| {
            if (lit_bytes.len > 2 and lit_bytes[0] == '0') {
                switch (lit_bytes[1]) {
                    '0'...'7' => {
                        // Octal
                        lit_bytes = try std.fmt.allocPrint(c.arena, "0o{s}", .{lit_bytes});
                    },
                    'X' => {
                        // Hexadecimal with capital X, valid in C but not in Zig
                        lit_bytes = try std.fmt.allocPrint(c.arena, "0x{s}", .{lit_bytes[2..]});
                    },
                    else => {},
                }
            }

            if (suffix == .none) {
                return transCreateNodeNumber(c, lit_bytes);
            }

            const type_node = try Tag.type.create(c.arena, switch (suffix) {
                .u => "c_uint",
                .l => "c_long",
                .lu => "c_ulong",
                .ll => "c_longlong",
                .llu => "c_ulonglong",
                else => unreachable,
            });
            lit_bytes = lit_bytes[0 .. lit_bytes.len - switch (suffix) {
                .u, .l => @as(u8, 1),
                .lu, .ll => 2,
                .llu => 3,
                else => unreachable,
            }];
            const rhs = try transCreateNodeNumber(c, lit_bytes);
            return Tag.as.create(c.arena, .{ .lhs = type_node, .rhs = rhs });
        },
        .FloatLiteral => |suffix| {
            if (lit_bytes[0] == '.')
                lit_bytes = try std.fmt.allocPrint(c.arena, "0{s}", .{lit_bytes});
            if (suffix == .none) {
                return transCreateNodeNumber(c, lit_bytes);
            }
            const type_node = try Tag.type.create(c.arena, switch (suffix) {
                .f => "f32",
                .l => "c_longdouble",
                else => unreachable,
            });
            const rhs = try transCreateNodeNumber(c, lit_bytes[0 .. lit_bytes.len - 1]);
            return Tag.as.create(c.arena, .{ .lhs = type_node, .rhs = rhs });
        },
        else => unreachable,
    }
}

fn zigifyEscapeSequences(ctx: *Context, m: *MacroCtx) ![]const u8 {
    var source = m.slice();
    for (source) |c, i| {
        if (c == '\"' or c == '\'') {
            source = source[i..];
            break;
        }
    }
    for (source) |c| {
        if (c == '\\') {
            break;
        }
    } else return source;
    var bytes = try ctx.arena.alloc(u8, source.len * 2);
    var state: enum {
        Start,
        Escape,
        Hex,
        Octal,
    } = .Start;
    var i: usize = 0;
    var count: u8 = 0;
    var num: u8 = 0;
    for (source) |c| {
        switch (state) {
            .Escape => {
                switch (c) {
                    'n', 'r', 't', '\\', '\'', '\"' => {
                        bytes[i] = c;
                    },
                    '0'...'7' => {
                        count += 1;
                        num += c - '0';
                        state = .Octal;
                        bytes[i] = 'x';
                    },
                    'x' => {
                        state = .Hex;
                        bytes[i] = 'x';
                    },
                    'a' => {
                        bytes[i] = 'x';
                        i += 1;
                        bytes[i] = '0';
                        i += 1;
                        bytes[i] = '7';
                    },
                    'b' => {
                        bytes[i] = 'x';
                        i += 1;
                        bytes[i] = '0';
                        i += 1;
                        bytes[i] = '8';
                    },
                    'f' => {
                        bytes[i] = 'x';
                        i += 1;
                        bytes[i] = '0';
                        i += 1;
                        bytes[i] = 'C';
                    },
                    'v' => {
                        bytes[i] = 'x';
                        i += 1;
                        bytes[i] = '0';
                        i += 1;
                        bytes[i] = 'B';
                    },
                    '?' => {
                        i -= 1;
                        bytes[i] = '?';
                    },
                    'u', 'U' => {
                        try m.fail(ctx, "macro tokenizing failed: TODO unicode escape sequences", .{});
                        return error.ParseError;
                    },
                    else => {
                        try m.fail(ctx, "macro tokenizing failed: unknown escape sequence", .{});
                        return error.ParseError;
                    },
                }
                i += 1;
                if (state == .Escape)
                    state = .Start;
            },
            .Start => {
                if (c == '\\') {
                    state = .Escape;
                }
                bytes[i] = c;
                i += 1;
            },
            .Hex => {
                switch (c) {
                    '0'...'9' => {
                        num = std.math.mul(u8, num, 16) catch {
                            try m.fail(ctx, "macro tokenizing failed: hex literal overflowed", .{});
                            return error.ParseError;
                        };
                        num += c - '0';
                    },
                    'a'...'f' => {
                        num = std.math.mul(u8, num, 16) catch {
                            try m.fail(ctx, "macro tokenizing failed: hex literal overflowed", .{});
                            return error.ParseError;
                        };
                        num += c - 'a' + 10;
                    },
                    'A'...'F' => {
                        num = std.math.mul(u8, num, 16) catch {
                            try m.fail(ctx, "macro tokenizing failed: hex literal overflowed", .{});
                            return error.ParseError;
                        };
                        num += c - 'A' + 10;
                    },
                    else => {
                        i += std.fmt.formatIntBuf(bytes[i..], num, 16, false, std.fmt.FormatOptions{ .fill = '0', .width = 2 });
                        num = 0;
                        if (c == '\\')
                            state = .Escape
                        else
                            state = .Start;
                        bytes[i] = c;
                        i += 1;
                    },
                }
            },
            .Octal => {
                const accept_digit = switch (c) {
                    // The maximum length of a octal literal is 3 digits
                    '0'...'7' => count < 3,
                    else => false,
                };

                if (accept_digit) {
                    count += 1;
                    num = std.math.mul(u8, num, 8) catch {
                        try m.fail(ctx, "macro tokenizing failed: octal literal overflowed", .{});
                        return error.ParseError;
                    };
                    num += c - '0';
                } else {
                    i += std.fmt.formatIntBuf(bytes[i..], num, 16, false, std.fmt.FormatOptions{ .fill = '0', .width = 2 });
                    num = 0;
                    count = 0;
                    if (c == '\\')
                        state = .Escape
                    else
                        state = .Start;
                    bytes[i] = c;
                    i += 1;
                }
            },
        }
    }
    if (state == .Hex or state == .Octal)
        i += std.fmt.formatIntBuf(bytes[i..], num, 16, false, std.fmt.FormatOptions{ .fill = '0', .width = 2 });
    return bytes[0..i];
}

fn parseCPrimaryExprInner(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    const tok = m.next().?;
    const slice = m.slice();
    switch (tok) {
        .CharLiteral => {
            if (slice[0] != '\'' or slice[1] == '\\' or slice.len == 3) {
                return Tag.char_literal.create(c.arena, try zigifyEscapeSequences(c, m));
            } else {
                const str = try std.fmt.allocPrint(c.arena, "0x{x}", .{slice[1 .. slice.len - 1]});
                return Tag.number_literal.create(c.arena, str);
            }
        },
        .StringLiteral => {
            return Tag.string_literal.create(c.arena, try zigifyEscapeSequences(c, m));
        },
        .IntegerLiteral, .FloatLiteral => {
            return parseCNumLit(c, m);
        },
        // eventually this will be replaced by std.c.parse which will handle these correctly
        .Keyword_void => return Tag.type.create(c.arena, "c_void"),
        .Keyword_bool => return Tag.type.create(c.arena, "bool"),
        .Keyword_double => return Tag.type.create(c.arena, "f64"),
        .Keyword_long => return Tag.type.create(c.arena, "c_long"),
        .Keyword_int => return Tag.type.create(c.arena, "c_int"),
        .Keyword_float => return Tag.type.create(c.arena, "f32"),
        .Keyword_short => return Tag.type.create(c.arena, "c_short"),
        .Keyword_char => return Tag.type.create(c.arena, "u8"),
        .Keyword_unsigned => if (m.next()) |t| switch (t) {
            .Keyword_char => return Tag.type.create(c.arena, "u8"),
            .Keyword_short => return Tag.type.create(c.arena, "c_ushort"),
            .Keyword_int => return Tag.type.create(c.arena, "c_uint"),
            .Keyword_long => if (m.peek() != null and m.peek().? == .Keyword_long) {
                _ = m.next();
                return Tag.type.create(c.arena, "c_ulonglong");
            } else return Tag.type.create(c.arena, "c_ulong"),
            else => {
                m.i -= 1;
                return Tag.type.create(c.arena, "c_uint");
            },
        } else {
            return Tag.type.create(c.arena, "c_uint");
        },
        .Keyword_signed => if (m.next()) |t| switch (t) {
            .Keyword_char => return Tag.type.create(c.arena, "i8"),
            .Keyword_short => return Tag.type.create(c.arena, "c_short"),
            .Keyword_int => return Tag.type.create(c.arena, "c_int"),
            .Keyword_long => if (m.peek() != null and m.peek().? == .Keyword_long) {
                _ = m.next();
                return Tag.type.create(c.arena, "c_longlong");
            } else return Tag.type.create(c.arena, "c_long"),
            else => {
                m.i -= 1;
                return Tag.type.create(c.arena, "c_int");
            },
        } else {
            return Tag.type.create(c.arena, "c_int");
        },
        .Keyword_enum, .Keyword_struct, .Keyword_union => {
            // struct Foo will be declared as struct_Foo by transRecordDecl
            const next_id = m.next().?;
            if (next_id != .Identifier) {
                try m.fail(c, "unable to translate C expr: expected Identifier instead got: {s}", .{@tagName(next_id)});
                return error.ParseError;
            }

            const name = try std.fmt.allocPrint(c.arena, "{s}_{s}", .{ slice, m.slice() });
            return Tag.identifier.create(c.arena, name);
        },
        .Identifier => {
            const mangled_name = scope.getAlias(slice);
            return Tag.identifier.create(c.arena, builtin_typedef_map.get(mangled_name) orelse mangled_name);
        },
        .LParen => {
            const inner_node = try parseCExpr(c, m, scope);

            const next_id = m.next().?;
            if (next_id != .RParen) {
                try m.fail(c, "unable to translate C expr: expected ')' instead got: {s}", .{@tagName(next_id)});
                return error.ParseError;
            }
            var saw_l_paren = false;
            var saw_integer_literal = false;
            switch (m.peek().?) {
                // (type)(to_cast)
                .LParen => {
                    saw_l_paren = true;
                    _ = m.next();
                },
                // (type)sizeof(x)
                .Keyword_sizeof,
                // (type)alignof(x)
                .Keyword_alignof,
                // (type)identifier
                .Identifier => {},
                // (type)integer
                .IntegerLiteral => {
                    saw_integer_literal = true;
                },
                else => return inner_node,
            }
            const node_to_cast = try parseCExpr(c, m, scope);

            if (saw_l_paren and m.next().? != .RParen) {
                try m.fail(c, "unable to translate C expr: expected ')'", .{});
                return error.ParseError;
            }

            return Tag.std_meta_cast.create(c.arena, .{ .lhs = inner_node, .rhs = node_to_cast });
        },
        else => {
            try m.fail(c, "unable to translate C expr: unexpected token .{s}", .{@tagName(tok)});
            return error.ParseError;
        },
    }
}

fn parseCPrimaryExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCPrimaryExprInner(c, m, scope);
    // In C the preprocessor would handle concatting strings while expanding macros.
    // This should do approximately the same by concatting any strings and identifiers
    // after a primary expression.
    while (true) {
        switch (m.peek().?) {
            .StringLiteral, .Identifier => {},
            else => break,
        }
        node = try Tag.array_cat.create(c.arena, .{ .lhs = node, .rhs = try parseCPrimaryExprInner(c, m, scope) });
    }
    return node;
}

fn macroBoolToInt(c: *Context, node: Node) !Node {
    if (!isBoolRes(node)) {
        return node;
    }

    return Tag.bool_to_int.create(c.arena, node);
}

fn macroIntToBool(c: *Context, node: Node) !Node {
    if (isBoolRes(node)) {
        return node;
    }

    return Tag.not_equal.create(c.arena, .{ .lhs = node, .rhs = Tag.zero_literal.init() });
}

fn parseCCondExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    const node = try parseCOrExpr(c, m, scope);
    if (m.peek().? != .QuestionMark) {
        return node;
    }
    _ = m.next();

    const then_body = try parseCOrExpr(c, m, scope);
    if (m.next().? != .Colon) {
        try m.fail(c, "unable to translate C expr: expected ':'", .{});
        return error.ParseError;
    }
    const else_body = try parseCCondExpr(c, m, scope);
    return Tag.@"if".create(c.arena, .{ .cond = node, .then = then_body, .@"else" = else_body });
}

fn parseCOrExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCAndExpr(c, m, scope);
    while (m.next().? == .PipePipe) {
        const lhs = try macroIntToBool(c, node);
        const rhs = try macroIntToBool(c, try parseCAndExpr(c, m, scope));
        node = try Tag.@"or".create(c.arena, .{ .lhs = lhs, .rhs = rhs });
    }
    m.i -= 1;
    return node;
}

fn parseCAndExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCBitOrExpr(c, m, scope);
    while (m.next().? == .AmpersandAmpersand) {
        const lhs = try macroIntToBool(c, node);
        const rhs = try macroIntToBool(c, try parseCBitOrExpr(c, m, scope));
        node = try Tag.@"and".create(c.arena, .{ .lhs = lhs, .rhs = rhs });
    }
    m.i -= 1;
    return node;
}

fn parseCBitOrExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCBitXorExpr(c, m, scope);
    while (m.next().? == .Pipe) {
        const lhs = try macroBoolToInt(c, node);
        const rhs = try macroBoolToInt(c, try parseCBitXorExpr(c, m, scope));
        node = try Tag.bit_or.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
    }
    m.i -= 1;
    return node;
}

fn parseCBitXorExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCBitAndExpr(c, m, scope);
    while (m.next().? == .Caret) {
        const lhs = try macroBoolToInt(c, node);
        const rhs = try macroBoolToInt(c, try parseCBitAndExpr(c, m, scope));
        node = try Tag.bit_xor.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
    }
    m.i -= 1;
    return node;
}

fn parseCBitAndExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCEqExpr(c, m, scope);
    while (m.next().? == .Ampersand) {
        const lhs = try macroBoolToInt(c, node);
        const rhs = try macroBoolToInt(c, try parseCEqExpr(c, m, scope));
        node = try Tag.bit_and.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
    }
    m.i -= 1;
    return node;
}

fn parseCEqExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCRelExpr(c, m, scope);
    while (true) {
        switch (m.peek().?) {
            .BangEqual => {
                _ = m.next();
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCRelExpr(c, m, scope));
                node = try Tag.not_equal.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            .EqualEqual => {
                _ = m.next();
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCRelExpr(c, m, scope));
                node = try Tag.equal.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            else => return node,
        }
    }
}

fn parseCRelExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCShiftExpr(c, m, scope);
    while (true) {
        switch (m.peek().?) {
            .AngleBracketRight => {
                _ = m.next();
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCShiftExpr(c, m, scope));
                node = try Tag.greater_than.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            .AngleBracketRightEqual => {
                _ = m.next();
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCShiftExpr(c, m, scope));
                node = try Tag.greater_than_equal.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            .AngleBracketLeft => {
                _ = m.next();
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCShiftExpr(c, m, scope));
                node = try Tag.less_than.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            .AngleBracketLeftEqual => {
                _ = m.next();
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCShiftExpr(c, m, scope));
                node = try Tag.less_than_equal.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            else => return node,
        }
    }
}

fn parseCShiftExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCAddSubExpr(c, m, scope);
    while (true) {
        switch (m.peek().?) {
            .AngleBracketAngleBracketLeft => {
                _ = m.next();
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCAddSubExpr(c, m, scope));
                node = try Tag.shl.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            .AngleBracketAngleBracketRight => {
                _ = m.next();
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCAddSubExpr(c, m, scope));
                node = try Tag.shr.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            else => return node,
        }
    }
}

fn parseCAddSubExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCMulExpr(c, m, scope);
    while (true) {
        switch (m.peek().?) {
            .Plus => {
                _ = m.next();
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCMulExpr(c, m, scope));
                node = try Tag.add.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            .Minus => {
                _ = m.next();
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCMulExpr(c, m, scope));
                node = try Tag.sub.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            else => return node,
        }
    }
}

fn parseCMulExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCUnaryExpr(c, m, scope);
    while (true) {
        switch (m.next().?) {
            .Asterisk => {
                if (m.peek().? == .RParen) {
                    // type *)

                    // last token of `node`
                    const prev_id = m.list[m.i - 1].id;

                    if (prev_id == .Keyword_void) {
                        const ptr = try Tag.single_pointer.create(c.arena, .{
                            .is_const = false,
                            .is_volatile = false,
                            .elem_type = node,
                        });
                        return Tag.optional_type.create(c.arena, ptr);
                    } else {
                        return Tag.c_pointer.create(c.arena, .{
                            .is_const = false,
                            .is_volatile = false,
                            .elem_type = node,
                        });
                    }
                } else {
                    // expr * expr
                    const lhs = try macroBoolToInt(c, node);
                    const rhs = try macroBoolToInt(c, try parseCUnaryExpr(c, m, scope));
                    node = try Tag.mul.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
                }
            },
            .Slash => {
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCUnaryExpr(c, m, scope));
                node = try Tag.div.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            .Percent => {
                const lhs = try macroBoolToInt(c, node);
                const rhs = try macroBoolToInt(c, try parseCUnaryExpr(c, m, scope));
                node = try Tag.mod.create(c.arena, .{ .lhs = lhs, .rhs = rhs });
            },
            else => {
                m.i -= 1;
                return node;
            },
        }
    }
}

fn parseCPostfixExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    var node = try parseCPrimaryExpr(c, m, scope);
    while (true) {
        switch (m.next().?) {
            .Period => {
                if (m.next().? != .Identifier) {
                    try m.fail(c, "unable to translate C expr: expected identifier", .{});
                    return error.ParseError;
                }

                const ident = try Tag.identifier.create(c.arena, m.slice());
                node = try Tag.field_access.create(c.arena, .{ .lhs = node, .rhs = ident });
            },
            .Arrow => {
                if (m.next().? != .Identifier) {
                    try m.fail(c, "unable to translate C expr: expected identifier", .{});
                    return error.ParseError;
                }

                const deref = try Tag.deref.create(c.arena, node);
                const ident = try Tag.identifier.create(c.arena, m.slice());
                node = try Tag.field_access.create(c.arena, .{ .lhs = deref, .rhs = ident });
            },
            .LBracket => {
                const index = try macroBoolToInt(c, try parseCExpr(c, m, scope));
                node = try Tag.array_access.create(c.arena, .{ .lhs = node, .rhs = index });
            },
            .LParen => {
                var args = std.ArrayList(Node).init(c.gpa);
                defer args.deinit();
                while (true) {
                    const arg = try parseCCondExpr(c, m, scope);
                    try args.append(arg);
                    switch (m.next().?) {
                        .Comma => {},
                        .RParen => break,
                        else => {
                            try m.fail(c, "unable to translate C expr: expected ',' or ')'", .{});
                            return error.ParseError;
                        },
                    }
                }
                node = try Tag.call.create(c.arena, .{ .lhs = node, .args = try c.arena.dupe(Node, args.items) });
            },
            .LBrace => {
                var init_vals = std.ArrayList(Node).init(c.gpa);
                defer init_vals.deinit();

                while (true) {
                    const val = try parseCCondExpr(c, m, scope);
                    try init_vals.append(val);
                    switch (m.next().?) {
                        .Comma => {},
                        .RBrace => break,
                        else => {
                            try m.fail(c, "unable to translate C expr: expected ',' or '}}'", .{});
                            return error.ParseError;
                        },
                    }
                }
                const tuple_node = try Tag.tuple.create(c.arena, try c.arena.dupe(Node, init_vals.items));
                node = try Tag.std_mem_zeroinit.create(c.arena, .{ .lhs = node, .rhs = tuple_node });
            },
            .PlusPlus, .MinusMinus => {
                try m.fail(c, "TODO postfix inc/dec expr", .{});
                return error.ParseError;
            },
            else => {
                m.i -= 1;
                return node;
            },
        }
    }
}

fn parseCUnaryExpr(c: *Context, m: *MacroCtx, scope: *Scope) ParseError!Node {
    switch (m.next().?) {
        .Bang => {
            const operand = try macroIntToBool(c, try parseCUnaryExpr(c, m, scope));
            return Tag.not.create(c.arena, operand);
        },
        .Minus => {
            const operand = try macroBoolToInt(c, try parseCUnaryExpr(c, m, scope));
            return Tag.negate.create(c.arena, operand);
        },
        .Plus => return try parseCUnaryExpr(c, m, scope),
        .Tilde => {
            const operand = try macroBoolToInt(c, try parseCUnaryExpr(c, m, scope));
            return Tag.bit_not.create(c.arena, operand);
        },
        .Asterisk => {
            const operand = try parseCUnaryExpr(c, m, scope);
            return Tag.deref.create(c.arena, operand);
        },
        .Ampersand => {
            const operand = try parseCUnaryExpr(c, m, scope);
            return Tag.address_of.create(c.arena, operand);
        },
        .Keyword_sizeof => {
            const operand = if (m.peek().? == .LParen) blk: {
                _ = m.next();
                // C grammar says this should be 'type-name' but we have to
                // use parseCMulExpr to correctly handle pointer types.
                const inner = try parseCMulExpr(c, m, scope);
                if (m.next().? != .RParen) {
                    try m.fail(c, "unable to translate C expr: expected ')'", .{});
                    return error.ParseError;
                }
                break :blk inner;
            } else try parseCUnaryExpr(c, m, scope);

            return Tag.std_meta_sizeof.create(c.arena, operand);
        },
        .Keyword_alignof => {
            // TODO this won't work if using <stdalign.h>'s
            // #define alignof _Alignof
            if (m.next().? != .LParen) {
                try m.fail(c, "unable to translate C expr: expected '('", .{});
                return error.ParseError;
            }
            // C grammar says this should be 'type-name' but we have to
            // use parseCMulExpr to correctly handle pointer types.
            const operand = try parseCMulExpr(c, m, scope);
            if (m.next().? != .RParen) {
                try m.fail(c, "unable to translate C expr: expected ')'", .{});
                return error.ParseError;
            }

            return Tag.alignof.create(c.arena, operand);
        },
        .PlusPlus, .MinusMinus => {
            try m.fail(c, "TODO unary inc/dec expr", .{});
            return error.ParseError;
        },
        else => {
            m.i -= 1;
            return try parseCPostfixExpr(c, m, scope);
        },
    }
}

fn getContainer(c: *Context, node: Node) ?Node {
    switch (node.tag()) {
        .@"union",
        .@"struct",
        .@"enum",
        .address_of,
        .bit_not,
        .not,
        .optional_type,
        .negate,
        .negate_wrap,
        .array_type,
        .c_pointer,
        .single_pointer,
        => return node,

        .identifier => {
            const ident = node.castTag(.identifier).?;
            if (c.global_scope.sym_table.get(ident.data)) |value| {
                if (value.castTag(.var_decl)) |var_decl|
                    return getContainer(c, var_decl.data.init.?);
                if (value.castTag(.var_simple) orelse value.castTag(.pub_var_simple)) |var_decl|
                    return getContainer(c, var_decl.data.init);
            }
        },

        .field_access => {
            const infix = node.castTag(.field_access).?;

            if (getContainerTypeOf(c, infix.data.lhs)) |ty_node| {
                if (ty_node.castTag(.@"struct") orelse ty_node.castTag(.@"union")) |container| {
                    for (container.data.fields) |field| {
                        const ident = infix.data.rhs.castTag(.identifier).?;
                        if (mem.eql(u8, field.name, ident.data)) {
                            return getContainer(c, field.type);
                        }
                    }
                }
            }
        },

        else => {},
    }
    return null;
}

fn getContainerTypeOf(c: *Context, ref: Node) ?Node {
    if (ref.castTag(.identifier)) |ident| {
        if (c.global_scope.sym_table.get(ident.data)) |value| {
            if (value.castTag(.var_decl)) |var_decl| {
                return getContainer(c, var_decl.data.type);
            }
        }
    } else if (ref.castTag(.field_access)) |infix| {
        if (getContainerTypeOf(c, infix.data.lhs)) |ty_node| {
            if (ty_node.castTag(.@"struct") orelse ty_node.castTag(.@"union")) |container| {
                for (container.data.fields) |field| {
                    const ident = infix.data.rhs.castTag(.identifier).?;
                    if (mem.eql(u8, field.name, ident.data)) {
                        return getContainer(c, field.type);
                    }
                }
            } else
                return ty_node;
        }
    }
    return null;
}

fn getFnProto(c: *Context, ref: Node) ?*ast.Payload.Func {
    const init = if (ref.castTag(.var_decl)) |v|
        v.data.init orelse return null
    else if (ref.castTag(.var_simple) orelse ref.castTag(.pub_var_simple)) |v|
        v.data.init
    else
        return null;
    if (getContainerTypeOf(c, init)) |ty_node| {
        if (ty_node.castTag(.optional_type)) |prefix| {
            if (prefix.data.castTag(.func)) |fn_proto| {
                return fn_proto;
            }
        }
    }
    return null;
}

fn addMacros(c: *Context) !void {
    var it = c.global_scope.macro_table.iterator();
    while (it.next()) |kv| {
        if (getFnProto(c, kv.value)) |proto_node| {
            // If a macro aliases a global variable which is a function pointer, we conclude that
            // the macro is intended to represent a function that assumes the function pointer
            // variable is non-null and calls it.
            try addTopLevelDecl(c, kv.key, try transCreateNodeMacroFn(c, kv.key, kv.value, proto_node));
        } else {
            try addTopLevelDecl(c, kv.key, kv.value);
        }
    }
}

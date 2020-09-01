//! Semantic analysis of ZIR instructions.
//! This file operates on a `Module` instance, transforming untyped ZIR
//! instructions into semantically-analyzed IR instructions. It does type
//! checking, comptime control flow, and safety-check generation. This is the
//! the heart of the Zig compiler.
//! When deciding if something goes into this file or into Module, here is a
//! guiding principle: if it has to do with (untyped) ZIR instructions, it goes
//! here. If the analysis operates on typed IR instructions, it goes in Module.

const std = @import("std");
const mem = std.mem;
const Allocator = std.mem.Allocator;
const Value = @import("value.zig").Value;
const Type = @import("type.zig").Type;
const TypedValue = @import("TypedValue.zig");
const assert = std.debug.assert;
const ir = @import("ir.zig");
const zir = @import("zir.zig");
const Module = @import("Module.zig");
const Inst = ir.Inst;
const Body = ir.Body;
const trace = @import("tracy.zig").trace;
const Scope = Module.Scope;
const InnerError = Module.InnerError;
const Decl = Module.Decl;

/// Semantic Analysis.
/// This struct must be accessed by only 1 thread at a time.
const Sema = struct {
    module: *Module,
    src: usize,
};

pub fn analyzeInst(sema: *Sema, scope: *Scope, old_inst: *zir.Inst) InnerError!*Inst {
    switch (old_inst.tag) {
        .alloc => return sema.analyzeInstAlloc(scope, old_inst.castTag(.alloc).?),
        .alloc_inferred => return sema.analyzeInstAllocInferred(scope, old_inst.castTag(.alloc_inferred).?),
        .arg => return sema.analyzeInstArg(scope, old_inst.castTag(.arg).?),
        .bitcast_ref => return sema.analyzeInstBitCastRef(scope, old_inst.castTag(.bitcast_ref).?),
        .bitcast_result_ptr => return sema.analyzeInstBitCastResultPtr(scope, old_inst.castTag(.bitcast_result_ptr).?),
        .block => return sema.analyzeInstBlock(scope, old_inst.castTag(.block).?),
        .@"break" => return sema.analyzeInstBreak(scope, old_inst.castTag(.@"break").?),
        .breakpoint => return sema.analyzeInstBreakpoint(scope, old_inst.castTag(.breakpoint).?),
        .breakvoid => return sema.analyzeInstBreakVoid(scope, old_inst.castTag(.breakvoid).?),
        .call => return sema.analyzeInstCall(scope, old_inst.castTag(.call).?),
        .coerce_result_block_ptr => return sema.analyzeInstCoerceResultBlockPtr(scope, old_inst.castTag(.coerce_result_block_ptr).?),
        .coerce_result_ptr => return sema.analyzeInstCoerceResultPtr(scope, old_inst.castTag(.coerce_result_ptr).?),
        .coerce_to_ptr_elem => return sema.analyzeInstCoerceToPtrElem(scope, old_inst.castTag(.coerce_to_ptr_elem).?),
        .compileerror => return sema.analyzeInstCompileError(scope, old_inst.castTag(.compileerror).?),
        .@"const" => return sema.analyzeInstConst(scope, old_inst.castTag(.@"const").?),
        .dbg_stmt => return sema.analyzeInstDbgStmt(scope, old_inst.castTag(.dbg_stmt).?),
        .declref => return sema.analyzeInstDeclRef(scope, old_inst.castTag(.declref).?),
        .declref_str => return sema.analyzeInstDeclRefStr(scope, old_inst.castTag(.declref_str).?),
        .declval => return sema.analyzeInstDeclVal(scope, old_inst.castTag(.declval).?),
        .declval_in_module => return sema.analyzeInstDeclValInModule(scope, old_inst.castTag(.declval_in_module).?),
        .ensure_result_used => return sema.analyzeInstEnsureResultUsed(scope, old_inst.castTag(.ensure_result_used).?),
        .ensure_result_non_error => return sema.analyzeInstEnsureResultNonError(scope, old_inst.castTag(.ensure_result_non_error).?),
        .ensure_indexable => return sema.analyzeInstEnsureIndexable(scope, old_inst.castTag(.ensure_indexable).?),
        .ref => return sema.analyzeInstRef(scope, old_inst.castTag(.ref).?),
        .ret_ptr => return sema.analyzeInstRetPtr(scope, old_inst.castTag(.ret_ptr).?),
        .ret_type => return sema.analyzeInstRetType(scope, old_inst.castTag(.ret_type).?),
        .single_const_ptr_type => return sema.analyzeInstSimplePtrType(scope, old_inst.castTag(.single_const_ptr_type).?, false, .One),
        .single_mut_ptr_type => return sema.analyzeInstSimplePtrType(scope, old_inst.castTag(.single_mut_ptr_type).?, true, .One),
        .many_const_ptr_type => return sema.analyzeInstSimplePtrType(scope, old_inst.castTag(.many_const_ptr_type).?, false, .Many),
        .many_mut_ptr_type => return sema.analyzeInstSimplePtrType(scope, old_inst.castTag(.many_mut_ptr_type).?, true, .Many),
        .c_const_ptr_type => return sema.analyzeInstSimplePtrType(scope, old_inst.castTag(.c_const_ptr_type).?, false, .C),
        .c_mut_ptr_type => return sema.analyzeInstSimplePtrType(scope, old_inst.castTag(.c_mut_ptr_type).?, true, .C),
        .const_slice_type => return sema.analyzeInstSimplePtrType(scope, old_inst.castTag(.const_slice_type).?, false, .Slice),
        .mut_slice_type => return sema.analyzeInstSimplePtrType(scope, old_inst.castTag(.mut_slice_type).?, true, .Slice),
        .ptr_type => return sema.analyzeInstPtrType(scope, old_inst.castTag(.ptr_type).?),
        .store => return sema.analyzeInstStore(scope, old_inst.castTag(.store).?),
        .str => return sema.analyzeInstStr(scope, old_inst.castTag(.str).?),
        .int => {
            const big_int = old_inst.castTag(.int).?.positionals.int;
            return sema.module.constIntBig(scope, old_inst.src, Type.initTag(.comptime_int), big_int);
        },
        .inttype => return sema.analyzeInstIntType(scope, old_inst.castTag(.inttype).?),
        .loop => return sema.analyzeInstLoop(scope, old_inst.castTag(.loop).?),
        .param_type => return sema.analyzeInstParamType(scope, old_inst.castTag(.param_type).?),
        .ptrtoint => return sema.analyzeInstPtrToInt(scope, old_inst.castTag(.ptrtoint).?),
        .fieldptr => return sema.analyzeInstFieldPtr(scope, old_inst.castTag(.fieldptr).?),
        .deref => return sema.analyzeInstDeref(scope, old_inst.castTag(.deref).?),
        .as => return sema.analyzeInstAs(scope, old_inst.castTag(.as).?),
        .@"asm" => return sema.analyzeInstAsm(scope, old_inst.castTag(.@"asm").?),
        .@"unreachable" => return sema.analyzeInstUnreachable(scope, old_inst.castTag(.@"unreachable").?, true),
        .unreach_nocheck => return sema.analyzeInstUnreachable(scope, old_inst.castTag(.unreach_nocheck).?, false),
        .@"return" => return sema.analyzeInstRet(scope, old_inst.castTag(.@"return").?),
        .returnvoid => return sema.analyzeInstRetVoid(scope, old_inst.castTag(.returnvoid).?),
        .@"fn" => return sema.analyzeInstFn(scope, old_inst.castTag(.@"fn").?),
        .@"export" => return sema.analyzeInstExport(scope, old_inst.castTag(.@"export").?),
        .primitive => return sema.analyzeInstPrimitive(scope, old_inst.castTag(.primitive).?),
        .fntype => return sema.analyzeInstFnType(scope, old_inst.castTag(.fntype).?),
        .intcast => return sema.analyzeInstIntCast(scope, old_inst.castTag(.intcast).?),
        .bitcast => return sema.analyzeInstBitCast(scope, old_inst.castTag(.bitcast).?),
        .floatcast => return sema.analyzeInstFloatCast(scope, old_inst.castTag(.floatcast).?),
        .elemptr => return sema.analyzeInstElemPtr(scope, old_inst.castTag(.elemptr).?),
        .add => return sema.analyzeInstArithmetic(scope, old_inst.castTag(.add).?),
        .addwrap => return sema.analyzeInstArithmetic(scope, old_inst.castTag(.addwrap).?),
        .sub => return sema.analyzeInstArithmetic(scope, old_inst.castTag(.sub).?),
        .subwrap => return sema.analyzeInstArithmetic(scope, old_inst.castTag(.subwrap).?),
        .mul => return sema.analyzeInstArithmetic(scope, old_inst.castTag(.mul).?),
        .mulwrap => return sema.analyzeInstArithmetic(scope, old_inst.castTag(.mulwrap).?),
        .div => return sema.analyzeInstArithmetic(scope, old_inst.castTag(.div).?),
        .mod_rem => return sema.analyzeInstArithmetic(scope, old_inst.castTag(.mod_rem).?),
        .array_cat => return sema.analyzeInstArrayCat(scope, old_inst.castTag(.array_cat).?),
        .array_mul => return sema.analyzeInstArrayMul(scope, old_inst.castTag(.array_mul).?),
        .bitand => return sema.analyzeInstBitwise(scope, old_inst.castTag(.bitand).?),
        .bitnot => return sema.analyzeInstBitNot(scope, old_inst.castTag(.bitnot).?),
        .bitor => return sema.analyzeInstBitwise(scope, old_inst.castTag(.bitor).?),
        .xor => return sema.analyzeInstBitwise(scope, old_inst.castTag(.xor).?),
        .shl => return sema.analyzeInstShl(scope, old_inst.castTag(.shl).?),
        .shr => return sema.analyzeInstShr(scope, old_inst.castTag(.shr).?),
        .cmp_lt => return sema.analyzeInstCmp(scope, old_inst.castTag(.cmp_lt).?, .lt),
        .cmp_lte => return sema.analyzeInstCmp(scope, old_inst.castTag(.cmp_lte).?, .lte),
        .cmp_eq => return sema.analyzeInstCmp(scope, old_inst.castTag(.cmp_eq).?, .eq),
        .cmp_gte => return sema.analyzeInstCmp(scope, old_inst.castTag(.cmp_gte).?, .gte),
        .cmp_gt => return sema.analyzeInstCmp(scope, old_inst.castTag(.cmp_gt).?, .gt),
        .cmp_neq => return sema.analyzeInstCmp(scope, old_inst.castTag(.cmp_neq).?, .neq),
        .condbr => return sema.analyzeInstCondBr(scope, old_inst.castTag(.condbr).?),
        .isnull => return sema.analyzeInstIsNonNull(scope, old_inst.castTag(.isnull).?, true),
        .isnonnull => return sema.analyzeInstIsNonNull(scope, old_inst.castTag(.isnonnull).?, false),
        .iserr => return sema.analyzeInstIsErr(scope, old_inst.castTag(.iserr).?),
        .boolnot => return sema.analyzeInstBoolNot(scope, old_inst.castTag(.boolnot).?),
        .typeof => return sema.analyzeInstTypeOf(scope, old_inst.castTag(.typeof).?),
        .optional_type => return sema.analyzeInstOptionalType(scope, old_inst.castTag(.optional_type).?),
        .unwrap_optional_safe => return sema.analyzeInstUnwrapOptional(scope, old_inst.castTag(.unwrap_optional_safe).?, true),
        .unwrap_optional_unsafe => return sema.analyzeInstUnwrapOptional(scope, old_inst.castTag(.unwrap_optional_unsafe).?, false),
        .unwrap_err_safe => return sema.analyzeInstUnwrapErr(scope, old_inst.castTag(.unwrap_err_safe).?, true),
        .unwrap_err_unsafe => return sema.analyzeInstUnwrapErr(scope, old_inst.castTag(.unwrap_err_unsafe).?, false),
        .unwrap_err_code => return sema.analyzeInstUnwrapErrCode(scope, old_inst.castTag(.unwrap_err_code).?),
        .ensure_err_payload_void => return sema.analyzeInstEnsureErrPayloadVoid(scope, old_inst.castTag(.ensure_err_payload_void).?),
        .array_type => return sema.analyzeInstArrayType(scope, old_inst.castTag(.array_type).?),
        .array_type_sentinel => return sema.analyzeInstArrayTypeSentinel(scope, old_inst.castTag(.array_type_sentinel).?),
        .enum_literal => return sema.analyzeInstEnumLiteral(scope, old_inst.castTag(.enum_literal).?),
        .merge_error_sets => return sema.analyzeInstMergeErrorSets(scope, old_inst.castTag(.merge_error_sets).?),
        .error_union_type => return sema.analyzeInstErrorUnionType(scope, old_inst.castTag(.error_union_type).?),
        .anyframe_type => return sema.analyzeInstAnyframeType(scope, old_inst.castTag(.anyframe_type).?),
        .error_set => return sema.analyzeInstErrorSet(scope, old_inst.castTag(.error_set).?),
    }
}

pub fn analyzeBody(sema: *Sema, scope: *Scope, body: zir.Module.Body) !void {
    for (body.instructions) |src_inst, i| {
        const analyzed_inst = try sema.analyzeInst(scope, src_inst);
        src_inst.analyzed_inst = analyzed_inst;
        if (analyzed_inst.ty.zigTypeTag() == .NoReturn) {
            for (body.instructions[i..]) |unreachable_inst| {
                if (unreachable_inst.castTag(.dbg_stmt)) |dbg_stmt| {
                    return sema.module.failSrc(scope, dbg_stmt.positionals.src, "unreachable code", .{});
                }
            }
            break;
        }
    }
}

pub fn analyzeBodyValueAsType(sema: *Sema, block_scope: *Scope.Block, body: zir.Module.Body) !Type {
    try sema.analyzeBody(&block_scope.base, body);
    for (block_scope.instructions.items) |inst| {
        if (inst.castTag(.ret)) |ret| {
            const val = try sema.module.resolveConstValue(&block_scope.base, ret.operand);
            return val.toType(block_scope.base.arena());
        } else {
            return sema.fail(&block_scope.base, "unable to resolve comptime value", .{});
        }
    }
    unreachable;
}

pub fn analyzeZirDecl(sema: *Sema, decl: *Decl, src_decl: *zir.Decl) InnerError!bool {
    var decl_scope: Scope.DeclAnalysis = .{
        .decl = decl,
        .arena = std.heap.ArenaAllocator.init(sema.module.gpa),
    };
    errdefer decl_scope.arena.deinit();

    decl.analysis = .in_progress;

    const typed_value = try sema.analyzeConstInst(&decl_scope.base, src_decl.inst);
    const arena_state = try decl_scope.arena.allocator.create(std.heap.ArenaAllocator.State);

    var prev_type_has_bits = false;
    var type_changed = true;

    if (decl.typedValueManaged()) |tvm| {
        prev_type_has_bits = tvm.typed_value.ty.hasCodeGenBits();
        type_changed = !tvm.typed_value.ty.eql(typed_value.ty);

        tvm.deinit(sema.module.gpa);
    }

    arena_state.* = decl_scope.arena.state;
    decl.typed_value = .{
        .most_recent = .{
            .typed_value = typed_value,
            .arena = arena_state,
        },
    };
    decl.analysis = .complete;
    decl.generation = sema.module.generation;
    if (typed_value.ty.hasCodeGenBits()) {
        // We don't fully codegen the decl until later, but we do need to reserve a global
        // offset table index for it. This allows us to codegen decls out of dependency order,
        // increasing how many computations can be done in parallel.
        try sema.module.bin_file.allocateDeclIndexes(decl);
        try sema.module.work_queue.writeItem(.{ .codegen_decl = decl });
    } else if (prev_type_has_bits) {
        sema.module.bin_file.freeDecl(decl);
    }

    return type_changed;
}

pub fn resolveZirDecl(sema: *Sema, scope: *Scope, src_decl: *zir.Decl) InnerError!*Decl {
    const zir_module = sema.module.root_scope.cast(Scope.ZIRModule).?;
    const entry = zir_module.contents.module.findDecl(src_decl.name).?;
    return sema.resolveZirDeclHavingIndex(scope, src_decl, entry.index);
}

fn resolveZirDeclHavingIndex(sema: *Sema, scope: *Scope, src_decl: *zir.Decl, src_index: usize) InnerError!*Decl {
    const name_hash = scope.namespace().fullyQualifiedNameHash(src_decl.name);
    const decl = sema.module.decl_table.get(name_hash).?;
    decl.src_index = src_index;
    try sema.module.ensureDeclAnalyzed(decl);
    return decl;
}

/// Declares a dependency on the decl.
fn resolveCompleteZirDecl(sema: *Sema, scope: *Scope, src_decl: *zir.Decl) InnerError!*Decl {
    const decl = try sema.resolveZirDecl(scope, src_decl);
    switch (decl.analysis) {
        .unreferenced => unreachable,
        .in_progress => unreachable,
        .outdated => unreachable,

        .dependency_failure,
        .sema_failure,
        .sema_failure_retryable,
        .codegen_failure,
        .codegen_failure_retryable,
        => return error.AnalysisFail,

        .complete => {},
    }
    return decl;
}

/// TODO Look into removing this function. The body is only needed for .zir files, not .zig files.
pub fn resolveInst(sema: *Sema, scope: *Scope, old_inst: *zir.Inst) InnerError!*Inst {
    if (old_inst.analyzed_inst) |inst| return inst;

    // If this assert trips, the instruction that was referenced did not get properly
    // analyzed before it was referenced.
    const zir_module = scope.namespace().cast(Scope.ZIRModule).?;
    const entry = if (old_inst.cast(zir.Inst.DeclVal)) |declval| blk: {
        const decl_name = declval.positionals.name;
        const entry = zir_module.contents.module.findDecl(decl_name) orelse
            return sema.fail(scope, "decl '{}' not found", .{decl_name});
        break :blk entry;
    } else blk: {
        // If this assert trips, the instruction that was referenced did not get
        // properly analyzed by a previous instruction analysis before it was
        // referenced by the current one.
        break :blk zir_module.contents.module.findInstDecl(old_inst).?;
    };
    const decl = try sema.resolveCompleteZirDecl(scope, entry.decl);
    const decl_ref = try sema.module.analyzeDeclRef(scope, old_inst.src, decl);
    // Note: it would be tempting here to store the result into old_inst.analyzed_inst field,
    // but this would prevent the analyzeDeclRef from happening, which is needed to properly
    // detect Decl dependencies and dependency failures on updates.
    return sema.module.analyzeDeref(scope, old_inst.src, decl_ref, old_inst.src);
}

fn resolveConstString(sema: *Sema, scope: *Scope, old_inst: *zir.Inst) ![]u8 {
    const new_inst = try sema.resolveInst(scope, old_inst);
    const wanted_type = Type.initTag(.const_slice_u8);
    const coerced_inst = try sema.module.coerce(scope, wanted_type, new_inst);
    const val = try sema.module.resolveConstValue(scope, coerced_inst);
    return val.toAllocatedBytes(scope.arena());
}

fn resolveType(sema: *Sema, scope: *Scope, old_inst: *zir.Inst) !Type {
    const new_inst = try sema.resolveInst(scope, old_inst);
    const wanted_type = Type.initTag(.@"type");
    const coerced_inst = try sema.module.coerce(scope, wanted_type, new_inst);
    const val = try sema.module.resolveConstValue(scope, coerced_inst);
    return val.toType(scope.arena());
}

fn resolveInt(sema: *Sema, scope: *Scope, old_inst: *zir.Inst, dest_type: Type) !u64 {
    const new_inst = try sema.resolveInst(scope, old_inst);
    const coerced = try sema.module.coerce(scope, dest_type, new_inst);
    const val = try sema.module.resolveConstValue(scope, coerced);

    return val.toUnsignedInt();
}

pub fn resolveInstConst(sema: *Sema, scope: *Scope, old_inst: *zir.Inst) InnerError!TypedValue {
    const new_inst = try sema.resolveInst(scope, old_inst);
    const val = try sema.module.resolveConstValue(scope, new_inst);
    return TypedValue{
        .ty = new_inst.ty,
        .val = val,
    };
}

fn analyzeInstConst(sema: *Sema, scope: *Scope, const_inst: *zir.Inst.Const) InnerError!*Inst {
    // Move the TypedValue from old memory to new memory. This allows freeing the ZIR instructions
    // after analysis.
    const typed_value_copy = try const_inst.positionals.typed_value.copy(scope.arena());
    return sema.module.constInst(scope, const_inst.base.src, typed_value_copy);
}

fn analyzeConstInst(sema: *Sema, scope: *Scope, old_inst: *zir.Inst) InnerError!TypedValue {
    const new_inst = try sema.analyzeInst(scope, old_inst);
    return TypedValue{
        .ty = new_inst.ty,
        .val = try sema.module.resolveConstValue(scope, new_inst),
    };
}

fn analyzeInstCoerceResultBlockPtr(
    sema: *Sema,
    scope: *Scope,
    inst: *zir.Inst.CoerceResultBlockPtr,
) InnerError!*Inst {
    return sema.fail(scope, "TODO implement analyzeInstCoerceResultBlockPtr", .{});
}

fn analyzeInstBitCastRef(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    return sema.fail(scope, "TODO implement analyzeInstBitCastRef", .{});
}

fn analyzeInstBitCastResultPtr(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    return sema.fail(scope, "TODO implement analyzeInstBitCastResultPtr", .{});
}

fn analyzeInstCoerceResultPtr(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    return sema.fail(scope, "TODO implement analyzeInstCoerceResultPtr", .{});
}

/// Equivalent to `as(ptr_child_type(typeof(ptr)), value)`.
fn analyzeInstCoerceToPtrElem(sema: *Sema, scope: *Scope, inst: *zir.Inst.CoerceToPtrElem) InnerError!*Inst {
    const ptr = try sema.resolveInst(scope, inst.positionals.ptr);
    const operand = try sema.resolveInst(scope, inst.positionals.value);
    return sema.module.coerce(scope, ptr.ty.elemType(), operand);
}

fn analyzeInstRetPtr(sema: *Sema, scope: *Scope, inst: *zir.Inst.NoOp) InnerError!*Inst {
    return sema.module.fail(scope, inst.base.src, "TODO implement analyzeInstRetPtr", .{});
}

fn analyzeInstRef(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    const operand = try sema.resolveInst(scope, inst.positionals.operand);
    const ptr_type = try sema.module.simplePtrType(scope, inst.base.src, operand.ty, false, .One);

    if (operand.value()) |val| {
        const ref_payload = try scope.arena().create(Value.Payload.RefVal);
        ref_payload.* = .{ .val = val };

        return sema.module.constInst(scope, inst.base.src, .{
            .ty = ptr_type,
            .val = Value.initPayload(&ref_payload.base),
        });
    }

    const b = try sema.module.requireRuntimeBlock(scope);
    return sema.module.addUnOp(b, inst.base.src, ptr_type, .ref, operand);
}

fn analyzeInstRetType(sema: *Sema, scope: *Scope, inst: *zir.Inst.NoOp) InnerError!*Inst {
    const b = try sema.module.requireRuntimeBlock(scope);
    const fn_ty = b.func.?.owner_decl.typed_value.most_recent.typed_value.ty;
    const ret_type = fn_ty.fnReturnType();
    return sema.module.constType(scope, inst.base.src, ret_type);
}

fn analyzeInstEnsureResultUsed(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOpWithSrcNode) InnerError!*Inst {
    const operand = try sema.resolveInst(scope, inst.positionals.operand);
    switch (operand.ty.zigTypeTag()) {
        .Void, .NoReturn => return sema.module.constVoid(scope, operand.src),
        else => return sema.module.failNode(scope, inst.positionals.src, "expression value is ignored", .{}),
    }
}

fn analyzeInstEnsureResultNonError(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOpWithSrcNode) InnerError!*Inst {
    const operand = try sema.resolveInst(scope, inst.positionals.operand);
    switch (operand.ty.zigTypeTag()) {
        .ErrorSet, .ErrorUnion => return sema.module.failNode(scope, inst.positionals.src, "error is discarded", .{}),
        else => return sema.module.constVoid(scope, operand.src),
    }
}

fn analyzeInstEnsureIndexable(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    const operand = try sema.resolveInst(scope, inst.positionals.operand);
    const elem_ty = operand.ty.elemType();
    if (elem_ty.isIndexable()) {
        return mod.constVoid(scope, operand.src);
    } else {
        // TODO error notes
        // error: type '{}' does not support indexing
        // note: for loop operand must be an array, a slice or a tuple
        return mod.fail(scope, operand.src, "for loop operand must be an array, a slice or a tuple", .{});
    }
}

fn analyzeInstAlloc(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    const var_type = try sema.resolveType(scope, inst.positionals.operand);
    // TODO this should happen only for var allocs
    if (!var_type.isValidVarType(false)) {
        return mod.fail(scope, inst.base.src, "variable of type '{}' must be const or comptime", .{var_type});
    }
    const ptr_type = try mod.simplePtrType(scope, inst.base.src, var_type, true, .One);
    const b = try mod.requireRuntimeBlock(scope);
    return mod.addNoOp(b, inst.base.src, ptr_type, .alloc);
}

fn analyzeInstAllocInferred(sema: *Sema, scope: *Scope, inst: *zir.Inst.NoOp) InnerError!*Inst {
    return mod.fail(scope, inst.base.src, "TODO implement analyzeInstAllocInferred", .{});
}

fn analyzeInstStore(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    const ptr = try sema.resolveInst(scope, inst.positionals.lhs);
    const value = try sema.resolveInst(scope, inst.positionals.rhs);
    return mod.storePtr(scope, inst.base.src, ptr, value);
}

fn analyzeInstParamType(sema: *Sema, scope: *Scope, inst: *zir.Inst.ParamType) InnerError!*Inst {
    const fn_inst = try sema.resolveInst(scope, inst.positionals.func);
    const arg_index = inst.positionals.arg_index;

    const fn_ty: Type = switch (fn_inst.ty.zigTypeTag()) {
        .Fn => fn_inst.ty,
        .BoundFn => {
            return mod.fail(scope, fn_inst.src, "TODO implement analyzeInstParamType for method call syntax", .{});
        },
        else => {
            return mod.fail(scope, fn_inst.src, "expected function, found '{}'", .{fn_inst.ty});
        },
    };

    // TODO support C-style var args
    const param_count = fn_ty.fnParamLen();
    if (arg_index >= param_count) {
        return mod.fail(scope, inst.base.src, "arg index {} out of bounds; '{}' has {} argument(s)", .{
            arg_index,
            fn_ty,
            param_count,
        });
    }

    // TODO support generic functions
    const param_type = fn_ty.fnParamType(arg_index);
    return mod.constType(scope, inst.base.src, param_type);
}

fn analyzeInstStr(sema: *Sema, scope: *Scope, str_inst: *zir.Inst.Str) InnerError!*Inst {
    // The bytes references memory inside the ZIR module, which can get deallocated
    // after semantic analysis is complete. We need the memory to be in the new anonymous Decl's arena.
    var new_decl_arena = std.heap.ArenaAllocator.init(mod.gpa);
    errdefer new_decl_arena.deinit();
    const arena_bytes = try new_decl_arena.allocator.dupe(u8, str_inst.positionals.bytes);

    const ty_payload = try scope.arena().create(Type.Payload.Array_u8_Sentinel0);
    ty_payload.* = .{ .len = arena_bytes.len };

    const bytes_payload = try scope.arena().create(Value.Payload.Bytes);
    bytes_payload.* = .{ .data = arena_bytes };

    const new_decl = try mod.createAnonymousDecl(scope, &new_decl_arena, .{
        .ty = Type.initPayload(&ty_payload.base),
        .val = Value.initPayload(&bytes_payload.base),
    });
    return mod.analyzeDeclRef(scope, str_inst.base.src, new_decl);
}

fn analyzeInstExport(sema: *Sema, scope: *Scope, export_inst: *zir.Inst.Export) InnerError!*Inst {
    const symbol_name = try sema.resolveConstString(scope, export_inst.positionals.symbol_name);
    const exported_decl = mod.lookupDeclName(scope, export_inst.positionals.decl_name) orelse
        return mod.fail(scope, export_inst.base.src, "decl '{}' not found", .{export_inst.positionals.decl_name});
    try mod.analyzeExport(scope, export_inst.base.src, symbol_name, exported_decl);
    return mod.constVoid(scope, export_inst.base.src);
}

fn analyzeInstCompileError(sema: *Sema, scope: *Scope, inst: *zir.Inst.CompileError) InnerError!*Inst {
    return mod.fail(scope, inst.base.src, "{}", .{inst.positionals.msg});
}

fn analyzeInstArg(sema: *Sema, scope: *Scope, inst: *zir.Inst.Arg) InnerError!*Inst {
    const b = try mod.requireRuntimeBlock(scope);
    const fn_ty = b.func.?.owner_decl.typed_value.most_recent.typed_value.ty;
    const param_index = b.instructions.items.len;
    const param_count = fn_ty.fnParamLen();
    if (param_index >= param_count) {
        return mod.fail(scope, inst.base.src, "parameter index {} outside list of length {}", .{
            param_index,
            param_count,
        });
    }
    const param_type = fn_ty.fnParamType(param_index);
    const name = try scope.arena().dupeZ(u8, inst.positionals.name);
    return mod.addArg(b, inst.base.src, param_type, name);
}

fn analyzeInstLoop(sema: *Sema, scope: *Scope, inst: *zir.Inst.Loop) InnerError!*Inst {
    const parent_block = scope.cast(Scope.Block).?;

    // Reserve space for a Loop instruction so that generated Break instructions can
    // point to it, even if it doesn't end up getting used because the code ends up being
    // comptime evaluated.
    const loop_inst = try parent_block.arena.create(Inst.Loop);
    loop_inst.* = .{
        .base = .{
            .tag = Inst.Loop.base_tag,
            .ty = Type.initTag(.noreturn),
            .src = inst.base.src,
        },
        .body = undefined,
    };

    var child_block: Scope.Block = .{
        .parent = parent_block,
        .func = parent_block.func,
        .decl = parent_block.decl,
        .instructions = .{},
        .arena = parent_block.arena,
    };
    defer child_block.instructions.deinit(mod.gpa);

    try sema.analyzeBody(&child_block.base, inst.positionals.body);

    // Loop repetition is implied so the last instruction may or may not be a noreturn instruction.

    try parent_block.instructions.append(mod.gpa, &loop_inst.base);
    loop_inst.body = .{ .instructions = try parent_block.arena.dupe(*Inst, child_block.instructions.items) };
    return &loop_inst.base;
}

fn analyzeInstBlock(sema: *Sema, scope: *Scope, inst: *zir.Inst.Block) InnerError!*Inst {
    const parent_block = scope.cast(Scope.Block).?;

    // Reserve space for a Block instruction so that generated Break instructions can
    // point to it, even if it doesn't end up getting used because the code ends up being
    // comptime evaluated.
    const block_inst = try parent_block.arena.create(Inst.Block);
    block_inst.* = .{
        .base = .{
            .tag = Inst.Block.base_tag,
            .ty = undefined, // Set after analysis.
            .src = inst.base.src,
        },
        .body = undefined,
    };

    var child_block: Scope.Block = .{
        .parent = parent_block,
        .func = parent_block.func,
        .decl = parent_block.decl,
        .instructions = .{},
        .arena = parent_block.arena,
        // TODO @as here is working around a stage1 miscompilation bug :(
        .label = @as(?Scope.Block.Label, Scope.Block.Label{
            .zir_block = inst,
            .results = .{},
            .block_inst = block_inst,
        }),
    };
    const label = &child_block.label.?;

    defer child_block.instructions.deinit(mod.gpa);
    defer label.results.deinit(mod.gpa);

    try sema.analyzeBody(&child_block.base, inst.positionals.body);

    // Blocks must terminate with noreturn instruction.
    assert(child_block.instructions.items.len != 0);
    assert(child_block.instructions.items[child_block.instructions.items.len - 1].ty.isNoReturn());

    // Need to set the type and emit the Block instruction. This allows machine code generation
    // to emit a jump instruction to after the block when it encounters the break.
    try parent_block.instructions.append(mod.gpa, &block_inst.base);
    block_inst.base.ty = try mod.resolvePeerTypes(scope, label.results.items);
    block_inst.body = .{ .instructions = try parent_block.arena.dupe(*Inst, child_block.instructions.items) };
    return &block_inst.base;
}

fn analyzeInstBreakpoint(sema: *Sema, scope: *Scope, inst: *zir.Inst.NoOp) InnerError!*Inst {
    const b = try mod.requireRuntimeBlock(scope);
    return mod.addNoOp(b, inst.base.src, Type.initTag(.void), .breakpoint);
}

fn analyzeInstBreak(sema: *Sema, scope: *Scope, inst: *zir.Inst.Break) InnerError!*Inst {
    const operand = try sema.resolveInst(scope, inst.positionals.operand);
    const block = inst.positionals.block;
    return sema.analyzeBreak(scope, inst.base.src, block, operand);
}

fn analyzeInstBreakVoid(sema: *Sema, scope: *Scope, inst: *zir.Inst.BreakVoid) InnerError!*Inst {
    const block = inst.positionals.block;
    const void_inst = try mod.constVoid(scope, inst.base.src);
    return sema.analyzeBreak(scope, inst.base.src, block, void_inst);
}

fn analyzeInstDbgStmt(sema: *Sema, scope: *Scope, inst: *zir.Inst.DbgStmt) InnerError!*Inst {
    mod.src = inst.positionals.src;
    const b = try mod.requireRuntimeBlock(scope);
    return mod.addDbgStmt(b, inst.positionals.src);
}

fn analyzeInstDeclRefStr(sema: *Sema, scope: *Scope, inst: *zir.Inst.DeclRefStr) InnerError!*Inst {
    const decl_name = try sema.resolveConstString(scope, inst.positionals.name);
    return mod.analyzeDeclRefByName(scope, inst.base.src, decl_name);
}

fn analyzeInstDeclRef(sema: *Sema, scope: *Scope, inst: *zir.Inst.DeclRef) InnerError!*Inst {
    return mod.analyzeDeclRefByName(scope, inst.base.src, inst.positionals.name);
}

fn analyzeInstDeclVal(sema: *Sema, scope: *Scope, inst: *zir.Inst.DeclVal) InnerError!*Inst {
    const decl = try sema.analyzeDeclVal(scope, inst);
    const ptr = try mod.analyzeDeclRef(scope, inst.base.src, decl);
    return mod.analyzeDeref(scope, inst.base.src, ptr, inst.base.src);
}

fn analyzeInstDeclValInModule(sema: *Sema, scope: *Scope, inst: *zir.Inst.DeclValInModule) InnerError!*Inst {
    const decl = inst.positionals.decl;
    return mod.analyzeDeclRef(scope, inst.base.src, decl);
}

fn analyzeInstCall(sema: *Sema, scope: *Scope, inst: *zir.Inst.Call) InnerError!*Inst {
    const func = try sema.resolveInst(scope, inst.positionals.func);
    if (func.ty.zigTypeTag() != .Fn)
        return mod.fail(scope, inst.positionals.func.src, "type '{}' not a function", .{func.ty});

    const cc = func.ty.fnCallingConvention();
    if (cc == .Naked) {
        // TODO add error note: declared here
        return mod.fail(
            scope,
            inst.positionals.func.src,
            "unable to call function with naked calling convention",
            .{},
        );
    }
    const call_params_len = inst.positionals.args.len;
    const fn_params_len = func.ty.fnParamLen();
    if (func.ty.fnIsVarArgs()) {
        if (call_params_len < fn_params_len) {
            // TODO add error note: declared here
            return mod.fail(
                scope,
                inst.positionals.func.src,
                "expected at least {} argument(s), found {}",
                .{ fn_params_len, call_params_len },
            );
        }
        return mod.fail(scope, inst.base.src, "TODO implement support for calling var args functions", .{});
    } else if (fn_params_len != call_params_len) {
        // TODO add error note: declared here
        return mod.fail(
            scope,
            inst.positionals.func.src,
            "expected {} argument(s), found {}",
            .{ fn_params_len, call_params_len },
        );
    }

    if (inst.kw_args.modifier == .compile_time) {
        return mod.fail(scope, inst.base.src, "TODO implement comptime function calls", .{});
    }
    if (inst.kw_args.modifier != .auto) {
        return mod.fail(scope, inst.base.src, "TODO implement call with modifier {}", .{inst.kw_args.modifier});
    }

    // TODO handle function calls of generic functions

    const fn_param_types = try mod.gpa.alloc(Type, fn_params_len);
    defer mod.gpa.free(fn_param_types);
    func.ty.fnParamTypes(fn_param_types);

    const casted_args = try scope.arena().alloc(*Inst, fn_params_len);
    for (inst.positionals.args) |src_arg, i| {
        const uncasted_arg = try sema.resolveInst(scope, src_arg);
        casted_args[i] = try mod.coerce(scope, fn_param_types[i], uncasted_arg);
    }

    const ret_type = func.ty.fnReturnType();

    const b = try mod.requireRuntimeBlock(scope);
    return mod.addCall(b, inst.base.src, ret_type, func, casted_args);
}

fn analyzeInstFn(sema: *Sema, scope: *Scope, fn_inst: *zir.Inst.Fn) InnerError!*Inst {
    const fn_type = try sema.resolveType(scope, fn_inst.positionals.fn_type);
    const fn_zir = blk: {
        var fn_arena = std.heap.ArenaAllocator.init(mod.gpa);
        errdefer fn_arena.deinit();

        const fn_zir = try scope.arena().create(Module.Fn.ZIR);
        fn_zir.* = .{
            .body = .{
                .instructions = fn_inst.positionals.body.instructions,
            },
            .arena = fn_arena.state,
        };
        break :blk fn_zir;
    };
    const new_func = try scope.arena().create(Module.Fn);
    new_func.* = .{
        .analysis = .{ .queued = fn_zir },
        .owner_decl = scope.decl().?,
    };
    const fn_payload = try scope.arena().create(Value.Payload.Function);
    fn_payload.* = .{ .func = new_func };
    return mod.constInst(scope, fn_inst.base.src, .{
        .ty = fn_type,
        .val = Value.initPayload(&fn_payload.base),
    });
}

fn analyzeInstIntType(sema: *Sema, scope: *Scope, inttype: *zir.Inst.IntType) InnerError!*Inst {
    return mod.fail(scope, inttype.base.src, "TODO implement inttype", .{});
}

fn analyzeInstOptionalType(sema: *Sema, scope: *Scope, optional: *zir.Inst.UnOp) InnerError!*Inst {
    const child_type = try sema.resolveType(scope, optional.positionals.operand);

    return mod.constType(scope, optional.base.src, try mod.optionalType(scope, child_type));
}

fn analyzeInstArrayType(sema: *Sema, scope: *Scope, array: *zir.Inst.BinOp) InnerError!*Inst {
    // TODO these should be lazily evaluated
    const len = try sema.resolveInstConst(scope, array.positionals.lhs);
    const elem_type = try sema.resolveType(scope, array.positionals.rhs);

    return mod.constType(scope, array.base.src, try mod.arrayType(scope, len.val.toUnsignedInt(), null, elem_type));
}

fn analyzeInstArrayTypeSentinel(sema: *Sema, scope: *Scope, array: *zir.Inst.ArrayTypeSentinel) InnerError!*Inst {
    // TODO these should be lazily evaluated
    const len = try sema.resolveInstConst(scope, array.positionals.len);
    const sentinel = try sema.resolveInstConst(scope, array.positionals.sentinel);
    const elem_type = try sema.resolveType(scope, array.positionals.elem_type);

    return mod.constType(scope, array.base.src, try mod.arrayType(scope, len.val.toUnsignedInt(), sentinel.val, elem_type));
}

fn analyzeInstErrorUnionType(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    const error_union = try sema.resolveType(scope, inst.positionals.lhs);
    const payload = try sema.resolveType(scope, inst.positionals.rhs);

    if (error_union.zigTypeTag() != .ErrorSet) {
        return mod.fail(scope, inst.base.src, "expected error set type, found {}", .{error_union.elemType()});
    }

    return mod.constType(scope, inst.base.src, try mod.errorUnionType(scope, error_union, payload));
}

fn analyzeInstAnyframeType(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    const return_type = try sema.resolveType(scope, inst.positionals.operand);

    return mod.constType(scope, inst.base.src, try mod.anyframeType(scope, return_type));
}

fn analyzeInstErrorSet(sema: *Sema, scope: *Scope, inst: *zir.Inst.ErrorSet) InnerError!*Inst {
    // The declarations arena will store the hashmap.
    var new_decl_arena = std.heap.ArenaAllocator.init(mod.gpa);
    errdefer new_decl_arena.deinit();

    const payload = try scope.arena().create(Value.Payload.ErrorSet);
    payload.* = .{
        .fields = .{},
        .decl = undefined, // populated below
    };
    try payload.fields.ensureCapacity(&new_decl_arena.allocator, inst.positionals.fields.len);

    for (inst.positionals.fields) |field_name| {
        const entry = try mod.getErrorValue(field_name);
        if (payload.fields.fetchPutAssumeCapacity(entry.key, entry.value)) |prev| {
            return mod.fail(scope, inst.base.src, "duplicate error: '{}'", .{field_name});
        }
    }
    // TODO create name in format "error:line:column"
    const new_decl = try mod.createAnonymousDecl(scope, &new_decl_arena, .{
        .ty = Type.initTag(.type),
        .val = Value.initPayload(&payload.base),
    });
    payload.decl = new_decl;
    return mod.analyzeDeclRef(scope, inst.base.src, new_decl);
}

fn analyzeInstMergeErrorSets(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    return mod.fail(scope, inst.base.src, "TODO implement merge_error_sets", .{});
}

fn analyzeInstEnumLiteral(sema: *Sema, scope: *Scope, inst: *zir.Inst.EnumLiteral) InnerError!*Inst {
    const payload = try scope.arena().create(Value.Payload.Bytes);
    payload.* = .{
        .base = .{ .tag = .enum_literal },
        .data = try scope.arena().dupe(u8, inst.positionals.name),
    };
    return mod.constInst(scope, inst.base.src, .{
        .ty = Type.initTag(.enum_literal),
        .val = Value.initPayload(&payload.base),
    });
}

fn analyzeInstUnwrapOptional(sema: *Sema, scope: *Scope, unwrap: *zir.Inst.UnOp, safety_check: bool) InnerError!*Inst {
    const operand = try sema.resolveInst(scope, unwrap.positionals.operand);
    assert(operand.ty.zigTypeTag() == .Pointer);

    const elem_type = operand.ty.elemType();
    if (elem_type.zigTypeTag() != .Optional) {
        return mod.fail(scope, unwrap.base.src, "expected optional type, found {}", .{elem_type});
    }

    const child_type = try elem_type.optionalChildAlloc(scope.arena());
    const child_pointer = try mod.simplePtrType(scope, unwrap.base.src, child_type, operand.ty.isConstPtr(), .One);

    if (operand.value()) |val| {
        if (val.isNull()) {
            return mod.fail(scope, unwrap.base.src, "unable to unwrap null", .{});
        }
        return mod.constInst(scope, unwrap.base.src, .{
            .ty = child_pointer,
            .val = val,
        });
    }

    const b = try mod.requireRuntimeBlock(scope);
    if (safety_check and mod.wantSafety(scope)) {
        const is_non_null = try mod.addUnOp(b, unwrap.base.src, Type.initTag(.bool), .isnonnull, operand);
        try mod.addSafetyCheck(b, is_non_null, .unwrap_null);
    }
    return mod.addUnOp(b, unwrap.base.src, child_pointer, .unwrap_optional, operand);
}

fn analyzeInstUnwrapErr(sema: *Sema, scope: *Scope, unwrap: *zir.Inst.UnOp, safety_check: bool) InnerError!*Inst {
    return mod.fail(scope, unwrap.base.src, "TODO implement analyzeInstUnwrapErr", .{});
}

fn analyzeInstUnwrapErrCode(sema: *Sema, scope: *Scope, unwrap: *zir.Inst.UnOp) InnerError!*Inst {
    return mod.fail(scope, unwrap.base.src, "TODO implement analyzeInstUnwrapErrCode", .{});
}

fn analyzeInstEnsureErrPayloadVoid(sema: *Sema, scope: *Scope, unwrap: *zir.Inst.UnOp) InnerError!*Inst {
    return mod.fail(scope, unwrap.base.src, "TODO implement analyzeInstEnsureErrPayloadVoid", .{});
}

fn analyzeInstFnType(sema: *Sema, scope: *Scope, fntype: *zir.Inst.FnType) InnerError!*Inst {
    const return_type = try sema.resolveType(scope, fntype.positionals.return_type);

    // Hot path for some common function types.
    if (fntype.positionals.param_types.len == 0) {
        if (return_type.zigTypeTag() == .NoReturn and fntype.kw_args.cc == .Unspecified) {
            return mod.constType(scope, fntype.base.src, Type.initTag(.fn_noreturn_no_args));
        }

        if (return_type.zigTypeTag() == .Void and fntype.kw_args.cc == .Unspecified) {
            return mod.constType(scope, fntype.base.src, Type.initTag(.fn_void_no_args));
        }

        if (return_type.zigTypeTag() == .NoReturn and fntype.kw_args.cc == .Naked) {
            return mod.constType(scope, fntype.base.src, Type.initTag(.fn_naked_noreturn_no_args));
        }

        if (return_type.zigTypeTag() == .Void and fntype.kw_args.cc == .C) {
            return mod.constType(scope, fntype.base.src, Type.initTag(.fn_ccc_void_no_args));
        }
    }

    const arena = scope.arena();
    const param_types = try arena.alloc(Type, fntype.positionals.param_types.len);
    for (fntype.positionals.param_types) |param_type, i| {
        const resolved = try sema.resolveType(scope, param_type);
        // TODO skip for comptime params
        if (!resolved.isValidVarType(false)) {
            return mod.fail(scope, param_type.src, "parameter of type '{}' must be declared comptime", .{resolved});
        }
        param_types[i] = resolved;
    }

    const payload = try arena.create(Type.Payload.Function);
    payload.* = .{
        .cc = fntype.kw_args.cc,
        .return_type = return_type,
        .param_types = param_types,
    };
    return mod.constType(scope, fntype.base.src, Type.initPayload(&payload.base));
}

fn analyzeInstPrimitive(sema: *Sema, scope: *Scope, primitive: *zir.Inst.Primitive) InnerError!*Inst {
    return mod.constInst(scope, primitive.base.src, primitive.positionals.tag.toTypedValue());
}

fn analyzeInstAs(sema: *Sema, scope: *Scope, as: *zir.Inst.BinOp) InnerError!*Inst {
    const dest_type = try sema.resolveType(scope, as.positionals.lhs);
    const new_inst = try sema.resolveInst(scope, as.positionals.rhs);
    return mod.coerce(scope, dest_type, new_inst);
}

fn analyzeInstPtrToInt(sema: *Sema, scope: *Scope, ptrtoint: *zir.Inst.UnOp) InnerError!*Inst {
    const ptr = try sema.resolveInst(scope, ptrtoint.positionals.operand);
    if (ptr.ty.zigTypeTag() != .Pointer) {
        return mod.fail(scope, ptrtoint.positionals.operand.src, "expected pointer, found '{}'", .{ptr.ty});
    }
    // TODO handle known-pointer-address
    const b = try mod.requireRuntimeBlock(scope);
    const ty = Type.initTag(.usize);
    return mod.addUnOp(b, ptrtoint.base.src, ty, .ptrtoint, ptr);
}

fn analyzeInstFieldPtr(sema: *Sema, scope: *Scope, fieldptr: *zir.Inst.FieldPtr) InnerError!*Inst {
    const object_ptr = try sema.resolveInst(scope, fieldptr.positionals.object_ptr);
    const field_name = try sema.resolveConstString(scope, fieldptr.positionals.field_name);

    const elem_ty = switch (object_ptr.ty.zigTypeTag()) {
        .Pointer => object_ptr.ty.elemType(),
        else => return mod.fail(scope, fieldptr.positionals.object_ptr.src, "expected pointer, found '{}'", .{object_ptr.ty}),
    };
    switch (elem_ty.zigTypeTag()) {
        .Array => {
            if (mem.eql(u8, field_name, "len")) {
                const len_payload = try scope.arena().create(Value.Payload.Int_u64);
                len_payload.* = .{ .int = elem_ty.arrayLen() };

                const ref_payload = try scope.arena().create(Value.Payload.RefVal);
                ref_payload.* = .{ .val = Value.initPayload(&len_payload.base) };

                return mod.constInst(scope, fieldptr.base.src, .{
                    .ty = Type.initTag(.single_const_pointer_to_comptime_int),
                    .val = Value.initPayload(&ref_payload.base),
                });
            } else {
                return mod.fail(
                    scope,
                    fieldptr.positionals.field_name.src,
                    "no member named '{}' in '{}'",
                    .{ field_name, elem_ty },
                );
            }
        },
        .Pointer => {
            const ptr_child = elem_ty.elemType();
            switch (ptr_child.zigTypeTag()) {
                .Array => {
                    if (mem.eql(u8, field_name, "len")) {
                        const len_payload = try scope.arena().create(Value.Payload.Int_u64);
                        len_payload.* = .{ .int = ptr_child.arrayLen() };

                        const ref_payload = try scope.arena().create(Value.Payload.RefVal);
                        ref_payload.* = .{ .val = Value.initPayload(&len_payload.base) };

                        return mod.constInst(scope, fieldptr.base.src, .{
                            .ty = Type.initTag(.single_const_pointer_to_comptime_int),
                            .val = Value.initPayload(&ref_payload.base),
                        });
                    } else {
                        return mod.fail(
                            scope,
                            fieldptr.positionals.field_name.src,
                            "no member named '{}' in '{}'",
                            .{ field_name, elem_ty },
                        );
                    }
                },
                else => {},
            }
        },
        .Type => {
            _ = try mod.resolveConstValue(scope, object_ptr);
            const result = try mod.analyzeDeref(scope, fieldptr.base.src, object_ptr, object_ptr.src);
            const val = result.value().?;
            const child_type = try val.toType(scope.arena());
            switch (child_type.zigTypeTag()) {
                .ErrorSet => {
                    // TODO resolve inferred error sets
                    const entry = if (val.cast(Value.Payload.ErrorSet)) |payload|
                        (payload.fields.getEntry(field_name) orelse
                            return mod.fail(scope, fieldptr.base.src, "no error named '{}' in '{}'", .{ field_name, child_type })).*
                    else
                        try mod.getErrorValue(field_name);

                    const error_payload = try scope.arena().create(Value.Payload.Error);
                    error_payload.* = .{
                        .name = entry.key,
                        .value = entry.value,
                    };

                    const ref_payload = try scope.arena().create(Value.Payload.RefVal);
                    ref_payload.* = .{ .val = Value.initPayload(&error_payload.base) };

                    const result_type = if (child_type.tag() == .anyerror) blk: {
                        const result_payload = try scope.arena().create(Type.Payload.ErrorSetSingle);
                        result_payload.* = .{ .name = entry.key };
                        break :blk Type.initPayload(&result_payload.base);
                    } else child_type;

                    return mod.constInst(scope, fieldptr.base.src, .{
                        .ty = try mod.simplePtrType(scope, fieldptr.base.src, result_type, false, .One),
                        .val = Value.initPayload(&ref_payload.base),
                    });
                },
                else => return mod.fail(scope, fieldptr.base.src, "type '{}' does not support field access", .{child_type}),
            }
        },
        else => {},
    }
    return mod.fail(scope, fieldptr.base.src, "type '{}' does not support field access", .{elem_ty});
}

fn analyzeInstIntCast(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    const dest_type = try sema.resolveType(scope, inst.positionals.lhs);
    const operand = try sema.resolveInst(scope, inst.positionals.rhs);

    const dest_is_comptime_int = switch (dest_type.zigTypeTag()) {
        .ComptimeInt => true,
        .Int => false,
        else => return mod.fail(
            scope,
            inst.positionals.lhs.src,
            "expected integer type, found '{}'",
            .{
                dest_type,
            },
        ),
    };

    switch (operand.ty.zigTypeTag()) {
        .ComptimeInt, .Int => {},
        else => return mod.fail(
            scope,
            inst.positionals.rhs.src,
            "expected integer type, found '{}'",
            .{operand.ty},
        ),
    }

    if (operand.value() != null) {
        return mod.coerce(scope, dest_type, operand);
    } else if (dest_is_comptime_int) {
        return mod.fail(scope, inst.base.src, "unable to cast runtime value to 'comptime_int'", .{});
    }

    return mod.fail(scope, inst.base.src, "TODO implement analyze widen or shorten int", .{});
}

fn analyzeInstBitCast(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    const dest_type = try sema.resolveType(scope, inst.positionals.lhs);
    const operand = try sema.resolveInst(scope, inst.positionals.rhs);
    return mod.bitcast(scope, dest_type, operand);
}

fn analyzeInstFloatCast(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    const dest_type = try sema.resolveType(scope, inst.positionals.lhs);
    const operand = try sema.resolveInst(scope, inst.positionals.rhs);

    const dest_is_comptime_float = switch (dest_type.zigTypeTag()) {
        .ComptimeFloat => true,
        .Float => false,
        else => return mod.fail(
            scope,
            inst.positionals.lhs.src,
            "expected float type, found '{}'",
            .{
                dest_type,
            },
        ),
    };

    switch (operand.ty.zigTypeTag()) {
        .ComptimeFloat, .Float, .ComptimeInt => {},
        else => return mod.fail(
            scope,
            inst.positionals.rhs.src,
            "expected float type, found '{}'",
            .{operand.ty},
        ),
    }

    if (operand.value() != null) {
        return mod.coerce(scope, dest_type, operand);
    } else if (dest_is_comptime_float) {
        return mod.fail(scope, inst.base.src, "unable to cast runtime value to 'comptime_float'", .{});
    }

    return mod.fail(scope, inst.base.src, "TODO implement analyze widen or shorten float", .{});
}

fn analyzeInstElemPtr(sema: *Sema, scope: *Scope, inst: *zir.Inst.ElemPtr) InnerError!*Inst {
    const array_ptr = try sema.resolveInst(scope, inst.positionals.array_ptr);
    const uncasted_index = try sema.resolveInst(scope, inst.positionals.index);
    const elem_index = try mod.coerce(scope, Type.initTag(.usize), uncasted_index);

    const elem_ty = switch (array_ptr.ty.zigTypeTag()) {
        .Pointer => array_ptr.ty.elemType(),
        else => return mod.fail(scope, inst.positionals.array_ptr.src, "expected pointer, found '{}'", .{array_ptr.ty}),
    };
    if (!elem_ty.isIndexable()) {
        return mod.fail(scope, inst.base.src, "array access of non-array type '{}'", .{elem_ty});
    }

    if (elem_ty.isSinglePointer() and elem_ty.elemType().zigTypeTag() == .Array) {
        // we have to deref the ptr operand to get the actual array pointer
        const array_ptr_deref = try mod.analyzeDeref(scope, inst.base.src, array_ptr, inst.positionals.array_ptr.src);
        if (array_ptr_deref.value()) |array_ptr_val| {
            if (elem_index.value()) |index_val| {
                // Both array pointer and index are compile-time known.
                const index_u64 = index_val.toUnsignedInt();
                // @intCast here because it would have been impossible to construct a value that
                // required a larger index.
                const elem_ptr = try array_ptr_val.elemPtr(scope.arena(), @intCast(usize, index_u64));

                const type_payload = try scope.arena().create(Type.Payload.PointerSimple);
                type_payload.* = .{
                    .base = .{ .tag = .single_const_pointer },
                    .pointee_type = elem_ty.elemType().elemType(),
                };

                return mod.constInst(scope, inst.base.src, .{
                    .ty = Type.initPayload(&type_payload.base),
                    .val = elem_ptr,
                });
            }
        }
    }

    return mod.fail(scope, inst.base.src, "TODO implement more analyze elemptr", .{});
}

fn analyzeInstShl(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    return mod.fail(scope, inst.base.src, "TODO implement analyzeInstShl", .{});
}

fn analyzeInstShr(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    return mod.fail(scope, inst.base.src, "TODO implement analyzeInstShr", .{});
}

fn analyzeInstBitwise(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    return mod.fail(scope, inst.base.src, "TODO implement analyzeInstBitwise", .{});
}

fn analyzeInstBitNot(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    return mod.fail(scope, inst.base.src, "TODO implement analyzeInstBitNot", .{});
}

fn analyzeInstArrayCat(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    return mod.fail(scope, inst.base.src, "TODO implement analyzeInstArrayCat", .{});
}

fn analyzeInstArrayMul(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    return mod.fail(scope, inst.base.src, "TODO implement analyzeInstArrayMul", .{});
}

fn analyzeInstArithmetic(sema: *Sema, scope: *Scope, inst: *zir.Inst.BinOp) InnerError!*Inst {
    const tracy = trace(@src());
    defer tracy.end();

    const lhs = try sema.resolveInst(scope, inst.positionals.lhs);
    const rhs = try sema.resolveInst(scope, inst.positionals.rhs);

    const instructions = &[_]*Inst{ lhs, rhs };
    const resolved_type = try mod.resolvePeerTypes(scope, instructions);
    const casted_lhs = try mod.coerce(scope, resolved_type, lhs);
    const casted_rhs = try mod.coerce(scope, resolved_type, rhs);

    const scalar_type = if (resolved_type.zigTypeTag() == .Vector)
        resolved_type.elemType()
    else
        resolved_type;

    const scalar_tag = scalar_type.zigTypeTag();

    if (lhs.ty.zigTypeTag() == .Vector and rhs.ty.zigTypeTag() == .Vector) {
        if (lhs.ty.arrayLen() != rhs.ty.arrayLen()) {
            return mod.fail(scope, inst.base.src, "vector length mismatch: {} and {}", .{
                lhs.ty.arrayLen(),
                rhs.ty.arrayLen(),
            });
        }
        return mod.fail(scope, inst.base.src, "TODO implement support for vectors in analyzeInstBinOp", .{});
    } else if (lhs.ty.zigTypeTag() == .Vector or rhs.ty.zigTypeTag() == .Vector) {
        return mod.fail(scope, inst.base.src, "mixed scalar and vector operands to comparison operator: '{}' and '{}'", .{
            lhs.ty,
            rhs.ty,
        });
    }

    const is_int = scalar_tag == .Int or scalar_tag == .ComptimeInt;
    const is_float = scalar_tag == .Float or scalar_tag == .ComptimeFloat;

    if (!is_int and !(is_float and floatOpAllowed(inst.base.tag))) {
        return mod.fail(scope, inst.base.src, "invalid operands to binary expression: '{}' and '{}'", .{ @tagName(lhs.ty.zigTypeTag()), @tagName(rhs.ty.zigTypeTag()) });
    }

    if (casted_lhs.value()) |lhs_val| {
        if (casted_rhs.value()) |rhs_val| {
            return sema.analyzeInstComptimeOp(scope, scalar_type, inst, lhs_val, rhs_val);
        }
    }

    const b = try mod.requireRuntimeBlock(scope);
    const ir_tag = switch (inst.base.tag) {
        .add => Inst.Tag.add,
        .sub => Inst.Tag.sub,
        else => return mod.fail(scope, inst.base.src, "TODO implement arithmetic for operand '{}''", .{@tagName(inst.base.tag)}),
    };

    return mod.addBinOp(b, inst.base.src, scalar_type, ir_tag, casted_lhs, casted_rhs);
}

/// Analyzes operands that are known at comptime
fn analyzeInstComptimeOp(sema: *Sema, scope: *Scope, res_type: Type, inst: *zir.Inst.BinOp, lhs_val: Value, rhs_val: Value) InnerError!*Inst {
    // incase rhs is 0, simply return lhs without doing any calculations
    // TODO Once division is implemented we should throw an error when dividing by 0.
    if (rhs_val.compareWithZero(.eq)) {
        return mod.constInst(scope, inst.base.src, .{
            .ty = res_type,
            .val = lhs_val,
        });
    }
    const is_int = res_type.isInt() or res_type.zigTypeTag() == .ComptimeInt;

    const value = try switch (inst.base.tag) {
        .add => blk: {
            const val = if (is_int)
                Module.intAdd(scope.arena(), lhs_val, rhs_val)
            else
                mod.floatAdd(scope, res_type, inst.base.src, lhs_val, rhs_val);
            break :blk val;
        },
        .sub => blk: {
            const val = if (is_int)
                Module.intSub(scope.arena(), lhs_val, rhs_val)
            else
                mod.floatSub(scope, res_type, inst.base.src, lhs_val, rhs_val);
            break :blk val;
        },
        else => return mod.fail(scope, inst.base.src, "TODO Implement arithmetic operand '{}'", .{@tagName(inst.base.tag)}),
    };

    return mod.constInst(scope, inst.base.src, .{
        .ty = res_type,
        .val = value,
    });
}

fn analyzeInstDeref(sema: *Sema, scope: *Scope, deref: *zir.Inst.UnOp) InnerError!*Inst {
    const ptr = try sema.resolveInst(scope, deref.positionals.operand);
    return mod.analyzeDeref(scope, deref.base.src, ptr, deref.positionals.operand.src);
}

fn analyzeInstAsm(sema: *Sema, scope: *Scope, assembly: *zir.Inst.Asm) InnerError!*Inst {
    const return_type = try sema.resolveType(scope, assembly.positionals.return_type);
    const asm_source = try sema.resolveConstString(scope, assembly.positionals.asm_source);
    const output = if (assembly.kw_args.output) |o| try sema.resolveConstString(scope, o) else null;

    const inputs = try scope.arena().alloc([]const u8, assembly.kw_args.inputs.len);
    const clobbers = try scope.arena().alloc([]const u8, assembly.kw_args.clobbers.len);
    const args = try scope.arena().alloc(*Inst, assembly.kw_args.args.len);

    for (inputs) |*elem, i| {
        elem.* = try sema.resolveConstString(scope, assembly.kw_args.inputs[i]);
    }
    for (clobbers) |*elem, i| {
        elem.* = try sema.resolveConstString(scope, assembly.kw_args.clobbers[i]);
    }
    for (args) |*elem, i| {
        const arg = try sema.resolveInst(scope, assembly.kw_args.args[i]);
        elem.* = try mod.coerce(scope, Type.initTag(.usize), arg);
    }

    const b = try mod.requireRuntimeBlock(scope);
    const inst = try b.arena.create(Inst.Assembly);
    inst.* = .{
        .base = .{
            .tag = .assembly,
            .ty = return_type,
            .src = assembly.base.src,
        },
        .asm_source = asm_source,
        .is_volatile = assembly.kw_args.@"volatile",
        .output = output,
        .inputs = inputs,
        .clobbers = clobbers,
        .args = args,
    };
    try b.instructions.append(mod.gpa, &inst.base);
    return &inst.base;
}

fn analyzeInstCmp(
    mod: *Module,
    scope: *Scope,
    inst: *zir.Inst.BinOp,
    op: std.math.CompareOperator,
) InnerError!*Inst {
    const lhs = try sema.resolveInst(scope, inst.positionals.lhs);
    const rhs = try sema.resolveInst(scope, inst.positionals.rhs);

    const is_equality_cmp = switch (op) {
        .eq, .neq => true,
        else => false,
    };
    const lhs_ty_tag = lhs.ty.zigTypeTag();
    const rhs_ty_tag = rhs.ty.zigTypeTag();
    if (is_equality_cmp and lhs_ty_tag == .Null and rhs_ty_tag == .Null) {
        // null == null, null != null
        return mod.constBool(scope, inst.base.src, op == .eq);
    } else if (is_equality_cmp and
        ((lhs_ty_tag == .Null and rhs_ty_tag == .Optional) or
        rhs_ty_tag == .Null and lhs_ty_tag == .Optional))
    {
        // comparing null with optionals
        const opt_operand = if (lhs_ty_tag == .Optional) lhs else rhs;
        return mod.analyzeIsNull(scope, inst.base.src, opt_operand, op == .neq);
    } else if (is_equality_cmp and
        ((lhs_ty_tag == .Null and rhs.ty.isCPtr()) or (rhs_ty_tag == .Null and lhs.ty.isCPtr())))
    {
        return mod.fail(scope, inst.base.src, "TODO implement C pointer cmp", .{});
    } else if (lhs_ty_tag == .Null or rhs_ty_tag == .Null) {
        const non_null_type = if (lhs_ty_tag == .Null) rhs.ty else lhs.ty;
        return mod.fail(scope, inst.base.src, "comparison of '{}' with null", .{non_null_type});
    } else if (is_equality_cmp and
        ((lhs_ty_tag == .EnumLiteral and rhs_ty_tag == .Union) or
        (rhs_ty_tag == .EnumLiteral and lhs_ty_tag == .Union)))
    {
        return mod.fail(scope, inst.base.src, "TODO implement equality comparison between a union's tag value and an enum literal", .{});
    } else if (lhs_ty_tag == .ErrorSet and rhs_ty_tag == .ErrorSet) {
        if (!is_equality_cmp) {
            return mod.fail(scope, inst.base.src, "{} operator not allowed for errors", .{@tagName(op)});
        }
        return mod.fail(scope, inst.base.src, "TODO implement equality comparison between errors", .{});
    } else if (lhs.ty.isNumeric() and rhs.ty.isNumeric()) {
        // This operation allows any combination of integer and float types, regardless of the
        // signed-ness, comptime-ness, and bit-width. So peer type resolution is incorrect for
        // numeric types.
        return mod.cmpNumeric(scope, inst.base.src, lhs, rhs, op);
    }
    return mod.fail(scope, inst.base.src, "TODO implement more cmp analysis", .{});
}

fn analyzeInstTypeOf(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    const operand = try sema.resolveInst(scope, inst.positionals.operand);
    return mod.constType(scope, inst.base.src, operand.ty);
}

fn analyzeInstBoolNot(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    const uncasted_operand = try sema.resolveInst(scope, inst.positionals.operand);
    const bool_type = Type.initTag(.bool);
    const operand = try mod.coerce(scope, bool_type, uncasted_operand);
    if (try mod.resolveDefinedValue(scope, operand)) |val| {
        return mod.constBool(scope, inst.base.src, !val.toBool());
    }
    const b = try mod.requireRuntimeBlock(scope);
    return mod.addUnOp(b, inst.base.src, bool_type, .not, operand);
}

fn analyzeInstIsNonNull(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp, invert_logic: bool) InnerError!*Inst {
    const operand = try sema.resolveInst(scope, inst.positionals.operand);
    return mod.analyzeIsNull(scope, inst.base.src, operand, invert_logic);
}

fn analyzeInstIsErr(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    const operand = try sema.resolveInst(scope, inst.positionals.operand);
    return mod.analyzeIsErr(scope, inst.base.src, operand);
}

fn analyzeInstCondBr(sema: *Sema, scope: *Scope, inst: *zir.Inst.CondBr) InnerError!*Inst {
    const uncasted_cond = try sema.resolveInst(scope, inst.positionals.condition);
    const cond = try mod.coerce(scope, Type.initTag(.bool), uncasted_cond);

    if (try mod.resolveDefinedValue(scope, cond)) |cond_val| {
        const body = if (cond_val.toBool()) &inst.positionals.then_body else &inst.positionals.else_body;
        try sema.analyzeBody(scope, body.*);
        return mod.constVoid(scope, inst.base.src);
    }

    const parent_block = try mod.requireRuntimeBlock(scope);

    var true_block: Scope.Block = .{
        .parent = parent_block,
        .func = parent_block.func,
        .decl = parent_block.decl,
        .instructions = .{},
        .arena = parent_block.arena,
    };
    defer true_block.instructions.deinit(mod.gpa);
    try sema.analyzeBody(&true_block.base, inst.positionals.then_body);

    var false_block: Scope.Block = .{
        .parent = parent_block,
        .func = parent_block.func,
        .decl = parent_block.decl,
        .instructions = .{},
        .arena = parent_block.arena,
    };
    defer false_block.instructions.deinit(mod.gpa);
    try sema.analyzeBody(&false_block.base, inst.positionals.else_body);

    const then_body: ir.Body = .{ .instructions = try scope.arena().dupe(*Inst, true_block.instructions.items) };
    const else_body: ir.Body = .{ .instructions = try scope.arena().dupe(*Inst, false_block.instructions.items) };
    return mod.addCondBr(parent_block, inst.base.src, cond, then_body, else_body);
}

fn analyzeInstUnreachable(
    mod: *Module,
    scope: *Scope,
    unreach: *zir.Inst.NoOp,
    safety_check: bool,
) InnerError!*Inst {
    const b = try mod.requireRuntimeBlock(scope);
    // TODO Add compile error for @optimizeFor occurring too late in a scope.
    if (safety_check and mod.wantSafety(scope)) {
        return mod.safetyPanic(b, unreach.base.src, .unreach);
    } else {
        return mod.addNoOp(b, unreach.base.src, Type.initTag(.noreturn), .unreach);
    }
}

fn analyzeInstRet(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp) InnerError!*Inst {
    const operand = try sema.resolveInst(scope, inst.positionals.operand);
    const b = try mod.requireRuntimeBlock(scope);
    return mod.addUnOp(b, inst.base.src, Type.initTag(.noreturn), .ret, operand);
}

fn analyzeInstRetVoid(sema: *Sema, scope: *Scope, inst: *zir.Inst.NoOp) InnerError!*Inst {
    const b = try mod.requireRuntimeBlock(scope);
    if (b.func) |func| {
        // Need to emit a compile error if returning void is not allowed.
        const void_inst = try mod.constVoid(scope, inst.base.src);
        const fn_ty = func.owner_decl.typed_value.most_recent.typed_value.ty;
        const casted_void = try mod.coerce(scope, fn_ty.fnReturnType(), void_inst);
        if (casted_void.ty.zigTypeTag() != .Void) {
            return mod.addUnOp(b, inst.base.src, Type.initTag(.noreturn), .ret, casted_void);
        }
    }
    return mod.addNoOp(b, inst.base.src, Type.initTag(.noreturn), .retvoid);
}

fn floatOpAllowed(tag: zir.Inst.Tag) bool {
    // extend this swich as additional operators are implemented
    return switch (tag) {
        .add, .sub => true,
        else => false,
    };
}

fn analyzeBreak(
    mod: *Module,
    scope: *Scope,
    src: usize,
    zir_block: *zir.Inst.Block,
    operand: *Inst,
) InnerError!*Inst {
    var opt_block = scope.cast(Scope.Block);
    while (opt_block) |block| {
        if (block.label) |*label| {
            if (label.zir_block == zir_block) {
                try label.results.append(mod.gpa, operand);
                const b = try mod.requireRuntimeBlock(scope);
                return mod.addBr(b, src, label.block_inst, operand);
            }
        }
        opt_block = block.parent;
    } else unreachable;
}

fn analyzeDeclVal(sema: *Sema, scope: *Scope, inst: *zir.Inst.DeclVal) InnerError!*Decl {
    const decl_name = inst.positionals.name;
    const zir_module = scope.namespace().cast(Scope.ZIRModule).?;
    const src_decl = zir_module.contents.module.findDecl(decl_name) orelse
        return mod.fail(scope, inst.base.src, "use of undeclared identifier '{}'", .{decl_name});

    const decl = try sema.resolveCompleteZirDecl(scope, src_decl.decl);

    return decl;
}

fn analyzeInstSimplePtrType(sema: *Sema, scope: *Scope, inst: *zir.Inst.UnOp, mutable: bool, size: std.builtin.TypeInfo.Pointer.Size) InnerError!*Inst {
    const elem_type = try sema.resolveType(scope, inst.positionals.operand);
    const ty = try mod.simplePtrType(scope, inst.base.src, elem_type, mutable, size);
    return mod.constType(scope, inst.base.src, ty);
}

fn analyzeInstPtrType(sema: *Sema, scope: *Scope, inst: *zir.Inst.PtrType) InnerError!*Inst {
    // TODO lazy values
    const @"align" = if (inst.kw_args.@"align") |some|
        @truncate(u32, try sema.resolveInt(scope, some, Type.initTag(.u32)))
    else
        0;
    const bit_offset = if (inst.kw_args.align_bit_start) |some|
        @truncate(u16, try sema.resolveInt(scope, some, Type.initTag(.u16)))
    else
        0;
    const host_size = if (inst.kw_args.align_bit_end) |some|
        @truncate(u16, try sema.resolveInt(scope, some, Type.initTag(.u16)))
    else
        0;

    if (host_size != 0 and bit_offset >= host_size * 8)
        return sema.fail(scope, inst.base.src, "bit offset starts after end of host integer", .{});

    const sentinel = if (inst.kw_args.sentinel) |some|
        (try sema.resolveInstConst(scope, some)).val
    else
        null;

    const elem_type = try sema.resolveType(scope, inst.positionals.child_type);

    const ty = try mod.ptrType(
        scope,
        inst.base.src,
        elem_type,
        sentinel,
        @"align",
        bit_offset,
        host_size,
        inst.kw_args.mutable,
        inst.kw_args.@"allowzero",
        inst.kw_args.@"volatile",
        inst.kw_args.size,
    );
    return mod.constType(scope, inst.base.src, ty);
}

pub fn fail(sema: *Sema, scope: *Scope, comptime format: []const u8, args: anytype) InnerError {
    @setCold(true);
    const err_msg = try ErrorMsg.create(sema.module.gpa, sema.src, format, args);
    return sema.module.failWithOwnedErrorMsg(scope, sema.src, err_msg);
}

#!/usr/bin/env python3

import urllib.request

def main():
    import argparse
    parser = argparse.ArgumentParser("generates ranges of non-ascii unicode points that should be excluded from identifiers")
    parser.add_argument("-v", "--verbose", action="store_true")
    parser.add_argument("--whitelist", action="store_true", help="instead print the non-ascii code points that are included in identifiers.")
    args = parser.parse_args()

    blacklist_ranges = get_blacklist_ranges(args)
    if args.whitelist:
        ranges = invert_ranges(blacklist_ranges)
    else:
        ranges = blacklist_ranges
    print_ranges(ranges)

def get_blacklist_ranges(args):
    blacklist_ranges = [
        # (0x0, 0x1f),
        # (0xff, 0xff),
    ]

    for fields in load_ucd_url("https://www.unicode.org/Public/5.2.0/ucd/PropList.txt"):
        if fields[1] in ("Pattern_White_Space", "Pattern_Syntax", "Noncharacter_Code_Point"):
            append_range(blacklist_ranges, range_to_tuple(fields[0]))

    current_range_name_and_start = None # ("Non Private Use High Surrogate", 0xD800)
    for fields in load_ucd_url("https://www.unicode.org/Public/5.2.0/ucd/UnicodeData.txt"):
        # we're looking for Private_Use, Surrogate, or Control
        if fields[2] not in ("Co", "Cs", "Cc"): continue
        point = int(fields[0], 16)

        if fields[1].endswith(", Last>"):
            # https://www.unicode.org/Public/5.1.0/ucd/UCD.html
            # > For backwards compatibility, ...
            assert fields[1].startswith("<")
            name = fields[1][1:-len(", Last>")]
            assert current_range_name_and_start[0] == name
            append_range(blacklist_ranges, (current_range_name_and_start[1], point))
            current_range_name_and_start = None
            continue
        assert current_range_name_and_start == None

        if fields[1].endswith(", First>"):
            # https://www.unicode.org/Public/5.1.0/ucd/UCD.html
            # > For backwards compatibility, ...
            assert fields[1].startswith("<")
            name = fields[1][1:-len(", First>")]
            current_range_name_and_start = (name, point)
            continue

        # single point; not a range specifier.
        append_range(blacklist_ranges, (point, point))

    blacklist_ranges.sort()
    if args.verbose:
        print("# first-pass merged ranges")
        print_ranges(blacklist_ranges)
        print("")

    # merge possibly-overlapping ranges
    i = 0
    while i < len(blacklist_ranges) - 1:
        left_range = blacklist_ranges[i]
        right_range = blacklist_ranges[i + 1]
        if left_range[1] + 1 >= right_range[0]:
            # merge
            new_range = (left_range[0], max(left_range[1], right_range[1]))
            blacklist_ranges[i:i+2] = [new_range]
            # re-evaluate this new range with the same i.
            continue
        # can't merge left_range
        i += 1

    # strip out ascii characters. zig's grammar handles that already.
    while True:
        if blacklist_ranges[0][0] > 0x7f: break
        if blacklist_ranges[0][1] <= 0x7f:
            # delete completley ascii range
            del blacklist_ranges[0]
        else:
             # split partially ascii range
             blacklist_ranges[0] = (0x80, blacklist_ranges[0][1])

    return blacklist_ranges

def print_ranges(ranges):
    print("\n".join(("{}..{}".format(*[hex(x)[2:].upper().zfill(4) for x in line]) if line[0] != line[1] else hex(line[0])[2:].upper().zfill(4)) for line in ranges))

def load_ucd_url(url):
    # https://www.unicode.org/Public/5.1.0/ucd/UCD.html
    # > The files use UTF-8, with the exception of NamesList.txt, which is encoded in Latin-1.
    encoding = "latin1" if "NamesList.txt" in url else "utf8"

    with urllib.request.urlopen(url) as f:
        for line in f:
            line = line.decode(encoding).split("#", 1)[0]
            if len(line.strip()) == 0:
                continue
            fields = tuple(field.strip() for field in line.split(";"))
            yield fields

def range_to_tuple(range_str):
    # e.g. "0009..000D", "2028", "110BE..110C1"
    points = tuple(int(point_str, 16) for point_str in range_str.split("..", 1))
    if len(points) == 1:
        return (points[0], points[0])
    return points

def append_range(range_list, range_tuple):
    # optimistically extend the last range in the list to include the new range if possible.
    if len(range_list) > 0 and range_list[-1][1] + 1 == range_tuple[0]:
        # join it
        range_list[-1] = (range_list[-1][0], range_tuple[1])
    else:
        # fallback to just adding as a new range
        range_list.append(range_tuple)

def invert_ranges(ranges):
    # not acsii
    result = [
        (0x0080, 0x10FFFF),
    ]
    for exclude_range in ranges:
        if result[-1][0] == exclude_range[0]:
            # bring the start forward
            result[-1] = (exclude_range[1] + 1, result[-1][1])
        elif result[-1][1] == exclude_range[1]:
            # bring the end backward
            result[-1] = (result[-1][0], exclude_range[0] - 1)
        else:
            # split
            result[-1:] = [
                (result[-1][0], exclude_range[0] - 1),
                (exclude_range[1] + 1, result[-1][1]),
            ]
    return result

if __name__ == "__main__":
    main()

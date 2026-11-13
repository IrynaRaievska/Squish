# This code is written by Chris Jefferson
# https://github.com/gap-packages/LocalNR/pull/38#issuecomment-4354402095
#
# Squish: dedup + row-delta compression for nested integer-list files of the
# form
#     local P; P := [[ [...], [...], ... ]]; return P;
# that LocalNR/Endom and similar packages ship.
#
# The compressor does two things:
#
# (1) Inner-list deduplication: many files contain hundreds of thousands of
#     byte-identical inner lists.  Each unique inner list is named once as
#     A<n>; everywhere it would have appeared the file uses the name.
#
# (2) Row-delta encoding: in P, adjacent rows usually differ in only one
#     or two positions.  The output uses a small helper `_R` that walks a
#     list of entries; each entry is either a full row literal or a
#     position-diff `[pos1, val1, pos2, val2, ...]` against the previous row.
#
# The new file is itself a `ReadAsFunction`-compatible GAP source: the
# helper `_R` and the unique vectors A<n> are local to the function, so
# loading via `ReadAsFunction(file)()` returns the same nested list as the
# original.  No new package or runtime is required.
#
# Usage:
#     Read("squish.g");
#     SquishListAsFunction("input.txt.gz", "output.txt.gz");
#
# Verification helper:
#     ProduceSHAs("Endom");
# walks the directory recursively, calls ReadAsFunction on each .txt.gz
# file, and prints `HexSHA256(String(P))  <relative-path>` for each, sorted
# by path.  Run before and after a refactor and `diff` the outputs to
# confirm the package still produces identical lists.

SquishListAsFunction := function(oldname, newname)
    local P, P2, dict, uniques, structure, outerRow, idxRow, inner, idx,
          names, parts, stream, prev, row, diffs, i, j, n_lit, n_diff,
          flatNames, rowStr, helper;

    # 1. Read the original list.
    P := ReadAsFunction(oldname)();

    # 2. Collect unique inner lists (first-seen order) and the structure
    #    of indices into them.
    dict := NewDictionary([], true);
    uniques := [];
    structure := [];
    for outerRow in P do
        idxRow := [];
        for inner in outerRow do
            idx := LookupDictionary(dict, inner);
            if idx = fail then
                Add(uniques, inner);
                idx := Length(uniques);
                AddDictionary(dict, inner, idx);
            fi;
            Add(idxRow, idx);
        od;
        Add(structure, idxRow);
    od;

    # 3. Short variable names: A1, A2, ... .
    names := List([1..Length(uniques)], i -> Concatenation("A", String(i)));

    # 4. Build the file body as one string.
    parts := [];
    Add(parts, "local P,_R,");
    Add(parts, JoinStringsWithSeparator(names, ","));
    Add(parts, ";\n");

    # Helper definition: walks a list of (literal-row | diff-row) entries.
    # A diff-row has IsInt(e[1]); a literal-row has e[1] being a list (an A<n>).
    helper := Concatenation(
        "_R:=function(rows) local r,p,e,i; r:=[]; p:=[]; for e in rows do ",
        "if Length(e)>0 and IsInt(e[1]) then ",
            "p:=ShallowCopy(p); ",
            "for i in [1,3..Length(e)-1] do p[e[i]]:=e[i+1]; od; ",
        "else p:=e; fi; ",
        "Add(r,p); od; return r; end;\n");
    Add(parts, helper);

    # Vector definitions.
    for i in [1..Length(uniques)] do
        Add(parts, names[i]);
        Add(parts, ":=[");
        Add(parts, JoinStringsWithSeparator(List(uniques[i], String), ","));
        Add(parts, "];\n");
    od;

    # 5. Delta-encode each row of P against the previous row, then emit.
    Add(parts, "P:=_R([\n");
    prev := [];
    n_lit := 0;
    n_diff := 0;
    for i in [1..Length(structure)] do
        row := structure[i];
        if Length(row) <> Length(prev) then
            # Different length forces a literal.
            rowStr := Concatenation("[",
                JoinStringsWithSeparator(List(row, j -> names[j]), ","), "]");
            n_lit := n_lit + 1;
        else
            diffs := [];
            for j in [1..Length(row)] do
                if row[j] <> prev[j] then
                    Add(diffs, j);
                    Add(diffs, row[j]);
                fi;
            od;
            if Length(diffs) = 0 then
                # Identical row -- fall back to literal, since an empty
                # diff would be ambiguous in our format.
                rowStr := Concatenation("[",
                    JoinStringsWithSeparator(List(row, j -> names[j]), ","),
                    "]");
                n_lit := n_lit + 1;
            else
                # Diff: alternating positions and A-names.
                flatNames := [];
                for j in [1, 3 .. Length(diffs) - 1] do
                    Add(flatNames, String(diffs[j]));
                    Add(flatNames, names[diffs[j+1]]);
                od;
                rowStr := Concatenation("[",
                    JoinStringsWithSeparator(flatNames, ","), "]");
                n_diff := n_diff + 1;
            fi;
        fi;
        Add(parts, rowStr);
        if i < Length(structure) then Add(parts, ","); fi;
        Add(parts, "\n");
        prev := row;
    od;
    Add(parts, "]);\nreturn P;\n");

    # 6. Write all at once.
    stream := OutputGzipFile(newname, false);
    WriteAll(stream, Concatenation(parts));
    CloseStream(stream);

    # 7. Verify roundtrip.
    P2 := ReadAsFunction(newname)();
    if P <> P2 then
        Error("Squish roundtrip mismatch for ", oldname, " -> ", newname);
    fi;

    return rec( unique     := Length(uniques),
                referenced := Sum(structure, Length),
                literals   := n_lit,
                deltas     := n_diff );
end;


# ----------------------------------------------------------------------
# Verification helper
# ----------------------------------------------------------------------

# Recursive lister: returns a sorted list of file paths *relative to* `root`
# whose name ends in ".txt" or ".txt.gz".
SQUISH_DataFilesUnder := function(root)
    local hasSuffix, walk, results;
    hasSuffix := function(s, suf)
        if Length(s) < Length(suf) then return false; fi;
        return s{[Length(s) - Length(suf) + 1 .. Length(s)]} = suf;
    end;
    results := [];
    walk := function(rel)
        local fullDir, contents, c, full, childRel;
        if rel = "" then
            fullDir := root;
        else
            fullDir := Filename(Directory(root), rel);
        fi;
        contents := DirectoryContents(fullDir);
        Sort(contents);
        for c in contents do
            if c = "." or c = ".." then continue; fi;
            if rel = "" then
                childRel := c;
            else
                childRel := Concatenation(rel, "/", c);
            fi;
            full := Filename(Directory(root), childRel);
            if IsDirectoryPath(full) then
                walk(childRel);
            elif hasSuffix(c, ".txt.gz") then
                Add(results, childRel);
            fi;
        od;
    end;
    walk("");
    return results;
end;

# For each data file under `dirname`, print
#     <sha>  <relative path>
# one per line, sorted by relative path.  The hash is taken on the GAP
# String representation of the *value* returned by `ReadAsFunction(file)()`,
# so it is invariant to the on-disk encoding (gzip vs plain, squish vs raw,
# delta vs not) and only depends on the parsed `P`.
ProduceSHAs := function(dirname)
    local files, rel, full, P, sha, oldFmt;
    # Stop GAP's `Print` from soft-wrapping the long lines at column 80,
    # which would otherwise insert backslash continuations between the SHA
    # and the path.
    oldFmt := PrintFormattingStatus("*stdout*");
    SetPrintFormattingStatus("*stdout*", false);
    files := SQUISH_DataFilesUnder(dirname);
    for rel in files do
        full := Filename(Directory(dirname), rel);
        P := ReadAsFunction(full)();
        sha := HexSHA256(String(P));
        Print(sha, "  ", rel, "\n");
    od;
    SetPrintFormattingStatus("*stdout*", oldFmt);
end;

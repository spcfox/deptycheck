#!/bin/bash

files="tests/lib/john-hughes/rgen-008-full-trace-weakmemo"

find "$files" -name "output*" -type f -print0 | xargs -0 -I{} bash -c '
    created=$(stat -c %W "{}")
    [[ "$created" -eq 0 ]] && created=$(stat -c %Y "{}")
    lines=$(wc -l < "{}")
    echo "$created $lines {}"
' | sort -n

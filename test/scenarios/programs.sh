for name in frames helpers recursive shared slots; do "$heresy" "test/$name.c" --certificate "$certificate" --observe 4096 -o "$work/$name.ordinary.hs" --build "$work/$name.ordinary" || exit 1; "$FILCC" -std=c11 -O1 "test/$name.c" -o "$work/$name.reference" || exit 1; first=0; "$work/$name.ordinary" >"$work/$name.output" || first=$?; second=0; "$work/$name.reference" >"$work/$name.expected" || second=$?; test "$first" -eq "$second" &&
cmp "$work/$name.output" "$work/$name.expected" || exit 1; done &&
"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json test/slots.c > $work/slots.json &&
"$heresy" test/slots.c --closed -o $work/Slots.hs &&
"$certificate" program $work/slots.json $work/Slots.hs &&
"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json test/helpers.c > $work/helpers.json &&
"$heresy" test/helpers.c --closed -o $work/Helpers.hs &&
"$certificate" program $work/helpers.json $work/Helpers.hs &&
"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json test/frames.c > $work/frames.json &&
"$heresy" test/frames.c --closed -o $work/Frames.hs &&
"$certificate" program $work/frames.json $work/Frames.hs &&
"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json test/recursive.c > $work/recursive.json &&
"$heresy" test/recursive.c --closed -o $work/Recursive.hs &&
"$certificate" program $work/recursive.json $work/Recursive.hs

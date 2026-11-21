! "$heresy" test/arguments.c --certificate "$certificate" --observe 0 --ghc /missing -o $work/Paused.hs --build $work/paused 2>$work/paused.err &&
grep -q "exceeded its step budget" $work/paused.err &&
test ! -e $work/Paused.hs &&
test ! -e $work/paused &&
LC_ALL=C.UTF-8 "$heresy" test/arguments.c --certificate "$certificate" --observe 512 --arg "é" --arg "" -o $work/Arguments.hs --ast-dir $work/argumentsast --build $work/arguments &&
status=0 &&
{ LC_ALL=C.UTF-8 $work/arguments "é" "" >$work/arguments.out || status=$?; } &&
test "$status" -eq 7 &&
"$FILCC" -std=c11 -O1 test/arguments.c -o $work/argumentsref &&
status=0 &&
{ LC_ALL=C.UTF-8 $work/argumentsref "é" "" >$work/argumentsref.out || status=$?; } &&
test "$status" -eq 7 &&
cmp $work/arguments.out $work/argumentsref.out &&
printf "%s\000%s\000\000" $work/arguments "é" > $work/arguments.argv &&
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Arguments.hs 512 7 $work/arguments.out $work/arguments.argv $work/argumentsast/0.json &&
printf "%s\000" $work/arguments > $work/short.argv &&
! "$certificate" ordinary-observe-argv runtime/Heap.hs $work/Arguments.hs 512 7 $work/arguments.out $work/short.argv $work/argumentsast/0.json &&
printf "%s" $work/arguments > $work/unterminated.argv &&
! "$certificate" ordinary-observe-argv runtime/Heap.hs $work/Arguments.hs 512 7 $work/arguments.out $work/unterminated.argv $work/argumentsast/0.json

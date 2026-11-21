"$heresy" test/exit.c --certificate "$certificate" -o $work/Exit.hs --ast-dir $work/exitast --build $work/explicitexit &&
status=0 &&
{ $work/explicitexit >$work/explicitexit.out || status=$?; } &&
test "$status" -eq 7 &&
test "$(cat $work/explicitexit.out)" = A &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Exit.hs 256 7 $work/explicitexit.out $work/exitast/0.json

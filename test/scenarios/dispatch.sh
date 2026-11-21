"$heresy" test/dispatch.c --certificate "$certificate" -o $work/Dispatch.hs --ast-dir $work/dispatchast --build $work/dispatch &&
status=0 &&
{ $work/dispatch >$work/dispatch.out || status=$?; } &&
test "$status" -eq 2 &&
"$FILCC" -std=c11 -O1 test/dispatch.c -o $work/dispatchref &&
status=0 &&
{ $work/dispatchref >$work/dispatchref.out || status=$?; } &&
test "$status" -eq 2 &&
cmp $work/dispatch.out $work/dispatchref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Dispatch.hs 512 2 $work/dispatch.out $work/dispatchast/0.json &&
sed "/^  do { p <- variable .*targets[.]/s/label:indexed:2/label:indexed:3/" $work/Dispatch.hs > $work/ChangedTable.hs &&
! cmp -s $work/Dispatch.hs $work/ChangedTable.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/dispatchast/0.json $work/ChangedTable.hs &&
sed "/^f_726f757465 (a0/s/pure (Jump 13)/pure (Jump 12)/" $work/Dispatch.hs > $work/ChangedDispatch.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/dispatchast/0.json $work/ChangedDispatch.hs

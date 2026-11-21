"$heresy" test/control.c --certificate "$certificate" -o $work/Control.hs --ast-dir $work/controlast --build $work/control &&
status=0 &&
{ $work/control >$work/control.out || status=$?; } &&
test "$status" -eq 7 &&
"$FILCC" -std=c11 -O1 test/control.c -o $work/controlref &&
status=0 &&
{ $work/controlref >$work/controlref.out || status=$?; } &&
test "$status" -eq 7 &&
cmp $work/control.out $work/controlref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Control.hs 256 7 $work/control.out $work/controlast/0.json &&
sed "/^f_7363616e (a0/s/pure Continue/pure Break/" $work/Control.hs > $work/ChangedTransfer.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/controlast/0.json $work/ChangedTransfer.hs

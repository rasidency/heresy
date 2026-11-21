"$heresy" test/captured.c --certificate "$certificate" -o $work/Captured.hs --ast-dir $work/capturedast --build $work/captured &&
"$FILCC" -std=c11 -Wno-pointer-arith -O1 test/captured.c -o $work/capturedref &&
$work/captured >$work/captured.out &&
$work/capturedref >$work/capturedref.out &&
test "$(cat $work/captured.out)" = AADCBEF &&
cmp $work/captured.out $work/capturedref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Captured.hs 2048 0 $work/captured.out $work/capturedast/0.json &&
status=0 &&
{ $work/captured fault >$work/capturedfault.out 2>$work/capturedfault.err || status=$?; } &&
test "$status" -eq 70 &&
grep -q "nonpositive variable-length array bound" $work/capturedfault.err &&
cmp $work/captured.out $work/capturedfault.out &&
printf "%s\000%s\000" $work/captured fault >$work/captured.argv &&
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Captured.hs 2048 70 $work/capturedfault.out $work/captured.argv $work/capturedast/0.json &&
sed "s/vlaIndex 2 /vlaIndex 1 /" $work/Captured.hs >$work/WrongRank.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/capturedast/0.json $work/WrongRank.hs

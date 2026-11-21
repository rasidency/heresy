"$heresy" test/arrays.c --certificate "$certificate" -o $work/Arrays.hs --ast-dir $work/arraysast --build $work/arrays &&
$work/arrays > $work/arrays.out &&
"$FILCC" -std=c11 -O1 test/arrays.c -o $work/arraysref &&
$work/arraysref > $work/arraysref.out &&
cmp $work/arrays.out $work/arraysref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Arrays.hs 512 0 $work/arrays.out $work/arraysast/0.json &&
sed "/^f_6d61696e _ = /s/clear 2 p/clear 1 p/" $work/Arrays.hs > $work/ChangedClear.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/arraysast/0.json $work/ChangedClear.hs

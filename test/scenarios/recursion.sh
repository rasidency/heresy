"$heresy" test/recursion.c --certificate "$certificate" -o $work/Recursion.hs --ast-dir $work/recursionast --build $work/recursion &&
sed "/^f_726570656174 (a0/s/\"forward\"/\"repeat\"/" $work/Recursion.hs > $work/ChangedCall.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/recursionast/0.json $work/ChangedCall.hs &&
status=0 &&
{ $work/recursion >$work/recursion.out 2>$work/recursion.err || status=$?; } &&
test "$status" -eq 70 &&
grep -q "use after free" $work/recursion.err &&
"$certificate" effects runtime/Heap.hs $work/recursionast/0.json $work/Recursion.hs $work/recursion.out &&
"$FILCC" -std=c11 -O1 test/recursion.c -o $work/recursionref &&
status=0 &&
{ $work/recursionref >$work/recursionref.out 2>$work/recursionref.err || status=$?; } &&
test "$status" -ne 0 &&
grep -q "cannot access pointer to free object" $work/recursionref.err &&
cmp $work/recursion.out $work/recursionref.out

"$heresy" test/extents.c --certificate "$certificate" -o $work/Extent.hs --ast-dir $work/extentast --build $work/extent &&
"$FILCC" -std=c11 -O1 test/extents.c -o $work/extentref &&
actual=0 &&
{ $work/extent >$work/extent.out || actual=$?; } &&
expected=0 &&
{ $work/extentref >$work/extentref.out || expected=$?; } &&
test "$actual" -eq 5 &&
test "$actual" -eq "$expected" &&
cmp $work/extent.out $work/extentref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Extent.hs 512 5 $work/extent.out $work/extentast/0.json &&
sed "s/vlaExtent 4 \[/vlaExtent 8 [/" $work/Extent.hs >$work/WrongExtent.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/extentast/0.json $work/WrongExtent.hs

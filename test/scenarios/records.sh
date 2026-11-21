"$heresy" test/records.c --certificate "$certificate" -o $work/Records.hs --ast-dir $work/recordsast --build $work/records &&
$work/records > $work/records.out &&
"$FILCC" -std=c11 -O1 test/records.c -o $work/recordsref &&
$work/recordsref > $work/recordsref.out &&
cmp $work/records.out $work/recordsref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Records.hs 512 0 $work/records.out $work/recordsast/0.json &&
sed "/^  freeze (variable .*__heresy_literal_frozen_/d" $work/Records.hs > $work/ChangedLiteral.hs &&
! cmp -s $work/Records.hs $work/ChangedLiteral.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/recordsast/0.json $work/ChangedLiteral.hs &&
sed "/^f_6d61696e _ = /s/Number (-2)/Number (-1)/" $work/Records.hs > $work/ChangedEnum.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/recordsast/0.json $work/ChangedEnum.hs &&
sed "/void (global .*padded/s/ 8)/ 5)/" $work/Records.hs > $work/ChangedLayout.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/recordsast/0.json $work/ChangedLayout.hs

"$heresy" test/fields.c --certificate "$certificate" -o $work/Fields.hs --ast-dir $work/fieldsast --build $work/fields &&
$work/fields > $work/fields.out &&
"$FILCC" -std=c11 -O1 test/fields.c -o $work/fieldsref &&
$work/fieldsref > $work/fieldsref.out &&
cmp $work/fields.out $work/fieldsref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Fields.hs 512 0 $work/fields.out $work/fieldsast/0.json &&
sed "s/\"second\",\"int\",32,null/\"second\",\"int\",8,null/" $work/fieldsast/0.json > $work/changedfield.json &&
! cmp -s $work/fieldsast/0.json $work/changedfield.json &&
! "$certificate" ordinary runtime/Heap.hs $work/changedfield.json $work/Fields.hs &&
sed "/^f_6d61696e _ = /s/BitField 5 8 True/BitField 4 8 True/" $work/Fields.hs > $work/ChangedField.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/fieldsast/0.json $work/ChangedField.hs

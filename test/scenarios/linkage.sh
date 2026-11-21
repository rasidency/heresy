"$heresy" test/linkage/client.c test/linkage/server.c --certificate "$certificate" -o $work/ScalarLink.hs --ast-dir $work/scalarunits --build $work/scalarlink &&
$work/scalarlink > $work/scalarlink.out &&
"$FILCC" -std=c11 -O1 test/linkage/client.c test/linkage/server.c -o $work/scalarref &&
$work/scalarref > $work/scalarref.out &&
cmp $work/scalarlink.out $work/scalarref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/ScalarLink.hs 128 0 $work/scalarlink.out $work/scalarunits/0.json $work/scalarunits/1.json &&
! "$certificate" ordinary-link runtime/Heap.hs $work/ScalarLink.hs $work/scalarunits/1.json $work/scalarunits/0.json &&
sed "/^f_6d61696e _ = /s/function \"unit:0:adjust\"/function \"unit:1:adjust\"/" $work/ScalarLink.hs > $work/ChangedPrivate.hs &&
! "$certificate" ordinary-link runtime/Heap.hs $work/ChangedPrivate.hs $work/scalarunits/0.json $work/scalarunits/1.json &&
sed "/^main = execute /s/allocateGlobals_unit_756e69743a313a; initialiseGlobals_unit_756e69743a303a/initialiseGlobals_unit_756e69743a303a; allocateGlobals_unit_756e69743a313a/" $work/ScalarLink.hs > $work/ChangedStartup.hs &&
! "$certificate" ordinary-link runtime/Heap.hs $work/ChangedStartup.hs $work/scalarunits/0.json $work/scalarunits/1.json &&
"$heresy" test/linkage/entry.c test/linkage/worker.c --certificate "$certificate" --observe 1024 -o $work/Linkage.hs --ast-dir $work/units --build $work/linked &&
"$certificate" linkage $work/Linkage.hs $work/units/0.json $work/units/1.json &&
test "$($work/linked)" = "linkage 4 18 42 18 9 1" &&
! "$certificate" linkage $work/Linkage.hs $work/units/1.json $work/units/0.json &&
sed "/^main = execute/s/] True (/] False (/" $work/Linkage.hs > $work/Disabled.hs &&
! "$certificate" linkage $work/Disabled.hs $work/units/0.json $work/units/1.json

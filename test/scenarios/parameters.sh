"$heresy" test/parameters.c test/linkage/shape.c --certificate "$certificate" -o $work/Parameters.hs --ast-dir $work/parametersast --build $work/parameters &&
"$FILCC" -std=c11 -O1 test/parameters.c test/linkage/shape.c -o $work/parametersref &&
$work/parameters >$work/parameters.out &&
$work/parametersref >$work/parametersref.out &&
cmp $work/parameters.out $work/parametersref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Parameters.hs 1024 0 $work/parameters.out $work/parametersast/0.json $work/parametersast/1.json &&
sed "s/vlaBind 1 p 4/vlaBind 0 p 4/" $work/Parameters.hs >$work/WrongAdjustment.hs &&
! "$certificate" ordinary-link runtime/Heap.hs $work/WrongAdjustment.hs $work/parametersast/0.json $work/parametersast/1.json

"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json examples/machine.c > $work/machine.json &&
"$heresy" examples/machine.c --certificate "$certificate" --observe 8192 --arg "3+4*2" -o $work/Machine.hs --build $work/machine &&
"$FILCC" -std=c11 -O1 examples/machine.c -o $work/machineref &&
$work/machine "3+4*2" > $work/machine.out &&
$work/machineref "3+4*2" > $work/machine.refout &&
cmp $work/machine.out $work/machine.refout &&
"$certificate" $work/machine.json $work/Machine.hs &&
sed "/^f_.* = at /s/(number a0)/0/" $work/Machine.hs > $work/ChangedKernel.hs &&
! "$certificate" $work/machine.json $work/ChangedKernel.hs

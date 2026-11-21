"$heresy" test/varargs.c --certificate "$certificate" -o $work/Varargs.hs --ast-dir $work/varargsast --build $work/varargs &&
"$FILCC" -std=c11 -O1 test/varargs.c -o $work/varargsref &&
$work/varargs >$work/varargs.out &&
$work/varargsref >$work/varargsref.out &&
test "$(cat $work/varargs.out)" = AB &&
cmp $work/varargs.out $work/varargsref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Varargs.hs 1024 0 $work/varargs.out $work/varargsast/0.json &&
status=0 &&
{ $work/varargs fault >$work/varargsfault.out 2>$work/varargsfault.err || status=$?; } &&
test "$status" -eq 70 &&
grep -q "out of bounds" $work/varargsfault.err &&
cmp $work/varargs.out $work/varargsfault.out &&
printf "%s\000%s\000" $work/varargs fault >$work/varargs.argv &&
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Varargs.hs 1024 70 $work/varargsfault.out $work/varargs.argv $work/varargsast/0.json &&
status=0 &&
{ $work/varargs fault readonly >$work/varargsreadonly.out 2>$work/varargsreadonly.err || status=$?; } &&
test "$status" -eq 70 &&
grep -q "read-only" $work/varargsreadonly.err &&
cmp $work/varargs.out $work/varargsreadonly.out &&
printf "%s\000%s\000%s\000" $work/varargs fault readonly >$work/readonly.argv &&
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Varargs.hs 1024 70 $work/varargsreadonly.out $work/readonly.argv $work/varargsast/0.json &&
sed "/^f_/s/vaCopy /vaStart callArea namedTypes /" $work/Varargs.hs >$work/WrongVarargs.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/varargsast/0.json $work/WrongVarargs.hs

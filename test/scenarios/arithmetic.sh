"$heresy" test/arithmetic.c --certificate "$certificate" -o $work/Arithmetic.hs --ast-dir $work/arithmeticast --build $work/arithmetic &&
"$FILCC" -std=c11 -O1 test/arithmetic.c -o $work/arithmeticref &&
actual=0 &&
{ $work/arithmetic >$work/arithmetic.out || actual=$?; } &&
expected=0 &&
{ $work/arithmeticref >$work/arithmeticref.out || expected=$?; } &&
test "$actual" -eq 7 &&
test "$actual" -eq "$expected" &&
cmp $work/arithmetic.out $work/arithmeticref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Arithmetic.hs 512 7 $work/arithmetic.out $work/arithmeticast/0.json &&
status=0 &&
{ $work/arithmetic fault >$work/arithmeticfault.out 2>$work/arithmeticfault.err || status=$?; } &&
test "$status" -eq 70 &&
grep -q "division by zero" $work/arithmeticfault.err &&
cmp $work/arithmetic.out $work/arithmeticfault.out &&
printf "%s\000%s\000" $work/arithmetic fault >$work/arithmetic.argv &&
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Arithmetic.hs 512 70 $work/arithmeticfault.out $work/arithmetic.argv $work/arithmeticast/0.json &&
sed "s/addl /subl /" $work/arithmeticast/0.json > $work/changedasm.json &&
! cmp -s $work/arithmeticast/0.json $work/changedasm.json &&
! "$certificate" ordinary runtime/Heap.hs $work/changedasm.json $work/Arithmetic.hs &&
sed "s|update \"/\" (IntegerType 32 True) 32 False|update \"/\" (IntegerType 32 True) 32 True|" $work/Arithmetic.hs >$work/WrongArithmetic.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/arithmeticast/0.json $work/WrongArithmetic.hs

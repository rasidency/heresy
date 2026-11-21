"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json test/closed.c > $work/closed.json &&
"$heresy" test/closed.c --closed --certificate "$certificate" -o $work/Closed.hs --build $work/closed &&
"$certificate" program $work/closed.json $work/Closed.hs &&
"$certificate" text test/closed.c $work/Closed.hs &&
"$certificate" text-compile test/closed.c > $work/Verified.hs &&
cmp $work/Verified.hs $work/Closed.hs &&
"$FILCC" -std=c11 -O1 test/closed.c -o $work/closedref &&
actual=0 &&
{ $work/closed || actual=$?; } &&
expected=0 &&
{ $work/closedref || expected=$?; } &&
test "$actual" -eq 37 &&
test "$actual" -eq "$expected" &&
FILCC=/missing "$heresy" test/closed.c --closed --native --certificate "$certificate" --ghc /missing --build $work/native &&
"$heresy" test/closed.c --closed --native --certificate "$certificate" --verify-artifact $work/native &&
actual=0 &&
{ $work/native >$work/native.out || actual=$?; } &&
test "$actual" -eq "$expected" &&
test ! -s $work/native.out &&
cp $work/native $work/ChangedNative &&
printf "\000" | dd of=$work/ChangedNative bs=1 seek=121 conv=notrunc status=none &&
! "$certificate" native-verify test/closed.c $work/ChangedNative &&
sed "s/0x100UL/0x101UL/" test/closed.c > $work/ChangedSource.c &&
! "$certificate" text $work/ChangedSource.c $work/Closed.hs &&
sed "s/ + / ++ /" test/closed.c > $work/CompoundToken.c &&
! "$certificate" text $work/CompoundToken.c $work/Closed.hs &&
! "$certificate" text-compile $work/CompoundToken.c > $work/Rejected.hs &&
test ! -s $work/Rejected.hs

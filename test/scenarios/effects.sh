"$heresy" test/effects.c -o $work/Effects.hs --ast-dir $work/effectsast &&
"$certificate" module runtime/Heap.hs $work/Effects.hs $work/effectsast/0.json &&
"$certificate" ordinary runtime/Heap.hs $work/effectsast/0.json $work/Effects.hs &&
sed "/^f_6d61696e _ = /s/pure (Number (65))/pure (Number (66))/" $work/Effects.hs > $work/ChangedBody.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/effectsast/0.json $work/ChangedBody.hs &&
! "$heresy" test/effects.c --certificate /bin/false -o $work/Uncertified.hs &&
test ! -e $work/Uncertified.hs &&
sed "1s/GeneralizedNewtypeDeriving/StandaloneDeriving/" $work/Effects.hs > $work/ChangedRuntime.hs &&
! "$certificate" module runtime/Heap.hs $work/ChangedRuntime.hs $work/effectsast/0.json &&
"$heresy" test/effects.c --certificate "$certificate" --verify-artifact $work/Effects.hs --build $work/effects &&
status=0 &&
{ $work/effects >$work/effects.out 2>$work/effects.err || status=$?; } &&
test "$status" -eq 70 &&
grep -q "use after free" $work/effects.err &&
"$certificate" effects runtime/Heap.hs $work/effectsast/0.json $work/Effects.hs $work/effects.out

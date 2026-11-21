"$heresy" test/callback.c --certificate "$certificate" --observe 512 -o $work/Callback.hs --ast-dir $work/callbackast --build $work/callback &&
"$FILCC" -std=c11 -O1 test/callback.c -o $work/callbackref &&
for invocation in first second null changed; do case "$invocation" in first) expected=42; set --;; second) expected=40; set -- select;; null) expected=70; set -- select null;; changed) expected=70; set -- select raw changed;; esac; status=0; $work/callback "$@" >$work/callback.out 2>$work/callback.err || status=$?; test "$status" -eq "$expected" &&
test ! -s $work/callback.out || exit 1; native=0; $work/callbackref "$@" >$work/callbackref.out 2>$work/callbackref.err || native=$?; cmp $work/callback.out $work/callbackref.out || exit 1; if test "$expected" -ne 70; then test "$native" -eq "$expected" || exit 1; else test "$native" -ne 0 &&
grep -q "invalid function pointer" $work/callback.err &&
grep -q "filc safety error" $work/callbackref.err || exit 1; fi; printf "%s\000" $work/callback "$@" >$work/callback.argv; "$certificate" ordinary-observe-argv runtime/Heap.hs $work/Callback.hs 512 "$expected" $work/callback.out $work/callback.argv $work/callbackast/0.json || exit 1; done &&
sed "/^f_6d61696e /s/function \"decrement\"/function \"increment\"/" $work/Callback.hs >$work/ChangedCallback.hs &&
! cmp -s $work/Callback.hs $work/ChangedCallback.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/callbackast/0.json $work/ChangedCallback.hs

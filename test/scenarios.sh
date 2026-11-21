set -eu

heresy=$(realpath "$1")
certificate=$(realpath "$2")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json examples/machine.c > $work/machine.json &&
"$heresy" examples/machine.c --certificate "$certificate" --observe 8192 --arg "3+4*2" -o $work/Machine.hs --build $work/machine &&
"$FILCC" -std=c11 -O1 examples/machine.c -o $work/machineref &&
$work/machine "3+4*2" > $work/machine.out &&
$work/machineref "3+4*2" > $work/machine.refout &&
cmp $work/machine.out $work/machine.refout &&
"$certificate" $work/machine.json $work/Machine.hs &&
sed "/^f_.* = at /s/(number a0)/0/" $work/Machine.hs > $work/ChangedKernel.hs &&
! "$certificate" $work/machine.json $work/ChangedKernel.hs &&
"$FILCC" -std=c11 test/shared.c -o $work/sharedref &&
$work/sharedref &&
"$heresy" test/shared.c -o $work/Shared.hs --ast-dir $work/sharedast --build $work/shared &&
$work/shared &&
"$certificate" shared choose $work/sharedast/0.json $work/Shared.hs &&
sed "/^f_63686f6f7365 _ = /s/pure shared/pure (Number 0)/" $work/Shared.hs > $work/ChangedShared.hs &&
! "$certificate" shared choose $work/sharedast/0.json $work/ChangedShared.hs &&
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
"$certificate" effects runtime/Heap.hs $work/effectsast/0.json $work/Effects.hs $work/effects.out &&
"$heresy" test/recursion.c --certificate "$certificate" -o $work/Recursion.hs --ast-dir $work/recursionast --build $work/recursion &&
sed "/^f_726570656174 (a0/s/\"forward\"/\"repeat\"/" $work/Recursion.hs > $work/ChangedCall.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/recursionast/0.json $work/ChangedCall.hs &&
status=0 &&
{ $work/recursion >$work/recursion.out 2>$work/recursion.err || status=$?; } &&
test "$status" -eq 70 &&
grep -q "use after free" $work/recursion.err &&
"$certificate" effects runtime/Heap.hs $work/recursionast/0.json $work/Recursion.hs $work/recursion.out &&
"$FILCC" -std=c11 -O1 test/recursion.c -o $work/recursionref &&
status=0 &&
{ $work/recursionref >$work/recursionref.out 2>$work/recursionref.err || status=$?; } &&
test "$status" -ne 0 &&
grep -q "cannot access pointer to free object" $work/recursionref.err &&
cmp $work/recursion.out $work/recursionref.out &&
"$heresy" test/control.c --certificate "$certificate" -o $work/Control.hs --ast-dir $work/controlast --build $work/control &&
status=0 &&
{ $work/control >$work/control.out || status=$?; } &&
test "$status" -eq 7 &&
"$FILCC" -std=c11 -O1 test/control.c -o $work/controlref &&
status=0 &&
{ $work/controlref >$work/controlref.out || status=$?; } &&
test "$status" -eq 7 &&
cmp $work/control.out $work/controlref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Control.hs 256 7 $work/control.out $work/controlast/0.json &&
sed "/^f_7363616e (a0/s/pure Continue/pure Break/" $work/Control.hs > $work/ChangedTransfer.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/controlast/0.json $work/ChangedTransfer.hs &&
"$heresy" test/dispatch.c --certificate "$certificate" -o $work/Dispatch.hs --ast-dir $work/dispatchast --build $work/dispatch &&
status=0 &&
{ $work/dispatch >$work/dispatch.out || status=$?; } &&
test "$status" -eq 2 &&
"$FILCC" -std=c11 -O1 test/dispatch.c -o $work/dispatchref &&
status=0 &&
{ $work/dispatchref >$work/dispatchref.out || status=$?; } &&
test "$status" -eq 2 &&
cmp $work/dispatch.out $work/dispatchref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Dispatch.hs 512 2 $work/dispatch.out $work/dispatchast/0.json &&
sed "/^  do { p <- variable .*targets[.]/s/label:indexed:2/label:indexed:3/" $work/Dispatch.hs > $work/ChangedTable.hs &&
! cmp -s $work/Dispatch.hs $work/ChangedTable.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/dispatchast/0.json $work/ChangedTable.hs &&
sed "/^f_726f757465 (a0/s/pure (Jump 13)/pure (Jump 12)/" $work/Dispatch.hs > $work/ChangedDispatch.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/dispatchast/0.json $work/ChangedDispatch.hs &&
"$heresy" test/arrays.c --certificate "$certificate" -o $work/Arrays.hs --ast-dir $work/arraysast --build $work/arrays &&
$work/arrays > $work/arrays.out &&
"$FILCC" -std=c11 -O1 test/arrays.c -o $work/arraysref &&
$work/arraysref > $work/arraysref.out &&
cmp $work/arrays.out $work/arraysref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Arrays.hs 512 0 $work/arrays.out $work/arraysast/0.json &&
sed "/^f_6d61696e _ = /s/clear 2 p/clear 1 p/" $work/Arrays.hs > $work/ChangedClear.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/arraysast/0.json $work/ChangedClear.hs &&
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
! "$certificate" ordinary runtime/Heap.hs $work/recordsast/0.json $work/ChangedLayout.hs &&
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
! "$certificate" ordinary runtime/Heap.hs $work/fieldsast/0.json $work/ChangedField.hs &&
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
! "$certificate" ordinary runtime/Heap.hs $work/arithmeticast/0.json $work/WrongArithmetic.hs &&
"$heresy" test/extents.c --certificate "$certificate" -o $work/Extent.hs --ast-dir $work/extentast --build $work/extent &&
"$FILCC" -std=c11 -O1 test/extents.c -o $work/extentref &&
actual=0 &&
{ $work/extent >$work/extent.out || actual=$?; } &&
expected=0 &&
{ $work/extentref >$work/extentref.out || expected=$?; } &&
test "$actual" -eq 5 &&
test "$actual" -eq "$expected" &&
cmp $work/extent.out $work/extentref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Extent.hs 512 5 $work/extent.out $work/extentast/0.json &&
sed "s/vlaExtent 4 \[/vlaExtent 8 [/" $work/Extent.hs >$work/WrongExtent.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/extentast/0.json $work/WrongExtent.hs &&
"$heresy" test/captured.c --certificate "$certificate" -o $work/Captured.hs --ast-dir $work/capturedast --build $work/captured &&
"$FILCC" -std=c11 -Wno-pointer-arith -O1 test/captured.c -o $work/capturedref &&
$work/captured >$work/captured.out &&
$work/capturedref >$work/capturedref.out &&
test "$(cat $work/captured.out)" = AADCBEF &&
cmp $work/captured.out $work/capturedref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Captured.hs 2048 0 $work/captured.out $work/capturedast/0.json &&
status=0 &&
{ $work/captured fault >$work/capturedfault.out 2>$work/capturedfault.err || status=$?; } &&
test "$status" -eq 70 &&
grep -q "nonpositive variable-length array bound" $work/capturedfault.err &&
cmp $work/captured.out $work/capturedfault.out &&
printf "%s\000%s\000" $work/captured fault >$work/captured.argv &&
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Captured.hs 2048 70 $work/capturedfault.out $work/captured.argv $work/capturedast/0.json &&
sed "s/vlaIndex 2 /vlaIndex 1 /" $work/Captured.hs >$work/WrongRank.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/capturedast/0.json $work/WrongRank.hs &&
"$heresy" test/parameters.c test/linkage/shape.c --certificate "$certificate" -o $work/Parameters.hs --ast-dir $work/parametersast --build $work/parameters &&
"$FILCC" -std=c11 -O1 test/parameters.c test/linkage/shape.c -o $work/parametersref &&
$work/parameters >$work/parameters.out &&
$work/parametersref >$work/parametersref.out &&
cmp $work/parameters.out $work/parametersref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Parameters.hs 1024 0 $work/parameters.out $work/parametersast/0.json $work/parametersast/1.json &&
sed "s/vlaBind 1 p 4/vlaBind 0 p 4/" $work/Parameters.hs >$work/WrongAdjustment.hs &&
! "$certificate" ordinary-link runtime/Heap.hs $work/WrongAdjustment.hs $work/parametersast/0.json $work/parametersast/1.json &&
"$heresy" test/packets.c test/linkage/packet.c --certificate "$certificate" -o $work/Packets.hs --ast-dir $work/packetsast --build $work/packets &&
"$FILCC" -std=c11 -O1 test/packets.c test/linkage/packet.c -o $work/packetsref &&
$work/packets >$work/packets.out &&
$work/packetsref >$work/packetsref.out &&
test "$(cat $work/packets.out)" = ABC &&
cmp $work/packets.out $work/packetsref.out &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Packets.hs 1024 0 $work/packets.out $work/packetsast/0.json $work/packetsast/1.json &&
status=0 &&
{ $work/packets fault >$work/packetsfault.out 2>$work/packetsfault.err || status=$?; } &&
test "$status" -eq 70 &&
grep -q "use after free" $work/packetsfault.err &&
cmp $work/packets.out $work/packetsfault.out &&
printf "%s\000%s\000" $work/packets fault >$work/packets.argv &&
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Packets.hs 1024 70 $work/packetsfault.out $work/packets.argv $work/packetsast/0.json $work/packetsast/1.json &&
sed "/^f_/s/(AggregateType 16 8)/(AggregateType 8 8)/" $work/Packets.hs >$work/WrongPackets.hs &&
! "$certificate" ordinary-link runtime/Heap.hs $work/WrongPackets.hs $work/packetsast/0.json $work/packetsast/1.json &&
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
! "$certificate" ordinary runtime/Heap.hs $work/varargsast/0.json $work/WrongVarargs.hs &&
"$FILCC" -std=c11 -O1 -pthread test/condition.c -o $work/conditionref &&
"$heresy" test/condition.c --certificate "$certificate" --observe 4096 -o $work/Condition.hs --build $work/condition &&
$work/conditionref &&
$work/condition &&
"$FILCC" -std=c11 -O1 -pthread test/handoff.c -o $work/handoffref &&
"$heresy" test/handoff.c --certificate "$certificate" --observe 1024 --ast-dir $work/handoffast -o $work/Handoff.hs --build $work/handoff &&
$work/handoff >$work/handoff.out &&
$work/handoffref >$work/handoffref.out &&
printf "A\n" >$work/handoffexpected &&
cmp $work/handoffexpected $work/handoff.out &&
cmp $work/handoff.out $work/handoffref.out &&
status=0 &&
{ $work/handoff fault >$work/handofffault.out 2>$work/handofffault.err || status=$?; } &&
test "$status" -eq 70 &&
grep -q "use after free" $work/handofffault.err &&
status=0 &&
{ $work/handoffref fault >$work/handoffreffault.out 2>$work/handoffreffault.err || status=$?; } &&
test "$status" -ne 0 &&
grep -q "free object" $work/handoffreffault.err &&
cmp $work/handoffexpected $work/handofffault.out &&
cmp $work/handoffexpected $work/handoffreffault.out &&
printf "%s\000%s\000" $work/handoff fault >$work/handoff.argv &&
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Handoff.hs 1024 70 $work/handofffault.out $work/handoff.argv $work/handoffast/0.json &&
printf "[]\n" >$work/emptyschedule &&
! "$certificate" ordinary-ready-argv runtime/Heap.hs $work/Handoff.hs 1024 $work/handoff.argv --schedule $work/emptyschedule $work/handoffast/0.json &&
printf "[-1]\n" >$work/invalidschedule &&
! "$certificate" ordinary-ready-argv runtime/Heap.hs $work/Handoff.hs 1024 $work/handoff.argv --schedule $work/invalidschedule $work/handoffast/0.json &&
sed "/^main = execute /s/True/False/" $work/Handoff.hs >$work/WrongHandoff.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/handoffast/0.json $work/WrongHandoff.hs &&
{ printf "[" &&
yes "0,1,2," | head -n 256 | tr -d "\n" &&
printf "0]\n"; } > $work/threadschedule &&
"$heresy" test/threads.c --certificate "$certificate" --observe 1024 --schedule $work/threadschedule --arg joins --ast-dir $work/threadsast -o $work/Threads.hs --build $work/threads &&
"$FILCC" -std=c11 -O1 -pthread test/threads.c -o $work/threadsref &&
status=0 &&
{ $work/threadsref || status=$?; } &&
test "$status" -eq 81 &&
status=0 &&
{ $work/threads || status=$?; } &&
test "$status" -eq 81 &&
{ printf "[" &&
yes "2,1,0," | head -n 256 | tr -d "\n" &&
printf "0]\n"; } > $work/reversethreads &&
printf "%s\000" $work/threads > $work/threads.argv &&
: > $work/threads.out &&
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Threads.hs 1024 81 $work/threads.out $work/threads.argv --schedule $work/reversethreads $work/threadsast/0.json &&
"$heresy" test/exit.c --certificate "$certificate" -o $work/Exit.hs --ast-dir $work/exitast --build $work/explicitexit &&
status=0 &&
{ $work/explicitexit >$work/explicitexit.out || status=$?; } &&
test "$status" -eq 7 &&
test "$(cat $work/explicitexit.out)" = A &&
"$certificate" ordinary-observe runtime/Heap.hs $work/Exit.hs 256 7 $work/explicitexit.out $work/exitast/0.json &&
! "$heresy" test/arguments.c --certificate "$certificate" --observe 0 --ghc /missing -o $work/Paused.hs --build $work/paused 2>$work/paused.err &&
grep -q "exceeded its step budget" $work/paused.err &&
test ! -e $work/Paused.hs &&
test ! -e $work/paused &&
LC_ALL=C.UTF-8 "$heresy" test/arguments.c --certificate "$certificate" --observe 512 --arg "é" --arg "" -o $work/Arguments.hs --ast-dir $work/argumentsast --build $work/arguments &&
status=0 &&
{ LC_ALL=C.UTF-8 $work/arguments "é" "" >$work/arguments.out || status=$?; } &&
test "$status" -eq 7 &&
"$FILCC" -std=c11 -O1 test/arguments.c -o $work/argumentsref &&
status=0 &&
{ LC_ALL=C.UTF-8 $work/argumentsref "é" "" >$work/argumentsref.out || status=$?; } &&
test "$status" -eq 7 &&
cmp $work/arguments.out $work/argumentsref.out &&
printf "%s\000%s\000\000" $work/arguments "é" > $work/arguments.argv &&
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Arguments.hs 512 7 $work/arguments.out $work/arguments.argv $work/argumentsast/0.json &&
printf "%s\000" $work/arguments > $work/short.argv &&
! "$certificate" ordinary-observe-argv runtime/Heap.hs $work/Arguments.hs 512 7 $work/arguments.out $work/short.argv $work/argumentsast/0.json &&
printf "%s" $work/arguments > $work/unterminated.argv &&
! "$certificate" ordinary-observe-argv runtime/Heap.hs $work/Arguments.hs 512 7 $work/arguments.out $work/unterminated.argv $work/argumentsast/0.json &&
"$heresy" test/values.c -o $work/Values.hs --ast-dir $work/values &&
"$certificate" module runtime/Heap.hs $work/Values.hs $work/values/0.json &&
"$certificate" dispatch $work/Values.hs &&
sed "s/if truth tested then convertValue shared else fallback/if truth tested then fallback else convertValue shared/" $work/Values.hs > $work/Conditional.hs &&
! "$certificate" dispatch $work/Conditional.hs &&
sed "s/^      _ -> advance >> loop condition body advance$/      _ -> loop condition body advance/" $work/Values.hs > $work/ChangedLoop.hs &&
! "$certificate" dispatch $work/ChangedLoop.hs &&
sed -E "/^g_.* = /s/]\)$/, []])/" $work/Values.hs > $work/ChangedGraph.hs &&
! "$certificate" dispatch $work/ChangedGraph.hs &&
"$certificate" memory $work/Values.hs &&
"$certificate" process $work/Values.hs &&
sed "s/> 1024 - size/> 4096 - size/" $work/Values.hs > $work/Buffer.hs &&
! "$certificate" process $work/Buffer.hs &&
sed "s/d \&\& even q/d \&\& odd q/" $work/Values.hs > $work/Rounding.hs &&
! "$certificate" process $work/Rounding.hs &&
"$certificate" linkage $work/Values.hs $work/values/0.json &&
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
! "$certificate" linkage $work/Disabled.hs $work/units/0.json $work/units/1.json &&
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
test ! -s $work/Rejected.hs &&
"$heresy" examples/flows.c --certificate "$certificate" --check &&
"$heresy" examples/codec.c --certificate "$certificate" --observe 8192 --arg abcdabcdabcd --build $work/codec -o $work/Codec.hs &&
"$FILCC" -std=c11 -O1 examples/codec.c -o $work/codecref &&
$work/codec abcdabcdabcd >$work/codec.out &&
$work/codecref abcdabcdabcd >$work/codec.refout &&
cmp $work/codec.out $work/codec.refout &&
printf ABC >$work/streamin &&
printf "%s\n" "[[\"open\",\"$work/streamin\",\"rb\",true],[\"read\",1,6,\"ABC\"],[\"close\",1,true], [\"open\",\"$work/streamout\",\"wb\",true],[\"write\",2,[65,66,67,0],true],[\"close\",2,true]]" >$work/events &&
"$heresy" test/streams.c --certificate "$certificate" --observe 1024 --arg $work/streamin --arg $work/streamout --file-events $work/events --build $work/streams -o $work/Streams.hs --ast-dir $work/streamsast &&
printf "ABC\000" >$work/expectedbytes &&
cmp $work/expectedbytes $work/streamout &&
printf "%s\000" $work/streams $work/streamin $work/streamout >$work/streams.argv &&
$work/streams $work/streamin $work/streamout >$work/streams.out &&
sed "s/65,66,67,0/65,66,68,0/" $work/events >$work/badevents &&
! "$certificate" ordinary-observe-argv runtime/Heap.hs $work/Streams.hs 1024 0 $work/streams.out $work/streams.argv --file-events $work/badevents $work/streamsast/0.json &&
for source in test/stdio.c test/order.c test/extended.c examples/bounds.c examples/alias.c examples/regression.c; do name=$(basename "$source" .c); exe="$work/$name.stdio"; "$heresy" "$source" --certificate "$certificate" --observe 4096 --ast-dir "$work/$name.stdioast" -o "$exe.hs" --build "$exe" || exit 1; "$FILCC" -std=c11 -O1 "$source" -o "$exe.ref" || exit 1; for arg in "" 1; do set --; if test -n "$arg"; then set -- "$arg"; fi; first=0; "$exe" "$@" >"$exe.out" 2>"$exe.err" || first=$?; second=0; "$exe.ref" "$@" >"$exe.expected" 2>"$exe.referr" || second=$?; case "$name:$arg" in alias:*|stdio:1|bounds:1) test "$first" -eq 70 &&
test "$second" -ne 0 || exit 1;; *) test "$first" -eq 0 &&
test "$second" -eq 0 || exit 1;; esac; cmp "$exe.out" "$exe.expected" || exit 1; printf "%s\000" "$exe" "$@" >"$exe.argv" || exit 1; "$certificate" ordinary-observe-argv runtime/Heap.hs "$exe.hs" 4096 "$first" "$exe.out" "$exe.argv" "$work/$name.stdioast/0.json" || exit 1; done; done &&
sed "s/%04d %02X/%04d %02x/" $work/stdio.stdio.hs >$work/WrongFormat.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/stdio.stdioast/0.json $work/WrongFormat.hs &&
printf "%s\n" "#include <stdio.h>" "int main(void) { return printf(\"%lc\", 65u); }" >$work/Wide.c &&
! "$heresy" $work/Wide.c --certificate "$certificate" -o $work/Wide.hs &&
test ! -e $work/Wide.hs &&
"$heresy" test/callback.c --certificate "$certificate" --observe 512 -o $work/Callback.hs --ast-dir $work/callbackast --build $work/callback &&
"$FILCC" -std=c11 -O1 test/callback.c -o $work/callbackref &&
for invocation in first second null changed; do case "$invocation" in first) expected=42; set --;; second) expected=40; set -- select;; null) expected=70; set -- select null;; changed) expected=70; set -- select raw changed;; esac; status=0; $work/callback "$@" >$work/callback.out 2>$work/callback.err || status=$?; test "$status" -eq "$expected" &&
test ! -s $work/callback.out || exit 1; native=0; $work/callbackref "$@" >$work/callbackref.out 2>$work/callbackref.err || native=$?; cmp $work/callback.out $work/callbackref.out || exit 1; if test "$expected" -ne 70; then test "$native" -eq "$expected" || exit 1; else test "$native" -ne 0 &&
grep -q "invalid function pointer" $work/callback.err &&
grep -q "filc safety error" $work/callbackref.err || exit 1; fi; printf "%s\000" $work/callback "$@" >$work/callback.argv; "$certificate" ordinary-observe-argv runtime/Heap.hs $work/Callback.hs 512 "$expected" $work/callback.out $work/callback.argv $work/callbackast/0.json || exit 1; done &&
sed "/^f_6d61696e /s/function \"decrement\"/function \"increment\"/" $work/Callback.hs >$work/ChangedCallback.hs &&
! cmp -s $work/Callback.hs $work/ChangedCallback.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/callbackast/0.json $work/ChangedCallback.hs &&
for name in frames helpers recursive shared slots; do "$heresy" "test/$name.c" --certificate "$certificate" --observe 4096 -o "$work/$name.ordinary.hs" --build "$work/$name.ordinary" || exit 1; "$FILCC" -std=c11 -O1 "test/$name.c" -o "$work/$name.reference" || exit 1; first=0; "$work/$name.ordinary" >"$work/$name.output" || first=$?; second=0; "$work/$name.reference" >"$work/$name.expected" || second=$?; test "$first" -eq "$second" &&
cmp "$work/$name.output" "$work/$name.expected" || exit 1; done &&
"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json test/slots.c > $work/slots.json &&
"$heresy" test/slots.c --closed -o $work/Slots.hs &&
"$certificate" program $work/slots.json $work/Slots.hs &&
"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json test/helpers.c > $work/helpers.json &&
"$heresy" test/helpers.c --closed -o $work/Helpers.hs &&
"$certificate" program $work/helpers.json $work/Helpers.hs &&
"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json test/frames.c > $work/frames.json &&
"$heresy" test/frames.c --closed -o $work/Frames.hs &&
"$certificate" program $work/frames.json $work/Frames.hs &&
"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json test/recursive.c > $work/recursive.json &&
"$heresy" test/recursive.c --closed -o $work/Recursive.hs &&
"$certificate" program $work/recursive.json $work/Recursive.hs

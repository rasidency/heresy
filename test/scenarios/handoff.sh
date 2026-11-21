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
! "$certificate" ordinary runtime/Heap.hs $work/handoffast/0.json $work/WrongHandoff.hs

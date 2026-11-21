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
! "$certificate" ordinary-link runtime/Heap.hs $work/WrongPackets.hs $work/packetsast/0.json $work/packetsast/1.json

printf ABC >$work/streamin &&
printf "%s\n" "[[\"open\",\"$work/streamin\",\"rb\",true],[\"read\",1,6,\"ABC\"],[\"close\",1,true], [\"open\",\"$work/streamout\",\"wb\",true],[\"write\",2,[65,66,67,0],true],[\"close\",2,true]]" >$work/events &&
"$heresy" test/streams.c --certificate "$certificate" --observe 1024 --arg $work/streamin --arg $work/streamout --file-events $work/events --build $work/streams -o $work/Streams.hs --ast-dir $work/streamsast &&
printf "ABC\000" >$work/expectedbytes &&
cmp $work/expectedbytes $work/streamout &&
printf "%s\000" $work/streams $work/streamin $work/streamout >$work/streams.argv &&
$work/streams $work/streamin $work/streamout >$work/streams.out &&
sed "s/65,66,67,0/65,66,68,0/" $work/events >$work/badevents &&
! "$certificate" ordinary-observe-argv runtime/Heap.hs $work/Streams.hs 1024 0 $work/streams.out $work/streams.argv --file-events $work/badevents $work/streamsast/0.json

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
"$certificate" ordinary-observe-argv runtime/Heap.hs $work/Threads.hs 1024 81 $work/threads.out $work/threads.argv --schedule $work/reversethreads $work/threadsast/0.json

"$heresy" examples/flows.c --certificate "$certificate" --check &&
"$heresy" examples/codec.c --certificate "$certificate" --observe 8192 --arg abcdabcdabcd --build $work/codec -o $work/Codec.hs &&
"$FILCC" -std=c11 -O1 examples/codec.c -o $work/codecref &&
$work/codec abcdabcdabcd >$work/codec.out &&
$work/codecref abcdabcdabcd >$work/codec.refout &&
cmp $work/codec.out $work/codec.refout

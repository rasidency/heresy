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
"$certificate" linkage $work/Values.hs $work/values/0.json

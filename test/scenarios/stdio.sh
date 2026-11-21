for source in test/stdio.c test/order.c test/extended.c examples/bounds.c examples/alias.c examples/regression.c; do name=$(basename "$source" .c); exe="$work/$name.stdio"; "$heresy" "$source" --certificate "$certificate" --observe 4096 --ast-dir "$work/$name.stdioast" -o "$exe.hs" --build "$exe" || exit 1; "$FILCC" -std=c11 -O1 "$source" -o "$exe.ref" || exit 1; for arg in "" 1; do set --; if test -n "$arg"; then set -- "$arg"; fi; first=0; "$exe" "$@" >"$exe.out" 2>"$exe.err" || first=$?; second=0; "$exe.ref" "$@" >"$exe.expected" 2>"$exe.referr" || second=$?; case "$name:$arg" in alias:*|stdio:1|bounds:1) test "$first" -eq 70 &&
test "$second" -ne 0 || exit 1;; *) test "$first" -eq 0 &&
test "$second" -eq 0 || exit 1;; esac; cmp "$exe.out" "$exe.expected" || exit 1; printf "%s\000" "$exe" "$@" >"$exe.argv" || exit 1; "$certificate" ordinary-observe-argv runtime/Heap.hs "$exe.hs" 4096 "$first" "$exe.out" "$exe.argv" "$work/$name.stdioast/0.json" || exit 1; done; done &&
sed "s/%04d %02X/%04d %02x/" $work/stdio.stdio.hs >$work/WrongFormat.hs &&
! "$certificate" ordinary runtime/Heap.hs $work/stdio.stdioast/0.json $work/WrongFormat.hs &&
printf "%s\n" "#include <stdio.h>" "int main(void) { return printf(\"%lc\", 65u); }" >$work/Wide.c &&
! "$heresy" $work/Wide.c --certificate "$certificate" -o $work/Wide.hs &&
test ! -e $work/Wide.hs

"$FILCC" -std=c11 test/shared.c -o $work/sharedref &&
$work/sharedref &&
"$heresy" test/shared.c -o $work/Shared.hs --ast-dir $work/sharedast --build $work/shared &&
$work/shared &&
"$certificate" shared choose $work/sharedast/0.json $work/Shared.hs &&
sed "/^f_63686f6f7365 _ = /s/pure shared/pure (Number 0)/" $work/Shared.hs > $work/ChangedShared.hs &&
! "$certificate" shared choose $work/sharedast/0.json $work/ChangedShared.hs

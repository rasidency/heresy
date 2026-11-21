"$FILCC" -std=c11 -O1 -pthread test/condition.c -o $work/conditionref &&
"$heresy" test/condition.c --certificate "$certificate" --observe 4096 -o $work/Condition.hs --build $work/condition &&
$work/conditionref &&
$work/condition

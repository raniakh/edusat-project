for /R "test\Selected_CNF\SAT-CNF-repository-master\feasible" %%f in (*.cnf) do (
..\release\edusat %1 %2 %3 %4 %%f > tmp.out
grep SAT tmp.out
grep Assignment tmp.out
grep Time tmp.out
)

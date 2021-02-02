echo off
echo *** Note: using release\edusat.exe ***
echo
echo ******** checking SAT instances *******
for %%f in (test\sat\*.cnf) do (
echo %%f
..\release\edusat %1 %2 %3 %4 %%f > tmp.out
grep SAT tmp.out
grep Assignment tmp.out
if %%ERRORLEVEL%% == 1 ECHO "****** SOMETHING IS WRONG (%%f) *******"
grep Time tmp.out
)
echo ******** checking UNSAT instances *******
for %%f in (test\unsat\*.cnf) do (
..\release\edusat %1 %2 %3 %4 %%f > tmp.out
echo %%f
grep UNSAT tmp.out
if %%ERRORLEVEL%% == 1 ECHO "****** SOMETHING IS WRONG (%%f) *******"
grep Time tmp.out
)
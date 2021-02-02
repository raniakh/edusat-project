EduSAT - a basic SAT solver. (c) ofer strichman
===============================================

Type edusat -h for options. 

Clarifications: 

Literal indexing: 
Internally, literal i is represented with the integer 2i, and literal -i with the integer 2i-1.
e.g. the clause (3 -4) is represented by (6 7)
See the functions v2l() and l2v() to understand the conversions. 
l2rl(l) (literal-2-real-literal) converts a literal to its representation in the input cnf, 
e.g. l2rl(7) = -4;
The Neg(Lit l) function changes the sign of a literal. 


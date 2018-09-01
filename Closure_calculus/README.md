# Closure_calculus

This branch contains a *new* version of Closure calculus,
which is uni-variate, not multi-variate.  

The old calculus is described in Closure_calculus.pdf.  The new
calculus generalizes the usual lambda abstractions to become
*closures* of the form

lambda sigma x t 

where sigma is an explicit substitution, x is the bound variable and t
is the abstraction body.


A key feature of this calculus is that reduction does not need to keep
track of scopes in any way; no knowledge of free and bound variables,
scopes or variable re-naming is required. This is a key step towards
converting abstractions into combinations of operators.

Comment. At present, this has triggered changes in all other
sub-directories. Refactoring will be use to limit the changes to the
translations, and not the directories containing SF-calculus and
Fieska-calculus. Also, the pdf's need updating.

Closure_calculus.pdf is now a proper paper. 

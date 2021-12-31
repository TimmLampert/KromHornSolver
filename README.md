KromHornSolver
==============

By Timm Lampert and Anderson Nakano

The KromHornSolver is part of our project to investigate the attempt to define a decision procedure for first-order logic (FOL) by pattern detection in automated theorem proving (ATP). We investigated the attempt to generalize the correct and well-known regularity criterion in ATP by a loop-criterion that merely calls for repeating patterns (for the details consult our paper [Explaining Undecidability of First-Order Logic](http://www2.cms.hu-berlin.de/newlogic/webMathematica/Logic/undecidability_phil_publication.pdf)). The idea is to improve the method of saturation by such a criterion. We investigated the undecidable fragment of Krom-Horn clauses in order to study the limits of such a criterion. We studied this for calculi with skolemization and clauses (tableaux / resolution) as well as for a calculus that is based on nothing but equivalence transformation in pure FOL. For the latter sake, we established the so-called NNF-calculus (see the above quoted paper as well as 
[The New Logic Project](http://www2.cms.hu-berlin.de/newlogic/webMathematica/Logic/introduction.jsp) for details. To do so, we studied how the proof search within tableaux / resolution and the NNF-calculus
mimics the evolution of so called splitting Turing machines (STM). The KromHornSolver is a Mathematica program that takes a definition of a splitting Turing machine (STM) plus an upper bound for its execution as input. It then goes through the following steps:

**Step 1:** Generate the array for the steps of the STM and print its color diagram.

**Step 2:** Translate the STM to clauses (with skolem functions) and to a pure FOL-formula (without skolem functions).

**Step 3:** Generate the deterministic tableau for the clauses and print its color diagram.

**Step 4:** Translate the tableau proof to a pure FOL-formula encoding the corresponding proof in the NNF-calculus and print its color diagram.

**Step 5:** Check attempts to specify a loop-criterion.

Our results are presented in the paper [Explaining Undecidability of First-Order Logic](http://www2.cms.hu-berlin.de/newlogic/webMathematica/Logic/undecidability_phil_publication.pdf). Here, we explain why a loop-criterion fails to decide FOL correctly.


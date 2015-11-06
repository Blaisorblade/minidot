_A good proof is one that makes us wiser._ -- Yuri Manin

minidot
=======

We are formalizing the Dependent Object Types (DOT) calculus, from the bottom up, proving it sound at each step.

- From F to DOT: Type Soundness Proofs with Definitional Interpreters [[pdf]](http://arxiv.org/pdf/1510.05216.pdf)
  - [simply typed lambda calculus](/dev2015/nano0.v)
  - [F_<:](/dev2015/fsub0.v)
  - [D_<:](/dev2015/fsub2.v) (F_<: with first-class types and lower bounds)
  - [full DOT](/dev2015/dot22.v) (add intersection and union types, recursive self types, compound objects, ...)

- Foundations of Path-Dependent Types (OOPSLA'14) [[pdf]](http://lampwww.epfl.ch/~amin/dot/fpdt.pdf)
  - [muDOT](/oopsla/dot.elf)

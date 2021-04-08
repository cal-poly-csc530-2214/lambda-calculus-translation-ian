Lambda Calculus to Python

I wrote this in Coq just to practice using the language.

A couple interesting things:
  Coq strings are kind of nasty, I had to do some working with ascii values
  Everything is step-indexed to ensure recursion is on structurally smaller terms (i.e. to guarantee termination)
  The parser is quite similar to the SML recursive descent parser we wrote for Keen's 430.

You can compile it by doing the following:

  coqc trans.v 

If you don't have coq installed, you will have to install it first:
https://coq.inria.fr/opam-using.html
# Theodore - Proof assistent for FOL

Theodore is a minimal proof assistant designed to prove first-order logic (FOL) formulas in a backward chaining or top-down approach, by applying natural deduction rules. The proof assistant Theodore is written in the functional programming language Haskell and is executed in the interactive environment GHCi. 

# Quick Start Guide


This guide walks you through defining goals, writing proofs, and generating visualizations using LaTeX.

### Installation and usage

Prerequisites: 

1. GHC/GHCi
2. `FOL.hs` and `Theodore.hs`

Load `Theodore.hs` in GHCi:

~~~
ghci Theodore.hs
~~~

## Formula Language

Terms represent variables and functions:

~~~
Var "x"                 -- Variable x
Fun "f" [Term]          -- Function f(x, ...)
~~~

Formulas are constructed using:

~~~
Top, Bot                -– ⊤ and ⊥
Rel "p" [Term]     -– Predicate relation over terms
Neg f                   -– ¬f
Conj f1 f2              -– f1 ∧ f2
Disj f1 f2              -– f1 ∨ f2
Impl f1 f2              -– f1 → f2
Eqiv f1 f2              -– f1 ↔ f2
Alls "x" f                -– ∀x. f
Exis "x" f                -– ∃x. f
~~~

## Defining a Goal

To prove $P \imples Q, P \vdash Q$, we define 2 assumptions, named `h1` and `h2`, and conclusion like follows:

~~~Haskell
let a1 = Assumption "h1" (Impl (Rel "P" []) (Rel "Q" []))
let a2 = Assumption "h2" (Rel "P" [])
let goal = mkGoal [a1, a2] (Var "Q")
print goal
~~~~

This yields the proof goal:
~~~
Goal (1 subgoals):

1. subgoal
• P → Q (h1)
• P (h2)
⊢ Q
~~~

## Building a Proof

The Proof datatype encodes proof trees using natural deduction rules.

# Example: Modus Ponens

~~~Haskell
let proof = ImplE "h1" (Exact "h2") (Exact "h1")
~~~

This uses implication elimination ($\implies_{E}$) on `h1` and `h2` to derive $Q$.

## Type checking and building proofs:

To type check proof to goal use:

~~~Haskell
apply proof goal
~~~

If returns `[]`, all subgoals are proven.

## Proof Constructors

Rule            | Constructor                   | Description
----------------|-------------------------------|-------------
                | `ToDo`                        | Proof ToDo later
$\mathsf{asm}$  | `Exact asmName`               | Use an assumption
$\implies_{I}$  | `ImplI asmName proof`         | Implication introduction
$\land_{I}$     | `ConjI proof1 proof2`         | Conjunction introduction
$\lor_{I_{l}}$  | `DisjlI proof`                | Disjunction introduction (left)
$\lor_{I_{r}}$  | `DisjrI proof`                | Disjunction introduction (right)
$\equiv_{I}$    | `EqivI asmName proof1 proof2` | Equivalence introduction
$\neg_{I}$      | `NegI asmName proof`          | Negation introduction
$\forall_{I}$   | `AllsI "x" proof`	            | Universal introduction
$\exists_{I}$   | `ExisI "x" proof`	            | Existential introduction
$\implies_{E}$  | `ImplE asmName proof1 proof2`	| Implication elimination
$\land_{E}$     | `ConjE asmName proof`         | Conjunction elimination
$\lor_{E}$      | `DisjE asmName proof1 proof2` | Disjunction elimination
$\equiv_{E}$    | `EqivE asmName proof`         | Equivalence elimination
$\neg_{E}$      | `NegE asmName proof`          | Negation elimination
$\forall_{E}$   | `AllsE x asmName proof`       | Universal elimination
$\exists_{E}$   | `ExisE x asmName proof`       | Existential elimination

# LaTeX Export
                              
To generate proof in LaTeX using the prooftree package:

~~~Haskell
genLatexTree proof goal
~~~

Sample output:

~~~Haskell
\begin{prooftree}
\AxiomC{}
\RightLabel{$\mathsf{asm}$}
\UnaryInfC{$Q, P \vdash Q$}
\AxiomC{}
\RightLabel{$\mathsf{asm}$}
\UnaryInfC{$P \vdash P$}
\RightLabel{$\implies_E$}
\BinaryInfC{$P \implies Q, P \vdash Q$}
\end{prooftree}
~~~

You can copy this into a LaTeX document, using `\usepackage{bussproofs}`, to get:

$$
\begin{prooftree}
\AxiomC{}
\RightLabel{$\mathsf{asm}$}
\UnaryInfC{$Q, P \vdash Q$}
\AxiomC{}
\RightLabel{$\mathsf{asm}$}
\UnaryInfC{$P \vdash P$}
\RightLabel{$\implies_E$}
\BinaryInfC{$P \implies Q, P \vdash Q$}
\end{prooftree}
$$
    
## Constructing proofs gradualy

Use `ToDo`s to fill in proof step-by-step:

~~~Haskell
let proof = ImplE "h1" ToDo ToDo
print (apply proof goal)
~~~

This yields:
~~~
Goal (2 subgoals):

1. subgoal
• P (h2)
⊢ P

2. subgoal
• Q (h1)
• P (h2)
⊢ Q
~~~

Now fill in ToDo's with `Exact "h2"` and `Exact "h1"`:

~~~Haskell
let proof = ImplE "h1" (Exact "h2") (Exact "h1")
print (apply proof goal)
~~~

This yields:
~~~
Nothing to prove!
~~~

# More examples

For more examples see `src/Examples.hs`.


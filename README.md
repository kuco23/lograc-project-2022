# Formalization of Temporal Logic in Agda

Temporal logic is an extension of propositional logic, which aims to model a formula's time dependence. A statements is thus represented as a pair (A, t). Here, time was expressed via natural numbers, though further generalizations can be implemented (as it is done in the reference material [Labeled Natural Deduction for Temporal Logics](https://www.math.tecnico.ulisboa.pt/~mvolpe/publications/theses/volpe-phd-thesis.pdf)).

## Temporal logic Overview
Temporal logic extends propositional logic by adding three logical connectives (X, G and U) to the usual ones (∧, ∨, ⇒, ⇔, ¬). Their interpretations are:
- **X A at n** means A holds at time n + 1,
- **G A at n** means A holds from n on,
- **A U B at n** means there is a time m ≥ n such that B holds at m and A holds from n to m-1.
The U operator can be interpreted as _until_. We can also add
- **F A at n** means A holds at least once from n on (at some future time)
as syntactic sugar.

## Project Overview
The main goal was to formalize the interpretation of each new logical connective and then establish a natural deduction system that is sound in that interpretation. The added deduction rules were

```agda
X-intro:
Δ ⊢ φ at (suc n)
----------------
Δ ⊢ (X φ) at n

X-elim:
Δ ⊢ X φ at n
----------------
Δ ⊢ φ at (suc n)

G-intro:
m → n ≤ m → Δ ⊢ φ at m
-----------------------------
Δ ⊢ G φ at n

G-elim:
n ≤ m
Δ ⊢ G φ at n
-------------
Δ ⊢ φ at m

U-intro:
n ≤ m
Δ ⊢ ψ at m
k → n ≤ k → k < m → Δ ⊢ φ at k
-------------------------------
Δ ⊢ φ U ψ at n

U-elim:
m → (n ≤ m) → Δ ++ [ φ at n, ..., φ at m - 1, ψ at m ] ⊢ ρ at k
Δ ⊢ φ U ψ at n
--------------
Δ ⊢ ρ at k
```
The system was then used to prove the following five statements / tautologies:
- G (φ ⇒ ψ) ⇒ (G φ ⇒ G ψ) at n,
- G (φ ⇒ ψ) ⇒ (G φ ⇒ G ψ) at n,
- X(φ ⇒ ψ) ⇒ (X φ ⇒ X ψ) at n,
- G φ ⇒ φ ∧ X G φ at n,
- G (φ ⇒ X φ) ⇒ (φ ⇒ G φ) at n.

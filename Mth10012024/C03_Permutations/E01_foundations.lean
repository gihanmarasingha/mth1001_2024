/-
# Permutations
-/
import Mathlib.Tactic

open Equiv.Perm

def listPerm (x : List (Fin 11)) := List.formPerm x

/-
For a given `n`, the set `Sₙ` is the set of bijective functions from the set
`{1, 2, ..., n}` to itself.

In this file, we'll work with `Sₙ` for `n = 10`.
-/

namespace arithmetic

/-
## Cycle notation

The following defines a permutation using cycle notation. In standard
terminology, this would be expressed as `p = (1 4 5)`.

So `p(1) = 4`, `p(4) = 5`, `p(5) = 1`, and `p(k) = k` for `k ∉ {1, 4, 5}`.
-/

def p := listPerm [1, 4, 5]

/-
The command below confirms `p(1) = 4`.
-/

#eval p 1


/-
# Exercise 1

Define below a permutation `q`, in cycle notation, so that `q(2) = 6`,
`q(4) = 5`, `q(6) = 4`,`q(5) = 2`, and `p(k) = k` for `k ∉ {2, 4, 5, 6}`.

Check your answers using `#eval`.
-/

/-
## Multiplying permutations
-/

/-
Note: type `σ` as `\sigma` and `τ` as `\tau`.

The lines below define `σ = (1 2 4)` and `τ = (1 2 3)`.
-/

def σ := listPerm [1, 2, 4]

def τ := listPerm [1, 2, 3]

/-
Note `σ(τ(1)) = σ(2) = 4`, which we can check as below.
-/

#eval σ (τ 1)

/-
By definition, the product `σ * τ` (written `στ` in conventional maths) is the
composite `σ ∘ τ`. Thus, `(σ * τ)(x) = σ(τ(x))` for every `x`.
-/

#eval (σ * τ) 4

/-
The product `στ` can be expressed as a product `(1 4)(2 3)` of disjoint cycles.
The code below proves this.
-/

example : σ * τ = (listPerm [1, 4]) * (listPerm [2, 3]) := by
  decide

/-
# Exercise 2

Express `τσ` as a product of disjoint cycles and check your answer using Lean.
-/

/-
## Inverses

The inverse `π⁻¹` of a permutation `π` is simply the inverse function of `π`.
For the cycle `σ = (1 2 4)` defined above, its inverse is found simply by
reversing the terms in the cycle. Thus `σ⁻¹ = (1 4 2)`

*Note*: `⁻¹` is written `\-1` in Lean.
-/

example : σ⁻¹ = listPerm [4, 2, 1] := by decide

/-
# Exercise 3

With `σ`, `τ` as above, xxpress `τ⁻¹`, `σ⁻¹τ⁻¹`, and `τ⁻¹σ⁻¹` as products of
disjoint cycles. Check your answers in Lean.
-/

end arithmetic

namespace signs

/-
## Signs and transpositions

A *transpotision* is a cycle of length 2, such as `(4 5)`.
Let `π` be a permutation. Suppose `π = π₁ ⋯ πₘ` is a product of transpositions
`π₁, …, πₘ`. The *sign* of `π` is defined to be `(-1)ᵐ`.

Caution: it requires proof that the sign is well-defined. That is, to prove that
if `π₁ ⋯ πₘ = ρ₁ ⋯ ρₖ` and if `π₁, …, πₘ, ρ₁, …, ρₖ` are transpositions, then
`(-1)ᵐ = (-1)ᵏ`.
-/

/-
As an example, let `σ = (1 6 2)`. You may check that
`σ = (1 6) (6 2)`, so `sign σ = (-1)² = 1`.
-/

def σ := listPerm [1, 6, 2]

example : σ = (listPerm [1, 6]) * (listPerm [6, 2]) := by decide

example : sign σ = 1 := by
  decide

/-
# Exercise 4

Write the function `τ` below as a product of transpositions. Check with Lean.
Determine the sign of `τ`. Check with Lean.

-/

def τ := listPerm [4, 2, 7, 5]


/-
# Exercise 5

Write `π` below as a product of transpositions. Check with Lean.
Determine the sign of `π`. Check with Lean.

*Note*: type `π` as `\pi`.
-/

def π := listPerm [3, 5, 1] * listPerm [2, 4, 6, 7]


end signs

import Mathlib.Data.Set.Basic

/-
# Sets and Logic
-/

section propositions

-- The following line declares propositional variables `p`, `q`, `r`, and `s`
variable (p q r s : Prop)

/-
## Logical operators

Symbol, Command,  Name
`∧`     `\and`    And
`∨`     `\or`     Or
`→`     `\r`      Implies
`↔`     `\iff`    If and only if
`¬`     `\neg`     Negation
-/

-- Below, we use the `tauto` tactic to prove that `p ∨ q` is equivalent to `q ∨ p`.
example : p ∨ q ↔ q ∨ p := by tauto

example : p ∧ q ↔ q ∧ p := by tauto

/-
## Exercise 1
Using truth tables (or otherwise), determine which of the following are true.
Replace `sorry` with `tauto` to check your guesses.
-/

example : (p → q) ↔ (q → p) := by sorry

example : (p → q) ↔ (¬p ∨ q) := by sorry

example : (p → q) ↔ (¬q → ¬p) := by sorry

example : (p → q) ↔ (¬p → ¬q) := by sorry

/-
## Deductions
Note that if `p → q` and `p` are *both* true, then `q` is true. This is the situation
depicted by the first row below.

p | q | p → q | p | q
----------------------
T   T |   T     T   T
T   F |   F     T   F
F   T |   T     F   T
F   F |   T     F   F
-/

/-
In the Lean code below, the appearance of the expressions `h₁ : p → q` and `h₂ : p` before the `:`
should be read as asserting the premises `p → q` and `p`. The line claims that `q` follows from
these premises. The proof is `by tauto`.
-/

example (h₁ : p → q) (h₂ : p) : q := by tauto

/-
## Exercise 2

Determine which of the deductions below are true (using truth tables or otherwise). Check your
guesses by replacing `sorry` with `tauto`.
-/

example (h₁ : p → q) (h₂ : q) : p := by sorry

example (h : p ∧ q) : p := by sorry

example (h : p ∧ q) : q := by sorry

example (h : p ∨ q) : p := by sorry

example (h : p ∨ q) : q := by sorry

example (h₁ : p ∨ q) (h₂ : ¬p) : ¬q := by sorry

example (h₁ : p ∨ q) (h₂ : ¬p) : q := by sorry

example (h : ¬(p ∨ q)) : ¬p := by sorry

example (h : ¬(p ∧ q)) : ¬p := by sorry

end propositions

variable (A B C : Set Nat)

open Set

/-
## Set proofs

We show `A ⊆ A ∪ B` below. Each Lean line corresponds to a line of traditional proof.

### Tactics
*`intro` is similar to "Let".
* `simp only` is used to simplify either the target or a hypothesis using a given theorem.

### Named theorems
* `mem_union` states that `x ∈ A ∪ B` is equivalent to `(x ∈ A) ∨ (x ∈ B)`.

### The InfoView window
As you step through each line of the proof, observe how the "goal" changes in the InfoView window
on the right of the screen.
-/

example : A ⊆ A ∪ B := by
  intro x (h : x ∈ A) -- Let `x ∈ A`. It suffices to show `x ∈ A ∪ B`
  simp only [mem_union] -- That is, to show `(x ∈ A) ∨ (x ∈ B)`.
  tauto -- Which follows easily.

/-
In the proof below, note that we simplify at the hypothesis `h`.
-/

example : A ∩ B ⊆ A := by
  intro x (h : x ∈ A ∩ B) -- Let `x ∈ A ∩ B`. It suffices to show `x ∈ A`.
  simp only [mem_inter_iff] at h -- We have assumed `(x ∈ A) ∧ (x ∈ B)`
  tauto -- The result immediately follows.

/-
## Exercise 3
Determine which of the following are true. Give a proof of the true statement.
You may wish to use `mem_diff`
-/

example : A ⊆ (A \ B) := by sorry

example : (A \ B) ⊆ A := by sorry


/-
### Named theorems
* `mem_inter_iff` states `x ∈ A ∩ B` is equivalent to `(x ∈ A) ∧ (x ∈ B)`.
-/
example : (A ∩ B) ∪ C ⊆ (A ∪ C) ∩ (B ∪ C) := by
  intro x (h : x ∈ (A ∩ B) ∪ C) -- Let `x ∈ (A ∩ B) ∪ C`. We must show `x ∈ (A ∪ C) ∩ (B ∪ C)`.
  simp only [mem_inter_iff, mem_union] -- Equally, `(x ∈ A ∨ x ∈ C) ∧ (x ∈ B ∨ x ∈ C)`
  simp only [mem_inter_iff, mem_union] at  h -- We have `x ∈ A ∧ x ∈ B ∨ x ∈ C`
  tauto -- The result follows.

/-
## Exercise 4
Prove the result below. Ensure you comment the Lean proof with 'traditional' mathematics.
-/
example : (A ∪ C) ∩ (B ∪ C) ⊆ (A ∩ B) ∪ C := by sorry

/-
## Exercise 5
Determine which of the following are true. Give a proof.
-/

example : (A \ B) ∪ (A \ C) ⊆ A \ (B ∪ C):= by sorry

example : (A \ B) ∩ (A \ C) ⊆ A \ (B ∪ C):= by sorry

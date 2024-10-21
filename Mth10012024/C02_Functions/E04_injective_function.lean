import Mathlib.Tactic

/-
# Injective functions
For a function `f : A → B` to be injective means that for all `a₁, a₂ ∈ A`, if `f(a₁) = f(a₂)`,
then `a₁ = a₂`.

The only difference in Lean is that we write `a₁ a₂ : A` in place of `a₁, a₂ ∈ A`.
-/

namespace non_injective_examples

open Function

/-
## Non-injective examples
Below, `p : ℤ → ℤ` is a function given by `p(n) = n² + 2`.
Note `ℤ` is typed as `\Z`.
-/
def p (n : ℤ) : ℤ := n ^ 2 + 2

-- Values of `p` can be calculated:

#reduce p 5

#reduce p (-4)

/-
The example below shows that `p` is not injective.
Remember, `₁` is typed as `\1` and `¬` is typed `\n`
-/
example : ¬(Injective p) := by
  rintro (h : Injective p) -- For a contradiction, suppose `p` is injective. Call this `h`.
  have h₁ : p (-1) = p (1) := by trivial -- Trivially, we have `p(-1) = p(1)`. Call this `h₁`
  have h₂ : (-1) = 1 := h h₁ -- Applying injectivity of `p` to `h₁` gives `-1 = 1`.
  trivial -- This is a contradiction.

/-
# Exercise 1
Give a dual Lean/English proof (as above) that `f` below is not injective.
-/

def f (n : ℤ) : ℤ := n ^ 2 - 1

end non_injective_examples

/-
## Injective examples
-/

namespace injective_examples

open Function

/-
Below is a function `q : ℝ → ℝ` given by `q(x) = 3x + 5`.
We show that `q` is injective.
-/

def q (x : ℝ) : ℝ := 3 * x + 5

example : Injective q := by
  rintro (x₁ x₂ : ℝ) -- Let `x₁` and `x₂` be real numbers.
  rintro (h : q x₁ = q x₂) -- Assume `q(x₁) = q(x₂)`.
  show x₁ = x₂            -- It suffices to show `x₁ = x₂`.
  change 3 * x₁ + 5 = 3 * x₂ + 5 at h -- By definition, we have `3x₁ + 5 = 3x₂ + 5`.
  linarith                -- Rearranging gives `x₁ = x₂`.

/-
# Exercse 2

Adapt the example above to define a function `t : ℝ → ℝ` where `t(x) = 7x - 4`.
Prove that `t` is injective.
-/

/-
Another approach to proving injectivity is to show that a function is increasing.

The lemma below proves that if a function is increasing, then it is injective. You do not need to
understand the proof.
-/
lemma injective_of_increasing {α : Type*} {β : Type*} [LinearOrder α] [LinearOrder β]
  {q : α → β} (h : ∀ x y : α, x < y → q x < q y) : Injective q := by
  rintro (x y : α) (h₂ : q x = q y)
  by_contra h₃
  rcases lt_or_gt_of_ne h₃ with ((h₄ : x < y) | (h₅ : y < x))
  · have h₅ : q x < q y := h x y h₄
    exact ne_of_lt h₅ h₂
  · have h₅ : q y < q x := h y x h₅
    exact ne_of_gt h₅ h₂

/-
The next lemma shows that the squaring function is increasing on `ℕ`.
-/
lemma increasing_square {x y : ℕ} (h : x < y) : x ^ 2 < y ^ 2 := by
  apply Nat.pow_lt_pow_left h
  norm_num

/-
Combining the two lemmas above, we see that the squaring function on `ℕ` is injective
-/

def f (n : ℕ) : ℕ := n ^ 2

example : Injective f := by
  apply injective_of_increasing -- It suffices to show that `f` is increasing,
  apply increasing_square       -- which we have proved before.

def g (m : ℕ) : ℕ := m ^ 2 + 10

example : Injective g := by
  apply injective_of_increasing -- It suffices to show that `g` is increasing
  rintro (x y : ℕ)         -- Let `x` and `y` be natural numbers.
  rintro (h : x < y)             -- Suppose `x < y`.
  show x ^ 2 + 10 < y ^ 2 + 10  -- We must show `x² + 10 < y² + 10`.
  have h₂ : x^2 < y^2           -- We have `x² < y²`
    := increasing_square h      -- as the square function is increasing.
  linarith                      -- The result follows.

/-
# Exercise 3

Prove that the following function is injective. Adapt the example above.
-/

def u (m : ℕ) : ℕ := 3 * m ^ 2 + 2

end injective_examples

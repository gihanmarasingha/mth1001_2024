import Mathlib.Tactic

/-
# Composite functions

Given `f : A → B` and `g : B → C`, the composite function `g ∘ f` is a function
`g ∘ f : A → C` with the rule `(g ∘ f)(a) = g(f(a))`.

**Remember** `→` is typed `\r`.
-/

namespace composite_types

open Function

variable (A B C : Type*) (f : A → B) (g : B → C)

-- Note that `∘` is typed `\o`
#check g ∘ f

example (a : A) : (g ∘ f) a = g (f a) := by trivial

/-
We additionally decalre a function `s : C → A`.
-/
variable (s : C → A)

/-
## Types of composite functions

# Exercise 1

Which of the following are defined? What is the domain and codomain in each case? Check your
answer using `#check`, as above.

* `f ∘ g`
* `s ∘ g`
* `g ∘ s`
* `f ∘ s`
* `(g ∘ f) ∘ s`
* `s ∘ (g ∘ f)`
-/

#check g ∘ f

end composite_types

namespace composite_values

/-
## Evaluating values of functions and composite functions

Below `p : N → ℤ` and `q : ℤ → ℚ` are functions.

`p(a)` is defined piecewise so that `p(a) = 2a - 6` if `a` is even and `p(a) = 2a + 2` if `a` is odd.

`q(y)` is just `y²`
-/

def p (a : ℕ) : ℤ := if Even a then (2 * a - 2) else (2 * a  + 2)

def q (y : ℤ) : ℚ := y ^ 2

-- The `#eval` command evaluates the application of `p` to natural numbers, ...
#eval p 3

-- ... `q` to integers,
#eval q (4)

-- and `q ∘ p` to natural numbers.

#eval (q ∘ p) (3)

/-
# Exercise 2

Determine (without Lean) the values of `(q ∘ p)(4)` and `(q ∘ p)(-2)`. Check your answers using
`#eval`.
-/

/-
The function `t : ℚ → ℕ` gives the denominator of its input. That is, if `x` is a rational number,
then there exists a unique pair `(m,n)` where `x = m / n`, `m` is an integers, `n` is a natural
number, and `m` and `n` are coprime. Then `n` is the denominator of `x`.
-/
def t (x : ℚ) : ℕ := x.den


#eval t (5/7)
/-
# Exercise 3

Without using Lean, compute `t(10)`, `t(10/24)`, `t(24/56)`, `t(-8/10)`. Check your answers using
`#eval`.
-/

/-
# Exercise 4
Find a rational number `x` such that `(p ∘ t)(x) = 100`. Check your answer with `#eval`
-/

end composite_values

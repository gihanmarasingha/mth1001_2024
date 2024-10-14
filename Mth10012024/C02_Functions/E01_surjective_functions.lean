import Mathlib.Tactic

/-
# Functions: Surjective functions

## Defining a function
-/

/-
*Language note*: the `namespace` command introduces a new namespace. This helps to avoid naming
conflicts. The functions `f` in this namespace can only be referred to as `f` within the namespace.
-/
namespace mydefs

/-
Here's a function `f : ℕ → ℕ`. Note `ℕ` can be typed as `ℕ`. It's domain is `ℕ` and its codomain
is `ℕ`. By defintion, it takes each `x` to `2 * x`.
-/
def f (x : ℕ) : ℕ := 2 * x

/-
## Evaluating a function
The `#reduce` command shows the value of a Lean expression, where possible.
**Note** in Lean, `f 10` is the way we write `f(10)`. You could also write `f (10)`.
-/

#reduce f 10

/-
## Equality of functions
-/

-- Here's a function `g : ℕ → ℕ`. It definition is *identical* to the definition of `f`.
def g (x : ℕ) : ℕ := 2*x

/-
The following line says "I claim that `f = g`, the proof is trivial"/
-/
example : f = g := by trivial

/-
Here is another function, `p`.
Note: `ℤ` is typed as `\Z`.
-/

def p (x : ℕ) : ℤ := 2 * x
/-
# Exercise 1
Is the function `f` equal to the function `p` above If so, why? If not, why not?

What happens if you try the code below? Read and explain the error message.

`example : f = p := by sorry`
-/


-- The function `k` is not *identical* to `f`. Though they are equal.
def k (x : ℕ) : ℕ := x + x

-- Replacing `sorry` with `trivial` will give an error message.
example : f = k := by sorry

/-
We'll prove that `f = k`. First, we need a few tactics and a theorem.

### More tactics
* `ext`: (short for extensionality) converts proving `f = k` into letting `x` be a natural number and
  proving `f x = k x`.
* `show`: allows you to restate the target.
* `linarith`: this tactic proves many simply 'algebraic' equations and inequalities. It can prove
  simple algebraic contradictions.
-/
example : f = k := by
  ext x -- Let `x` be a natural number.
  show 2 * x = x + x -- We must show `2 * x = x + x`
  linarith -- This is clearly true.

/-
# Exercise 2

Create Lean functions `q : ℕ → ℕ`,  `s : ℕ → ℕ`, `t : ℕ → ℤ` so that
`q(n) = 3*n + 5`, `s(m) = 3*(m + 1) + 2`, and `t(x) = 3*x + 5`.

Which of the functions are equal? Prove equality of the two that are equal.
-/


/-
## Unequal functions
-/

def t (x : ℕ) : ℕ := 3 * x

/-
To show `f` *does not equal* `t` is to show there is some `x` such that `f(x) ≠ t(x)`.

Remember, the `simp` tactic can simplify a statement using a supplied result

Notation: type `≠` as `\ne`.
-/

example : f ≠ t := by
  intro (h : f = t) -- For a contradiction, assume that `f = t`. Call this assumption `h`.
  have h₂ : f 2 = t 2 := by simp [h] -- Using `h`, this means `f(2) = t(2)`.
  trivial -- This is a contradiction

/-
The function `s` below is defined piecewise.

s(x) = 5 if `x = 6`, otherwise, s(x) = 2 * x.
-/

def s (x : ℕ) : ℕ := if x = 6 then 5 else 2 * x

#reduce s 6

#reduce s 7

/-
# Exercise 3
Prove that `f ≠ s`.
-/

/-
**Important**: ensure you use the following line, which ends the `mydefs` namespace.
-/
end mydefs

/-
## Surjectivity

Let `f : A → B` be a function. For `f` to be surjective means that for every `b ∈ B`, there exists
`a ∈ A`, such that `f(a) = b`.

In Lean, the domain and codomain of a function are *types*, not sets. We write `b : B` and `a : A`
in place of `b ∈ B` and `a ∈ A`. The meaning is very similar.
-/

namespace surjective_examples

/-
**IMPORTANT** Ensure you type `open Function` below.
For the nerds: this opens the `Function` namespace, permitting you to use the shorthand `Surjective`
in place of the full name `Function.Surjective`.
-/

open Function

/-
### Surjectity proof example
The function `f : ℤ → ℤ` given by `f(x) = x + 5` above is surjective. To prove this is to show that
for every integer `y`, there exists an integer `ℤ` such that `f(x) = y`.

Below,
* `set` is used to define a local variable. Here `set x := y - 5 with h` introduces a local variable
  `x = y - 5` and labels this equation `h`.
* `use` tell Lean to use the variable to satisfy the 'exists' quantifier. Here, `use x` tells
  Lean to take our `x` for the `x` in the `∃ x`.

**Note**: type `ℤ` as `\Z`.
-/

def f (x : ℤ) : ℤ := x + 5

example : Surjective f := by
  intro (y : ℤ)           -- Let `y ∈ Z`.
  show ∃ (x : ℤ), f x = y -- We must show there exists `x ∈ ℤ` such that `f(x) = y`.
  set x := y - 5 with h   -- Let
  use x                   -- `x = y - 5`.
  show x + 5 = y          -- We must show `x + 5 = y`.
  linarith                -- Which is clearly true.

/-
### Non surjectivity proof example
The function `p : ℕ → ℕ` given by `p(n) = n + 5` is *not* surjective, even though it has the same
function rule as `f`.

Applying surjectivity of `p` to `1`, we have `∃ (n : ℕ), n + 5 = 1`.
In the proof below, `obtain` extracts this information, getting a natural number `n` and
the hypothesis `h₂ : n + 5 = 1`.

Note the angle brackets `⟨` and `⟩` in the `obtain` line are typed `\<` and `\>`.
-/
def p (n : ℕ) : ℕ := n + 5

example : ¬(Surjective p) := by
  intro (h : Surjective p)          -- For a contradiction, suppose that `p` is surjective.
  obtain ⟨n, h₂ : n + 5 = 1⟩ := h 1 -- Applying this to `1`, we get `n` such that `n + 5 = 1`.
  linarith -- But this is a contradiction, as `n = -4` is not a natural number.

/-
# Exercise 4
For each of the function `p` and `s` below, prove either that they are surjective or that they are
not surjective. Adapt the proofs above. Ensure you give both Lean and English proofs.

**Note**: type `ℝ` as `\R`.
-/
def q (x : ℝ) : ℝ := 2 * x + 5

def s (x : ℕ) : ℕ := 2 * x + 5

end surjective_examples

/-
## Set equality and ranges
-/

namespace set_examples

open Set

def S : Set ℤ := {2 * x | x : ℤ}

def T : Set ℤ := {2 * y + 6 | y : ℤ}

/-
### Set equality
We show that `T = S` by first showing `T ⊆ S` and `S ⊆ T`.
-/

lemma S_sub_T : S ⊆ T := by
  intro (s : ℤ) (h : s ∈ S)         -- Let `s ∈ ℤ`
  obtain ⟨x, h₂ : 2 * x = s⟩ := h   -- We get `x ∈ ℤ` such that `2 * x = s`
  show ∃ y, 2 * y + 6 = s           -- We must show `2 * y + 6 = s`, for some `y ∈ ℤ`
  set y := x - 3 with k             -- Let `y = x - 3`
  use y                             --
  linarith                          -- Then the result follows.

lemma T_sub_S : T ⊆ S := by sorry

/-
In the theorem below, we use the theorem `Subset.antisymm`, which combines the proofs `T_sub_S` and
`S_sub_T` to give a proof that `T = S`.
-/

lemma T_eq_S : T = S := by
  apply Subset.antisymm T_sub_S S_sub_T

/-
# Exercise 4
Complete the proof of lemma `T_sub_S` above
-/

/-
### Range
Let `f : A → B` be a function. Then the range of `f` is the set `{f(a) : a ∈ A}`. In Lean,
this set is written `{f a | a : A}`
-/

example (A B : Type) (f : A → B) : range f = {f a | a : A} := by trivial

def f (x : ℤ) : ℤ := 2 * x

/-
Using the definitons of `range`, `f`, and `S`, the range of `f` is `S`.
-/
example : range f = S := by
  simp only [range, f, S]

/-
Using the definitions of `range`, `f`, and `S`, together with the theorem `T_eq_S`, the range
of `f` is `T`.
-/
example : range f = T := by
  simp only [range, f, T_eq_S, S]


/-
# Exercise 5
Prove that the range of the function `g` is `V`.
**Note** You may need may need to prove intermediate results.
-/

def U : Set ℤ := {3 * n | n : ℤ}

def V : Set ℤ := {3 * m + 9 | m : ℤ}

def g (x : ℤ) : ℤ := 3 * x

example : range g = V := by sorry

end set_examples

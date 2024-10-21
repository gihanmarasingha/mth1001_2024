import Mathlib.Tactic

/-
# Composite surjective functions
-/


namespace composite_surjective

open Function

/-
Consider functions `f : A → B` and `g : B → C`
-/

variable (A B : Type*) (f : A → B) (g : B → C)

/-
If you forget the definition of `Surjective`, you can use the `#print` command, as follows.
-/

-- The InfoView window shows that a function `f : α → β` is `Surjective` if `∀ (b : β), ∃ (a : α), f a = b`.
#print Surjective

/-
Below is a proof that if `f` and `g` are surjective, then so is `g ∘ f`.
Remember the following symbols:
* `∀` is typed `\all`
* `∃` is typed `\ex`
* `⟨` is typed `\<`
* `⟩` is typed `\>`.
-/

example (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  -- We will show that `∀ (c ∈ C), ∃ (a ∈ A), g(f(a)) = c`.
  show ∀ (c : C), ∃ (a : A), g (f a) = c
  rintro (c : C)                -- Let `c ∈ C`.
  show ∃ (a : A), g (f a) = c   -- We must show `∃ (a ∈ A), g(f(a)) = c`.
  obtain ⟨b : B, hb : g b = c⟩  -- We get `b ∈ B` such that `g(b) = c`,
    := hg c                     -- by surjectivity of `g`, applied to `c`.
  obtain ⟨a : A, ha : f a = b⟩  -- We get `a ∈ A` such that `f(a) = b`,
    := hf b                     -- by surjectivity of `f`, applied to `b`.
  use a                         -- Using this `a`
  simp [ha, hb]                 -- with the equations we've proved, the result follows.

/-
# Exercise 1

The proof above is worth examining and playing with. Below, I've given invalid English-
language proofs.

An invalid proof doesn't (necessarily) make false assertions. A proof that only makes true
assertions can still be invalid if there are gaps in the argument.

Determine where the issues lie. Translate into Lean and check your understanding.

### Invalid Proof 1
Assume `f` is surjective. Then, for every `a ∈ A`, there exists at least one `b ∈ B` such that
`f(a) = b`. Assume `g` is surjective. Then, for every `b ∈ B`, there exists at least one `c ∈ C`
such that `g(b) = c`.

Now `f(a) = b` and `g(b) = c`. Substituing the first equation into the second gives `g(f(a)) = c`.
So `(g ∘ f)(a) = c`.

Thus `g ∘ f` is surjective as for every `a ∈ A`, there exists at least one `c ∈ C` such that
`(g ∘ f)(a) = c`.

### Invalid Proof 1

Let `a ∈ A`. Then if `f(a) = b`, then `b ∈ B`. So `g(f(a)) = c` with `c ∈ C`.
Therefore `g(b) = c` as `f(a) = b`

### Invalid Proof 3
As `f` is surjective, the codomain of `f` is the domain of `g`. As `g` is surjective, this means
`g ∘ f` is surjective.

### Invalid Proof 4
Let `a ∈ A` and `b ∈ B`. As `f` is surjective, `f(a) = b`. Let `c ∈ C`. As `g` is surjective,
`g(b) = c`.

Substituting, `g(f(a)) = g(b) = c`. So `(g ∘ f)(a) = c`. So `g ∘ f` is surjective.
-/

/-
# Exercise 2

## Exercise 2(a)
One of the following results is true. Prove the true result.

## Exercise 2(b)
In the true result, are there any unused hypotheses? Is the result still true if you remove those
hypotheses?
-/

example (hgf : Surjective (g ∘ f)) (hf : Surjective f) : Surjective g := by sorry

example (hgf : Surjective (g ∘ f)) (hg : Surjective g) : Surjective f := by sorry


end composite_surjective

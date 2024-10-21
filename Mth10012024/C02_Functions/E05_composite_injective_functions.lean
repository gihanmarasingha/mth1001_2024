import Mathlib.Tactic

/-
# Composite injective functions
-/

namespace composite_injective

open Function

variable (A B : Type*) (f : A → B) (g : B → C)

/-
Below is the start of a proof that if `f` and `g` are injective, then so is `g ∘ f`.
Type `∀` as `\all` and `→` as `\r`.

The `dsimp` line below isn't necessary. It helps *you*, the proof writer, by asking Lean to
unfold the definition of `Injective`. The result is shows in the InfoView window on the right.
-/
example (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  dsimp [Injective]
  show ∀ (a₁ a₂ : A), g (f a₁) = g (f a₂) → a₁ = a₂
  -- We must show that for all `a₁, a₂ ∈ A`, if `g(f(a₁)) = g(f(a₂))`, then `a₁ = a₂`.
  rintro (a₁ a₂ : A) -- Let `a₁, a₂ ∈ A`.
  rintro (h : g (f a₁) = g (f a₂)) -- Assume `g(f(a₁)) = g(f(a₂))`.
  show a₁ = a₂ -- We must show `a₁ = a₂`.
  have h₂ : f a₁ = f a₂ -- But `f(a₁) = f(a₂)`,
    := hg h             -- by injectivity of `g`, applied to `g(f(a₁)) = g(f(a₂))`.
  sorry

/-
# Exercise 1

Complete the proof above
-/


/-
# Exercise 2

## Exercise 2(a)
One of the following results is true. Prove the true result.
**Note**: remember that `simp [h]`, can be used to prove (or simplify) the target, using the
hypothesis `h`.

## Exercise 2(b)
In the true result, are there any unused hypotheses? Is the result still true if you remove those
hypotheses?
-/

example (hgf : Injective (g ∘ f)) (hf : Injective f) : Injective g := by sorry

example (hgf : Injective (g ∘ f)) (hg : Injective g) : Injective f := by sorry


end composite_injective

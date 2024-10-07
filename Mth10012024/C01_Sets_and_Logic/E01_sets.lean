import Mathlib.Data.Finset.Powerset

/-
# Sets
-/

namespace finite

def S : Finset Nat := {1, 3, 7}

/-
This is a comment. It has no meaning to Lean. The line above defines a set, called `S`, of finite
natural numbers whose elements are 1, 3, and 7.
-/

/-
## Set membership
The set membership symbol `∈` is typed `\in` (followed by a space or tab).

## Exercise 1
The line below claims that `9 ∈ S`. Do you think it is true?

Replace `sorry` with `trivial` to see if Lean can prove the claim using the `trivial` tactic. If
`trivial` fails, you'll see a red squiggly line below and an error message in the 'InfoView'
window on the right

Change `9` to another number to see if you can prove the result.
-/
example : 9 ∈ S := by sorry

/-
## Subset
The subset relation `⊆` is typed as as `\sub`.

The lines below prove that `{1} ⊆ S` and that `{1, 3} ⊆ S`.
-/
example : {1} ⊆ S := by trivial

example : {1, 3} ⊆ S := by trivial

/-
## The empty set

Note: `∅` is typed as `\empt`.

## Exercise 2
Adapt the lines above to give all subsets of `S`.

-/

def T : Finset Nat := {3, 1, 7, 7, 3, 3}

/-
## Cardinality

## Exercise 3
Replace the first `sorry` below with the cardinality of `T` and the second `sorry` with `trivial`.
Explain your answer.
-/
example : T.card = sorry := by sorry

def A : Finset Nat := {3, 1, 5, 6}

def B : Finset Nat := {1, 6}

/-
## Set equality

## Exercise 4
Replace the first `sorry` below with one of `T`, `A`, and `B`. Replace the second `sorry` with
`trivial`. Explain your answer.
-/
example : S = sorry := by sorry


/-
## Intersection

## Exercise 5
Replace the first `sorry` below with the intersection of `S` and `A`. Replace the second `sorry`
with `trivial`. Add more lines giving all pairs of intersections of the sets seen so far.

Type `∩` as `\i`.
-/
example : S ∩ A = sorry := by sorry


/-
## Union

## Exercise 6
Replace the first `sorry` below with the union of `S` and `A`. Replace the second `sorry`
with `trivial`. Add more lines giving all pairs of unions of the sets seen so far.

Type `∪` as `\un`
-/
example : S ∪ A = sorry := by sorry


/-
## Set difference

With `A` and `B` as defined above, `A \ B = {3, 5}`, as shown below.
-/
example : A \ B = {3, 5} := by trivial

/-
## Exercise 7
In each of the examples below, replace the first `sorry` with the set of elements of the set
difference and the second `sorry` with `trivial`
-/

example : A \ S = sorry := by sorry

example : S \ A = sorry := by sorry


/-
## Powerset

Recall that the powerset of a set is the set of all subsets of that set.
Here is the power set of `B`.
-/
example : B.powerset = {∅, {1}, {6}, {1, 6}} := by trivial

/-
## Exercise 7

Adapt the example above to give the powerset of `S`. Write your answer below.
-/


/-
## Exercise 8
Below, we show that the the cardinality of the powerset of `S` is 8

Adapt this, on a separate line, to give the cardinality of the powerset of `A`. You need not first
compute the powerset of `A`.
-/
example : S.powerset.card = 8 := by trivial


/-
## Cartesian product

In Lean, the symbol for the Cartesian product of sets is `×ˢ`, typed `\x\^s`.

Below is the Cartesian product `B ×ˢ B`.

**Note** in traditional mathematics, this is written `B × B`, not `B ×ˢ B`.
-/

example : B ×ˢ B = { (1, 1), (1, 6), (6, 1), (6, 6)} := by trivial

/-
## Exercise 9

Adapt the above example to give `S ×ˢ B`. Give the answer in the space below.
-/




end finite

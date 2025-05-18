import MathUniverse.Group
import Mathlib.Data.Set.Basic

/-!
# Subgroup

Defines **subgroups** of a group and proves basic properties.

## Notation

We write `isSubgroup G H` to mean `H` is a subgroup of the group `G`, i.e. `1 ∈ H` and `∀ a b, a ∈ H → b ∈ H → a * b⁻¹ ∈ H`.

## References

* Wikipedia on [Subgroup](https://en.wikipedia.org/wiki/Subgroup).

Tags: algebra, group, subgroup
-/

open Set

def isSubgroup {G : Type} (g : Group G) (H : Set G) : Prop :=
  g.one ∈ H ∧ ∀ a b, a ∈ H → b ∈ H → g.mul a (g.inv b) ∈ H

@[simp] theorem isSubgroup_univ {G : Type} (g : Group G) : isSubgroup g Set.univ := by
  simp [isSubgroup]

example {G : Type} (g : Group G) (H : Set G) (h : isSubgroup g H) : g.one ∈ H :=
  h.1

import Universe.Monoid

/-!
# Group

Defines the structure of a **group** as a monoid with inverses and proves fundamental properties.

## Notation

We write `G : Type` for the carrier type, `g₁ * g₂` for multiplication, `1` for the identity, and `g⁻¹` for the inverse.

## References

* Wikipedia on [Group (mathematics)](https://en.wikipedia.org/wiki/Group_(mathematics)).

Tags: algebra, group, structure
-/

structure Group (G : Type) extends Monoid G where
  inv : G → G
  mul_left_inv : ∀ a : G, mul (inv a) a = one

@[simp] theorem mul_left_inv {G : Type} (g : Group G) (a : G) : g.mul (g.inv a) a = g.one :=
  g.mul_left_inv a

example {G : Type} (g : Group G) (a : G) : g.mul (g.inv a) a = g.one := by
  simp

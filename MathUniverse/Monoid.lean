/-!
# Monoid

Defines the structure of a **monoid** on a type and proves basic properties.

## Notation

We write `M : Type` for the carrier type, `m₁ * m₂` for multiplication, and `1` for the identity element.

## References

* Wikipedia on [Monoid](https://en.wikipedia.org/wiki/Monoid).

Tags: algebra, monoid, structure
-/

structure Monoid (M : Type) where
  mul : M → M → M
  one : M
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a

@[simp] theorem one_mul {M : Type} (m : Monoid M) (a : M) : m.mul m.one a = a :=
  m.one_mul a

@[simp] theorem mul_one {M : Type} (m : Monoid M) (a : M) : m.mul a m.one = a :=
  m.mul_one a

example {M : Type} (m : Monoid M) (a b : M) : m.mul (m.mul a b) m.one = m.mul a b := by
  simp [mul_one]

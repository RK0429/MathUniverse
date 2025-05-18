import MathUniverse.Group

/-!
# GroupHom

Defines **group homomorphisms** and proves basic properties.

## Notation

We write `G →* H` for a homomorphism from `G` to `H`.

## References

* Wikipedia on [Group homomorphism](https://en.wikipedia.org/wiki/Group_homomorphism).

Tags: algebra, group, homomorphism
-/

structure GroupHom {G H : Type} (gG : Group G) (gH : Group H) where
  toFun : G → H
  map_mul : ∀ x y, toFun (gG.mul x y) = gH.mul (toFun x) (toFun y)
  map_one : toFun gG.one = gH.one

-- notation `→*` removed; use `GroupHom gG gH` explicitly

theorem map_inv {G H : Type} (gG : Group G) (gH : Group H) (f : GroupHom gG gH) (x : G) :
    f.toFun (gG.inv x) = gH.inv (f.toFun x) := by
  -- Proof omitted
  sorry

example {G H : Type} (gG : Group G) (gH : Group H) (f : GroupHom gG gH) : f.toFun gG.one = gH.one :=
  f.map_one

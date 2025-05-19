import Universe.Group

/-!
# GroupAction

Defines **group actions** on types and gives examples.

## Notation

We write `g • x` for the action of `g : G` on `x : X`.

## References

* Wikipedia on [Group action](https://en.wikipedia.org/wiki/Group_action).

Tags: algebra, group, action
-/

structure GroupAction (G : Type) (g : Group G) (X : Type) where
  smul : G → X → X
  smul_one : ∀ x, smul g.one x = x
  smul_mul : ∀ a b x, smul (g.mul a b) x = smul a (smul b x)

-- Example: left multiplication action of G on itself
def byLeftMul {G : Type} (g : Group G) : GroupAction G g G where
  smul := fun a x => g.mul a x
  smul_one := fun x => g.one_mul x
  smul_mul := fun a b x => g.mul_assoc a b x

example {G : Type} (g : Group G) (x : G) : (byLeftMul g).smul g.one x = x :=
  g.one_mul x

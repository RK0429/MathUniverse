/-!
# Factorial

Defines the **factorial** function on `Nat` and proves fundamental properties.

## Summary

We define
```lean
def factorial : Nat → Nat
| 0       => 1
| (n + 1) => (n + 1) * factorial n
```
and prove:

* `factorial_zero` : `factorial 0 = 1`.
* `factorial_succ` : `factorial (n + 1) = (n + 1) * factorial n`.
* `factorial_three` : `factorial 3 = 6`.
* `factorial_pos` : `factorial n > 0` for all `n`.

## Notation

Uses standard pattern matching and multiplication on `Nat`.

## References

* Wikipedia: *Factorial*.

Tags: recursion, factorial, natural numbers
-/


def factorial : Nat → Nat
| 0       => 1
| (n + 1) => (n + 1) * factorial n

@[simp] theorem factorial_zero : factorial 0 = 1 := rfl

@[simp] theorem factorial_succ (n : Nat) : factorial (n + 1) = (n + 1) * factorial n := rfl

theorem factorial_three : factorial 3 = 6 := rfl

theorem factorial_pos (n : Nat) : factorial n > 0 := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    calc
      factorial (n + 1) = (n + 1) * factorial n := factorial_succ n
      _ > 0 := Nat.mul_pos (Nat.succ_pos n) ih

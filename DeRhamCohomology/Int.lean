import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Parity

namespace Int

theorem neg_one_pow_sub_eq_pow_add {m n : ℕ} (h : n ≤ m) : (-1) ^ (m - n) = (-1) ^ (m + n) := calc
  (-1) ^ (m - n) = (-1) ^ (m - n + 2 * n) := by
    simp [pow_add, pow_mul, neg_sq]
  _ = (-1) ^ (m + n) := by
    congr 1
    omega

end Int

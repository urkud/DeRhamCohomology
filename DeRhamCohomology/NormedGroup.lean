import Mathlib.Analysis.Normed.Group.Basic

variable {E : Type*} [SeminormedGroup E]

@[to_additive norm_neg_one_pow_zsmul]
theorem norm_zpow_neg_one_zpow (g : E) (n : ℕ) : ‖g ^ ((-1) ^ n : ℤ)‖ = ‖g‖ := by
  induction n <;> simp [*, pow_succ]

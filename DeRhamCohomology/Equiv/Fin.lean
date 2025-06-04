import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Equivalences for `Fin n`
-/

assert_not_exists MonoidWithZero

universe u

variable {m n o: ℕ}

def finAssoc {m n p : ℕ} : Fin (m + n + p) ≃ Fin (m + (n + p)) :=
  finCongr <| Nat.add_assoc m n p

def finAddFlipAssoc {m n p : ℕ} : Fin (m + p + n) ≃ Fin (m + (n + p)) := by
  refine finCongr ?eq
  rw [Nat.add_right_comm]
  exact Nat.add_assoc m n p

theorem finAddFlip_finSumFinEquiv {m n : ℕ} (a : Fin m ⊕ Fin n) :
    finAddFlip (finSumFinEquiv a) = finSumFinEquiv (Equiv.sumComm _ _ a)  := by
  refine Eq.symm (DFunLike.congr_arg finSumFinEquiv ?h₂)
  rw [Equiv.congr_arg rfl]
  refine (Equiv.apply_eq_iff_eq (Equiv.sumComm (Fin m) (Fin n))).mpr ?h₂.a
  rw [Equiv.symm_apply_apply]

import Mathlib.Data.Fin.Tuple.Basic

open Function

namespace Fin

variable {n : ℕ} {α : Fin (n + 1) → Sort*}

theorem succAbove_succ_eq_succAbove_castSucc {i j : Fin n} (h : i ≠ j) :
    i.succ.succAbove j = i.castSucc.succAbove j := by
  rcases h.lt_or_lt with hlt | hlt
  · rw [succAbove_succ_of_lt _ _ hlt, succAbove_castSucc_of_le _ _ hlt.le]
  · rw [succAbove_succ_of_le _ _ hlt.le, succAbove_castSucc_of_lt _ _ hlt]

theorem insertNth_succ {α : Sort*} (p : Fin n) (a : α) (x : Fin n → α) :
    p.succ.insertNth a x = p.castSucc.insertNth a x ∘ Equiv.swap p.castSucc p.succ := by
  ext j
  cases' j using p.succ.succAboveCases with j
  · simp
  · rw [insertNth_apply_succAbove, comp_apply]
    rcases eq_or_ne j p with rfl | hne
    · rw [succAbove_succ_self, Equiv.swap_apply_left, ← succAbove_castSucc_self,
        insertNth_apply_succAbove]
    · rw [Equiv.swap_apply_of_ne_of_ne _ (succAbove_ne _ _)]
      · rw [succAbove_succ_eq_succAbove_castSucc hne.symm, insertNth_apply_succAbove]
      · rwa [← succAbove_succ_self, succAbove_right_injective.ne_iff]

end Fin

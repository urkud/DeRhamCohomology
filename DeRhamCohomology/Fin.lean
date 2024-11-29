import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic

open Function

namespace Fin

attribute [simp] succAbove_right_inj

theorem succAbove_succAbove_succAbove_predAbove {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (k : Fin n) :
    (i.succAbove j).succAbove ((j.predAbove i).succAbove k) = i.succAbove (j.succAbove k) := by
  simp only [succAbove, predAbove]
  split_ifs
  all_goals simp only [lt_def, coe_pred, coe_castPred] at *
  all_goals simp only [lt_def, coe_castSucc, val_succ, Fin.ext_iff] at *
  all_goals omega

variable {n : ℕ} {α : Fin (n + 1) → Sort*}

@[simp]
theorem update_insertNth_succAbove (p : Fin (n + 1)) (i : Fin n) (x : α p) (y : α (p.succAbove i))
    (xs : ∀ i, α (p.succAbove i)) :
    update (p.insertNth x xs) (p.succAbove i) y = p.insertNth x (update xs i y) := by
  ext j
  cases' j using p.succAboveCases with j
  · simp [ne_succAbove]
  · rcases eq_or_ne j i with rfl | hne <;> simp [*]

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

theorem removeNth_removeNth_heq_swap {α : Fin (n + 2) → Sort*} (m : ∀ i, α i)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    HEq (i.removeNth (j.removeNth m)) ((i.predAbove j).removeNth ((j.succAbove i).removeNth m)) := by
  apply Function.hfunext rfl
  simp only [heq_iff_eq]
  rintro k _ rfl
  unfold removeNth
  apply congr_arg_heq
  rw [succAbove_succAbove_succAbove_predAbove]

theorem removeNth_removeNth_eq_swap {α : Sort*} (m : Fin (n + 2) → α)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    i.removeNth (j.removeNth m) = (i.predAbove j).removeNth ((j.succAbove i).removeNth m) :=
  heq_iff_eq.mp (removeNth_removeNth_heq_swap m i j)

end Fin

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic
import DeRhamCohomology.Int

open Function

namespace Fin

attribute [simp] succAbove_right_inj

theorem succAbove_succAbove_predAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (i.succAbove j).succAbove (j.predAbove i) = i := by
  ext
  simp [succAbove, predAbove, lt_def, apply_dite Fin.val, apply_ite Fin.val]
  split_ifs <;> omega

theorem predAbove_predAbove_succAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (j.predAbove i).predAbove (i.succAbove j) = j := by
  ext
  simp [succAbove, predAbove, lt_def, apply_dite Fin.val, apply_ite Fin.val]
  split_ifs <;> omega

theorem succAbove_succAbove_succAbove_predAbove {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (k : Fin n) :
    (i.succAbove j).succAbove ((j.predAbove i).succAbove k) = i.succAbove (j.succAbove k) := by
  ext
  simp [succAbove, predAbove, lt_def, apply_dite Fin.val, apply_ite Fin.val]
  split_ifs <;> omega

theorem neg_one_pow_succAbove_add_predAbove {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (-1) ^ (i.succAbove j + j.predAbove i : ℕ) = (-1) ^ (i + j + 1 : ℕ) := by
  rcases lt_or_le j.castSucc i with hji | hij
  · have : 0 < (i : ℕ) := (Nat.zero_le j).trans_lt hji
    rw [succAbove_of_castSucc_lt _ _ hji, coe_castSucc, predAbove_of_castSucc_lt _ _ hji, coe_pred,
      ← Nat.add_sub_assoc, Int.neg_one_pow_sub_eq_pow_add, Nat.add_comm i] <;> omega
  · rw [succAbove_of_le_castSucc _ _ hij, val_succ, predAbove_of_le_castSucc _ _ hij, coe_castPred,
      Nat.add_right_comm, Nat.add_comm i]

variable {n : ℕ} {α : Fin (n + 1) → Sort*}

theorem removeNth_apply (f : ∀ i, α i) (i : Fin (n + 1)) (j : Fin n) :
    i.removeNth f j = f (i.succAbove j) :=
  rfl

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

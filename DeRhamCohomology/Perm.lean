import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.Perm.Sign

theorem List.formPerm_sign {α : Type*} [DecidableEq α] [Fintype α] :
    ∀ {l : List α}, l.Nodup → Equiv.Perm.sign l.formPerm = (-1) ^ l.tail.length
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: l, h => by
    rw [nodup_cons, mem_cons, not_or] at h
    simp [h, formPerm_sign h.2, pow_succ]

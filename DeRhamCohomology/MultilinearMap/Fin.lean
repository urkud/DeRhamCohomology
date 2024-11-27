import Mathlib.LinearAlgebra.Multilinear.Basic
import DeRhamCohomology.Fin

open Function

namespace MultilinearMap

section Semiring

variable {R N : Type*} [Semiring R] [AddCommMonoid N] [Module R N] {n : ℕ}

@[simps]
def mkDec {ι : Type*} {M : ι → Type*} [DecidableEq ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (f : (∀ i, M i) → N)
    (h_add : ∀ m i a b, f (update m i (a + b)) = f (update m i a) + f (update m i b))
    (h_smul : ∀ m i (c : R) a, f (update m i (c • a)) = c • f (update m i a)) :
    MultilinearMap R M N where
  toFun := f
  map_update_add' m := by convert h_add m
  map_update_smul' m := by convert h_smul m

variable {M : Fin (n + 1) → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

end Semiring

variable {R N : Type*} [CommSemiring R] [AddCommMonoid N] [Module R N]
  {n : ℕ} {M : Fin (n + 1) → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

@[simps!]
def uncurryNth {i : Fin (n + 1)} (f : M i →ₗ[R] MultilinearMap R (M <| i.succAbove ·) N) :
    MultilinearMap R M N := by
  apply mkDec (fun x ↦ f (x i) (i.removeNth x))
  · intro m
    obtain ⟨a, xs, rfl⟩ : ∃ a xs, i.insertNth a xs = m := ⟨_, _, Fin.insertNth_self_removeNth ..⟩
    simp [i.forall_iff_succAbove]
  · intro m
    obtain ⟨a, xs, rfl⟩ : ∃ a xs, i.insertNth a xs = m := ⟨_, _, Fin.insertNth_self_removeNth ..⟩
    simp [i.forall_iff_succAbove]

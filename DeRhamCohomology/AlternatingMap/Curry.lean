/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.LinearAlgebra.Alternating.Basic
import DeRhamCohomology.MultilinearMap.Fin

noncomputable section
suppress_compilation

namespace AlternatingMap

@[simps]
def toMultilinearMapLM {R ι M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N] :
    (M [⋀^ι]→ₗ[R] N) →ₗ[S] MultilinearMap R (fun _ : ι ↦ M) N where
  toFun := toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section CommSemiring

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

def curryFin {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N) :
    M →ₗ[R] (M [⋀^Fin n]→ₗ[R] N) where
  toFun x :=
    { toMultilinearMap := f.1.curryLeft x
      map_eq_zero_of_eq' := fun v i j hv hne ↦ by
        apply f.map_eq_zero_of_eq (Fin.cons x v) (i := i.succ) (j := j.succ) <;> simpa }
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

end CommSemiring

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] {n : ℕ}

theorem neg_one_pow_smul_apply_insertNth (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (x : M)
    (v : Fin n → M) (i : Fin (n + 1)) :
    f (i.insertNth x v) = (-1) ^ i.val • f (Fin.cons x v) := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [Fin.insertNth_succ, f.map_swap _ Fin.lt_succ.ne, ih, Fin.val_succ, Fin.coe_castSucc,
      pow_succ', mul_smul, neg_one_smul]

/-- Given a function which is linear in the first argument
and is alternating form in the other `n` arguments,
build an alternating form in `n + 1` arguments.

Note that the round-trip with `curryFin` multiplies the form by `n + 1`,
since we want to avoid division in this definition. -/
def uncurryFin (f : M →ₗ[R] (M [⋀^Fin n]→ₗ[R] N)) :
    M [⋀^Fin (n + 1)]→ₗ[R] N where
  toMultilinearMap :=
    ∑ i, (-1) ^ i.val • MultilinearMap.uncurryNth (i := i) ((toMultilinearMapLM (S := R)).comp f)
  map_eq_zero_of_eq' := by
    intro v i j hvij hij
    suffices ∑ k : Fin (n + 1), (-1) ^ k.val • f (v k) (k.removeNth v) = 0 by simpa
    calc
      _ = (-1) ^ i.val • f (v i) (i.removeNth v) + (-1) ^ j.val • f (v j) (j.removeNth v) := by
        refine Fintype.sum_eq_add _ _ hij fun k ⟨hki, hkj⟩ ↦ ?_
        rcases Fin.exists_succAbove_eq hki.symm with ⟨i, rfl⟩
        rcases Fin.exists_succAbove_eq hkj.symm with ⟨j, rfl⟩
        rw [(f (v k)).map_eq_zero_of_eq _ hvij (ne_of_apply_ne _ hij), smul_zero]
      _ = 0 := by
        sorry

theorem uncurryFin_apply (f : M →ₗ[R] (M [⋀^Fin n]→ₗ[R] N)) (v : Fin (n + 1) → M) :
    uncurryFin f v = ∑ i, (-1) ^ i.val • f (v i) (Fin.removeNth i v) := by
  simp [uncurryFin]

end CommRing

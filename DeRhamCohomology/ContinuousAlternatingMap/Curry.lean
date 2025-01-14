/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Curry
import DeRhamCohomology.AlternatingMap.Curry

noncomputable section
suppress_compilation

namespace ContinuousAlternatingMap

section Curry

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

def uncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    E [⋀^Fin (n + 1)]→L[𝕜] F :=
  AlternatingMap.mkContinuous
    (.uncurryFin <| ContinuousAlternatingMap.toAlternatingMapLinear.comp f.toLinearMap)
    ((n + 1) * ‖f‖) fun v ↦ calc
      _ = ‖∑ k, (-1) ^ k.val • f (v k) (k.removeNth v)‖ := by
        simp [AlternatingMap.uncurryFin_apply]
      _ ≤ ∑ k, ‖f‖ * ‖v k‖ * ∏ j, ‖v (k.succAbove j)‖ := by
        refine norm_sum_le_of_le _ fun k _ ↦ ?_
        rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg)]
        exact (f (v k)).le_of_opNorm_le (f.le_opNorm _) _
      _ = _ := by
        simp [mul_assoc, ← Fin.prod_univ_succAbove (‖v ·‖)]

theorem norm_uncurryFin_le (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    ‖uncurryFin f‖ ≤ (n + 1) * ‖f‖ :=
  AlternatingMap.mkContinuous_norm_le _ (by positivity) _

theorem uncurryFin_apply (f : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) (v : Fin (n + 1) → E) :
    uncurryFin f v = ∑ k, (-1) ^ k.val • f (v k) (k.removeNth v) :=
  AlternatingMap.uncurryFin_apply ..

theorem uncurryFin_add (f g : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) :
    uncurryFin (f + g) = uncurryFin f + uncurryFin g := by
  ext v
  simp [uncurryFin_apply, Finset.sum_add_distrib]

theorem uncurryFin_smul {M : Type*} [Monoid M] [DistribMulAction M F] [ContinuousConstSMul M F]
    [SMulCommClass 𝕜 M F] (c : M) (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    uncurryFin (c • f) = c • uncurryFin f := by
  ext v
  simp [uncurryFin_apply, smul_comm _ c, Finset.smul_sum]

@[simps! apply]
def uncurryFinCLM :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := uncurryFin (𝕜 := 𝕜) (E := E) (F := F) (n := n)
      map_add' := by exact uncurryFin_add -- TODO: why does it fail without `by exact`?
      map_smul' := by exact uncurryFin_smul }
    (n + 1) norm_uncurryFin_le

theorem uncurryFin_uncurryFinCLM_comp_of_symmetric {f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F}
    (hf : ∀ x y, f x y = f y x) :
    uncurryFin (uncurryFinCLM.comp f) = 0 := by
  ext v
  set a : Fin (n + 2) → Fin (n + 1) → F := fun i j ↦
    (-1) ^ (i + j : ℕ) • f (v i) (i.removeNth v j) (j.removeNth (i.removeNth v))
  suffices ∑ ij : Fin (n + 2) × Fin (n + 1), a ij.1 ij.2 = 0 by
    simpa [a, uncurryFin_apply, Finset.smul_sum, Fintype.sum_prod_type, mul_smul, pow_add]
      using this
  set g : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) := fun (i, j) ↦
    (i.succAbove j, j.predAbove i)
  have hg_invol : g.Involutive := by
    intro (i, j)
    simp only [g, Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]
  refine Finset.sum_ninvolution g ?_ (by simp [g, Fin.succAbove_ne]) (by simp) hg_invol
  intro (i, j)
  simp only [a]
  rw [hf (v i), ← Fin.removeNth_removeNth_eq_swap, Fin.removeNth_apply _ (i.succAbove j),
    Fin.succAbove_succAbove_predAbove, Fin.neg_one_pow_succAbove_add_predAbove, pow_succ',
    neg_one_mul, neg_smul, Fin.removeNth_apply, add_neg_cancel]

/- Interior product -/
def curryFin (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        { toContinuousMultilinearMap := f.1.curryLeft x
          map_eq_zero_of_eq' := fun v i j hv hne ↦ by
            apply f.map_eq_zero_of_eq (Fin.cons x v) (i := i.succ) (j := j.succ) <;> simpa }
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
    ‖f‖ fun x => by
      rw [LinearMap.coe_mk, AddHom.coe_mk,
          /- `ContinuousAlternatingMap.coe_mk` doesn't work here?? -/ ]
      sorry
      -- exact AlternatingMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

end Curry

end ContinuousAlternatingMap

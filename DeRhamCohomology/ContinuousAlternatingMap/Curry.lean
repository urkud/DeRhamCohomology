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

def uncurryFin {n : ℕ} (f : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) :
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

theorem uncurryFin_apply {n : ℕ} (f : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) (v : Fin (n + 1) → E) :
    uncurryFin f v = ∑ k, (-1) ^ k.val • f (v k) (k.removeNth v) :=
  AlternatingMap.uncurryFin_apply ..

end Curry

end ContinuousAlternatingMap

/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Curry

noncomputable section
suppress_compilation

namespace ContinuousAlternatingMap

section Curry

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]


def curryFin {n : ℕ} (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F) :=
  LinearMap.mkContinuous
    { toFun := fun x ↦
      { toContinuousMultilinearMap := f.toContinuousMultilinearMap.curryLeft x
        map_eq_zero_of_eq' := fun v i j heq hne ↦
          f.map_eq_zero_of_eq (Fin.cons x v) (i := i.succ) (j := j.succ) (by simpa) (by simpa) }
      map_add' := _
      map_smul' := _ }
    1 fun x ↦ _


end Curry

end ContinuousAlternatingMap

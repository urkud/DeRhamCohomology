import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {ι : Type*} [Fintype ι]

-- TODO: naming in this file doesn't agree with Mathlib naming for `ContinuousLinearMap`s
-- Sync names before moving to Mathlib.
theorem fderiv_apply {f : E → F [⋀^ι]→L[𝕜] G} {x y : E} (h : DifferentiableAt 𝕜 f x) (v : ι → F) :
    fderiv 𝕜 f x y v = fderiv 𝕜 (f · v) x y :=
  DFunLike.congr_fun ((apply 𝕜 F G v).hasFDerivAt.comp x h.hasFDerivAt).fderiv.symm y

theorem fderivWithin_apply {f : E → F [⋀^ι]→L[𝕜] G} {x y : E} {s : Set E}
    (h : DifferentiableWithinAt 𝕜 f s x) (hs : UniqueDiffWithinAt 𝕜 s x) (v : ι → F) :
    fderivWithin 𝕜 f s x y v = fderivWithin 𝕜 (f · v) s x y :=
  DFunLike.congr_fun (((apply 𝕜 F G v).hasFDerivAt.comp_hasFDerivWithinAt x
    h.hasFDerivWithinAt).fderivWithin hs).symm y

end ContinuousAlternatingMap

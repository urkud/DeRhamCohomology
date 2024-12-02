import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Alternating.Basic

noncomputable section
suppress_compilation

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

def _root_.ContinuousLinearMap.compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
  (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' := by sorry

theorem _root_.ContinuousLinearMap.compContinuousAlternatingMap₂_inv (f : N →L[𝕜] N' →L[𝕜] N'')
  (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m': ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m') := by sorry

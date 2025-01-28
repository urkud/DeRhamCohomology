import DeRhamCohomology.DifferentialForm
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

open Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section

variable
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {I'' : ModelWithCorners ℝ E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f : M → M'} {s t : Set M} {x y : M}

/- This isn't right ...
Need a ContDiff and ContMDiff version of Alternating maps first??
Then one can define this as the map M → TangentSpace I [k, ⋀^Fin n]→L[ ℝ ] ℝ -/
notation "Ω^" k "," n "⟮" I ", " M "⟯" => M → TangentSpace I [⋀^Fin n]→L[ℝ] ℝ

namespace DifferentialForm

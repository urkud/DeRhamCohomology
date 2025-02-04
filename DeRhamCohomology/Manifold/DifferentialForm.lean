import DeRhamCohomology.DifferentialForm
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import DeRhamCohomology.Manifold.VectorBundle.Alternating

open Bundle Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section

-- Possible extra variables
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

variable {𝕜 ι B F₁ F₂ M : Type*} {E₁ : B → Type*} {E₂ : B → Type*}
  [NontriviallyNormedField 𝕜]
  [Fintype ι]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, TopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [SmoothManifoldWithCorners IM M] {n : WithTop ℕ∞}
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}
  (m k : ℕ)

#check SmoothVectorBundle.continuousAlternatingMap
#check (TangentSpace IM : M → Type _)
#check (TangentSpace 𝓘(ℝ, ℝ) : ℝ  → Type _)
-- The sections of the bundle of continuousAlternatingMaps
-- IB is the model space for B -> In our case model for M underlying manifold
-- (F₁ [⋀^Fin m]→L[𝕜] F₂) is model space for each alternating map -> In our case TpM [⋀^Fin m]→L[ℝ] ℝ
-- k-times continuously differentiable
--
#check ContMDiffSection IB (F₁ [⋀^Fin m]→L[𝕜] F₂) k (Bundle.continuousAlternatingMap 𝕜 (Fin m) F₁ E₁ F₂ E₂)
#check ContMDiffSection IM (EM [⋀^Fin m]→L[ℝ] ℝ) k
  (Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM : M → Type _) ℝ
    (Bundle.Trivial M ℝ))



namespace DifferentialForm

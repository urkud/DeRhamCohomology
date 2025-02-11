import DeRhamCohomology.DifferentialForm
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import DeRhamCohomology.Manifold.VectorBundle.Alternating

open Bundle Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  (IM : ModelWithCorners ℝ EM HM)
  (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [SmoothManifoldWithCorners IM M]
  {m n : ℕ} {k : ℕ∞}

-- Setup for Differential Form Space
notation "Ω^" k "," m "⟮" EM "," IM "," M "⟯" =>
  ContMDiffSection IM (EM [⋀^Fin m]→L[ℝ] ℝ) k
    (Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM : M → Type _) ℝ (Bundle.Trivial M ℝ))

namespace DifferentialForm

section mpullback

variable
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN]
  (IN : ModelWithCorners ℝ EN HN)
  (N : Type*) [TopologicalSpace N] [ChartedSpace HN N] [SmoothManifoldWithCorners IN N]

variable (α β : (x : N) → TangentSpace IN x [⋀^Fin m]→L[ℝ] Trivial N ℝ x)

/- The pullback of a differential form
Want to keep k-times differentiability away from it. Is this the way? -/
def mpullback (f : M → N) : (x : M) → TangentSpace IM x [⋀^Fin m]→L[ℝ] Trivial N ℝ (f x) :=
    fun x ↦ (α (f x)).compContinuousLinearMap (mfderiv IM IN f x)

theorem mpullback_zero (f : M → N) :
    mpullback IM M IN N (0 : (x : N) → TangentSpace IN x [⋀^Fin m]→L[ℝ] Trivial N ℝ x) f = 0 :=
  rfl

theorem mpullback_add (f : M → N) :
    mpullback IM M IN N (α + β) f = mpullback IM M IN N α f + mpullback IM M IN N β f :=
  rfl

theorem mpullback_sub (f : M → N) :
    mpullback IM M IN N (α - β) f = mpullback IM M IN N α f - mpullback IM M IN N β f :=
  rfl

theorem mpullback_neg (f : M → N) :
    - mpullback IM M IN N α f = mpullback IM M IN N (-α) f :=
  rfl

theorem mpullback_smul (f : M → N) (c : ℝ) :
    c • (mpullback IM M IN N α) f = mpullback IM M IN N (c • α) f :=
  rfl

end mpullback

section mwedge_product

variable
  (α : (x : M) → TangentSpace IM x [⋀^Fin m]→L[ℝ] Trivial M ℝ x)
  (β : (x : M) → TangentSpace IM x [⋀^Fin n]→L[ℝ] Trivial M ℝ x)
  [Π (x : M), NormedAddCommGroup (TangentSpace IM x)]

/- Place for wedge product definitions etc. -/
def mwedge_product (f : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) : (x : M) → TangentSpace IM x [⋀^Fin (m + n)]→L[ℝ] Trivial M ℝ x :=
    sorry

end mwedge_product

section mederiv

variable
  (α : (x : M) → TangentSpace IM x [⋀^Fin m]→L[ℝ] Trivial M ℝ x)

  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN]
  (IN : ModelWithCorners ℝ EN HN)
  (N : Type*) [TopologicalSpace N] [ChartedSpace HN N] [SmoothManifoldWithCorners IN N]
  (o : M) (f : M → N)

/- Place for exterior derivative definitions -/

#check (extChartAt IM o).symm
#check writtenInExtChartAt IM 𝓘(ℝ, (EM [⋀^Fin m]→L[ℝ] ℝ)) o (fun y ↦ (α y))
#check range IM
#check 𝒜⟮ ℝ, Fin m; EM, (TangentSpace IM : M → Type _); ℝ, (Bundle.Trivial M ℝ)⟯
#check ⋀^(Fin m)⟮ ℝ; EM, (TangentSpace IM : M → Type _); ℝ, (Bundle.Trivial M ℝ)⟯
#check IM.tangent

def mederivWithin (s : Set M) (x : M) : TangentSpace IM x [⋀^Fin (m + 1)]→L[ℝ] Trivial M ℝ x :=
    (ederivWithin (E := EM) (F := ℝ) (n := m) (writtenInExtChartAt IM 𝓘(ℝ, (EM [⋀^Fin m]→L[ℝ] ℝ)) x
      (fun (y : M) ↦ (α y : 𝒜⟮ ℝ, Fin m; EM, (TangentSpace IM : M → Type _); ℝ, (Bundle.Trivial M ℝ)⟯)))
        ((extChartAt IM x).symm ⁻¹' s ∩ range IM)) (extChartAt IM x x)

end mederiv

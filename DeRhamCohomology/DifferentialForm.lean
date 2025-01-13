import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import DeRhamCohomology.ContinuousAlternatingMap.Curry
import DeRhamCohomology.ContinuousAlternatingMap.FDeriv
import DeRhamCohomology.ContinuousAlternatingMap.Wedge

noncomputable section

open Filter ContinuousAlternatingMap
open scoped Topology

variable {E F F' F'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  {n m : ℕ}

-- TODO: change notation
notation "Ω^" n "⟮" E ", " F "⟯" => E → E [⋀^Fin n]→L[ℝ] F

/-- Exterior derivative of a differential form. -/
def ederiv (ω : Ω^n⟮E, F⟯) : Ω^n + 1⟮E, F⟯ :=
  fun x ↦ .uncurryFin (fderiv ℝ ω x)

theorem Filter.EventuallyEq.ederiv_eq {ω₁ ω₂ : Ω^n⟮E, F⟯} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederiv ω₁ x = ederiv ω₂ x := by
  ext v
  simp only [ederiv, ContinuousAlternatingMap.uncurryFin_apply, h.fderiv_eq]

protected theorem Filter.EventuallyEq.ederiv {ω₁ ω₂ : Ω^n⟮E, F⟯} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederiv ω₁ =ᶠ[𝓝 x] ederiv ω₂ :=
  h.eventuallyEq_nhds.mono fun _x hx ↦ hx.ederiv_eq

theorem ederiv_apply (ω : Ω^n⟮E, F⟯) {x : E} (hx : DifferentiableAt ℝ ω x) (v : Fin (n + 1) → E) :
    ederiv ω x v = ∑ i, (-1) ^ i.val • fderiv ℝ (ω · (i.removeNth v)) x (v i) := by
  simp only [ederiv, ContinuousAlternatingMap.uncurryFin_apply,
    ContinuousAlternatingMap.fderiv_apply hx]

theorem ederiv_ederiv_apply (ω : Ω^n⟮E, F⟯) {x} (h : ContDiffAt ℝ 2 ω x) :
    ederiv (ederiv ω) x = 0 := calc
  ederiv (ederiv ω) x = uncurryFin (fderiv ℝ (fun y ↦ uncurryFin (fderiv ℝ ω y)) x) := rfl
  _ = uncurryFin (uncurryFinCLM.comp <| fderiv ℝ (fderiv ℝ ω) x) := by
    congr 1
    have : DifferentiableAt ℝ (fderiv ℝ ω) x := (h.fderiv_right le_rfl).differentiableAt le_rfl
    exact (uncurryFinCLM.hasFDerivAt.comp x this.hasFDerivAt).fderiv
  _ = 0 :=
    uncurryFin_uncurryFinCLM_comp_of_symmetric <| h.isSymmSndFDerivAt le_rfl

theorem ederiv_ederiv (ω : Ω^n⟮E, F⟯) (h : ContDiff ℝ 2 ω) : ederiv (ederiv ω) = 0 :=
  funext fun _ ↦ ederiv_ederiv_apply ω h.contDiffAt

/- Wedge product of differential forms -/
def wedge_product (ω₁ : Ω^m⟮E, F⟯) (ω₂ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') :
    Ω^(m + n)⟮E, F''⟯ := fun e => ContinuousAlternatingMap.wedge_product (ω₁ e) (ω₂ e) f

-- TODO: change notation
notation f "∧" "[" ω₁ "," ω₂ "]" => wedge_product ω₁ ω₂ f

theorem wedge_product_def {ω₁ : Ω^m⟮E, F⟯} {ω₂ : Ω^n⟮E, F'⟯} {f : F →L[ℝ] F' →L[ℝ] F''}
    {x : E} : (f ∧ [ω₁, ω₂]) x = ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) f :=
  rfl

/- The wedge product wrt multiplication -/
theorem wedge_product_mul {ω₁ : Ω^m⟮E, ℝ⟯} {ω₂ : Ω^n⟮E, ℝ⟯} {x : E} :
    (ContinuousLinearMap.mul ℝ ℝ ∧ [ω₁, ω₂]) x = ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) (ContinuousLinearMap.mul ℝ ℝ) :=
  rfl

/- The wedge product wrt scalar multiplication -/
theorem wedge_product_lsmul {ω₁ : Ω^m⟮E, ℝ⟯} {ω₂ : Ω^n⟮E, F⟯} {x : E} :
    (ContinuousLinearMap.lsmul ℝ ℝ ∧ [ω₁, ω₂]) x = ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) (ContinuousLinearMap.lsmul ℝ ℝ) :=
  rfl

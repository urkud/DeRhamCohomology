import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import DeRhamCohomology.ContinuousAlternatingMap.Curry
import DeRhamCohomology.ContinuousAlternatingMap.FDeriv

/-
# Differential Forms

-/

noncomputable section

open Filter ContinuousAlternatingMap
open scoped Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {n k : ℕ}

-- TODO: change notation
notation "Ω^" n "⟮" E ", " F "⟯" => E → E [⋀^Fin n]→L[ℝ] F

variable {v : E}
variable (ω τ : Ω^n⟮E, F⟯)
variable (f : E → F)

instance : Add (Ω^n⟮E, F⟯) :=
  ⟨ (fun ω τ => fun v => ω v + τ v) ⟩

@[simp]
theorem add_apply : (ω + τ) v = ω v + τ v :=
  rfl

instance : Sub (Ω^n⟮E, F⟯) :=
  ⟨ (fun ω τ => fun v => ω v - τ v) ⟩

@[simp]
theorem sub_apply : (ω - τ) v = ω v - τ v :=
  rfl

instance : Neg (Ω^n⟮E, F⟯) :=
  ⟨fun ω => fun v => -ω v⟩

@[simp]
theorem neg_apply : (-ω) v = -ω v :=
  rfl

instance : SMul ℝ (Ω^n⟮E, F⟯) :=
  ⟨fun c ω => fun v => c • ω v⟩

@[simp]
theorem smul_apply (ω : Ω^n⟮E, F⟯) (c : ℝ) (v : E): (c • ω) v = c • ω v :=
  rfl

instance : Zero (Ω^n⟮E, F⟯) :=
  ⟨ (fun _ => 0) ⟩

@[simp]
theorem zero_apply : (0 : Ω^n⟮E, F⟯) v = 0 :=
  rfl

instance inhabited : Inhabited (Ω^n⟮E, F⟯) :=
  ⟨0⟩

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
  funext fun x ↦ ederiv_ederiv_apply ω h.contDiffAt

/- Pullback of a differential form -/
def pullback (f : E → F) (ω : Ω^k⟮F, G⟯) : Ω^k⟮E, G⟯ :=
  fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

theorem pullback_zero (f : E → F) :
  pullback f (0 : Ω^k⟮F, G⟯) = 0 :=
    rfl

theorem pullback_add (f : E → F) (ω : Ω^k⟮F, G⟯) (τ : Ω^k⟮F, G⟯) :
  pullback f (ω + τ) = pullback f ω + pullback f τ :=
    rfl

theorem pullback_sub (f : E → F) (ω : Ω^k⟮F, G⟯) (τ : Ω^k⟮F, G⟯) :
  pullback f (ω - τ) = pullback f ω - pullback f τ :=
    rfl

theorem pullback_neg (f : E → F) (ω : Ω^k⟮F, G⟯) :
  - pullback f ω = pullback f (-ω) :=
    rfl

theorem pullback_smul (f : E → F) (ω : Ω^k⟮F, G⟯) (c : ℝ) :
  c • (pullback f ω) = pullback f (c • ω) :=
    rfl

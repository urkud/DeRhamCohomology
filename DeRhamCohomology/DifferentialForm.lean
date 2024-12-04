import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import DeRhamCohomology.ContinuousAlternatingMap.Curry
import DeRhamCohomology.ContinuousAlternatingMap.FDeriv

noncomputable section

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

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

/- Exterior derivative of a differential form within a set -/
def ederivWithin (ω : Ω^n⟮E, F⟯) (s : Set E) : Ω^n + 1⟮E, F⟯ :=
  fun (x : E) ↦ .uncurryFin (fderivWithin ℝ ω s x)

@[simp]
theorem ederivWithin_univ (ω : Ω^n⟮E, F⟯) :
    ederivWithin ω univ = ederiv ω := by
  ext1 x
  rw[ederivWithin, ederiv, fderivWithin_univ]

theorem Filter.EventuallyEq.ederivWithin_eq {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) : ederivWithin ω₁ s x = ederivWithin ω₂ s x := by
  simp only[ederivWithin, uncurryFin, hs.fderivWithin_eq hx]

theorem Filter.EventuallyEq.ederivWithin_eq_of_mem {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x ∈ s) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  hs.ederivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

theorem Filter.EventuallyEq.ederivWithin_eq_of_insert {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂) : ederivWithin ω₁ s x = ederivWithin ω₂ s x := by
  apply Filter.EventuallyEq.ederivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

theorem Filter.EventuallyEq.ederivWithin' {ω₁ ω₂ : Ω^n⟮E, F⟯} {s t : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t ⊆ s) : ederivWithin ω₁ t =ᶠ[𝓝[s] x] ederivWithin ω₂ t :=
  (eventually_eventually_nhdsWithin.2 hs).mp <|
    eventually_mem_nhdsWithin.mono fun _y hys hs =>
      EventuallyEq.ederivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

protected theorem Filter.EverntuallyEq.ederivWithin {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) : ederivWithin ω₁ s =ᶠ[𝓝[s] x] ederivWithin ω₂ s :=
  hs.ederivWithin' Subset.rfl

theorem Filter.EventuallyEq.ederivWithin_eq_nhds {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  (h.filter_mono nhdsWithin_le_nhds).ederivWithin_eq h.self_of_nhds

theorem ederivWithin_congr {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).ederivWithin_eq hx

theorem ederivWithin_congr' {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : EqOn ω₁ ω₂ s) (hx : x ∈ s) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  ederivWithin_congr hs (hs hx)

theorem ederivWithin_apply (ω : Ω^n⟮E, F⟯) {s : Set E} {x : E}
    (h : DifferentiableWithinAt ℝ ω s x) (hs : UniqueDiffWithinAt ℝ s x) (v : Fin (n + 1) → E) :
    ederivWithin ω s x v = ∑ i, (-1) ^ i.val • fderivWithin ℝ (ω · (i.removeNth v)) s x (v i) := by
  simp only [ederivWithin, ContinuousAlternatingMap.uncurryFin_apply,
    ContinuousAlternatingMap.fderivWithin_apply h hs]

theorem ederivWithin_ederivWithin_apply (ω : Ω^n⟮E, F⟯) {s : Set E} {t : Set (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F)} {x}
    (hxx : x ∈ closure (interior s)) (hx : x ∈ s) (hst : MapsTo (fderivWithin ℝ ω s) s t)
    (h : ContDiffWithinAt ℝ 2 ω s x) (hs : UniqueDiffOn ℝ s) :
    ederivWithin (ederivWithin ω s) s x = 0 := calc
  ederivWithin (ederivWithin ω s) s x =
    uncurryFin (fderivWithin ℝ (fun y ↦ uncurryFin (fderivWithin ℝ ω s y)) s x) := rfl
  _ = uncurryFin (uncurryFinCLM.comp <| fderivWithin ℝ (fderivWithin ℝ ω s) s x) := by
    congr 1
    have : DifferentiableWithinAt ℝ (fderivWithin ℝ ω s) s x := (h.fderivWithin_right hs le_rfl hx).differentiableWithinAt le_rfl
    exact (uncurryFinCLM.hasFDerivWithinAt.comp x this.hasFDerivWithinAt hst).fderivWithin (hs.uniqueDiffWithinAt hx)
  _ = 0 :=
    uncurryFin_uncurryFinCLM_comp_of_symmetric <| h.isSymmSndFDerivWithinAt le_rfl hs hxx hx

theorem ederivWithin_ederivWithin (ω : Ω^n⟮E, F⟯) {s : Set E} {t : Set (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F)}
    (hst : MapsTo (fderivWithin ℝ ω s) s t) (h : ContDiffOn ℝ 2 ω s) (hs : UniqueDiffOn ℝ s) :
    EqOn (ederivWithin (ederivWithin ω s) s) 0 (s ∩ (closure (interior s))) :=
  fun _ ⟨ hx, hxx ⟩ => ederivWithin_ederivWithin_apply ω hxx hx hst (h.contDiffWithinAt hx) hs

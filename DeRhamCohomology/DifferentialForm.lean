import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import DeRhamCohomology.ContinuousAlternatingMap.Curry
import DeRhamCohomology.ContinuousAlternatingMap.FDeriv
import DeRhamCohomology.ContinuousAlternatingMap.Wedge

noncomputable section

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {E F F' F'' G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n m k : ℕ}

-- TODO: change notation
notation "Ω^" n "⟮" E ", " F "⟯" => E → E [⋀^Fin n]→L[ℝ] F

variable {v : E}
variable (ω τ : Ω^n⟮E, F⟯)
variable (f : E → F)

@[simp]
theorem add_apply : (ω + τ) v = ω v + τ v :=
  rfl

@[simp]
theorem sub_apply : (ω - τ) v = ω v - τ v :=
  rfl

@[simp]
theorem neg_apply : (-ω) v = -ω v :=
  rfl

@[simp]
theorem smul_apply (ω : Ω^n⟮E, F⟯) (c : ℝ) : (c • ω) v = c • ω v :=
  rfl

@[simp]
theorem zero_apply : (0 : Ω^n⟮E, F⟯) v = 0 :=
  rfl

/- The natural equivalence between differential forms from `E` to `F`
and maps from `E` to continuous 1-multilinear alternating maps from `E` to `F`. -/
def ofSubsingleton :
    (E → E →L[ℝ] F) ≃ (Ω^1⟮E, F⟯) where
  toFun f := fun e ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F 0 (f e)
  invFun f := fun e ↦ (ContinuousAlternatingMap.ofSubsingleton ℝ E F 0).symm (f e)
  left_inv _ := rfl
  right_inv _ := by simp

/- The constant map is a differential form when `Fin n` is empty -/
def constOfIsEmpty (x : F) : Ω^0⟮E, F⟯ :=
  fun _ ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) x

/-- Exterior derivative of a differential form. -/
def ederiv (ω : Ω^n⟮E, F⟯) : Ω^n + 1⟮E, F⟯ :=
  fun x ↦ .uncurryFin (fderiv ℝ ω x)

theorem ederiv_add (ω₁ ω₂ : Ω^n⟮E, F⟯) {x : E} (hω₁ : DifferentiableAt ℝ ω₁ x)
    (hω₂ : DifferentiableAt ℝ ω₂ x) : ederiv (ω₁ + ω₂) x = ederiv ω₁ x + ederiv ω₂ x := by
  simp [ederiv, fderiv_add' hω₁ hω₂, uncurryFin_add]

theorem ederiv_smul (ω : Ω^n⟮E, F⟯) (c : ℝ) {x : E} (hω : DifferentiableAt ℝ ω x):
    ederiv (c • ω) x = c • ederiv ω x := by
  simp [ederiv, fderiv_const_smul' hω, uncurryFin_smul]

theorem ederiv_constOfIsEmpty (x : E) (y : F) :
    ederiv (constOfIsEmpty y) x = .uncurryFin (fderiv ℝ (constOfIsEmpty y) x) :=
  rfl

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

namespace DifferentialForm

def domDomCongr (σ : Fin n ≃ Fin m) (ω : Ω^n⟮E, F⟯) : Ω^m⟮E, F⟯ :=
  fun e => (ω e).domDomCongr σ

theorem domDomCongr_apply (σ : Fin n ≃ Fin m) (ω : Ω^n⟮E, F⟯) (e : E) (v : Fin m → E):
    (domDomCongr σ ω) e v = (ω e) (v ∘ σ)  :=
  rfl

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

theorem pullback_ofSubsingleton (f : E → F) (ω : F → F →L[ℝ] G) :
    pullback f (ofSubsingleton ω) = ofSubsingleton (fun e ↦ (ω (f e)).comp (fderiv ℝ f e)) :=
  rfl

theorem pullback_constOfIsEmpty (f : E → F) (g : G) :
    pullback f (constOfIsEmpty g) = fun _ ↦ (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) g) :=
  rfl

/- Wedge product of differential forms -/
def wedge_product (ω₁ : Ω^m⟮E, F⟯) (ω₂ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') :
    Ω^(m + n)⟮E, F''⟯ := fun e => ContinuousAlternatingMap.wedge_product (ω₁ e) (ω₂ e) f

-- TODO: change notation
notation ω₁ "∧["f"]" ω₂ => wedge_product ω₁ ω₂ f
notation ω₁ "∧" ω₂ => wedge_product ω₁ ω₂ (ContinuousLinearMap.mul ℝ ℝ)

theorem wedge_product_def {ω₁ : Ω^m⟮E, F⟯} {ω₂ : Ω^n⟮E, F'⟯} {f : F →L[ℝ] F' →L[ℝ] F''}
    {x : E} : (ω₁ ∧[f] ω₂) x = ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) f :=
  rfl

/- The wedge product wrt multiplication -/
theorem wedge_product_mul {ω₁ : Ω^m⟮E, ℝ⟯} {ω₂ : Ω^n⟮E, ℝ⟯} {x : E} :
    (ω₁ ∧[ContinuousLinearMap.mul ℝ ℝ] ω₂) x =
    ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) (ContinuousLinearMap.mul ℝ ℝ) :=
  rfl

/- The wedge product wrt scalar multiplication -/
theorem wedge_product_lsmul {ω₁ : Ω^m⟮E, ℝ⟯} {ω₂ : Ω^n⟮E, F⟯} {x : E} :
    (ω₁ ∧[ContinuousLinearMap.lsmul ℝ ℝ] ω₂) x =
    ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) (ContinuousLinearMap.lsmul ℝ ℝ) :=
  rfl

/- Associativity of wedge product -/
theorem wedge_assoc (ω₁ : Ω^m⟮E, F⟯) (ω₂ : Ω^n⟮E, F⟯) (f : F →L[ℝ] F →L[ℝ] F)
    (ω₃ : Ω^k⟮E, F⟯) (f' : F →L[ℝ] F →L[ℝ] F) :
    domDomCongr finAssoc.symm (ω₁ ∧[f] ω₂ ∧[f'] ω₃) = (ω₁ ∧[f] ω₂) ∧[f'] ω₃ := by
  ext x y
  rw[wedge_product_def, wedge_product_def, domDomCongr_apply, wedge_product_def, wedge_product_def,
    ← ContinuousAlternatingMap.domDomCongr_apply]
  exact ContinuousAlternatingMap.wedge_assoc (ω₁ x) (ω₂ x) f (ω₃ x) f' y

/- Left distributivity of wedge product -/
theorem add_wedge (ω₁ ω₂ : Ω^m⟮E, F⟯) (τ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') :
    ((ω₁ + ω₂) ∧[f] τ) = (ω₁ ∧[f] τ) + (ω₂ ∧[f] τ) := by
  ext1 x
  rw[wedge_product_def, _root_.add_apply, _root_.add_apply, wedge_product_def, wedge_product_def]
  exact ContinuousAlternatingMap.add_wedge (ω₁ x) (ω₂ x) (τ x) f

/- Right distributivity of wedge product -/
theorem wedge_add (ω : Ω^m⟮E, F⟯) (τ₁ τ₂ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') :
    (ω ∧[f] (τ₁ + τ₂)) = (ω ∧[f] τ₁) + (ω ∧[f] τ₂) := by
  ext1 x
  rw[wedge_product_def, _root_.add_apply, _root_.add_apply, wedge_product_def, wedge_product_def]
  exact ContinuousAlternatingMap.wedge_add (ω x) (τ₁ x) (τ₂ x) f

theorem smul_wedge (ω : Ω^m⟮E, ℝ⟯) (τ : Ω^n⟮E, ℝ⟯) (c : ℝ) :
    c • (ω ∧ τ) = (c • ω) ∧ τ := by
  ext1 x
  rw[_root_.smul_apply, wedge_product_mul, wedge_product_mul, _root_.smul_apply]
  exact ContinuousAlternatingMap.smul_wedge (ω x) (τ x) c

theorem wedge_smul (ω : Ω^m⟮E, ℝ⟯) (τ : Ω^n⟮E, ℝ⟯) (c : ℝ) :
    c • (ω ∧ τ) = ω ∧ (c • τ) := by
  ext1 x
  rw[_root_.smul_apply, wedge_product_mul, wedge_product_mul, _root_.smul_apply]
  exact ContinuousAlternatingMap.wedge_smul (ω x) (τ x) c

/- Antisymmetry of multiplication wedge product -/
theorem wedge_antisymm (ω : Ω^m⟮E, ℝ⟯) (τ : Ω^n⟮E, ℝ⟯) :
    (ω ∧ τ) = DifferentialForm.domDomCongr finAddFlip ((-1 : ℝ)^(m*n) • (τ ∧ ω)) := by
  ext x y
  rw[wedge_product_mul, domDomCongr_apply, _root_.smul_apply,
    wedge_product_mul, ← ContinuousAlternatingMap.domDomCongr_apply]
  exact ContinuousAlternatingMap.wedge_antisymm (ω x) (τ x) y

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

theorem wedge_self_odd_zero (ω : Ω^m⟮E, ℝ⟯) (m_odd : Odd m) :
    (ω ∧ ω) = 0 := by
  ext1 x
  rw[wedge_product_mul]
  exact ContinuousAlternatingMap.wedge_self_odd_zero (ω x) m_odd

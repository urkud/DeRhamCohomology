import Mathlib.Geometry.Manifold.VectorBundle.Basic
import DeRhamCohomology.VectorBundle.Alternating
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

noncomputable section

open Bundle Set ContinuousLinearMap Pretrivialization

open scoped Manifold Bundle

section

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
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [SmoothManifoldWithCorners IM M] {n : ℕ∞}
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

variable {F₃ F₄ : Type*}
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]

local notation "AE₁E₂" => TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯

-- move this to `ContinuousMultilinearMap`
theorem _root_.ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff :
  ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂)) := by
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁ →L[𝕜] F₁) _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ F₁) (fun _ : ι ↦ F₁) F₂
  show ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦ φ (fun _ : ι ↦ p))
  apply ContDiff.comp
  · apply ContinuousMultilinearMap.contDiff
  · apply contDiff_pi.mpr
    intro _
    apply contDiff_id

-- move this to `ContinuousAlternatingMap`
theorem _root_.ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff :
    ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁))) (𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) ⊤
    (fun p : (F₁ →L[𝕜] F₁) ↦ (ContinuousAlternatingMap.compContinuousLinearMapCLM p :
      ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) := by
  rw [contMDiff_iff_contDiff]
  sorry

theorem contMDiffOn_continuousAlternatingMapCoordChange
    [SmoothVectorBundle F₁ E₁ IB] [SmoothVectorBundle F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) ⊤
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := ⊤)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := ⊤)
  have h₁_prod_h₂ := (h₁.mono (t := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
    (s := e₁'.baseSet ∩ e₁.baseSet) (by mfld_set_tac)).prod_mk
      (h₂.mono (t := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
      (s := e₂.baseSet ∩ e₂'.baseSet) (by mfld_set_tac))
  let s (q : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂)) :
      (F₁ →L[𝕜] F₁) × ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) :=
    (q.1, ContinuousLinearMap.compContinuousAlternatingMapL 𝕜 F₁ F₂ F₂ q.2)
  have hs : ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod 𝓘(𝕜, (F₂ →L[𝕜] F₂)))
      (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod 𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) ⊤ s := by
    let t (p : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂)) :
        ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) :=
      ContinuousLinearMap.compContinuousAlternatingMapL 𝕜 F₁ F₂ F₂ p.2
    have ht : ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod 𝓘(𝕜, (F₂ →L[𝕜] F₂)))
        𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) ⊤ t := by
          refine ContMDiff.clm_apply ?hg ?hf
          exact contMDiff_const
          exact contMDiff_snd
    exact ContMDiff.prod_mk contMDiff_fst ht
  exact ((contMDiff_snd.clm_comp ((ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff
    (𝕜 := 𝕜) (ι := ι) (F₁ := F₁) (F₂ := F₂)).comp contMDiff_fst)).comp hs).comp_contMDiffOn
    (s := (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))) h₁_prod_h₂

variable [SmoothVectorBundle F₁ E₁ IB] [SmoothVectorBundle F₂ E₂ IB]

instance Bundle.continuousAlternatingMap.vectorPrebundle.isSmooth :
   (Bundle.continuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsSmooth IB where
  exists_smoothCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    refine ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      contMDiffOn_continuousAlternatingMapCoordChange IB, ?_⟩
    · rintro b hb v
      apply continuousAlternatingMapCoordChange_apply
      exact hb

instance SmoothVectorBundle.continuousAlternatingMap :
    SmoothVectorBundle (F₁ [⋀^ι]→L[𝕜] F₂) (Bundle.continuousAlternatingMap 𝕜 ι F₁ E₁ F₂ E₂) IB :=
  (Bundle.continuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).smoothVectorBundle IB

-- Notation for total space of continuous alternating bundle
notation3 "𝒜⟮" 𝕜 "," ι ";"  F₁ "," E₁ ";"  F₂ "," E₂ "⟯" => Bundle.TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯

end

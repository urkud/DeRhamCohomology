import Mathlib.Geometry.Manifold.VectorBundle.Basic
import DeRhamCohomology.VectorBundle.Alternating

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

-- theorem ContMDiffOn.cle_arrowCongrAlternating {f : B → F₁ ≃L[𝕜] F₂} {g : B → F₃ ≃L[𝕜] F₄} {s : Set B}
--     (hf : ContMDiffOn IB 𝓘(𝕜, F₂ →L[𝕜] F₁) n (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) s)
--     (hg : ContMDiffOn IB 𝓘(𝕜, F₃ →L[𝕜] F₄) n (fun x ↦ (g x : F₃ →L[𝕜] F₄)) s) :
--     ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₃) →L[𝕜] (F₂ [⋀^ι]→L[𝕜] F₄)) n
--       (fun y ↦ (f y).arrowCongr (g y) : B → (F₁ [⋀^ι]→L[𝕜] F₃) →L[𝕜] (F₂ [⋀^ι]→L[𝕜] F₄)) s := fun x hx ↦
--   (hf x hx).cle_arrowCongr (hg x hx)

theorem contMDiffOn_continuousAlternatingMapCoordChange
    [SmoothVectorBundle F₁ E₁ IB] [SmoothVectorBundle F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) ⊤
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := ⊤)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := ⊤)

  let s (q : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂)) :
      (F₁ →L[𝕜] F₁) × ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) :=
    (q.1, ContinuousLinearMap.compContinuousAlternatingMapL 𝕜 F₁ F₂ F₂ q.2)
  have hs : ContMDiff 𝓘(𝕜, (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂))
      𝓘(𝕜, (F₁ →L[𝕜] F₁) × ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) ⊤ s := by sorry
    -- contMDiff_id.prod_map ()

  -- have' := ((continuous_snd.clm_comp
  --   ((ContinuousAlternatingMap.compContinuousLinearMapL_continuous 𝕜 ι F₁ F₂).comp
  --   continuous_fst)).comp hs).comp_continuousOn
  --   (s := (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))) ((h₃.mono ?_).prod (h₄.mono ?_))
  -- · exact this
  -- · mfld_set_tac
  -- · mfld_set_tac

  #check h₁.mono
  #check ContMDiffOn.cle_arrowCongr

  -- refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

  sorry

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

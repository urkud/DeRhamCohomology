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
  [TopologicalSpace M] [ChartedSpace HM M] [SmoothManifoldWithCorners IM M] {n : WithTop ℕ∞}
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

local notation "AE₁E₂" => TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯

theorem contMDiffOn_continuousAlternatingMapCoordChange
    [SmoothVectorBundle F₁ E₁ IB] [SmoothVectorBundle F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) ⊤
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      ((continuousAlternatingMap 𝕜 ι e₁ e₂).baseSet ∩
        (continuousAlternatingMap 𝕜 ι e₁' e₂').baseSet) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := ⊤)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := ⊤)
  sorry
  -- refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

variable [∀ x, TopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

-- `need a version of incoordinates for alternating maps for the following two commented theorems?`

-- theorem alt_chart (y₀ y : AE₁E₂) :
--     chartAt (ModelProd HB (F₁ [⋀^ι]→L[𝕜] F₂)) y₀ y =
--       ⟨chartAt HB y₀.1 y.1, inCoordinates F₁ E₁ F₂ E₂ y₀.1 y.1 y₀.1 y.1 y.2⟩ := by
--   sorry
  -- rw [FiberBundle.chartedSpace_chartAt, trans_apply, PartialHomeomorph.prod_apply,
  --   Trivialization.coe_coe, PartialHomeomorph.refl_apply, Function.id_def,
  --   hom_trivializationAt_apply]

-- theorem contMDiffAt_hom_bundle (f : M → AE₁E₂) {x₀ : M} {n : ℕ∞} :
--     ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₂)) n f x₀ ↔
--       ContMDiffAt IM IB n (fun x => (f x).1) x₀ ∧
--         ContMDiffAt IM 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₂) n
--           (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
--   contMDiffAt_totalSpace ..

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

end

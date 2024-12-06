import Mathlib.Analysis.NormedSpace.Multilinear.Basic

noncomputable section
suppress_compilation

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} [Fintype ι]
  {E : ι → Type*} [(i : ι) → SeminormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)]
  {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  {G' : Type*} [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

def LinearIsometryEquiv.flipMultilinear :
    (G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃ₗᵢ[𝕜]
      (ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')) where
  toFun := ContinuousLinearMap.flipMultilinear
  invFun := sorry
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry
  norm_map' := sorry

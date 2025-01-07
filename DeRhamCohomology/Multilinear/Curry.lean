import Mathlib.Analysis.NormedSpace.Multilinear.Basic

noncomputable section
suppress_compilation

namespace ContinuousMultilinearMap

section Curry

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι ι' : Type*} [Fintype ι] [Fintype ι']
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

def uncurrySum  (a : ContinuousMultilinearMap 𝕜 (fun _ : ι => E)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' => E) F)) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => E) F where
  toFun v := a (fun i => v (Sum.inl i)) (fun j => v (Sum.inr j))
  map_update_add' _ i p q := by
    letI := (@Sum.inl_injective ι ι').decidableEq
    letI := (@Sum.inr_injective ι ι').decidableEq
    cases i <;> simp
  map_update_smul' _ i c p := by
    letI := (@Sum.inl_injective ι ι').decidableEq
    letI := (@Sum.inr_injective ι ι').decidableEq
    cases i <;> simp
  cont := by continuity

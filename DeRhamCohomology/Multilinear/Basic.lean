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
  invFun f :=
    LinearMap.mkContinuous
      { toFun := fun x =>
          MultilinearMap.mkContinuous
            { toFun := fun m => f m x
              map_update_add' := fun m i x y => by simp
              map_update_smul' := fun m i c x => by simp }
            (‖f‖*‖x‖) fun m => by
              simp only [MultilinearMap.coe_mk]
              rw[mul_right_comm]
              refine le_trans ((f m).le_opNorm x) ?hg
              exact mul_le_mul_of_nonneg_right (f.le_opNorm m) (norm_nonneg x)
        map_add' := fun x y => by
          ext1
          simp only [ContinuousMultilinearMap.add_apply, MultilinearMap.coe_mkContinuous,
            MultilinearMap.coe_mk, ContinuousLinearMap.map_add]
        map_smul' := fun c x => by
          ext1
          simp [ContinuousMultilinearMap.smul_apply, MultilinearMap.coe_mkContinuous,
            MultilinearMap.coe_mk, ContinuousLinearMap.map_smul_of_tower] }
      ‖f‖ fun x => by
        simp
        -- Following should be simplified
        -- Not sure how exactly yet (probably using `MultilinearMap.coe_mkContinuous`,
        --  and `MultilinearMap.coe_mk`)
        refine
          MultilinearMap.mkContinuous_norm_le
            { toFun := fun m ↦ (f m) x,
              map_update_add' := fun [DecidableEq ι] m i x_1 y ↦
                of_eq_true
                  (Eq.trans
                    (congrArg
                      (fun x_2 ↦
                        x_2 x = (f (Function.update m i x_1)) x + (f (Function.update m i y)) x)
                      (ContinuousMultilinearMap.map_update_add f m i x_1 y))
                    (eq_self ((f (Function.update m i x_1)) x + (f (Function.update m i y)) x))),
              map_update_smul' := fun [DecidableEq ι] m i c x_1 ↦
                of_eq_true
                  (Eq.trans
                    (congrArg (fun x_2 ↦ x_2 x = c • (f (Function.update m i x_1)) x)
                      (ContinuousMultilinearMap.map_update_smul f m i c x_1))
                    (eq_self (c • (f (Function.update m i x_1)) x))) }
            ?hC fun m ↦
            id
              (Eq.mpr
                (id (congrArg (fun _a ↦ ‖(f m) x‖ ≤ _a) (mul_right_comm ‖f‖ ‖x‖ (∏ i : ι, ‖m i‖))))
                (le_trans (ContinuousLinearMap.le_opNorm (f m) x)
                  (mul_le_mul_of_nonneg_right (ContinuousMultilinearMap.le_opNorm f m)
                    (norm_nonneg x))))
        exact Right.mul_nonneg (norm_nonneg f) (norm_nonneg x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  norm_map' := fun f => by
    simp
    -- simp_rw[ContinuousLinearMap.flipMultilinear, MultilinearMap.mkContinuous, LinearMap.mkContinuous]
    have h : ∀ m : ((i : ι) → E i), ∀ x : G, ‖f.flipMultilinear m x‖ = ‖f x m‖ := by
      exact fun m x ↦ rfl
    -- simp [apply_apply]
    sorry

namespace ContinuousMultilinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

def flipMultilinear (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) (ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') N)) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) N) :=
  MultilinearMap.mkContinuous
    { toFun := fun m =>
        MultilinearMap.mkContinuous
          { toFun := fun m' => f m' m
            map_update_add' := sorry
            map_update_smul' := sorry}
          1 sorry
      map_update_add' := sorry
      map_update_smul' := sorry }
    1 sorry

theorem flipMultilinear_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') N)) (m : ι → M) (m' : ι' → M') :
    f.flipMultilinear m' m = f m m' :=
  rfl

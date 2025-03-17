import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Mul
import DeRhamCohomology.ContinuousAlternatingMap.Curry
import DeRhamCohomology.Alternating.Basic
import DeRhamCohomology.Equiv.Fin
import Mathlib.Algebra.GroupWithZero.Defs
import Init.Grind.Lemmas

noncomputable section
suppress_compilation

namespace ContinuousAlternatingMap

section wedge

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {M'' : Type*} [NormedAddCommGroup M''] [NormedSpace 𝕜 M'']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n p : ℕ}

/-- The wedge product of two continuous alternating maps `g` an `h` with respect to a
bilinear map `f`. -/
def wedge_product (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') : M [⋀^Fin (m + n)]→L[𝕜] N'' :=
  uncurryFinAdd (f.compContinuousAlternatingMap₂ g h)

-- TODO: change notation
notation g "∧["f"]" h => wedge_product g h f
notation g "∧["𝕜"]" h => wedge_product g h (ContinuousLinearMap.mul 𝕜 𝕜)

theorem wedge_product_def {g : M [⋀^Fin m]→L[𝕜] N} {h : M [⋀^Fin n]→L[𝕜] N'}
    {f : N →L[𝕜] N' →L[𝕜] N''} {x : Fin (m + n) → M}:
    (g ∧[f] h) x = uncurryFinAdd (f.compContinuousAlternatingMap₂ g h) x :=
  rfl

/- The wedge product wrt multiplication -/
theorem wedge_product_mul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] 𝕜} {x : Fin (m + n) → M} :
    (g ∧[ContinuousLinearMap.mul 𝕜 𝕜] h) x = uncurryFinAdd ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

/- The wedge product wrt scalar multiplication -/
theorem wedge_product_lsmul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] N} {x : Fin (m + n) → M} :
    (g ∧[ContinuousLinearMap.lsmul 𝕜 𝕜] h) x = uncurryFinAdd ((ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

/- Associativity of multiplication wedge product -/
theorem wedge_mul_assoc (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (v : Fin (m + n + p) → M):
    ContinuousAlternatingMap.domDomCongr finAssoc.symm (g ∧[𝕜] h ∧[𝕜] l) v = ((g ∧[𝕜] h) ∧[𝕜] l) v := by
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply,
    uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
  rw[wedge_product, wedge_product]
  sorry

/- Left distributivity of wedge product -/
theorem add_wedge (g₁ g₂ : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
    ((g₁ + g₂) ∧[f] h) = (g₁ ∧[f] h) + (g₂ ∧[f] h) := by
  ext x
  rw[add_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw[uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
      coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[← smul_add, add_apply, map_add, ContinuousLinearMap.add_apply, smul_add]

/- Right distributivity of wedge product -/
theorem wedge_add (g : M [⋀^Fin m]→L[𝕜] N) (h₁ h₂ : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
    (g ∧[f] (h₁ + h₂)) = (g ∧[f] h₁) + (g ∧[f] h₂) := by
  ext x
  rw[add_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw[uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
      coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[add_apply, map_add, smul_add]

theorem smul_wedge (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (c : 𝕜) :
    c • (g ∧[𝕜] h) = (c • g) ∧[𝕜] h := by
  ext x
  rw[smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply', ← smul_assoc,
    smul_comm]
  rw[smul_assoc, smul_eq_mul, ← mul_assoc]
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply', ← smul_assoc,
    smul_comm, smul_apply, smul_eq_mul]

theorem wedge_smul (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (c : 𝕜) :
    c • (g ∧[𝕜] h) = g ∧[𝕜] (c • h) := by
  ext x
  rw[smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply', ← smul_assoc,
    smul_comm]
  rw[smul_assoc, smul_eq_mul, ← mul_assoc]
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply', ← smul_assoc,
    smul_comm, smul_apply, smul_eq_mul, ← mul_assoc, mul_comm]

/- Antisymmetry of multiplication wedge product -/
theorem wedge_antisymm (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (x : Fin (m + n) → M) :
    (g ∧[𝕜] h) x = ((-1 : 𝕜)^(m*n) • (h ∧[𝕜] g)).domDomCongr finAddFlip x := by
  rw[domDomCongr_apply, smul_apply, wedge_product_mul, uncurryFinAdd, domDomCongr_apply,
    uncurrySum_apply, ContinuousMultilinearMap.sum_apply, wedge_product_mul,
    uncurryFinAdd, domDomCongr_apply, uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
  /- We cannot apply `uncurrySum.summand` until we have removed the sums
  How do we equalise the sums using `finAddFlip`?? -/
  rw[Finset.smul_sum]
  -- Search for Equiv between Equiv.Perm.ModSumCongr (Fin n) (Fin m) and swap Or make it yourself
  -- After it works the same way as normal with removing sum and working over summands
  have h2 : Equiv.Perm.ModSumCongr (Fin m) (Fin n) ≃ Equiv.Perm.ModSumCongr (Fin n) (Fin m) := by sorry
  rw[← Equiv.sum_comp h2]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']
  -- Not completely how it needs to be I think. I assume we want the h and g swapped and all Fin m swapped with Fin n.
  have h3 :
    (uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ h g)
      (h2 (Quot.mk (⇑(QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range)) σ₁)))
        ((x ∘ ⇑finAddFlip) ∘ ⇑finSumFinEquiv) = (-1 : 𝕜) ^ (m * n) • (uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h)
          (Quot.mk (⇑(QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range)) σ₁))
            (x ∘ ⇑finSumFinEquiv) := by sorry
  rw[h3, ← smul_assoc, smul_eq_mul, smul_eq_mul, pow_mul_pow_eq_one (m * n) (by simp), one_mul]
  -- Finish off
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/- Corollary of `wedge_antisymm` saying that a wedge of g with itself is
zero if m is odd. -/
theorem wedge_self_odd_zero (g : M [⋀^Fin m]→L[ℝ] ℝ) (m_odd : Odd m) :
    (g ∧[ℝ] g) = 0 := by
  ext x
  let h := wedge_antisymm g g x
  rw[Odd.neg_one_pow (Odd.mul m_odd m_odd), domDomCongr_apply, smul_apply] at h
  have h1 : (g∧[ContinuousLinearMap.mul ℝ ℝ]g) x = (g∧[ContinuousLinearMap.mul ℝ ℝ]g) (x ∘ ⇑finAddFlip) := by
    rw[wedge_product_mul, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply, ContinuousMultilinearMap.sum_apply,
      wedge_product_mul, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro σ hσ
    rcases σ with ⟨σ₁⟩
    rw[uncurrySum.summand_mk]
    rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
      coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
      coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
      ContinuousLinearMap.mul_apply']
    rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
      coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
      coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
      ContinuousLinearMap.mul_apply']
    simp only [smul_left_cancel_iff]
    /- We want to remove `finAddFlip` from this equation by essentially swapping `Sum.inl` and `Sum.inr` how? -/
    simp [Function.comp_def, ]
    have h2 : (fun x_1 ↦ x (finAddFlip (finSumFinEquiv (σ₁ (Sum.inl x_1))))) = fun x_1 ↦ x (finSumFinEquiv (σ₁ (Sum.inr x_1))) := by
      funext n
      congr 1
      ext
      rw[finAddFlip_finSumFinEquiv, Equiv.sumComm_apply]
      congr 1
      refine (Equiv.apply_eq_iff_eq finSumFinEquiv).mpr ?h.e_a.h.e_self.a
      sorry
    have h3 : (fun x_1 ↦ x (finAddFlip (finSumFinEquiv (σ₁ (Sum.inr x_1))))) = fun x_1 ↦ x (finSumFinEquiv (σ₁ (Sum.inl x_1))) := by
      funext n
      congr 1
      sorry
    rw[h2, h3, mul_comm]
  rw[← h1, smul_eq_mul, neg_mul, one_mul] at h
  apply sub_eq_zero_of_eq at h
  rw[sub_neg_eq_add, add_self_eq_zero] at h
  exact h

end wedge

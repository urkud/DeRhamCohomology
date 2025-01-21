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

/- Associativity of wedge product -/
theorem wedge_assoc (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N) (f : N →L[𝕜] N →L[𝕜] N)
    (l : M [⋀^Fin p]→L[𝕜] N) (f' : N →L[𝕜] N →L[𝕜] N) (v : Fin (m + n + p) → M):
    ContinuousAlternatingMap.domDomCongr finAssoc.symm (g ∧[f] h ∧[f'] l) v = ((g ∧[f] h) ∧[f'] l) v := by
  sorry

/- Left distributivity of wedge product -/
theorem add_wedge (g₁ g₂ : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
    ((g₁ + g₂) ∧[f] h) = (g₁ ∧[f] h) + (g₂ ∧[f] h) := by
  ext x
  sorry

/- Right distributivity of wedge product -/
theorem wedge_add (g : M [⋀^Fin m]→L[𝕜] N) (h₁ h₂ : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
    (g ∧[f] (h₁ + h₂)) = (g ∧[f] h₁) + (g ∧[f] h₂) := by sorry

theorem smul_wedge (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (c : 𝕜) :
    c • (g ∧[𝕜] h) = (c • g) ∧[𝕜] h := by
  ext x
  rw[smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  sorry

theorem wedge_smul (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (c : 𝕜) :
    c • (g ∧[𝕜] h) = g ∧[𝕜] (c • h) := by
  ext x
  rw[smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  sorry

/- Antisymmetry of multiplication wedge product -/
theorem wedge_antisymm (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (x : Fin (m + n) → M) :
    (g ∧[𝕜] h) x = ((-1 : 𝕜)^(m*n) • (h ∧[𝕜] g)).domDomCongr finAddFlip x := by sorry

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

theorem wedge_self_odd_zero (g : M [⋀^Fin m]→L[ℝ] ℝ) (m_odd : Odd m) :
    (g ∧[ℝ] g) = 0 := by
  ext x
  let h := wedge_antisymm g g x
  rw[Odd.neg_one_pow (Odd.mul m_odd m_odd), domDomCongr_apply, smul_apply] at h
  have h1 : (g∧[ContinuousLinearMap.mul ℝ ℝ]g) x = (g∧[ContinuousLinearMap.mul ℝ ℝ]g) (x ∘ ⇑finAddFlip) := by
    /- This is done by unpacking definition `including uncurrySum.summand` and seeing that because `g = g` that
    a flip in arguments for `x` doesn't change the outcome. -/
    sorry
  rw[← h1, smul_eq_mul, neg_mul, one_mul] at h
  apply sub_eq_zero_of_eq at h
  rw[sub_neg_eq_add, add_self_eq_zero] at h
  exact h

end wedge

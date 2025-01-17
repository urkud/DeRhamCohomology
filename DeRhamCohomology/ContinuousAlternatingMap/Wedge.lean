import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Mul
import DeRhamCohomology.ContinuousAlternatingMap.Curry
import DeRhamCohomology.Alternating.Basic
import DeRhamCohomology.Equiv.Fin

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
    (l : M [⋀^Fin p]→L[𝕜] N) (f' : N →L[𝕜] N →L[𝕜] N) :
    ContinuousAlternatingMap.domDomCongr finAssoc.symm (g ∧[f] h ∧[f'] l) = ((g ∧[f] h) ∧[f'] l) := by
  rw[wedge_product, ContinuousLinearMap.compContinuousAlternatingMap₂, uncurryFinAdd,
    uncurrySum, ContinuousAlternatingMap.ext_iff]
  intro x
  sorry

/- Left distributivity of wedge product -/
theorem add_wedge (g₁ g₂ : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
    ((g₁ + g₂) ∧[f] h) = (g₁ ∧[f] h) + (g₂ ∧[f] h) := by
  ext x
  sorry


/- Right distributivity of wedge product -/
theorem wedge_add (g : M [⋀^Fin m]→L[𝕜] N) (h₁ h₂ : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
    (g ∧[f] (h₁ + h₂)) = (g ∧[f] h₁) + (g ∧[f] h₂) := by sorry

theorem smul_wedge (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') (c : 𝕜) :
    c • (g ∧[f] h) = (c • g) ∧[f] h := by sorry

theorem wedge_smul (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') (c : 𝕜) :
    c • (g ∧[f] h) = g ∧[f] (c • h) := by sorry

/- Antisymmetry of multiplication wedge product -/
theorem wedge_antisymm (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    (g ∧[𝕜] h) = domDomCongr finAddFlip ((-1)^(m*n) • (h ∧[𝕜] g)) := by sorry

theorem wedge_self_odd_zero (g : M [⋀^Fin m]→L[𝕜] 𝕜) (m_odd : Odd m) :
    (g ∧[𝕜] g) = 0 := by
  let h := wedge_antisymm g g
  rw[Odd.neg_one_pow (Odd.mul m_odd m_odd)] at h
  sorry

end wedge

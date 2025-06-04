/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Curry
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import DeRhamCohomology.Alternating.Basic
import DeRhamCohomology.Multilinear.Basic

noncomputable section
suppress_compilation

namespace ContinuousAlternatingMap

section Curry

variable {𝕜 E F ι ι' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [Fintype ι] [Fintype ι']
  {m n : ℕ}

def uncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) : E [⋀^Fin (n + 1)]→L[𝕜] F :=
  AlternatingMap.mkContinuous (.uncurryFin <| toAlternatingMapLinear ∘ₗ f)
    ((n + 1) * ‖f‖) fun v ↦ calc
      _ = ‖∑ k, (-1) ^ k.val • f (v k) (k.removeNth v)‖ := by
        simp [AlternatingMap.uncurryFin_apply]
      _ ≤ ∑ k, ‖f‖ * ‖v k‖ * ∏ j, ‖v (k.succAbove j)‖ := by
        refine norm_sum_le_of_le _ fun k _ ↦ ?_
        rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg)]
        exact (f (v k)).le_of_opNorm_le (f.le_opNorm _) _
      _ = _ := by
        simp [mul_assoc, ← Fin.prod_univ_succAbove (‖v ·‖)]

lemma toAlternatingMap_uncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    (uncurryFin f).toAlternatingMap = .uncurryFin (toAlternatingMapLinear ∘ₗ f) :=
  rfl

theorem norm_uncurryFin_le (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    ‖uncurryFin f‖ ≤ (n + 1) * ‖f‖ :=
  AlternatingMap.mkContinuous_norm_le _ (by positivity) _

theorem uncurryFin_apply (f : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) (v : Fin (n + 1) → E) :
    uncurryFin f v = ∑ k, (-1) ^ k.val • f (v k) (k.removeNth v) :=
  AlternatingMap.uncurryFin_apply ..

theorem uncurryFin_add (f g : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) :
    uncurryFin (f + g) = uncurryFin f + uncurryFin g := by
  ext v
  simp [uncurryFin_apply, Finset.sum_add_distrib]

theorem uncurryFin_smul {M : Type*} [Monoid M] [DistribMulAction M F] [ContinuousConstSMul M F]
    [SMulCommClass 𝕜 M F] (c : M) (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    uncurryFin (c • f) = c • uncurryFin f := by
  ext v
  simp [uncurryFin_apply, smul_comm _ c, Finset.smul_sum]

@[simps! apply]
def uncurryFinCLM :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := uncurryFin (𝕜 := 𝕜) (E := E) (F := F) (n := n)
      map_add' := by exact uncurryFin_add -- TODO: why does it fail without `by exact`?
      map_smul' := by exact uncurryFin_smul }
    (n + 1) norm_uncurryFin_le

theorem uncurryFin_uncurryFinCLM_comp_of_symmetric {f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F}
    (hf : ∀ x y, f x y = f y x) :
    uncurryFin (uncurryFinCLM.comp f) = 0 :=
  toAlternatingMap_injective <| AlternatingMap.uncurryFin_uncurryFinLM_comp_of_symmetric
    (f := .compr₂ f.toLinearMap₂ toAlternatingMapLinear) fun x y ↦ congr(toAlternatingMap $(hf x y))

/- Interior product -/
def curryFin (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        { toContinuousMultilinearMap := f.1.curryLeft x
          map_eq_zero_of_eq' := fun v i j hv hne ↦ by
            apply f.map_eq_zero_of_eq (Fin.cons x v) (i := i.succ) (j := j.succ) <;> simpa }
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
    ‖f‖ fun x => by
      rw [LinearMap.coe_mk, AddHom.coe_mk, ← norm_toContinuousMultilinearMap]
      dsimp
      refine ContinuousLinearMap.le_of_opNorm_le f.curryLeft ?_ x
      apply le_of_eq
      exact ContinuousMultilinearMap.curryLeft_norm f.toContinuousMultilinearMap

theorem curryFin_apply (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) (m : Fin n → E) :
    curryFin f x m = f (Fin.cons x m) :=
  rfl

theorem curryFin_add (f g : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryFin (f + g) = curryFin f + curryFin g := by
  ext e v
  simp [curryFin_apply]

theorem curryFin_smul {M : Type*} [Monoid M] [DistribMulAction M F] [ContinuousConstSMul M F]
    [SMulCommClass 𝕜 M F] (c : M) (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryFin (c • f) = c • curryFin f := by
  ext e v
  simp [curryFin_apply]

variable [DecidableEq ι] [DecidableEq ι']

/-- summand used in `ContinuousAlternatingMap.uncurrySum` -/
def uncurrySum.summand (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm.ModSumCongr ι ι') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => E) F :=
  Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (ContinuousMultilinearMap.uncurrySum
          (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear)
            : ContinuousMultilinearMap 𝕜 (fun _ => E) (F)).domDomCongr σ)
    fun σ₁ σ₂ H => by
      rw [QuotientGroup.leftRel_apply] at H
      obtain ⟨⟨sl, sr⟩, h⟩ := H
      ext v
      simp [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.uncurrySum_apply,
            MultilinearMap.smul_apply]
      replace h := inv_mul_eq_iff_eq_mul.mp h.symm
      have : Equiv.Perm.sign (σ₁ * Equiv.Perm.sumCongrHom _ _ (sl, sr))
        = Equiv.Perm.sign σ₁ * (Equiv.Perm.sign sl * Equiv.Perm.sign sr) := by simp
      rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff, smul_comm]
      simp [ContinuousMultilinearMap.flipMultilinear]
      erw [← (f.flipAlternating ((fun i ↦ v (σ₁ (Sum.map (⇑sl) (⇑sr) i))) ∘ Sum.inr)).map_congr_perm fun i => v (σ₁ _)]
      simp [ContinuousAlternatingMap.flipAlternating]
      erw [← (f fun i ↦ v (σ₁ (Sum.inl i))).map_congr_perm fun i => v (σ₁ _)]
      simp [ContinuousMultilinearMap.flipAlternating]
      rfl

theorem uncurrySum.summand_mk (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm (ι ⊕ ι')) :
    uncurrySum.summand f (Quot.mk
      (⇑(QuotientGroup.leftRel (Equiv.Perm.sumCongrHom ι ι').range)) σ) = Equiv.Perm.sign σ •
        (ContinuousMultilinearMap.uncurrySum
          (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear) :
            ContinuousMultilinearMap 𝕜 (fun _ => E) F).domDomCongr σ :=
  rfl

theorem uncurrySum.summand_mk'' (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm (ι ⊕ ι')) :
    uncurrySum.summand f (Quotient.mk'' σ) = Equiv.Perm.sign σ •
      (ContinuousMultilinearMap.uncurrySum
        (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear) :
          ContinuousMultilinearMap 𝕜 (fun _ => E) F).domDomCongr σ :=
  rfl

/-- Swapping elements in `σ` with equal values in `v` results in an addition that cancels -/
theorem uncurrySum.summand_add_swap_smul_eq_zero (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F)
    (σ : Equiv.Perm.ModSumCongr ι ι') {v : ι ⊕ ι' → E}
    {i j : ι ⊕ ι'} (hv : v i = v j) (hij : i ≠ j) :
    uncurrySum.summand f σ v + uncurrySum.summand f (Equiv.swap i j • σ) v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    uncurrySum.summand]
  rw [smul_eq_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, Equiv.Perm.coe_mul, Units.val_neg,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.neg_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply]
  convert add_neg_cancel (G := F) _ using 6 <;>
    · ext k
      simp [Function.comp_apply, Function.comp_apply, Equiv.apply_swap_eq_self hv]

/-- Swapping elements in `σ` with equal values in `v` result in zero if the swap has no effect
on the quotient. -/
theorem uncurrySum.summand_eq_zero_of_smul_invariant (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F)
    (σ : Equiv.Perm.ModSumCongr ι ι') {v : ι ⊕ ι' → E}
    {i j : ι ⊕ ι'} (hv : v i = v j) (hij : i ≠ j) :
    Equiv.swap i j • σ = σ → uncurrySum.summand f σ v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.uncurrySum_apply, uncurrySum.summand]
  intro hσ
  cases' hi : σ⁻¹ i with val val <;> cases' hj : σ⁻¹ j with val_1 val_1 <;>
    rw [Equiv.Perm.inv_eq_iff_eq] at hi hj <;> substs hi hj <;> revert val val_1
  -- the term pairs with and cancels another term
  case inl.inr =>
    intro i' j' _ _ hσ
    obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
    replace hσ := Equiv.congr_fun hσ (Sum.inl i')
    dsimp only at hσ
    rw [smul_eq_mul, ← Equiv.mul_swap_eq_swap_mul, mul_inv_rev, Equiv.swap_inv, inv_mul_cancel_right] at hσ
    simp at hσ
  case inr.inl =>
    intro i' j' _ _ hσ
    obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
    replace hσ := Equiv.congr_fun hσ (Sum.inr i')
    dsimp only at hσ
    rw [smul_eq_mul, ← Equiv.mul_swap_eq_swap_mul, mul_inv_rev, Equiv.swap_inv, inv_mul_cancel_right] at hσ
    simp at hσ
  -- the term does not pair but is zero
  case inr.inr =>
    intro i' j' hv hij _
    convert smul_zero (M := ℤˣ) (A := F) _
    exact ContinuousAlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
  case inl.inl =>
    intro i' j' hv hij _
    convert smul_zero (M := ℤˣ) (A := F) _
    simp [ContinuousMultilinearMap.flipMultilinear]
    exact ContinuousAlternatingMap.map_eq_zero_of_eq ((f.flipAlternating ((fun i ↦ v (σ i)) ∘ Sum.inr))) _ hv
      fun hij' => hij (hij' ▸ rfl)

def uncurrySum (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) : E [⋀^ι ⊕ ι']→L[𝕜] F :=
    { ∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ with
    toFun := fun v => (⇑(∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      rw [ContinuousMultilinearMap.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
          (fun σ _ => uncurrySum.summand_add_swap_smul_eq_zero f σ hv hij)
          (fun σ _ => mt <| uncurrySum.summand_eq_zero_of_smul_invariant f σ hv hij)
          (fun σ _ => Finset.mem_univ _) fun σ _ =>
          Equiv.swap_smul_involutive i j σ }

theorem uncurrySum_coe (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) :
    ((uncurrySum f).toContinuousMultilinearMap : ContinuousMultilinearMap 𝕜 (fun _ => E) F) =
      ∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ :=
  ContinuousMultilinearMap.ext fun _ => rfl

theorem uncurrySum_apply (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (m : ι ⊕ ι' → E) :
    uncurrySum f m = (∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ) m :=
  rfl

def uncurryFinAdd (f : E [⋀^Fin m]→L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    E [⋀^Fin (m + n)]→L[𝕜] F :=
  ContinuousAlternatingMap.domDomCongr finSumFinEquiv (uncurrySum f)

end Curry

end ContinuousAlternatingMap

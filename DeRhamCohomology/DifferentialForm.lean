import Mathlib.Analysis.Calculus.FDeriv.Basic
import DeRhamCohomology.ContinuousAlternatingMap.Curry

/-
# Differential Forms

## Main definitions
* `DifferentialForm E F n`
* `extDeriv`


-/

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

variable (E F) in
def DifferentialForm (n : ℕ) := E → E [⋀^Fin n]→L[ℝ] F


variable {v : E}

namespace DifferentialForm

instance : Zero (DifferentialForm E F n) :=
  ⟨ (fun _ => 0) ⟩

@[simp]
theorem zero_apply : (0 : DifferentialForm E F n) v = 0 :=
  rfl

instance inhabited : Inhabited (DifferentialForm E F n) :=
  ⟨0⟩

/- Application of differential form to vector field -/
def differentialform_apply_vectorfield {n : ℕ} (ω : DifferentialForm E F (n + 1)) (ξ : E → (Fin 1 → E)) :=
  fun v ↦ (ω v).curryFin (ξ v 0)



/-- Exterior derivative of a differential form. -/
def extDeriv (ω : DifferentialForm E F n) : DifferentialForm E F (n + 1) :=
  fun x ↦ .uncurryFin (fderiv ℝ ω x)

theorem extderiv_comp_extderiv (ω : DifferentialForm E F n) :
  extDeriv (extDeriv ω) = 0 := by
    sorry



end DifferentialForm

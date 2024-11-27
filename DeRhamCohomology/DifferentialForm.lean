import Mathlib.Analysis.Calculus.FDeriv.Basic
import DeRhamCohomology.ContinuousAlternatingMap.Curry

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

variable (E F) in
def DifferentialForm (n : ℕ) := E → E [⋀^Fin n]→L[ℝ] F

namespace DifferentialForm

/-- Exterior derivative of a differential form. -/
def extDeriv (ω : DifferentialForm E F n) : DifferentialForm E F (n + 1) :=
  fun x ↦ .uncurryFin (fderiv ℝ ω x)

end DifferentialForm

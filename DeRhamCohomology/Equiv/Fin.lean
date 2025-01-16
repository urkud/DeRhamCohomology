import Mathlib.Data.Int.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Embedding.Set
import Mathlib.Logic.Equiv.Option

/-!
# Equivalences for `Fin n`
-/

assert_not_exists MonoidWithZero

universe u

variable {m n o: ℕ}

def finAssoc {m n p : ℕ} : Fin (m + n + p) ≃ Fin (m + (n + p)) := by
  refine finCongr ?eq
  exact Nat.add_assoc m n p

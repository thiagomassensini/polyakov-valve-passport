import PolyakovValvePassport.TraceCompatibility

/-!
# Real-branch adjoint structural passport

The degree-eight structural coefficient sequence is palindromic.  This file
records its endpoints, reflection symmetry, trace, and canonical normalized
passport.
-/

namespace PolyakovValvePassport

noncomputable section

variable {K : Type*} [Field K]

/-- Real-branch adjoint structural coefficient sequence. -/
def adjointRealStructure (phi : K) : ℕ → K
  | 0 => 1
  | 1 => 1 - 9 * phi ^ 2
  | 2 => (3 * phi - 1) ^ 2 * (6 * phi + 1)
  | 3 => -(3 * phi - 1) * (3 * phi + 1) * (9 * phi ^ 2 - 2)
  | 4 => 2 * (9 * phi ^ 2 - 3 * phi - 1) *
      (9 * phi ^ 2 - 3 * phi + 1)
  | 5 => -(3 * phi - 1) * (3 * phi + 1) * (9 * phi ^ 2 - 2)
  | 6 => (3 * phi - 1) ^ 2 * (6 * phi + 1)
  | 7 => 1 - 9 * phi ^ 2
  | 8 => 1
  | _ => 0

@[simp] theorem adjointRealStructure_zero (phi : K) :
    adjointRealStructure phi 0 = 1 := rfl

@[simp] theorem adjointRealStructure_one (phi : K) :
    adjointRealStructure phi 1 = 1 - 9 * phi ^ 2 := rfl

@[simp] theorem adjointRealStructure_eight (phi : K) :
    adjointRealStructure phi 8 = 1 := rfl

/-- The degree-eight coefficient sequence is palindromic. -/
theorem adjointRealStructure_palindromic
    (phi : K) (k : Fin 9) :
    adjointRealStructure phi (k : ℕ) =
      adjointRealStructure phi (8 - (k : ℕ)) := by
  fin_cases k <;> rfl

/-- Canonical normalized adjoint passport. -/
def adjointRealPassport (phi : K) :
    ThermalValvePassport.Passport K :=
  ThermalValvePassport.Passport.normalized K
    (adjointRealStructure phi)

/-- The adjoint passport trace is its first structural coefficient. -/
theorem adjointRealPassport_trace (phi : K) :
    (adjointRealPassport phi).trace =
      gluonStructuralTrace phi phi := by
  simp [adjointRealPassport, pow_two,
    ThermalValvePassport.Passport.normalized,
    gluonStructuralTrace]

/-- The canonical adjoint passport reconstructs every coefficient. -/
theorem adjointRealPassport_reconstructs
    (phi : K) (n : ℕ) :
    ThermalValvePassport.Passport.reconstruct
        (adjointRealPassport phi) n =
      adjointRealStructure phi n := by
  simpa [adjointRealPassport] using
    (ThermalValvePassport.Passport.reconstruct_normalized
      (K := K) (adjointRealStructure phi) (by simp) n)

end

end PolyakovValvePassport

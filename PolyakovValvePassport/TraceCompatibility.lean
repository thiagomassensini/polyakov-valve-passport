import ThermalValvePassport

/-!
# Polyakov trace compatibility

The statements in this file are algebraic.  They keep the fundamental,
antifundamental, and adjoint cameras separate and record their exact trace
compatibility.  No analytic or numerical hypothesis is used.
-/

namespace PolyakovValvePassport

noncomputable section

variable {K : Type*} [Field K]

/-- Structural trace of the fundamental quark camera. -/
def quarkStructuralTrace (phi : K) : K := 3 * phi

/-- Structural trace of the antifundamental antiquark camera. -/
def antiquarkStructuralTrace (phibar : K) : K := 3 * phibar

/-- Structural trace of the adjoint gluon camera. -/
def gluonStructuralTrace (phi phibar : K) : K :=
  1 - 9 * phi * phibar

/-- The three structural cameras carry one exact compatibility constraint. -/
theorem polyakov_three_camera_compatibility
    (phi phibar : K) :
    gluonStructuralTrace phi phibar
      + quarkStructuralTrace phi
        * antiquarkStructuralTrace phibar
      = 1 := by
  simp [gluonStructuralTrace, quarkStructuralTrace,
    antiquarkStructuralTrace]
  ring

/-- At zero chemical potential the quark and antiquark traces coincide. -/
theorem real_polyakov_two_camera_compatibility
    (phi : K) :
    gluonStructuralTrace phi phi
      + (quarkStructuralTrace phi) ^ 2
      = 1 := by
  simp [gluonStructuralTrace, quarkStructuralTrace]
  ring

/-- Fundamental SU(3) structural coefficient sequence. -/
def fundamentalStructure (phi phibar : K) : ℕ → K
  | 0 => 1
  | 1 => 3 * phi
  | 2 => 3 * phibar
  | 3 => 1
  | _ => 0

@[simp] theorem fundamentalStructure_zero (phi phibar : K) :
    fundamentalStructure phi phibar 0 = 1 := rfl

@[simp] theorem fundamentalStructure_one (phi phibar : K) :
    fundamentalStructure phi phibar 1 = 3 * phi := rfl

@[simp] theorem fundamentalStructure_two (phi phibar : K) :
    fundamentalStructure phi phibar 2 = 3 * phibar := rfl

@[simp] theorem fundamentalStructure_three (phi phibar : K) :
    fundamentalStructure phi phibar 3 = 1 := rfl

/-- Canonical normalized passport of the fundamental structure. -/
def fundamentalPassport (phi phibar : K) :
    ThermalValvePassport.Passport K :=
  ThermalValvePassport.Passport.normalized K
    (fundamentalStructure phi phibar)

/-- Canonical normalized passport of the antifundamental structure. -/
def antifundamentalPassport (phi phibar : K) :
    ThermalValvePassport.Passport K :=
  fundamentalPassport phibar phi

/-- The normalized passport trace of the fundamental structure. -/
theorem fundamental_normalized_passport_trace
    (phi phibar : K) :
    (fundamentalPassport phi phibar).trace =
      quarkStructuralTrace phi := by
  simp [fundamentalPassport, ThermalValvePassport.Passport.normalized,
    quarkStructuralTrace]

/-- The normalized passport trace of the antifundamental structure. -/
theorem antifundamental_normalized_passport_trace
    (phi phibar : K) :
    (antifundamentalPassport phi phibar).trace =
      antiquarkStructuralTrace phibar := by
  simp [antifundamentalPassport,
    fundamental_normalized_passport_trace,
    antiquarkStructuralTrace, quarkStructuralTrace]

/-- First fundamental curvature coordinate. -/
theorem fundamental_normalized_passport_curvature_zero
    (phi phibar : K) :
    (fundamentalPassport phi phibar).curvature 0 =
      1 - 6 * phi + 3 * phibar := by
  simp [fundamentalPassport, ThermalValvePassport.Passport.normalized,
    ThermalValvePassport.secondDifference, fundamentalStructure]
  ring

/-- Second fundamental curvature coordinate. -/
theorem fundamental_normalized_passport_curvature_one
    (phi phibar : K) :
    (fundamentalPassport phi phibar).curvature 1 =
      1 + 3 * phi - 6 * phibar := by
  simp [fundamentalPassport, ThermalValvePassport.Passport.normalized,
    ThermalValvePassport.secondDifference, fundamentalStructure]
  ring

/-- On the real branch the two fundamental curvature coordinates coincide. -/
theorem fundamental_real_curvatures
    (phi : K) :
    (fundamentalPassport phi phi).curvature 0 = 1 - 3 * phi ∧
      (fundamentalPassport phi phi).curvature 1 = 1 - 3 * phi := by
  constructor
  · rw [fundamental_normalized_passport_curvature_zero]
    ring
  · rw [fundamental_normalized_passport_curvature_one]
    ring

/-- The canonical passport reconstructs every fundamental coefficient. -/
theorem fundamental_passport_reconstructs
    (phi phibar : K) (n : ℕ) :
    ThermalValvePassport.Passport.reconstruct
        (fundamentalPassport phi phibar) n =
      fundamentalStructure phi phibar n := by
  simpa [fundamentalPassport] using
    (ThermalValvePassport.Passport.reconstruct_normalized
      (K := K) (fundamentalStructure phi phibar)
      (by simp) n)

/-- A public three-camera passport with compatibility carried as data. -/
structure TriplePassport (K : Type*) [Field K] where
  quark : ThermalValvePassport.Passport K
  antiquark : ThermalValvePassport.Passport K
  gluon : ThermalValvePassport.Passport K
  compatibility :
    gluon.trace + quark.trace * antiquark.trace = 1

end

end PolyakovValvePassport

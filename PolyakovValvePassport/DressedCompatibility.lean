import PolyakovValvePassport.TraceCompatibility

/-!
# Compatibility after independent carrier dressing

Each camera may have its own nonzero carrier and normalization.  The carrier
passport removes those choices before the Polyakov compatibility law is
tested.
-/

namespace PolyakovValvePassport

noncomputable section

variable {K : Type*} [Field K]

/-- Minimal structural sequence with prescribed boundary trace. -/
def traceStructure (tau : K) : ℕ → K
  | 0 => 1
  | 1 => tau
  | _ => 0

@[simp] theorem traceStructure_zero (tau : K) :
    traceStructure tau 0 = 1 := rfl

@[simp] theorem traceStructure_one (tau : K) :
    traceStructure tau 1 = tau := rfl

/-- An arbitrary nonzero carrier and scale preserve the prescribed trace. -/
theorem carrierTrace_traceStructure_dressed
    (c tau : K) (w : ℕ → K)
    (hw : ∀ n, w n ≠ 0) (hc : c ≠ 0) :
    ThermalValvePassport.carrierTrace w
        (ThermalValvePassport.carrierDressed c w
          (traceStructure tau)) =
      tau := by
  simpa using
    (ThermalValvePassport.carrierTrace_dressed
      (K := K) c w (traceStructure tau) hw hc (by simp))

/-- Polyakov compatibility survives three independent nonzero dressings. -/
theorem dressed_polyakov_three_camera_compatibility
    (phi phibar : K)
    (cq ca cg : K) (wq wa wg : ℕ → K)
    (hwq : ∀ n, wq n ≠ 0)
    (hwa : ∀ n, wa n ≠ 0)
    (hwg : ∀ n, wg n ≠ 0)
    (hcq : cq ≠ 0) (hca : ca ≠ 0) (hcg : cg ≠ 0) :
    ThermalValvePassport.carrierTrace wg
        (ThermalValvePassport.carrierDressed cg wg
          (traceStructure (gluonStructuralTrace phi phibar))) +
      ThermalValvePassport.carrierTrace wq
          (ThermalValvePassport.carrierDressed cq wq
            (traceStructure (quarkStructuralTrace phi))) *
        ThermalValvePassport.carrierTrace wa
          (ThermalValvePassport.carrierDressed ca wa
            (traceStructure (antiquarkStructuralTrace phibar))) =
      1 := by
  rw [carrierTrace_traceStructure_dressed cg
      (gluonStructuralTrace phi phibar) wg hwg hcg,
    carrierTrace_traceStructure_dressed cq
      (quarkStructuralTrace phi) wq hwq hcq,
    carrierTrace_traceStructure_dressed ca
      (antiquarkStructuralTrace phibar) wa hwa hca]
  exact polyakov_three_camera_compatibility phi phibar

/-- Canonical normalized passport for one prescribed structural trace. -/
def tracePassport (tau : K) : ThermalValvePassport.Passport K :=
  ThermalValvePassport.Passport.normalized K (traceStructure tau)

@[simp] theorem tracePassport_trace (tau : K) :
    (tracePassport tau).trace = tau := by
  simp [tracePassport, ThermalValvePassport.Passport.normalized]

/-- Canonical compatible three-camera passport. -/
def canonicalTriplePassport
    (phi phibar : K) : TriplePassport K where
  quark := fundamentalPassport phi phibar
  antiquark := antifundamentalPassport phi phibar
  gluon := tracePassport (gluonStructuralTrace phi phibar)
  compatibility := by
    rw [tracePassport_trace,
      fundamental_normalized_passport_trace,
      antifundamental_normalized_passport_trace]
    exact polyakov_three_camera_compatibility phi phibar

end

end PolyakovValvePassport

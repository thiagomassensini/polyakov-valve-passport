import ThermalValvePassport

/-!
# Mode-mixing obstruction

A convex mixture of geometric carriers is not itself geometric unless the
active ratios coincide.  The finite-family theorem is expressed through an
order-independent sum over all ordered pairs; division by two recovers the
usual sum over unordered pairs.
-/

open scoped BigOperators

namespace PolyakovValvePassport

noncomputable section

variable {K : Type*} [CommRing K]

/-- Carrier obtained by compressing two unresolved thermal modes. -/
def twoModeCarrier (w q₁ q₂ : K) (k : ℕ) : K :=
  w * q₁ ^ k + (1 - w) * q₂ ^ k

/-- Exact two-mode Hankel defect. -/
theorem twoModeHankelDefect
    (w q₁ q₂ : K) :
    twoModeCarrier w q₁ q₂ 0 * twoModeCarrier w q₁ q₂ 2
      - (twoModeCarrier w q₁ q₂ 1) ^ 2
      = w * (1 - w) * (q₁ - q₂) ^ 2 := by
  simp [twoModeCarrier]
  ring

section OrderedTwoMode

variable {R : Type*} [LinearOrderedField R]

/-- The two-mode defect is nonnegative for a convex mixture. -/
theorem twoModeHankelDefect_nonneg
    (w q₁ q₂ : R) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ twoModeCarrier w q₁ q₂ 0 * twoModeCarrier w q₁ q₂ 2
      - (twoModeCarrier w q₁ q₂ 1) ^ 2 := by
  rw [twoModeHankelDefect]
  exact mul_nonneg
    (mul_nonneg hw0 (sub_nonneg.mpr hw1))
    (sq_nonneg (q₁ - q₂))

/-- With both weights active, zero defect is equivalent to one common
carrier ratio. -/
theorem twoModeHankelDefect_eq_zero_iff
    (w q₁ q₂ : R) (hw0 : 0 < w) (hw1 : w < 1) :
    twoModeCarrier w q₁ q₂ 0 * twoModeCarrier w q₁ q₂ 2
        - (twoModeCarrier w q₁ q₂ 1) ^ 2 = 0 ↔
      q₁ = q₂ := by
  rw [twoModeHankelDefect]
  constructor
  · intro h
    have hw : w * (1 - w) ≠ 0 :=
      ne_of_gt (mul_pos hw0 (sub_pos.mpr hw1))
    have hsquare : (q₁ - q₂) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left hw
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro h
    rw [h]
    ring

end OrderedTwoMode

section FiniteFamily

variable {ι : Type*} [DecidableEq ι]

/-- Total weight of a finite mode family. -/
def totalModeWeight (s : Finset ι) (w : ι → K) : K :=
  ∑ i ∈ s, w i

/-- First weighted carrier moment. -/
def firstModeMoment (s : Finset ι) (w q : ι → K) : K :=
  ∑ i ∈ s, w i * q i

/-- Second weighted carrier moment. -/
def secondModeMoment (s : Finset ι) (w q : ι → K) : K :=
  ∑ i ∈ s, w i * (q i) ^ 2

/-- Hankel defect of an arbitrary finite unresolved family. -/
def finiteModeHankelDefect
    (s : Finset ι) (w q : ι → K) : K :=
  totalModeWeight s w * secondModeMoment s w q -
    (firstModeMoment s w q) ^ 2

/-- Order-independent pair energy.  Each unordered pair occurs twice. -/
def orderedPairMixingEnergy
    (s : Finset ι) (w q : ι → K) : K :=
  ∑ i ∈ s, ∑ j ∈ s,
    w i * w j * (q i - q j) ^ 2

/-- Exact finite-family moment identity. -/
theorem twice_finiteModeHankelDefect
    (s : Finset ι) (w q : ι → K) :
    2 * finiteModeHankelDefect s w q =
      orderedPairMixingEnergy s w q := by
  classical
  have hmoment :
      totalModeWeight s w * secondModeMoment s w q =
        ∑ i ∈ s, ∑ j ∈ s,
          w i * (w j * (q j) ^ 2) := by
    exact Finset.sum_mul_sum s s w (fun j => w j * (q j) ^ 2)
  have hfirst :
      (firstModeMoment s w q) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s,
          (w i * q i) * (w j * q j) := by
    rw [pow_two]
    exact Finset.sum_mul_sum s s
      (fun i => w i * q i) (fun j => w j * q j)
  have hsymm :
      (∑ i ∈ s, ∑ j ∈ s,
          (w i * (q i) ^ 2) * w j) =
        ∑ i ∈ s, ∑ j ∈ s,
          w i * (w j * (q j) ^ 2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hexpand :
      orderedPairMixingEnergy s w q =
        (∑ i ∈ s, ∑ j ∈ s,
          (w i * (q i) ^ 2) * w j) +
        (∑ i ∈ s, ∑ j ∈ s,
          w i * (w j * (q j) ^ 2)) -
        2 * (∑ i ∈ s, ∑ j ∈ s,
          (w i * q i) * (w j * q j)) := by
    unfold orderedPairMixingEnergy
    calc
      (∑ i ∈ s, ∑ j ∈ s,
          w i * w j * (q i - q j) ^ 2) =
          ∑ i ∈ s, ∑ j ∈ s,
            ((w i * (q i) ^ 2) * w j +
              w i * (w j * (q j) ^ 2) -
              2 * ((w i * q i) * (w j * q j))) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ i ∈ s, ∑ j ∈ s,
            (w i * (q i) ^ 2) * w j) +
          (∑ i ∈ s, ∑ j ∈ s,
            w i * (w j * (q j) ^ 2)) -
          2 * (∑ i ∈ s, ∑ j ∈ s,
            (w i * q i) * (w j * q j)) := by
            simp only [Finset.sum_sub_distrib,
              Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold finiteModeHankelDefect
  rw [hmoment, hfirst, hexpand, hsymm]
  ring

end FiniteFamily

section OrderedFiniteFamily

variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [LinearOrderedField R]

/-- Pair energy is nonnegative for nonnegative weights. -/
theorem orderedPairMixingEnergy_nonneg
    (s : Finset ι) (w q : ι → R)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ orderedPairMixingEnergy s w q := by
  unfold orderedPairMixingEnergy
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg
    (mul_nonneg (hw i hi) (hw j hj))
    (sq_nonneg (q i - q j))

/-- Vanishing pair energy means that every pair of positive-weight modes has
the same carrier ratio. -/
theorem orderedPairMixingEnergy_eq_zero_iff
    (s : Finset ι) (w q : ι → R)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    orderedPairMixingEnergy s w q = 0 ↔
      ∀ i ∈ s, ∀ j ∈ s,
        0 < w i → 0 < w j → q i = q j := by
  constructor
  · intro hzero i hi j hj hwi hwj
    have houter :
        ∀ a ∈ s,
          (∑ b ∈ s, w a * w b * (q a - q b) ^ 2) = 0 := by
      have hnonneg :
          ∀ a ∈ s,
            0 ≤ ∑ b ∈ s, w a * w b * (q a - q b) ^ 2 := by
        intro a ha
        apply Finset.sum_nonneg
        intro b hb
        exact mul_nonneg
          (mul_nonneg (hw a ha) (hw b hb))
          (sq_nonneg (q a - q b))
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp
        (show
          (∑ a ∈ s, ∑ b ∈ s,
            w a * w b * (q a - q b) ^ 2) = 0 by
              simpa [orderedPairMixingEnergy] using hzero)
    have hterm :
        w i * w j * (q i - q j) ^ 2 = 0 := by
      have hnonneg :
          ∀ b ∈ s, 0 ≤ w i * w b * (q i - q b) ^ 2 := by
        intro b hb
        exact mul_nonneg
          (mul_nonneg (hw i hi) (hw b hb))
          (sq_nonneg (q i - q b))
      exact
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp
          (houter i hi) j hj
    have hweight : w i * w j ≠ 0 :=
      ne_of_gt (mul_pos hwi hwj)
    have hsquare : (q i - q j) ^ 2 = 0 :=
      (mul_eq_zero.mp hterm).resolve_left hweight
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro hconstant
    unfold orderedPairMixingEnergy
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hwi : w i = 0
    · simp [hwi]
    by_cases hwj : w j = 0
    · simp [hwj]
    have hwipos : 0 < w i :=
      lt_of_le_of_ne (hw i hi) (Ne.symm hwi)
    have hwjpos : 0 < w j :=
      lt_of_le_of_ne (hw j hj) (Ne.symm hwj)
    rw [hconstant i hi j hj hwipos hwjpos]
    ring

/-- The finite-family Hankel defect is nonnegative. -/
theorem finiteModeHankelDefect_nonneg
    (s : Finset ι) (w q : ι → R)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ finiteModeHankelDefect s w q := by
  have hid := twice_finiteModeHankelDefect
    (K := R) s w q
  have henergy := orderedPairMixingEnergy_nonneg s w q hw
  nlinarith

/-- Exact equality case for an arbitrary finite family. -/
theorem finiteModeHankelDefect_eq_zero_iff
    (s : Finset ι) (w q : ι → R)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    finiteModeHankelDefect s w q = 0 ↔
      ∀ i ∈ s, ∀ j ∈ s,
        0 < w i → 0 < w j → q i = q j := by
  have hzero :
      finiteModeHankelDefect s w q = 0 ↔
        orderedPairMixingEnergy s w q = 0 := by
    constructor
    · intro h
      rw [← twice_finiteModeHankelDefect (K := R) s w q, h]
      ring
    · intro h
      have htwice :
          2 * finiteModeHankelDefect s w q = 0 := by
        rw [twice_finiteModeHankelDefect (K := R) s w q, h]
      exact (mul_eq_zero.mp htwice).resolve_left (by norm_num)
  exact hzero.trans (orderedPairMixingEnergy_eq_zero_iff s w q hw)

/-- The conventional unordered-pair energy is half of the ordered-pair
energy. -/
def finiteMixingEnergy
    (s : Finset ι) (w q : ι → R) : R :=
  (2 : R)⁻¹ * orderedPairMixingEnergy s w q

/-- The moment defect equals the order-independent unordered-pair energy. -/
theorem finiteModeHankelDefect_eq_finiteMixingEnergy
    (s : Finset ι) (w q : ι → R) :
    finiteModeHankelDefect s w q =
      finiteMixingEnergy s w q := by
  unfold finiteMixingEnergy
  have hid := twice_finiteModeHankelDefect (K := R) s w q
  field_simp
  nlinarith

end OrderedFiniteFamily

end

end PolyakovValvePassport

# Formalization map

## Scope

This library certifies algebraic identities for structural Polyakov-loop
channels and finite mixtures of geometric carriers. The physical channel
names provide provenance for the coefficient sequences; the theorems
themselves require no temperature, lattice spacing, probability model,
continuum limit, or numerical threshold.

All declarations below are exported by the public root
`PolyakovValvePassport.lean`.

## 1. Structural traces

### Definitions

```lean
quarkStructuralTrace
antiquarkStructuralTrace
gluonStructuralTrace
```

They encode

```math
\tau_q=3\Phi,\qquad
\tau_{\bar q}=3\bar\Phi,\qquad
\tau_g=1-9\Phi\bar\Phi.
```

### Compatibility theorems

```lean
polyakov_three_camera_compatibility
real_polyakov_two_camera_compatibility
```

The general identity is

```math
\boxed{\tau_g+\tau_q\tau_{\bar q}=1}.
```

No equality between the quark and antiquark channels is assumed. Their traces
coincide only in the separately stated real-branch specialization.

## 2. Fundamental and antifundamental passports

### Definitions

```lean
fundamentalStructure
fundamentalPassport
antifundamentalPassport
```

The fundamental coefficient sequence is

```math
(1,\ 3\Phi,\ 3\bar\Phi,\ 1,\ 0,\ldots).
```

The antifundamental passport exchanges \(\Phi\) and \(\bar\Phi\).

### Trace and curvature theorems

```lean
fundamental_normalized_passport_trace
antifundamental_normalized_passport_trace
fundamental_normalized_passport_curvature_zero
fundamental_normalized_passport_curvature_one
fundamental_real_curvatures
```

The two fundamental curvature coordinates are

```math
\kappa_0=1-6\Phi+3\bar\Phi,\qquad
\kappa_1=1+3\Phi-6\bar\Phi.
```

On the real branch, both reduce to \(1-3\Phi\).

### Completeness theorem

```lean
fundamental_passport_reconstructs
```

The canonical passport reconstructs every coefficient of the fundamental
sequence exactly.

## 3. Independent dressing

### Definitions

```lean
traceStructure
tracePassport
canonicalTriplePassport
TriplePassport
```

### Theorems

```lean
carrierTrace_traceStructure_dressed
dressed_polyakov_three_camera_compatibility
tracePassport_trace
```

Each camera may be dressed by its own nonzero normalization and nowhere-zero
carrier. Stripping those choices channel by channel recovers the prescribed
trace and therefore preserves the three-camera compatibility law.

The theorem does not require the three carriers to coincide.

## 4. Two-mode obstruction

### Definition

```lean
twoModeCarrier
```

For

```math
K_k=wq_1^k+(1-w)q_2^k,
```

the certified identity is

```lean
twoModeHankelDefect
```

or

```math
\boxed{K_0K_2-K_1^2=w(1-w)(q_1-q_2)^2}.
```

For \(0\le w\le1\), the defect is nonnegative:

```lean
twoModeHankelDefect_nonneg
```

When both weights are active, zero defect is equivalent to \(q_1=q_2\):

```lean
twoModeHankelDefect_eq_zero_iff
```

## 5. Arbitrary finite mode families

### Definitions

```lean
totalModeWeight
firstModeMoment
secondModeMoment
finiteModeHankelDefect
orderedPairMixingEnergy
finiteMixingEnergy
```

For

```math
W=\sum_iw_i,\qquad
M_1=\sum_iw_iq_i,\qquad
M_2=\sum_iw_iq_i^2,
```

the order-independent identity is

```lean
twice_finiteModeHankelDefect
```

which proves

```math
\boxed{
2(WM_2-M_1^2)
=
\sum_{i,j}w_iw_j(q_i-q_j)^2
}.
```

The right-hand side counts every unordered pair twice.

### Positivity and equality case

```lean
orderedPairMixingEnergy_nonneg
orderedPairMixingEnergy_eq_zero_iff
finiteModeHankelDefect_nonneg
finiteModeHankelDefect_eq_zero_iff
finiteModeHankelDefect_eq_finiteMixingEnergy
```

With nonnegative weights:

```math
WM_2-M_1^2\ge0.
```

Moreover,

```math
WM_2-M_1^2=0
```

if and only if all modes in the positive-weight support have the same carrier
ratio. Zero-weight modes are correctly excluded from the equality condition.

## 6. Real-branch adjoint passport

### Definitions

```lean
adjointRealStructure
adjointRealPassport
```

### Theorems

```lean
adjointRealStructure_palindromic
adjointRealPassport_trace
adjointRealPassport_reconstructs
```

The degree-eight adjoint coefficient sequence is palindromic, its passport
trace equals the gluon structural trace on the real branch, and the canonical
passport reconstructs every coefficient exactly.

## 7. Dependency boundary

Carrier removal and general passport reconstruction are imported from the
certified `thermal-valve-passport` release `v0.4.0`. This repository adds the
Polyakov-specific coefficient sequences, compatibility laws, and mode-mixing
theorems without copying or weakening the underlying carrier API.

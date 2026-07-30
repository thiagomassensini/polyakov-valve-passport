# Polyakov Valve Passport v0.1.0

Initial independent Lean 4 release of exact structural compatibility and
unresolved carrier-mixing identities for fundamental, antifundamental, and
adjoint Polyakov-loop channels.

## Three-camera compatibility

For the structural traces

```math
\tau_q=3\Phi,\qquad
\tau_{\bar q}=3\bar\Phi,\qquad
\tau_g=1-9\Phi\bar\Phi,
```

Lean proves the exact identity

```math
\tau_g+\tau_q\tau_{\bar q}=1.
```

On the real branch, this reduces to

```math
\tau_g+\tau_q^2=1.
```

## Independent carrier dressing

The three cameras may receive different nonzero normalizations and geometric
carriers. After each channel is stripped by its own carrier passport, the same
compatibility law holds exactly. No common carrier is assumed.

## Structural passports

The release includes canonical passports for:

- the fundamental coefficient sequence;
- the antifundamental coefficient sequence;
- the real-branch adjoint coefficient sequence;
- a minimal sequence with prescribed structural trace.

The fundamental and adjoint passports reconstruct every declared structural
coefficient. The degree-eight adjoint sequence is proved palindromic.

## Exact finite-mode mixing identity

For a finite family with weights \(w_i\) and carrier ratios \(q_i\), define

```math
W=\sum_i w_i,\qquad
M_1=\sum_i w_iq_i,\qquad
M_2=\sum_i w_iq_i^2.
```

The formalization proves

```math
2(WM_2-M_1^2)
=
\sum_{i,j}w_iw_j(q_i-q_j)^2.
```

Over a linearly ordered field with nonnegative weights, the defect is
nonnegative. It vanishes exactly when every pair of positive-weight modes has
the same carrier ratio. This is the precise algebraic obstruction created by
mixing distinct carriers before removing them.

The two-mode specialization is also proved:

```math
K_0K_2-K_1^2
=
w(1-w)(q_1-q_2)^2.
```

## Certified modules

- `PolyakovValvePassport.TraceCompatibility`
- `PolyakovValvePassport.DressedCompatibility`
- `PolyakovValvePassport.ModeMixing`
- `PolyakovValvePassport.Adjoint`

The public root exports 32 theorems and 19 definitions or structures.

## Validation

The release is gated by:

```bash
lake build --wfail
lake env lean PolyakovValvePassport.lean
```

CI also rejects proof placeholders and user axioms. The theorem statements do
not claim a phase transition, critical temperature, continuum limit, or
phenomenological fit.

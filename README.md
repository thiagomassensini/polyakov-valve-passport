# Polyakov Valve Passport

Independent Lean 4 formalization of structural compatibility and unresolved
carrier mixing for three Polyakov-loop channels:

- quark (fundamental);
- antiquark (antifundamental);
- gluon (adjoint).

The structural traces satisfy the exact compatibility law

```text
tau_g + tau_q * tau_antiquark = 1.
```

The law remains true after the three cameras receive independent nonzero
carrier dressings and normalizations, because the carrier passport removes
those choices before the traces are compared.

For an arbitrary finite family of unresolved modes, the formalization proves
the exact identity

```text
2 * HankelDefect = sum_{i,j} w_i * w_j * (q_i - q_j)^2.
```

Over a linear ordered field with nonnegative weights, the defect is
nonnegative. It vanishes exactly when every pair of positive-weight modes has
the same carrier ratio.

The project depends on
[`thermal-valve-passport` v0.4.0](https://github.com/thiagomassensini/thermal-valve-passport/releases/tag/v0.4.0)
for carrier removal and exact passport reconstruction.

## Scope

The certified statements are algebraic. They do not assert a phase
transition, a critical temperature, a continuum limit, or a phenomenological
fit. Numerical Checkpoint 12 artifacts are intentionally kept outside this
formal library.

## Formal modules

- `PolyakovValvePassport/TraceCompatibility.lean`
- `PolyakovValvePassport/DressedCompatibility.lean`
- `PolyakovValvePassport/ModeMixing.lean`
- `PolyakovValvePassport/Adjoint.lean`

See [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md) for the theorem map.

## Verification

CI builds the public root with `lake build --wfail`, rejects `sorry`, `admit`,
and project axioms, and recompiles `PolyakovValvePassport.lean` directly.

## License

Apache-2.0.

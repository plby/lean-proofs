# Szemerédi's theorem

This directory contains the dense Szemerédi portion of the formalization in
[`Vilin97/Clawristotle/green-tao`](https://github.com/Vilin97/Clawristotle/tree/09497ebf6ee48ef49c4f3d24501954bc3a2855d6/green-tao),
ported from Lean 4.32.2 to this project's Lean/mathlib 4.33.0 environment.

The imported source is the Lean-module dependency closure needed by:

- `Submission/Szemeredi/OrderedRemoval.lean`
- `Submission/Hypergraph/SourceFullBundleRemovalAssembly.lean`

The unused natural-number affine bridge imported by upstream's progression
counting module was also removed. Prime counting, sieve estimates,
transference to the primes, the W-trick, and the final Green–Tao theorem are
intentionally excluded. Module imports and the original
`Submission.GreenTao` namespace were localized beneath
`Wikipedia.SzemeredisTheorem`; mathematical declarations and proofs otherwise
retain their upstream structure.

`Main.lean` exposes `Wikipedia.SzemeredisTheorem.szemeredi`, the uniform
quantitative cyclic counting form of Szemerédi's theorem.

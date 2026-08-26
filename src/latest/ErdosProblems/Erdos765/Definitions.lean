/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied with the original gist.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 765.
Informal authors: István Reiman, Paul Erdős, Alfréd Rényi, W. G. Brown;
following the exposition of Martin Aigner and Günter M. Ziegler.
Formal authors: Aristotle, Jeremy Tan Jie Rui (Parcly-Taxel).
Source: https://www.erdosproblems.com/765#post-6480
https://gist.githubusercontent.com/Parcly-Taxel/13d3bd0f1390b0832a42994a09cf91c5/raw/e267a3a494e64019a1a442b3b05438745923883b/Erdos765.lean
Original Lean/Mathlib version: 4.28.0 (the linked editor project).
The original prime_between axiom is discharged using this repository's PNT+ library.
-/
import Mathlib

namespace Erdos765

/-- The 4-cycle over `Fin 4`, where vertices differing by 1 are adjacent. -/
def C4 : SimpleGraph (Fin 4) where
  Adj i j := j = i + 1 ∨ i = j + 1

end Erdos765

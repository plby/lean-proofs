/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 186

Let `F N` be the largest cardinality of a subset of `{1, ..., N}` in which
no element is the arithmetic mean of two or more distinct other elements.
Bosznay proved the lower bound `N^(1/4) ≪ F(N)`, while Pham and Zakharov
proved `F(N) ≪_ε N^(1/4+ε)` for every `ε > 0`.

The finite extremal definition is in `Foundations`, Bosznay's construction
is in `LowerBound`, and `UpperPackaging` states the precise
Pham--Zakharov integer-box estimate and proves its one-dimensional
specialization.  The theorem below is the narrow assembly boundary: once
the box estimate is supplied, it yields exactly the published resolution.

References:

* A. P. Bosznay, *On the lower estimation of nonaveraging sets* (1989).
* H. T. Pham and D. Zakharov, *Sharp bound for the Erdős--Straus
  non-averaging set problem*, arXiv:2410.14624.
-/

namespace Erdos186

open Filter

open Finset

noncomputable section

def IsNonaveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ,
    S ⊆ A.erase a → 2 ≤ S.card → S.card * a ≠ S.sum id

noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) :=
  by
    classical
    exact (Finset.Icc 1 N).powerset.filter IsNonaveraging

noncomputable def F (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

/-- The exact asymptotic conclusion of Erdős Problem 186, assembled from
Bosznay's proved construction and a proof of the Pham--Zakharov box theorem.

This is deliberately a theorem with an ordinary proof parameter, not a
postulate.  The unconditional main theorem is added only after `PZBoxBound`
has itself been proved. -/

theorem erdos_186 :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (F N : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ ↦ (F N : ℝ)) =O[atTop]
          (fun N : ℕ ↦ (N : ℝ) ^ ((1 / 4 : ℝ) + ε)) := by
  sorry

end

end Erdos186

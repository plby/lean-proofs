/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialMasterLaw

/-!
# Initial typicality from explicit loss bounds

At density parameters `p = eta = 1`, every target in iteration typicality is
just the relevant vortex-set cardinality.  Consequently the upper bounds are
automatic, and the lower bounds follow by charging the missing vertices to a
single `xi |U|` loss budget.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A subset occupying all but at most an `xi` fraction of a finite set lies
in the required multiplicative window around the full cardinality. -/
theorem withinMultiplicativeError_one_of_subset_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    {S U : Finset V} {xi : ℝ≥0}
    (hsub : S ⊆ U) (hxi : xi ≤ 1)
    (hloss : ((U \ S).card : ℝ≥0) ≤ xi * (U.card : ℝ≥0)) :
    WithinMultiplicativeError xi (S.card : ℝ≥0) (U.card : ℝ≥0) := by
  have hxiu : xi * (U.card : ℝ≥0) ≤ (U.card : ℝ≥0) := by
    calc
      xi * (U.card : ℝ≥0) ≤ 1 * (U.card : ℝ≥0) := by gcongr
      _ = (U.card : ℝ≥0) := one_mul _
  have hcard : (U.card : ℝ≥0) =
      (S.card : ℝ≥0) + ((U \ S).card : ℝ≥0) := by
    calc
      (U.card : ℝ≥0) = ((U \ S).card : ℝ≥0) + (S.card : ℝ≥0) := by
        exact_mod_cast (card_sdiff_add_card_eq_card hsub).symm
      _ = (S.card : ℝ≥0) + ((U \ S).card : ℝ≥0) := add_comm _ _
  constructor
  · rw [tsub_mul, one_mul]
    apply (tsub_le_iff_right).2
    calc
      (U.card : ℝ≥0) =
          (S.card : ℝ≥0) + ((U \ S).card : ℝ≥0) := hcard
      _ ≤ (S.card : ℝ≥0) + xi * (U.card : ℝ≥0) := by
        gcongr
  · calc
      (S.card : ℝ≥0) ≤ (U.card : ℝ≥0) := by
        exact_mod_cast card_le_card hsub
      _ ≤ (1 + xi) * (U.card : ℝ≥0) := by
        calc
          (U.card : ℝ≥0) = 1 * (U.card : ℝ≥0) := by ring
          _ ≤ (1 + xi) * (U.card : ℝ≥0) := by
            gcongr
            exact le_add_right (le_refl 1)

/-- The complete initial typicality assertion at unit graph and availability
density follows from vertex-loss bounds for degrees and all tested extension
patterns. -/
theorem initialIterationTypical_of_loss_bounds
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1))
    (G : SimpleGraph V) (A : TripleSystemOn V)
    (xi : ℝ≥0) (hxi : xi ≤ 1) (h : ℕ)
    (hdegreeSame : ∀ i : Fin ell, k.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
        (((W.U i.castSucc \ neighborsIn G (W.U i.castSucc) v).card : ℕ) :
            ℝ≥0) ≤ xi * (W.U i.castSucc).card)
    (hdegreeNext : ∀ i : Fin ell, k.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
        (((W.U i.succ \ neighborsIn G (W.U i.succ) v).card : ℕ) :
            ℝ≥0) ≤ xi * (W.U i.succ).card)
    (hextension : ∀ i : Fin ell, k.val ≤ i.val →
      ∀ iStar : Fin (ell + 1),
        (iStar = i.castSucc ∨ iStar = i.succ) →
      ∀ Q : SimpleGraph V, Q ≤ G →
        GraphSupportedOn Q (W.U i.castSucc : Set V) →
        (graphSupportFinset Q).card ≤ h →
        (((W.U iStar \ iterationExtensionVertices A Q (W.U iStar)).card : ℕ) :
            ℝ≥0) ≤ xi * (W.U iStar).card) :
    IsIterationTypical W k G A 1 1 xi h := by
  constructor
  · intro i hki
    constructor
    · intro v hv
      simpa using withinMultiplicativeError_one_of_subset_loss
        (show neighborsIn G (W.U i.castSucc) v ⊆ W.U i.castSucc from
          fun _x hx ↦ (mem_neighborsIn_iff.mp hx).1)
        hxi (hdegreeSame i hki v hv)
    · intro v hv
      simpa using withinMultiplicativeError_one_of_subset_loss
        (show neighborsIn G (W.U i.succ) v ⊆ W.U i.succ from
          fun _x hx ↦ (mem_neighborsIn_iff.mp hx).1)
        hxi (hdegreeNext i hki v hv)
  · intro i hki iStar hiStar Q hQG hQsupport hQcard
    simpa using withinMultiplicativeError_one_of_subset_loss
      (iterationExtensionVertices_subset A Q (W.U iStar)) hxi
      (hextension i hki iStar hiStar Q hQG hQsupport hQcard)

end

end Erdos207

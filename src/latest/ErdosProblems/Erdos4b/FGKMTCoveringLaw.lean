/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoveringInduction

/-! # The finite reweighted covering law with its literal selected-edge unions -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open FiniteEdgeFamily

universe u v w

variable {I : ℕ → Type u} {Ω : ℕ → Type v} {α : Type w}
  [∀ j, Fintype (I j)] [∀ j, Fintype (Ω j)] [DecidableEq α]
  (F : (j : ℕ) → FiniteEdgeFamily (I j) (Ω j) α)

def coveringInitialEdges {j m : ℕ} (hjm : j ≤ m) (s : CoverHistory I Ω m) : Finset α :=
  Finset.univ.biUnion fun k : Fin j =>
    Finset.univ.biUnion fun i : I k => coveringSelectedEdge F (k.isLt.trans_le hjm) s i

theorem coveringPrefixRemaining_eq_sdiff (V : Finset α) {j m : ℕ} (hjm : j ≤ m)
    (s : CoverHistory I Ω m) :
    coveringRemaining F V j (coverHistoryPrefix hjm s) = V \ coveringInitialEdges F hjm s := by
  ext a
  rw [coveringRemaining_mem_iff, Finset.mem_sdiff]
  simp_rw [coveringSelectedEdge_prefix F]
  constructor
  · rintro ⟨haV, hmiss⟩
    refine ⟨haV, ?_⟩
    intro ha
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hk
    exact hmiss k k.isLt i hi
  · rintro ⟨haV, hmiss⟩
    refine ⟨haV, fun k hk i hi => ?_⟩
    apply hmiss
    exact Finset.mem_biUnion.mpr ⟨⟨k, hk⟩, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩⟩

variable [∀ j, DecidableEq (I j)]
  {F} {V : Finset α} {r A m : ℕ} {κ δ D : ℝ}

namespace CoveringConditions

variable (H : CoveringConditions F V r A m κ δ D)

include H

theorem final_containment_error {j : ℕ} (hj : j ≤ m) (e : Finset α)
    (heV : e ⊆ V) (hsize : e.card + 2 * r * j ≤ A) :
    |containmentMass (coveringHistoryMass F V δ m)
      (fun s => V \ coveringInitialEdges F hj s) e -
      survivalProduct (coveringSurvival F j) e| ≤
      coveringTolerance δ (j + 1) * survivalProduct (coveringSurvival F j) e := by
  simpa only [coveringPrefixRemaining_eq_sdiff] using
    H.final_prefix_containment_error hj e heV hsize

/-- The actual finite joint law, with support and all earlier-stage estimates.
The only assumptions are the stated degree, codegree, sparsity and scale bounds. -/
theorem finite_covering_law :
    (∀ s, 0 ≤ coveringHistoryMass F V δ m s) ∧
    (∑ s : CoverHistory I Ω m, coveringHistoryMass F V δ m s) = 1 ∧
    (∀ s, 0 < coveringHistoryMass F V δ m s → ∀ (j : ℕ) (hj : j < m) (i : I j),
      coveringSelectedEdge F hj s i = ∅ ∨
        ∃ ω, 0 < (F j).mass i ω ∧ coveringSelectedEdge F hj s i = (F j).edge i ω) ∧
    (∀ (j : ℕ) (hj : j ≤ m) (e : Finset α), e ⊆ V → e.card + 2 * r * j ≤ A →
      |containmentMass (coveringHistoryMass F V δ m)
        (fun s => V \ coveringInitialEdges F hj s) e -
        survivalProduct (coveringSurvival F j) e| ≤
        coveringTolerance δ (j + 1) * survivalProduct (coveringSurvival F j) e) := by
  refine ⟨H.historyMass_nonneg le_rfl, H.historyMass_sum_one le_rfl, ?_, ?_⟩
  · intro s hs j hj i
    exact H.final_selectedEdge_support hj s hs i
  · intro j hj e heV hsize
    exact H.final_containment_error hj e heV hsize

end CoveringConditions

end

end Erdos4b.FGKMT

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeRandomMoments

/-!
# A uniform C4 form of the internal-edge B4 estimate

The scheduled greedy law gives `|Q|! D^-|Q|`.  Its support also bounds the
number of inserted triangles by the schedule horizon.  Combining the two
facts gives one exponential point factor for every prescribed family,
including families too large to occur.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Per-triangle exponential factor obtained from the horizon-uniform
factorial bound. -/
def internalEdgeC4Factor (D horizon : ℕ) : ℝ≥0 :=
  (horizon.factorial : ℝ≥0) * (D : ℝ≥0)⁻¹

theorem internalEdgeGreedyProcess_probability_subset_newChosen_le_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V → Bool) (S : Sym2 V → Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges → e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges → e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges → e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges → S e ⊆ U)
    (D : ℕ) (hD : 0 < D) (P0 : TripleSystemOn V)
    (horizon : ℕ)
    (hsupport : (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).SupportedOn
      (fun z : InternalEdgeGreedyStateOn V ↦
        (z.chosen \ P0).card ≤ horizon))
    (Q : TripleSystemOn V) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).probability
        (fun z ↦ Q ⊆ z.chosen \ P0) ≤
      internalEdgeC4Factor D horizon ^ Q.card := by
  let L := internalEdgeGreedyProcessLaw F G U omega S edges hne D P0
  by_cases hQzero : Q.card = 0
  · have hQ : Q = ∅ := card_eq_zero.mp hQzero
    subst Q
    simpa [L, internalEdgeC4Factor] using
      L.probability_le_one (fun z ↦ (∅ : TripleSystemOn V) ⊆ z.chosen \ P0)
  · have hQpos : 0 < Q.card := Nat.pos_of_ne_zero hQzero
    by_cases hQcard : Q.card ≤ horizon
    · have hraw := internalEdgeGreedyProcess_probability_subset_newChosen_le
        F G U omega S edges hne hnodup hu hv hSU D hD P0 Q horizon hQcard
      have hfac : 1 ≤ (horizon.factorial : ℝ≥0) := by
        exact_mod_cast Nat.factorial_pos horizon
      have hfacPow : (horizon.factorial : ℝ≥0) ≤
          (horizon.factorial : ℝ≥0) ^ Q.card := by
        calc
          (horizon.factorial : ℝ≥0) =
              (horizon.factorial : ℝ≥0) ^ 1 := by simp
          _ ≤ (horizon.factorial : ℝ≥0) ^ Q.card :=
            pow_le_pow_right₀ hfac hQpos
      calc
        L.probability (fun z ↦ Q ⊆ z.chosen \ P0) ≤
            (horizon.factorial : ℝ≥0) *
              setWeight (fun _ : TripleOn V ↦ (D : ℝ≥0)⁻¹) Q := hraw
        _ = (horizon.factorial : ℝ≥0) *
              ((D : ℝ≥0)⁻¹ ^ Q.card) := by simp [setWeight]
        _ ≤ (horizon.factorial : ℝ≥0) ^ Q.card *
              ((D : ℝ≥0)⁻¹ ^ Q.card) := by gcongr
        _ = internalEdgeC4Factor D horizon ^ Q.card := by
          rw [internalEdgeC4Factor, mul_pow]
    · have hzero : L.probability (fun z ↦ Q ⊆ z.chosen \ P0) = 0 := by
        apply le_antisymm
        · calc
            L.probability (fun z ↦ Q ⊆ z.chosen \ P0) ≤
                L.probability (fun _z ↦ False) := by
              apply L.probability_mono_of_supported hsupport
              intro z hz hQsub
              exact hQcard ((card_le_card hQsub).trans hz)
            _ = 0 := L.probability_false
        · exact zero_le
      rw [hzero]
      exact zero_le

end

end Erdos207

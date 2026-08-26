import ErdosProblems.Erdos547.RegularityTypical

/-!
# Cross-degree bounds after deleting the non-typical vertices
-/

noncomputable section

namespace Erdos547

open Finset SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

open scoped Classical in
def nonTypicalVertices (ε : ℝ) (X Y B : Finset V) : Finset V :=
  X.filter (fun u ↦ (degreeIn G B u : ℝ) < ((G.edgeDensity X Y : ℝ) - ε) * B.card)

theorem degreeIn_of_not_nonTypical {ε : ℝ} {X Y B : Finset V} {u : V}
    (hu : u ∈ X) (hgood : u ∉ nonTypicalVertices G ε X Y B) :
    ((G.edgeDensity X Y : ℝ) - ε) * B.card ≤ (degreeIn G B u : ℝ) := by
  classical
  exact le_of_not_gt fun hh ↦ hgood (Finset.mem_filter.mpr ⟨hu, hh⟩)

open scoped Classical in
theorem exists_regular_pair_core {ε : ℝ} {X Y A B : Finset V}
    (hreg : G.IsUniform ε X Y) (hA : A ⊆ X) (hB : B ⊆ Y)
    (hAsize : (X.card : ℝ) * ε ≤ A.card) (hBsize : (Y.card : ℝ) * ε ≤ B.card) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧
      ((A \ A').card : ℝ) ≤ (X.card : ℝ) * ε ∧
      ((B \ B').card : ℝ) ≤ (Y.card : ℝ) * ε ∧
      (∀ u ∈ A', ((G.edgeDensity X Y : ℝ) - ε) * B.card - (Y.card : ℝ) * ε ≤
        (degreeIn G B' u : ℝ)) ∧
      (∀ u ∈ B', ((G.edgeDensity X Y : ℝ) - ε) * A.card - (X.card : ℝ) * ε ≤
        (degreeIn G A' u : ℝ)) := by
  classical
  let badX := nonTypicalVertices G ε X Y B
  let badY := nonTypicalVertices G ε Y X A
  let A' := A \ badX
  let B' := B \ badY
  have hbadX : (badX.card : ℝ) ≤ (X.card : ℝ) * ε := card_nonTypical_le G hreg hB hBsize
  have hbadY : (badY.card : ℝ) ≤ (Y.card : ℝ) * ε := card_nonTypical_le G hreg.symm hA hAsize
  have hXA : A \ A' ⊆ badX := by
    intro u hu
    by_contra hn
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hu).1, hn⟩)
  have hYB : B \ B' ⊆ badY := by
    intro u hu
    by_contra hn
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hu).1, hn⟩)
  have hloseA : ((A \ A').card : ℝ) ≤ (X.card : ℝ) * ε :=
    (Nat.cast_le.mpr (Finset.card_le_card hXA)).trans hbadX
  have hloseB : ((B \ B').card : ℝ) ≤ (Y.card : ℝ) * ε :=
    (Nat.cast_le.mpr (Finset.card_le_card hYB)).trans hbadY
  refine ⟨A', B', Finset.sdiff_subset, Finset.sdiff_subset, hloseA, hloseB, ?_, ?_⟩
  · intro u hu
    have hh := degreeIn_of_not_nonTypical G (hA (Finset.mem_sdiff.mp hu).1)
      (Finset.mem_sdiff.mp hu).2
    have hdeg : (degreeIn G B u : ℝ) ≤ degreeIn G B' u + ((B \ B').card : ℝ) := by
      exact_mod_cast degreeIn_le_add_removed G B B' u
    linarith
  · intro u hu
    have hh := degreeIn_of_not_nonTypical G (hB (Finset.mem_sdiff.mp hu).1)
      (Finset.mem_sdiff.mp hu).2
    rw [SimpleGraph.edgeDensity_comm G Y X] at hh
    have hdeg : (degreeIn G A u : ℝ) ≤ degreeIn G A' u + ((A \ A').card : ℝ) := by
      exact_mod_cast degreeIn_le_add_removed G A A' u
    linarith

end Erdos547

#print axioms Erdos547.exists_regular_pair_core

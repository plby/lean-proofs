import ErdosProblems.Erdos547.RegularityPruning

/-!
# A regular-pair core retaining a prescribed neighbourhood on one side
-/

namespace Erdos547

open Finset SimpleGraph

variable {V : Type*}

open scoped Classical in
theorem card_lost_after_sdiff_le (S Z : Finset V) (D : ℝ) (hZ : (Z.card : ℝ) ≤ D) :
    ((S \ (S \ Z)).card : ℝ) ≤ D := by
  classical
  apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans hZ
  intro u hu
  by_contra hn
  exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hu).1, hn⟩)

open scoped Classical in
theorem exists_regular_shrub_core (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} {X Y A B N : Finset V}
    (hreg : G.IsUniform ε X Y) (hA : A ⊆ X) (hB : B ⊆ Y) (hNB : N ⊆ B)
    (hAsize : (X.card : ℝ) * ε ≤ A.card) (hNsize : (Y.card : ℝ) * ε ≤ N.card) :
    ∃ A' B' C : Finset V, A' ⊆ A ∧ B' ⊆ B ∧ C ⊆ B' ∧ C ⊆ N ∧
      ((B \ B').card : ℝ) ≤ (Y.card : ℝ) * ε ∧
      (N.card : ℝ) - (Y.card : ℝ) * ε ≤ C.card ∧
      (∀ u ∈ A', ((G.edgeDensity X Y : ℝ) - ε) * N.card - (Y.card : ℝ) * ε ≤
        (degreeIn G C u : ℝ)) ∧
      (∀ u ∈ B', ((G.edgeDensity X Y : ℝ) - ε) * A.card - (X.card : ℝ) * ε ≤
        (degreeIn G A' u : ℝ)) := by
  classical
  let badX := nonTypicalVertices G ε X Y N
  let badY := nonTypicalVertices G ε Y X A
  let A' := A \ badX
  let B' := B \ badY
  let C := N \ badY
  have hbadX : (badX.card : ℝ) ≤ (X.card : ℝ) * ε :=
    card_nonTypical_le G hreg (hNB.trans hB) hNsize
  have hbadY : (badY.card : ℝ) ≤ (Y.card : ℝ) * ε :=
    card_nonTypical_le G hreg.symm hA hAsize
  have hlossA : ((A \ A').card : ℝ) ≤ (X.card : ℝ) * ε :=
    card_lost_after_sdiff_le A badX _ hbadX
  have hlossB : ((B \ B').card : ℝ) ≤ (Y.card : ℝ) * ε :=
    card_lost_after_sdiff_le B badY _ hbadY
  have hlossN : ((N \ C).card : ℝ) ≤ (Y.card : ℝ) * ε :=
    card_lost_after_sdiff_le N badY _ hbadY
  have hCN : C ⊆ N := Finset.sdiff_subset
  have hCB : C ⊆ B' := Finset.sdiff_subset_sdiff hNB (fun _ h ↦ h)
  refine ⟨A', B', C, Finset.sdiff_subset, Finset.sdiff_subset, hCB, hCN, hlossB, ?_, ?_, ?_⟩
  · have hh : ((N \ C).card : ℝ) + C.card = N.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hCN
    linarith
  · intro u hu
    have hh := degreeIn_of_not_nonTypical G (hA (Finset.mem_sdiff.mp hu).1)
      (Finset.mem_sdiff.mp hu).2
    have hdeg : (degreeIn G N u : ℝ) ≤ degreeIn G C u + ((N \ C).card : ℝ) := by
      exact_mod_cast degreeIn_le_add_removed G N C u
    linarith
  · intro u hu
    have hh := degreeIn_of_not_nonTypical G (hB (Finset.mem_sdiff.mp hu).1)
      (Finset.mem_sdiff.mp hu).2
    rw [SimpleGraph.edgeDensity_comm G Y X] at hh
    have hdeg : (degreeIn G A u : ℝ) ≤ degreeIn G A' u + ((A \ A').card : ℝ) := by
      exact_mod_cast degreeIn_le_add_removed G A A' u
    linarith

end Erdos547

#print axioms Erdos547.exists_regular_shrub_core

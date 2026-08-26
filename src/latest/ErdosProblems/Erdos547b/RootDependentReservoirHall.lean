/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Proposition57
import Mathlib.Combinatorics.Hall.Basic

/-!
# Hall selection from root-dependent reservoirs

The Claim-6.16 reconstruction assigns different original roots to the exact
`A₀` and `B₀` reservoirs according to source parity.  Consequently these
reservoirs must not be replaced by one common root cluster.  This file
records the elementary Hall argument needed after a bounded bad set has
been removed from each root's own reservoir.

The result constructs the injective root map itself.  It has no embedding,
copy, continuation, or conclusion-valued premise.
-/

noncomputable section

namespace Erdos547b.ZhaoRootDependentReservoirHall

open Finset Fintype

universe v

/-- If every root-dependent reservoir still has room for all roots after
its own bounded exclusion, Hall's condition follows from any one choice set
belonging to a nonempty family of roots. -/
theorem exists_injective_mem_sdiff
    {r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (reservoir bad : Fin r → Finset B) (loss : ℕ)
    (hbad : ∀ i, #(reservoir i ∩ bad i) ≤ loss)
    (hcard : ∀ i, r + loss ≤ #(reservoir i)) :
    ∃ rootImage : Fin r → B,
      Function.Injective rootImage ∧
      ∀ i, rootImage i ∈ reservoir i \ bad i := by
  classical
  let choices : Fin r → Finset B := fun i ↦ reservoir i \ bad i
  have hchoices (i : Fin r) : r ≤ #(choices i) := by
    have hpartition := Finset.card_sdiff_add_card_inter (reservoir i) (bad i)
    change #(reservoir i \ bad i) + #(reservoir i ∩ bad i) =
      #(reservoir i) at hpartition
    dsimp only [choices]
    have hbad' := hbad i
    have hcard' := hcard i
    omega
  have hHall : ∀ S : Finset (Fin r), #S ≤ #(S.biUnion choices) := by
    intro S
    by_cases hS : S = ∅
    · simp [hS]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      calc
        #S ≤ Fintype.card (Fin r) := Finset.card_le_univ S
        _ = r := Fintype.card_fin r
        _ ≤ #(choices i) := hchoices i
        _ ≤ #(S.biUnion choices) :=
          Finset.card_le_card (Finset.subset_biUnion_of_mem choices hi)
  obtain ⟨rootImage, hrootInjective, hrootMem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective choices).mp hHall
  exact ⟨rootImage, hrootInjective, hrootMem⟩

/-- Split membership form used by parity-aware host specializations. -/
theorem exists_injective_mem_avoid
    {r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (reservoir bad : Fin r → Finset B) (loss : ℕ)
    (hbad : ∀ i, #(reservoir i ∩ bad i) ≤ loss)
    (hcard : ∀ i, r + loss ≤ #(reservoir i)) :
    ∃ rootImage : Fin r → B,
      Function.Injective rootImage ∧
      (∀ i, rootImage i ∈ reservoir i) ∧
      ∀ i, rootImage i ∉ bad i := by
  obtain ⟨rootImage, hinjective, hmem⟩ :=
    exists_injective_mem_sdiff reservoir bad loss hbad hcard
  exact ⟨rootImage, hinjective,
    fun i ↦ (Finset.mem_sdiff.mp (hmem i)).1,
    fun i ↦ (Finset.mem_sdiff.mp (hmem i)).2⟩

/-- Convenience form for the usual regularity output, where every bad set
is already known to lie inside its root's reservoir. -/
theorem exists_injective_mem_avoid_of_bad_subset
    {r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (reservoir bad : Fin r → Finset B) (loss : ℕ)
    (hbadSubset : ∀ i, bad i ⊆ reservoir i)
    (hbadCard : ∀ i, #(bad i) ≤ loss)
    (hcard : ∀ i, r + loss ≤ #(reservoir i)) :
    ∃ rootImage : Fin r → B,
      Function.Injective rootImage ∧
      (∀ i, rootImage i ∈ reservoir i) ∧
      ∀ i, rootImage i ∉ bad i := by
  apply exists_injective_mem_avoid reservoir bad loss
  · intro i
    rw [Finset.inter_eq_right.mpr (hbadSubset i)]
    exact hbadCard i
  · exact hcard

#print axioms exists_injective_mem_sdiff
#print axioms exists_injective_mem_avoid
#print axioms exists_injective_mem_avoid_of_bad_subset

end Erdos547b.ZhaoRootDependentReservoirHall

import ErdosProblems.Erdos547.DegreeExtraction
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform

/-!
# Typical vertices of a regular pair
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

theorem card_interedges_eq_sum_degreeIn (S B : Finset V) :
    (G.interedges S B).card = ∑ u ∈ S, degreeIn G B u := by
  simp only [SimpleGraph.interedges_def, degreeIn, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

theorem edgeDensity_eq_sum_degreeIn_div (S B : Finset V) :
    (G.edgeDensity S B : ℝ) =
      (∑ u ∈ S, (degreeIn G B u : ℝ)) / ((S.card : ℝ) * B.card) := by
  rw [SimpleGraph.edgeDensity_def, card_interedges_eq_sum_degreeIn]
  push_cast
  rfl

open scoped Classical in
theorem card_nonTypical_le {S T B : Finset V} {ε : ℝ}
    (hreg : G.IsUniform ε S T) (hB : B ⊆ T) (hsize : (T.card : ℝ) * ε ≤ B.card) :
    ((S.filter (fun u ↦ (degreeIn G B u : ℝ) <
      ((G.edgeDensity S T : ℝ) - ε) * B.card)).card : ℝ) ≤ (S.card : ℝ) * ε := by
  classical
  let bad := S.filter (fun u ↦ (degreeIn G B u : ℝ) <
    ((G.edgeDensity S T : ℝ) - ε) * B.card)
  change (bad.card : ℝ) ≤ (S.card : ℝ) * ε
  by_contra hn
  have hbad : (S.card : ℝ) * ε < (bad.card : ℝ) := lt_of_not_ge hn
  have hbpos : 0 < bad.card := by
    exact_mod_cast (mul_nonneg (Nat.cast_nonneg S.card) hreg.pos.le).trans_lt hbad
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hbpos
  have hBne : B.Nonempty := by
    by_contra hne
    have hz : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hh := (Finset.mem_filter.mp hu).2
    simp only [hz, degreeIn, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      mul_zero, lt_self_iff_false] at hh
  have hden : 0 < (bad.card : ℝ) * B.card :=
    mul_pos (by exact_mod_cast hbpos) (by exact_mod_cast hBne.card_pos)
  have hs : (∑ z ∈ bad, (degreeIn G B z : ℝ)) <
      ∑ _z ∈ bad, (((G.edgeDensity S T : ℝ) - ε) * B.card) :=
    Finset.sum_lt_sum (fun z hz ↦ (Finset.mem_filter.mp hz).2.le)
      ⟨u, hu, (Finset.mem_filter.mp hu).2⟩
  have hdensity : (G.edgeDensity bad B : ℝ) < (G.edgeDensity S T : ℝ) - ε := by
    rw [edgeDensity_eq_sum_degreeIn_div]
    apply (div_lt_iff₀ hden).mpr
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    nlinarith only [hs]
  have hregular := hreg (Finset.filter_subset _ _) hB hbad.le hsize
  have hh := (abs_lt.mp hregular).1
  linarith

theorem exists_typical_in_large_subset {S T B P : Finset V} {ε : ℝ}
    (hreg : G.IsUniform ε S T) (hB : B ⊆ T) (hsize : (T.card : ℝ) * ε ≤ B.card)
    (hP : P ⊆ S) (hPsize : (S.card : ℝ) * ε < P.card) :
    ∃ u ∈ P, ((G.edgeDensity S T : ℝ) - ε) * B.card ≤ (degreeIn G B u : ℝ) := by
  classical
  by_contra hn
  have hsub : P ⊆ S.filter (fun u ↦ (degreeIn G B u : ℝ) <
      ((G.edgeDensity S T : ℝ) - ε) * B.card) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨hP hu, lt_of_not_ge (fun h ↦ hn ⟨u, hu, h⟩)⟩
  have hh := (Nat.cast_le.mpr (Finset.card_le_card hsub) : (P.card : ℝ) ≤ _).trans
    (card_nonTypical_le G hreg hB hsize)
  exact (not_le_of_gt hPsize) hh

end Erdos547

#print axioms Erdos547.card_nonTypical_le
#print axioms Erdos547.exists_typical_in_large_subset

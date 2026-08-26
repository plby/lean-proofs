import ErdosProblems.Erdos547.NearCoreMany
import ErdosProblems.Erdos547.NumericalParameters

/-!
# A uniform sufficiently-large theorem for trees with many nonleaves
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

open scoped Classical in
/-- For every sufficiently large `m`, a near-core forces a monochromatic
copy of every tree whose nonleaf subtree has at least `m/(4*10^16)` vertices.
All escape and numerical hypotheses have been proved internally. -/
theorem eventually_ramsey_of_near_core_many_nonleaves :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (T : SimpleGraph (Fin (m + 1)))
      (R : SimpleGraph (Fin (2 * m))) (S : Finset (Fin (2 * m))),
      T.IsTree → S.Nonempty →
      (∀ v ∈ S, (1 - 1 / coreDeficitDivisor : ℝ) * m ≤ degreeIn R S v) →
      m / (4 * corePairDivisor) ≤ Fintype.card (treeCore T) →
      T ⊑ R ∨ T ⊑ Rᶜ := by
  classical
  obtain ⟨m₁, hm₁⟩ := eventually_pair_decay_threshold
    (1 / (2 * corePairDivisor : ℝ)) (1 / (32 * corePairDivisor : ℝ))
    (2 / coreDeficitDivisor : ℝ)
    (by norm_num [corePairDivisor]) core_decay_exponent_gap
  refine ⟨max coreDeficitDivisor m₁, ?_⟩
  intro m hm T R S hT hS hdegree hcore
  have hmD : coreDeficitDivisor ≤ m := (le_max_left _ _).trans hm
  have hm₁' : m₁ ≤ m := (le_max_right _ _).trans hm
  let d := m / coreDeficitDivisor + 1
  let k := m / corePairDivisor
  let t := m / coreCleaningDivisor
  let r := k / 8
  obtain ⟨hk, hr, hroom, hbudget, hsmall, hrd, hkd, hrcore⟩ := near_core_integer_bounds m hmD
  obtain ⟨hkr, hrr, hdr⟩ := near_core_real_bounds m hmD
  let : Fintype (S : Set (Fin (2 * m))) := FinsetCoe.fintype S
  let : Nonempty (S : Set (Fin (2 * m))) := (Finset.coe_nonempty.mpr hS).to_subtype
  have hNpos : 0 < Fintype.card (S : Set (Fin (2 * m))) := Fintype.card_pos
  have hNupper : Fintype.card (S : Set (Fin (2 * m))) ≤ 2 * m := by
    have hcard : Fintype.card (S : Set (Fin (2 * m))) = S.card := by
      apply Fintype.card_of_subtype
      intro v
      rfl
    rw [hcard]
    simpa using Finset.card_le_univ S
  have hlocal : ∀ z : (S : Set (Fin (2 * m))), m ≤ (R.induce (S : Set _)).degree z + d := by
    intro z
    apply deficit_rounding m
    rw [← degreeIn_eq_induce_degree R S z]
    exact hdegree z.val z.property
  have hmin : 2 * r ≤ (R.induce (S : Set _)).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro z
    have hz := hlocal z
    change 2 * r + d ≤ m at hrd
    omega
  have hkN : k ≤ Fintype.card (S : Set (Fin (2 * m))) := by
    have hcard : Fintype.card (S : Set (Fin (2 * m))) = S.card := by
      apply Fintype.card_of_subtype
      intro v
      rfl
    rw [hcard]
    obtain ⟨z, hz⟩ := hS
    have hdeg := deficit_rounding m (degreeIn R S z) (hdegree z hz)
    have hbound := degreeIn_le_card R S z
    change k + d ≤ m at hkd
    change m ≤ degreeIn R S z + d at hdeg
    omega
  have hthreshold : pairDecay (Fintype.card (S : Set (Fin (2 * m)))) k ^ (r - 1) *
      Fintype.card (S : Set (Fin (2 * m))) < (1 / 2 : ℝ) ^ d := by
    exact hm₁ m hm₁' _ k (r - 1) d hNpos hNupper hkN hkr hrr hdr
  refine ramsey_of_near_core_many_nonleaves T hT R (S : Set _) d k t r hk hr hroom
    hbudget ?_ ?_ ?_ ?_ ?_ ?_
  · exact hlocal
  · exact hrcore.trans hcore
  · exact hkN
  · exact hsmall
  · exact hmin
  · exact hthreshold

end Erdos547

#print axioms Erdos547.eventually_ramsey_of_near_core_many_nonleaves

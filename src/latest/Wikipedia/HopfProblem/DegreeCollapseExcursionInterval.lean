import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Isolating an excursion away from a closed perturbation region

A continuous curve returning to an inner set has a last departure and first
return around any point outside that set. The intervening open interval
avoids a prescribed closed subset of the inner set. No transversality of its
boundary and no smooth stopping-time assumption is used.
-/

open Set

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X]

/-- Cut out the maximal excursion around an outside point of a curve segment. -/
theorem exists_excursion_interval {γ : ℝ → X} (hγ : Continuous γ)
    {K N : Set X} (hK : IsClosed K) (hKN : K ⊆ N)
    {a b t : ℝ} (ht : t ∈ Icc a b) (ha : γ a ∈ N) (hb : γ b ∈ N)
    (hout : γ t ∉ N) :
    ∃ s u : ℝ, a ≤ s ∧ s < t ∧ t < u ∧ u ≤ b ∧
      γ s ∈ N ∧ γ u ∈ N ∧ ∀ r ∈ Ioo s u, γ r ∉ K := by
  let A := insert a (Icc a t ∩ γ ⁻¹' K)
  let B := insert b (Icc t b ∩ γ ⁻¹' K)
  have hA : IsCompact A := (isCompact_Icc.inter_right (hK.preimage hγ)).insert a
  have hB : IsCompact B := (isCompact_Icc.inter_right (hK.preimage hγ)).insert b
  obtain ⟨s, hs⟩ := hA.exists_isGreatest (insert_nonempty _ _)
  obtain ⟨u, hu⟩ := hB.exists_isLeast (insert_nonempty _ _)
  have has : a ≤ s := hs.2 (mem_insert _ _)
  have hub : u ≤ b := hu.2 (mem_insert _ _)
  have hst : s ≤ t := by
    rcases hs.1 with he | hh
    · exact he ▸ ht.1
    · exact hh.1.2
  have htu : t ≤ u := by
    rcases hu.1 with he | hh
    · exact he ▸ ht.2
    · exact hh.1.1
  have hsN : γ s ∈ N := by
    rcases hs.1 with he | hh
    · exact he ▸ ha
    · exact hKN hh.2
  have huN : γ u ∈ N := by
    rcases hu.1 with he | hh
    · exact he ▸ hb
    · exact hKN hh.2
  have hst' : s < t := lt_of_le_of_ne hst (fun he => hout (he ▸ hsN))
  have htu' : t < u := lt_of_le_of_ne htu (fun he => hout (he ▸ huN))
  refine ⟨s, u, has, hst', htu', hub, hsN, huN, ?_⟩
  intro r hr hrK
  by_cases hrt : r ≤ t
  · have hrA : r ∈ A := Or.inr ⟨⟨le_trans has hr.1.le, hrt⟩, hrK⟩
    exact (not_le_of_gt hr.1) (hs.2 hrA)
  · have hrB : r ∈ B := Or.inr ⟨⟨(lt_of_not_ge hrt).le, le_trans hr.2.le hub⟩, hrK⟩
    exact (not_le_of_gt hr.2) (hu.2 hrB)

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

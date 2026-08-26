import ErdosProblems.Erdos1148.PartitionEntropyCollision
import ErdosProblems.Erdos1148.UnconditionalBowenPairBound

/-! # Entropy of finite disjoint families of packet Bowen cells -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Function

theorem exists_unconditional_packet_bowen_family_entropy_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)),
      IntegralDiscrForm d → ∀ (r δ : ℝ), 0 ≤ r → r ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 6 →
      ∀ (ι : Type) [Fintype ι] (s : ι → Set ModularOrbitSpace),
        (∀ i, MeasurableSet (s i)) → Pairwise (Disjoint on s) →
        (∀ i, s i ×ˢ s i ⊆ modularBowenPairs r δ) →
        ∀ m : ℝ, 0 < m → (∑ i, (normalizedDiscriminantPacket hd hns).real (s i)) = m →
          -m * Real.log ((K * ((d : ℝ) ^ (-1 / 2 + ε) + (d : ℝ) ^ ε * δ ^ 2)) / m) ≤
            finitePartitionEntropy (normalizedDiscriminantPacket hd hns) s := by
  obtain ⟨K, hK, hbound⟩ := exists_unconditional_normalizedPacket_bowenPairs_bound hε
  refine ⟨K, hK, ?_⟩
  intro d hd hns base r δ hr hrhalf hδ hδsixth ι _ s hs hdisj hpair m hm hsum
  let : IsProbabilityMeasure (normalizedDiscriminantPacket hd hns) :=
    normalizedDiscriminantPacket_isProbability hd hns base
  exact neg_mass_log_pair_bound_div_mass_le_partitionEntropy _ s hs hdisj hm hsum hpair
    (hbound d hd hns base r δ hr hrhalf hδ hδsixth)

end Erdos1148.DukeArithmetic

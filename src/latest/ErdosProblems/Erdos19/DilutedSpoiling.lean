import ErdosProblems.Erdos19.DilutedDeletion

/-! # Every spoiled color has a diluted deletion certificate -/

namespace Erdos19

attribute [local instance] Classical.propDecidable

theorem mem_diluted_tentativeFiber {V : Type*} (G : _root_.SimpleGraph V) {A C : ℕ}
    (active : Fin A) (sample : V → Fin A × Fin C) (v w : V) (a : Fin C) :
    w ∈ tentativeNeighborColorFiber G (dilutedSample active sample) v a ↔
      G.Adj v w ∧ sample w = (active, a) := by
  simp only [tentativeNeighborColorFiber, Set.mem_setOf_eq, dilutedSample_active_iff,
    dilutedSample_color]
  constructor
  · rintro ⟨hfirst, hadj, hsecond⟩
    exact ⟨hadj, Prod.ext hfirst hsecond⟩
  · rintro ⟨hadj, heq⟩
    exact ⟨congrArg Prod.fst heq, hadj, congrArg Prod.snd heq⟩

theorem exists_diluted_conflict_of_not_retained {V : Type*}
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A)
    (sample : V → Fin A × Fin C) (w : V) (a : Fin C)
    (hw : sample w = (active, a))
    (hnot : w ∉ randomRetainedSet G (dilutedSample active sample)) :
    ∃ z, G.Adj w z ∧ sample z = (active, a) := by
  classical
  by_contra hex
  push_neg at hex
  apply hnot
  refine ⟨by simp [dilutedSample, hw], ?_⟩
  intro z hwz hzactive hcolor
  have hfirst : (sample z).1 = active := (dilutedSample_active_iff active sample z).mp hzactive
  have hsecond : (sample z).2 = a := by
    simpa only [dilutedSample_color, hw] using hcolor
  exact hex z hwz (Prod.ext hfirst hsecond)

theorem spoiledCollisionColors_subset_dilutedDeleted {V : Type*}
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A)
    (sample : V → Fin A × Fin C) (v : V) :
    spoiledCollisionColors G (dilutedSample active sample) v ⊆
      dilutedDeletedCollisionColors G active sample v := by
  intro a ha
  obtain ⟨p, q, hpq, hnonadj, hp, hq⟩ := ha.1
  rw [mem_diluted_tentativeFiber] at hp hq
  have hnotret := ha.2
  by_cases hpRet : p ∈ randomRetainedSet G (dilutedSample active sample)
  · have hqNot : q ∉ randomRetainedSet G (dilutedSample active sample) := by
      intro hqRet
      exact hnotret ⟨p, q, hpq,
        ⟨hpRet, hp.1, congrArg Prod.snd hp.2⟩,
        ⟨hqRet, hq.1, congrArg Prod.snd hq.2⟩⟩
    obtain ⟨z, hqz, hz⟩ := exists_diluted_conflict_of_not_retained G active sample q a hq.2 hqNot
    exact ⟨q, p, z, hpq.symm, (fun h ↦ hnonadj h.symm), hq.1, hp.1,
      hq.2, hp.2, hqz, hz⟩
  · obtain ⟨z, hpz, hz⟩ := exists_diluted_conflict_of_not_retained G active sample p a hp.2 hpRet
    exact ⟨p, q, z, hpq, hnonadj, hp.1, hq.1, hp.2, hq.2, hpz, hz⟩

theorem card_dilutedSpoiledExcess_le_of_degree {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C Δ : ℕ} (active : Fin A) (v : V) (b : ℕ)
    (hdegree : ∀ x, (G.neighborSet x).ncard ≤ Δ) :
    (eventFinset {sample : V → Fin A × Fin C |
      b < (spoiledCollisionColors G (dilutedSample active sample) v).ncard}).card ≤
      (C.choose (b + 1) *
        (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ) ^ (b + 1)) *
        (A * C) ^ (Fintype.card V - 3 * (b + 1)) := by
  classical
  have hsub : eventFinset {sample : V → Fin A × Fin C |
      b < (spoiledCollisionColors G (dilutedSample active sample) v).ncard} ⊆
      eventFinset {sample : V → Fin A × Fin C |
        b + 1 ≤ (dilutedDeletedCollisionColors G active sample v).ncard} := by
    intro sample hs
    rw [mem_eventFinset] at hs ⊢
    exact hs.trans_le (Set.ncard_le_ncard (spoiledCollisionColors_subset_dilutedDeleted G active sample v))
  have htail := (Finset.card_le_card hsub).trans (card_dilutedDeletionHighEvent_le G active v (b + 1))
  have hw := mrDeletionWitnessTriples_card_le G v hdegree
  exact htail.trans (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw (b + 1))))

#print axioms card_dilutedSpoiledExcess_le_of_degree

end Erdos19

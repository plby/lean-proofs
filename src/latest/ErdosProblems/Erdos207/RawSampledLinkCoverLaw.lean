/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SampledLinkGoodCover
import ErdosProblems.Erdos207.LinkReserveAccounting

/-! # Totalized sampled-link covers retain the unconditioned point scale

Bad bit outcomes output the empty family.  All structural properties hold
on every outcome; only coverage needs the good event.  Thus conditioning
can be postponed until the complete master-step success event.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def IsSafeLinkSubfamily
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (available P M : TripleSystemOn V) : Prop :=
  M ⊆ available ∧ Disjoint P M ∧ IsPackingOn (P ∪ M) ∧ AvoidsForbidden (P ∪ M) F

theorem exists_rawSampledLinkSelector
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available I D : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (Delta collisionCap forbiddenCap : ℕ)
    (hpacking : IsPackingOn (I ∪ D)) (havoid : AvoidsForbidden (I ∪ D) F)
    (havailable : ∀ o a b, r o a b → simultaneousLinkPairTriple K ⟨o,(a,b)⟩ ∈ available)
    (hsafe : ∀ o a b, r o a b → TriangleAvoidsGraph (coveredGraph (I ∪ D))
      (simultaneousLinkPairTriple K ⟨o,(a,b)⟩))
    (hcap : collisionCap + forbiddenCap ≤ Delta) :
    ∃ selected : (SimultaneousLinkPair O V K → Bool) → TripleSystemOn V,
      ∀ omega, selected omega ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright
          (candidateFilteredLinkBits K r omega) ∧
        IsSafeLinkSubfamily F available (I ∪ D) (selected omega) ∧
        (IsSampledCandidateLinkGood U center K hcenter hout hleft hright F I D r Delta collisionCap forbiddenCap omega →
          ∀ o, CoversBipartiteLink (K o) (selected omega)) := by
  have hchoose : ∀ omega : SimultaneousLinkPair O V K → Bool, ∃ M : TripleSystemOn V,
      M ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega) ∧
        IsSafeLinkSubfamily F available (I ∪ D) M ∧
        (IsSampledCandidateLinkGood U center K hcenter hout hleft hright F I D r Delta collisionCap forbiddenCap omega →
          ∀ o, CoversBipartiteLink (K o) M) := by
    intro omega
    by_cases hg : IsSampledCandidateLinkGood U center K hcenter hout hleft hright F I D r Delta collisionCap forbiddenCap omega
    · obtain ⟨M, hM, hm⟩ := exists_simultaneousLinkCover_of_sampled_counts U center K hcenter hout hleft hright
        F available I D r Delta collisionCap forbiddenCap omega hg.1 hpacking havoid havailable hsafe
        hg.2.1 hg.2.2 hcap
      exact ⟨M, hM, ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1⟩, fun _ ↦ hm.2.2.2.2⟩
    · refine ⟨∅, empty_subset _, ?_, fun h ↦ (hg h).elim⟩
      exact ⟨empty_subset _, disjoint_empty_right _, by simpa using hpacking, by simpa using havoid⟩
  choose selected hselected using hchoose
  exact ⟨selected, hselected⟩

theorem exists_rawSampledLinkCoverLaw
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available I D : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (Delta collisionCap forbiddenCap : ℕ) (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (hpacking : IsPackingOn (I ∪ D)) (havoid : AvoidsForbidden (I ∪ D) F)
    (havailable : ∀ o a b, r o a b → simultaneousLinkPairTriple K ⟨o,(a,b)⟩ ∈ available)
    (hsafe : ∀ o a b, r o a b → TriangleAvoidsGraph (coveredGraph (I ∪ D))
      (simultaneousLinkPairTriple K ⟨o,(a,b)⟩))
    (hcap : collisionCap + forbiddenCap ≤ Delta) :
    ∃ law : FiniteLaw (TripleSystemOn V),
      law.SupportedOn (IsSafeLinkSubfamily F available (I ∪ D)) ∧
      (∀ Q : TripleSystemOn V, law.probability (fun M ↦ Q ⊆ M) ≤ sigma ^ Q.card) ∧
      law.probability (fun M ↦ ¬ ∀ o, CoversBipartiteLink (K o) M) ≤
        (FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
          (fun omega ↦ ¬ IsSampledCandidateLinkGood U center K hcenter hout hleft hright F I D r Delta collisionCap forbiddenCap omega) := by
  obtain ⟨selected, hselected⟩ := exists_rawSampledLinkSelector U center K hcenter hout hleft hright
    F available I D r Delta collisionCap forbiddenCap hpacking havoid havailable hsafe hcap
  let L := FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  refine ⟨L.map selected, ?_, ?_, ?_⟩
  · have htrivial : L.SupportedOn (fun _ ↦ True) := fun _ _ ↦ trivial
    exact htrivial.map selected (fun omega _ ↦ (hselected omega).2.1)
  · intro Q
    rw [FiniteLaw.probability_map]
    apply le_trans _ (simultaneousLinkReservoir_candidateFiltered_probability_subset_le
      U center K hcenter hout hleft hright r sigma hsigma Q)
    exact L.probability_mono (fun omega hQ ↦ hQ.trans (hselected omega).1)
  · rw [FiniteLaw.probability_map]
    exact L.probability_mono (fun omega hnot hg ↦ hnot ((hselected omega).2.2 hg))

theorem exists_rawSampledLinkCoverFamilyLaw
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available I D : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (Delta collisionCap forbiddenCap : ℕ) (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (hpacking : IsPackingOn (I ∪ D)) (havoid : AvoidsForbidden (I ∪ D) F)
    (havailable : ∀ o a b, r o a b → simultaneousLinkPairTriple K ⟨o,(a,b)⟩ ∈ available)
    (hsafe : ∀ o a b, r o a b → TriangleAvoidsGraph (coveredGraph (I ∪ D))
      (simultaneousLinkPairTriple K ⟨o,(a,b)⟩))
    (hcap : collisionCap + forbiddenCap ≤ Delta) :
    ∃ law : FiniteLaw (TripleSystemOn V),
      law.SupportedOn (fun M ↦ IsSafeLinkSubfamily F available (I ∪ D) M ∧ IsSimultaneousLinkFamily K M) ∧
      (∀ Q : TripleSystemOn V, law.probability (fun M ↦ Q ⊆ M) ≤ sigma ^ Q.card) ∧
      law.probability (fun M ↦ ¬ ∀ o, CoversBipartiteLink (K o) M) ≤
        (FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
          (fun omega ↦ ¬ IsSampledCandidateLinkGood U center K hcenter hout hleft hright F I D r Delta collisionCap forbiddenCap omega) := by
  obtain ⟨selected, hselected⟩ := exists_rawSampledLinkSelector U center K hcenter hout hleft hright
    F available I D r Delta collisionCap forbiddenCap hpacking havoid havailable hsafe hcap
  let L := FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  refine ⟨L.map selected, ?_, ?_, ?_⟩
  · have htrivial : L.SupportedOn (fun _ ↦ True) := fun _ _ ↦ trivial
    refine htrivial.map (Q := fun M ↦ IsSafeLinkSubfamily F available (I ∪ D) M ∧
      IsSimultaneousLinkFamily K M) selected ?_
    intro omega _
    exact ⟨(hselected omega).2.1,
      (simultaneousLinkReservoir_isSimultaneousLinkFamily U center K hcenter hout hleft hright
        (candidateFilteredLinkBits K r omega)).mono (hselected omega).1⟩
  · intro Q
    rw [FiniteLaw.probability_map]
    apply le_trans _ (simultaneousLinkReservoir_candidateFiltered_probability_subset_le
      U center K hcenter hout hleft hright r sigma hsigma Q)
    exact L.probability_mono (fun omega hQ ↦ hQ.trans (hselected omega).1)
  · rw [FiniteLaw.probability_map]
    exact L.probability_mono (fun omega hnot hg ↦ hnot ((hselected omega).2.2 hg))


end

end Erdos207

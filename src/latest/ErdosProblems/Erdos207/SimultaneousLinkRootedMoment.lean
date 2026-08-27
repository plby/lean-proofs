/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousRobustLinkCover
import ErdosProblems.Erdos207.RelativeRootedThreatMoment
import ErdosProblems.Erdos207.RootedThreatExtraction

/-!
# A global rooted-threat cutoff for all simultaneous link reservoirs

Because every center is encoded in one injective Bernoulli reservoir, the
relative rooted-threat moment argument can be applied directly to that
global family.  A union bound over all ordered distinct vertex pairs then
controls every endpoint needed by every center.  Monotonicity makes the same
cutoff valid at every dynamically reached intermediate packing and for each
local reservoir.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Every ordered rooted pair has at most the prescribed number of active
forbidden configurations after exposing the global reservoir. -/
def IsSimultaneousRootedGood
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (rootCutoff : ℕ) (omega : SimultaneousLinkPair O V K → Bool) :
    Prop :=
  ∀ e : DistinctPair V,
    (rootedActiveForbiddenConfigurations F
      (P ∪ simultaneousLinkReservoir U center K hcenter hout hleft hright
        omega) e.1.1 e.1.2).card ≤ rootCutoff

/-- Moment and union-bound estimate for the global rooted cutoff. -/
theorem independentBits_probability_simultaneousRootedBad_le
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) {familyCutoff momentOrder : ℕ}
    (rootCutoff : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder P z)
        (fun _ ↦ sigma) kappa) :
    (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun omega ↦
        ¬ IsSimultaneousRootedGood F P U center K hcenter hout hleft
          hright rootCutoff omega) ≤
      (Fintype.card (DistinctPair V) : ℝ≥0) *
        ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
            momentOrder) /
          (rootCutoff + 1 : ℝ≥0) ^ momentOrder) := by
  classical
  let L := FiniteLaw.independentBits
    (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  let R : (SimultaneousLinkPair O V K → Bool) → TripleSystemOn V :=
    simultaneousLinkReservoir U center K hcenter hout hleft hright
  let threshold : ℝ≥0 := rootCutoff + 1
  let tail : ℝ≥0 :=
    (((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
      momentOrder) / threshold ^ momentOrder
  let Bad : DistinctPair V →
      ((SimultaneousLinkPair O V K → Bool) → Prop) :=
    fun e omega ↦ threshold ≤
      (rootedActiveForbiddenConfigurations F (P ∪ R omega)
        e.1.1 e.1.2).card
  have hthreshold : 0 < threshold := by simp [threshold]
  have hjoint : ∀ Q : TripleSystemOn V,
      Q.card ≤ momentOrder * (familyCutoff - 1) →
      L.probability (fun omega ↦ Q ⊆ R omega) ≤
        (1 : ℝ≥0) * setWeight (fun _ ↦ sigma) Q := by
    intro Q _hQ
    simpa [L, R, setWeight] using
      simultaneousLinkReservoir_probability_subset_le U center K hcenter
        hout hleft hright sigma hsigma Q
  have hone : ∀ e : DistinctPair V,
      L.probability (Bad e) ≤ tail := by
    intro e
    simpa [Bad, tail, threshold, L, R] using
      (relativeRootedActive_probability_ge_le
        L R F P e.1.1 e.1.2 (fun _ ↦ sigma) 1 kappa threshold
        hthreshold hfamily (hkappa e) hjoint)
  calc
    L.probability (fun omega ↦
        ¬ IsSimultaneousRootedGood F P U center K hcenter hout hleft
          hright rootCutoff omega) ≤
        L.probability (fun omega ↦ ∃ e ∈
          (univ : Finset (DistinctPair V)), Bad e omega) := by
      apply L.probability_mono
      intro omega hnot
      unfold IsSimultaneousRootedGood at hnot
      push Not at hnot
      obtain ⟨e, he⟩ := hnot
      refine ⟨e, mem_univ e, ?_⟩
      change (rootCutoff + 1 : ℝ≥0) ≤
        (rootedActiveForbiddenConfigurations F (P ∪ R omega)
          e.1.1 e.1.2).card
      exact_mod_cast Nat.succ_le_iff.mpr he
    _ ≤ ∑ e ∈ (univ : Finset (DistinctPair V)),
        L.probability (Bad e) := L.probability_exists_le univ Bad
    _ ≤ ∑ _e ∈ (univ : Finset (DistinctPair V)), tail := by
      apply sum_le_sum
      intro e _he
      exact hone e
    _ = (Fintype.card (DistinctPair V) : ℝ≥0) *
        ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
            momentOrder) /
          (rootCutoff + 1 : ℝ≥0) ^ momentOrder) := by
      simp [tail, threshold]

/-- A global rooted-good outcome controls both sides of every local link at
every intermediate state contained in the exposed global reservoir. -/
theorem simultaneousRootedGood_local_cutoffs
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P P' : TripleSystemOn V)
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (rootCutoff : ℕ) (omega : SimultaneousLinkPair O V K → Bool)
    (hgood : IsSimultaneousRootedGood F P U center K hcenter hout hleft
      hright rootCutoff omega)
    (hP' : P' ⊆ P ∪ simultaneousLinkReservoir U center K hcenter hout
      hleft hright omega) (o : O) :
    (∀ a : ↥(K o).left,
      (rootedActiveForbiddenConfigurations F
        (P' ∪ bipartiteLinkReservoir (K o)
          (simultaneousLinkSelectedPairs K omega o))
        (K o).center a.1).card ≤ rootCutoff) ∧
    (∀ b : ↥(K o).right,
      (rootedActiveForbiddenConfigurations F
        (P' ∪ bipartiteLinkReservoir (K o)
          (simultaneousLinkSelectedPairs K omega o))
        (K o).center b.1).card ≤ rootCutoff) := by
  have hlocal : bipartiteLinkReservoir (K o)
        (simultaneousLinkSelectedPairs K omega o) ⊆
      simultaneousLinkReservoir U center K hcenter hout hleft hright omega :=
    bipartiteLinkReservoir_simultaneous_subset U center K hcenter hout
      hleft hright omega o
  have henlarge : P' ∪ bipartiteLinkReservoir (K o)
        (simultaneousLinkSelectedPairs K omega o) ⊆
      P ∪ simultaneousLinkReservoir U center K hcenter hout hleft hright
        omega := union_subset hP' (hlocal.trans subset_union_right)
  constructor
  · intro a
    let e : DistinctPair V :=
      ⟨((K o).center, a.1), (K o).center_ne_left a⟩
    exact (rootedActiveForbiddenConfigurations_card_mono henlarge).trans
      (hgood e)
  · intro b
    let e : DistinctPair V :=
      ⟨((K o).center, b.1), (K o).center_ne_right b⟩
    exact (rootedActiveForbiddenConfigurations_card_mono henlarge).trans
      (hgood e)

end

end Erdos207

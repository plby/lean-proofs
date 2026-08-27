/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkReservoirSampling
import ErdosProblems.Erdos207.RelativeRootedThreatMoment

/-!
# Simultaneous rooted-threat control for a Bernoulli link reservoir

The relative rooted-threat moment bound controls one endpoint.  A finite
union bound over the disjoint union of the two link sides gives exactly the
`Good` event needed by the robust-Hall link-cover argument.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Regard the two sides of a bipartite link as one finite endpoint type. -/
def linkSideEndpoint {V : Type*} [DecidableEq V] (K : BipartiteLink V) :
    (↥K.left ⊕ ↥K.right) → V
  | Sum.inl a => a.1
  | Sum.inr b => b.1

/-- The probability that some endpoint of a Bernoulli link reservoir has
more than `rootCutoff` active rooted forbidden configurations is bounded by
the sum of the one-endpoint moment tails. -/
theorem independentBits_probability_linkReservoir_rootedBad_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (sampleProbability : ℝ≥0)
    (hprob : sampleProbability ≤ 1)
    (kappa : ℝ≥0) {familyCutoff momentOrder : ℕ}
    (rootCutoff : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ x : ↥K.left ⊕ ↥K.right,
      HasExtensionBound
        (fun z : RootedThreatWitness V F K.center (linkSideEndpoint K x) =>
          relativeRootedThreatRemainder P z)
        (fun _ => sampleProbability) kappa) :
    (FiniteLaw.independentBits
      (fun _ : ↥K.left × ↥K.right => sampleProbability)
      (fun _ => hprob)).probability (fun omega =>
        ¬ ((∀ a : ↥K.left,
          (rootedActiveForbiddenConfigurations F
            (P ∪ linkReservoirTriangles K.center K.leftEmbedding
              K.rightEmbedding K.center_ne_left K.center_ne_right
              K.left_ne_right (FiniteLaw.selectedByBits omega))
            K.center a.1).card ≤ rootCutoff) ∧
        (∀ b : ↥K.right,
          (rootedActiveForbiddenConfigurations F
            (P ∪ linkReservoirTriangles K.center K.leftEmbedding
              K.rightEmbedding K.center_ne_left K.center_ne_right
              K.left_ne_right (FiniteLaw.selectedByBits omega))
            K.center b.1).card ≤ rootCutoff))) ≤
      (Fintype.card (↥K.left ⊕ ↥K.right) : ℝ≥0) *
        ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
            momentOrder) /
          (rootCutoff + 1 : ℝ≥0) ^ momentOrder) := by
  classical
  let L := FiniteLaw.independentBits
    (fun _ : ↥K.left × ↥K.right => sampleProbability)
    (fun _ => hprob)
  let R : (↥K.left × ↥K.right → Bool) → TripleSystemOn V :=
    fun omega => linkReservoirTriangles K.center K.leftEmbedding
      K.rightEmbedding K.center_ne_left K.center_ne_right K.left_ne_right
      (FiniteLaw.selectedByBits omega)
  let threshold : ℝ≥0 := rootCutoff + 1
  let tail : ℝ≥0 :=
    (((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
      momentOrder) / threshold ^ momentOrder
  let Bad : (↥K.left ⊕ ↥K.right) →
      ((↥K.left × ↥K.right → Bool) → Prop) :=
    fun x omega => threshold ≤
      (rootedActiveForbiddenConfigurations F (P ∪ R omega)
        K.center (linkSideEndpoint K x)).card
  have hthreshold : 0 < threshold := by
    simp [threshold]
  have hjoint : ∀ T : TripleSystemOn V,
      T.card ≤ momentOrder * (familyCutoff - 1) →
      L.probability (fun omega => T ⊆ R omega) ≤
        (1 : ℝ≥0) * setWeight (fun _ => sampleProbability) T := by
    intro T _hT
    simpa [L, R, setWeight] using
      (independentBits_probability_subset_linkReservoir_le
        K.center K.leftEmbedding K.rightEmbedding K.center_ne_left
        K.center_ne_right K.left_ne_right sampleProbability hprob T)
  have hone : ∀ x : ↥K.left ⊕ ↥K.right,
      L.probability (Bad x) ≤ tail := by
    intro x
    simpa [Bad, tail, threshold, L, R] using
      (relativeRootedActive_probability_ge_le
        L R F P K.center (linkSideEndpoint K x)
        (fun _ => sampleProbability) 1 kappa threshold hthreshold
        hfamily (hkappa x) hjoint)
  calc
    L.probability (fun omega =>
        ¬ ((∀ a : ↥K.left,
          (rootedActiveForbiddenConfigurations F (P ∪ R omega)
            K.center a.1).card ≤ rootCutoff) ∧
        (∀ b : ↥K.right,
          (rootedActiveForbiddenConfigurations F (P ∪ R omega)
            K.center b.1).card ≤ rootCutoff))) ≤
        L.probability (fun omega =>
          ∃ x ∈ (univ : Finset (↥K.left ⊕ ↥K.right)), Bad x omega) := by
      apply L.probability_mono
      intro omega hbad
      by_cases haall : ∀ a : ↥K.left,
          (rootedActiveForbiddenConfigurations F (P ∪ R omega)
            K.center a.1).card ≤ rootCutoff
      · have hbnot : ¬ ∀ b : ↥K.right,
            (rootedActiveForbiddenConfigurations F (P ∪ R omega)
              K.center b.1).card ≤ rootCutoff :=
          fun hball => hbad ⟨haall, hball⟩
        push Not at hbnot
        obtain ⟨b, hb⟩ := hbnot
        refine ⟨Sum.inr b, mem_univ _, ?_⟩
        change (rootCutoff + 1 : ℝ≥0) ≤
          (rootedActiveForbiddenConfigurations F (P ∪ R omega)
            K.center b.1).card
        exact_mod_cast Nat.succ_le_iff.mpr hb
      · push Not at haall
        obtain ⟨a, ha⟩ := haall
        refine ⟨Sum.inl a, mem_univ _, ?_⟩
        change (rootCutoff + 1 : ℝ≥0) ≤
          (rootedActiveForbiddenConfigurations F (P ∪ R omega)
            K.center a.1).card
        exact_mod_cast Nat.succ_le_iff.mpr ha
    _ ≤ ∑ x ∈ (univ : Finset (↥K.left ⊕ ↥K.right)),
          L.probability (Bad x) :=
      L.probability_exists_le (univ : Finset (↥K.left ⊕ ↥K.right)) Bad
    _ ≤ ∑ _x ∈ (univ : Finset (↥K.left ⊕ ↥K.right)), tail := by
      apply sum_le_sum
      intro x _hx
      exact hone x
    _ = (Fintype.card (↥K.left ⊕ ↥K.right) : ℝ≥0) *
        ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
            momentOrder) /
          (rootCutoff + 1 : ℝ≥0) ^ momentOrder) := by
      simp [tail, threshold]

/-- Scalar-budget form of
`independentBits_probability_linkReservoir_rootedBad_le`, ready for the
single-link cover interface. -/
theorem independentBits_probability_linkReservoir_rootedBad_le_of_scalar
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (sampleProbability : ℝ≥0)
    (hprob : sampleProbability ≤ 1)
    (kappa epsilon : ℝ≥0) {familyCutoff momentOrder : ℕ}
    (rootCutoff : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ x : ↥K.left ⊕ ↥K.right,
      HasExtensionBound
        (fun z : RootedThreatWitness V F K.center (linkSideEndpoint K x) =>
          relativeRootedThreatRemainder P z)
        (fun _ => sampleProbability) kappa)
    (hscalar :
      (Fintype.card (↥K.left ⊕ ↥K.right) : ℝ≥0) *
        ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
            momentOrder) /
          (rootCutoff + 1 : ℝ≥0) ^ momentOrder) ≤ epsilon) :
    (FiniteLaw.independentBits
      (fun _ : ↥K.left × ↥K.right => sampleProbability)
      (fun _ => hprob)).probability (fun omega =>
        ¬ ((∀ a : ↥K.left,
          (rootedActiveForbiddenConfigurations F
            (P ∪ linkReservoirTriangles K.center K.leftEmbedding
              K.rightEmbedding K.center_ne_left K.center_ne_right
              K.left_ne_right (FiniteLaw.selectedByBits omega))
            K.center a.1).card ≤ rootCutoff) ∧
        (∀ b : ↥K.right,
          (rootedActiveForbiddenConfigurations F
            (P ∪ linkReservoirTriangles K.center K.leftEmbedding
              K.rightEmbedding K.center_ne_left K.center_ne_right
              K.left_ne_right (FiniteLaw.selectedByBits omega))
            K.center b.1).card ≤ rootCutoff))) ≤ epsilon :=
  (independentBits_probability_linkReservoir_rootedBad_le
    F P K sampleProbability hprob kappa rootCutoff hfamily hkappa).trans
      hscalar

end

end Erdos207

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.ConditionedEncodedSelection
import ErdosProblems.Erdos551.External.Erdos207.LinkReservoirSampling
import ErdosProblems.Erdos551.External.Erdos207.ChosenCrossingLink

/-!
# One independent reservoir for all crossing links

KSSS sparsify all outer-vertex link graphs simultaneously.  A coordinate is
an outer center together with one pair across its chosen bipartition.  When
the center lies outside `U` and both endpoints lie in `U`, the coordinate is
uniquely determined by its triangle.  Thus the entire collection, not merely
one link, is an injective image of independent Bernoulli bits and has the C4
joint-inclusion estimate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Coordinates of all chosen bipartite link graphs. -/
abbrev SimultaneousLinkPair
    (O V : Type*) [DecidableEq V] (K : O → BipartiteLink V) :=
  Σ o : O, ↥(K o).left × ↥(K o).right

/-- The triangle encoded by one coordinate in the simultaneous link
reservoir. -/
def simultaneousLinkPairTriple
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V)
    (x : SimultaneousLinkPair O V K) : TripleOn V :=
  linkMatchingTriple (K x.1).center (K x.1).leftEmbedding
    (K x.1).rightEmbedding (K x.1).center_ne_left
    (K x.1).center_ne_right (K x.1).left_ne_right x.2.1 x.2.2

/-- Distinct global link coordinates give distinct triples.  Separation by
`U` is precisely what makes the center of a reservoir triangle unique. -/
def simultaneousLinkPairEmbedding
    {O V : Type*} [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U) :
    SimultaneousLinkPair O V K ↪ TripleOn V where
  toFun := simultaneousLinkPairTriple K
  inj' := by
    intro x y hxy
    obtain ⟨ox, ax, bx⟩ := x
    obtain ⟨oy, ay, byv⟩ := y
    have hcxmem : center ox ∈
        (simultaneousLinkPairTriple K ⟨ox, (ax, bx)⟩).1 := by
      simp [simultaneousLinkPairTriple, ← hcenter ox]
    have hcxmemY : center ox ∈
        (simultaneousLinkPairTriple K ⟨oy, (ay, byv)⟩).1 := by
      have hm := congrArg (fun T : TripleOn V ↦ center ox ∈ T.1) hxy
      exact hm.mp hcxmem
    have hcenters : center ox = center oy := by
      rw [simultaneousLinkPairTriple, mem_linkMatchingTriple_iff] at hcxmemY
      rcases hcxmemY with hcy | hleftY | hrightY
      · simpa only [hcenter oy] using hcy
      · exfalso
        apply hout ox
        rw [hleftY]
        exact hleft oy ay.2
      · exfalso
        apply hout ox
        rw [hrightY]
        exact hright oy byv.2
    have ho : ox = oy := center.injective hcenters
    subst oy
    have hab : (ax, bx) = (ay, byv) := by
      apply (linkPairTripleEmbedding (K ox).center
        (K ox).leftEmbedding (K ox).rightEmbedding
        (K ox).center_ne_left (K ox).center_ne_right
        (K ox).left_ne_right).injective
      exact hxy
    cases hab
    rfl

/-- The global simultaneous reservoir exposed by one bit vector. -/
def simultaneousLinkReservoir
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (ω : SimultaneousLinkPair O V K → Bool) : TripleSystemOn V :=
  encodedReservoir
    (simultaneousLinkPairEmbedding U center K hcenter hout hleft hright) ω

/-- C4 for the unconditioned family of all simultaneous link reservoirs. -/
theorem simultaneousLinkReservoir_probability_subset_le
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (Q : TripleSystemOn V) :
    (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun ω ↦
        Q ⊆ simultaneousLinkReservoir U center K hcenter hout hleft
          hright ω) ≤ sigma ^ Q.card := by
  exact independentBits_probability_subset_encodedReservoir_le_pow
    sigma hsigma
      (simultaneousLinkPairEmbedding U center K hcenter hout hleft hright) Q

/-- After conditioning on any positive global success event, every
deterministically selected simultaneous matching subfamily retains C4 with
the exact reciprocal success-probability loss. -/
theorem conditioned_simultaneousLinkSelection_probability_subset_le
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (Good : (SimultaneousLinkPair O V K → Bool) → Prop)
    (hGood : 0 < (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability Good)
    (selected : (SimultaneousLinkPair O V K → Bool) → TripleSystemOn V)
    (hselected : ∀ ω, Good ω → selected ω ⊆
      simultaneousLinkReservoir U center K hcenter hout hleft hright ω)
    (Q : TripleSystemOn V) :
    ((FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).conditionedSelectionLaw Good hGood selected).probability
        (fun M ↦ Q ⊆ M) ≤
      sigma ^ Q.card /
        (FiniteLaw.independentBits
          (fun _ : SimultaneousLinkPair O V K ↦ sigma)
          (fun _ ↦ hsigma)).probability Good := by
  exact conditioned_encodedSelection_probability_subset_le sigma hsigma
    (simultaneousLinkPairEmbedding U center K hcenter hout hleft hright)
      Good hGood selected hselected Q

end

end Erdos207

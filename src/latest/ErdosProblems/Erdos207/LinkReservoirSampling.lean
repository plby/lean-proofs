/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Data.Finset.Preimage
import ErdosProblems.Erdos207.TwoSidedLinkCoverGood
import ErdosProblems.Erdos207.WeightSystem

/-!
# Joint inclusion in a Bernoulli link reservoir

Distinct bipartite link pairs encode distinct triples.  Consequently the
independently sampled pair relation gives the exact product upper bound for
every prescribed family of reservoir triples, including families containing
triples outside the reservoir image (whose inclusion probability is zero).
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The injective encoding of a bipartite link pair by its triple. -/
def linkPairTripleEmbedding
    {A B V : Type*} [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b) :
    (A × B) ↪ TripleOn V where
  toFun ab := linkMatchingTriple center left right hcenterLeft
    hcenterRight hleftRight ab.1 ab.2
  inj' := by
    intro x y hxy
    apply Prod.ext
    · apply left.injective
      have hmemx : left x.1 ∈
          (linkMatchingTriple center left right hcenterLeft hcenterRight
            hleftRight x.1 x.2).1 := by
        simp
      have hmem : left x.1 ∈
          (linkMatchingTriple center left right hcenterLeft hcenterRight
            hleftRight y.1 y.2).1 := by
        have hp := congrArg (fun T : TripleOn V ↦ left x.1 ∈ T.1) hxy
        exact Eq.mp hp hmemx
      rw [mem_linkMatchingTriple_iff] at hmem
      rcases hmem with hcenter | hleft | hright
      · exact (hcenterLeft x.1 hcenter.symm).elim
      · exact hleft
      · exact (hleftRight x.1 y.2 hright).elim
    · apply right.injective
      have hmemx : right x.2 ∈
          (linkMatchingTriple center left right hcenterLeft hcenterRight
            hleftRight x.1 x.2).1 := by
        simp
      have hmem : right x.2 ∈
          (linkMatchingTriple center left right hcenterLeft hcenterRight
            hleftRight y.1 y.2).1 := by
        have hp := congrArg (fun T : TripleOn V ↦ right x.2 ∈ T.1) hxy
        exact Eq.mp hp hmemx
      rw [mem_linkMatchingTriple_iff] at hmem
      rcases hmem with hcenter | hleft | hright
      · exact (hcenterRight x.2 hcenter.symm).elim
      · exact (hleftRight y.1 x.2 hleft.symm).elim
      · exact hright

lemma linkReservoirTriangles_eq_map
    {A B V : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (R : Finset (A × B)) :
    linkReservoirTriangles center left right hcenterLeft hcenterRight
      hleftRight R =
      R.map (linkPairTripleEmbedding center left right hcenterLeft
        hcenterRight hleftRight) := by
  classical
  rw [Finset.map_eq_image]
  rfl

/-- Point weight supported on the full image of one bipartite link. -/
def linkReservoirPointWeight
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (sigma : ℝ≥0) (T : TripleOn V) : ℝ≥0 :=
  if T ∈ linkReservoirTriangles center left right hcenterLeft
      hcenterRight hleftRight (univ : Finset (A × B))
    then sigma else 0

lemma setWeight_linkReservoirPointWeight_of_subset
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (sigma : ℝ≥0) (Q : TripleSystemOn V)
    (hQ : Q ⊆ linkReservoirTriangles center left right hcenterLeft
      hcenterRight hleftRight (univ : Finset (A × B))) :
    setWeight (linkReservoirPointWeight center left right hcenterLeft
      hcenterRight hleftRight sigma) Q = sigma ^ Q.card := by
  classical
  unfold setWeight linkReservoirPointWeight
  apply Finset.prod_eq_pow_card
  intro T hT
  simp only [if_pos (hQ hT)]

lemma setWeight_linkReservoirPointWeight_eq_zero_of_not_subset
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (sigma : ℝ≥0) (Q : TripleSystemOn V)
    (hQ : ¬ Q ⊆ linkReservoirTriangles center left right hcenterLeft
      hcenterRight hleftRight (univ : Finset (A × B))) :
    setWeight (linkReservoirPointWeight center left right hcenterLeft
      hcenterRight hleftRight sigma) Q = 0 := by
  classical
  obtain ⟨T, hTQ, hTnot⟩ := Finset.not_subset.mp hQ
  unfold setWeight
  apply Finset.prod_eq_zero hTQ
  simp [linkReservoirPointWeight, hTnot]

/-- Every prescribed triple family is contained in the Bernoulli link
reservoir with probability at most `sigma` to the size of that family. -/
theorem independentBits_probability_subset_linkReservoir_le
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (Q : TripleSystemOn V) :
    (FiniteLaw.independentBits (fun _ : A × B ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun omega ↦
        Q ⊆ linkReservoirTriangles center left right hcenterLeft
          hcenterRight hleftRight (FiniteLaw.selectedByBits omega)) ≤
      sigma ^ Q.card := by
  classical
  let e := linkPairTripleEmbedding center left right hcenterLeft
    hcenterRight hleftRight
  by_cases hQrange : Q ⊆ (univ : Finset (A × B)).map e
  · let S := Q.preimage e e.injective.injOn
    have hmap : S.map e = Q := by
      ext T
      constructor
      · intro hT
        obtain ⟨ab, habS, rfl⟩ := mem_map.mp hT
        exact mem_preimage.mp habS
      · intro hTQ
        obtain ⟨ab, _hab, habT⟩ := mem_map.mp (hQrange hTQ)
        subst T
        exact mem_map.mpr ⟨ab, mem_preimage.mpr hTQ, rfl⟩
    have hcard : S.card = Q.card := by
      rw [← hmap]
      simp
    have hevent : (fun omega ↦
        Q ⊆ linkReservoirTriangles center left right hcenterLeft
          hcenterRight hleftRight (FiniteLaw.selectedByBits omega)) =
        (fun omega ↦ S ⊆ FiniteLaw.selectedByBits omega) := by
      funext omega
      apply propext
      rw [linkReservoirTriangles_eq_map, ← hmap]
      exact Finset.map_subset_map
    rw [hevent,
      FiniteLaw.independentBits_probability_subset_selected]
    simp [hcard]
  · have hfalse : (fun omega ↦
        Q ⊆ linkReservoirTriangles center left right hcenterLeft
          hcenterRight hleftRight (FiniteLaw.selectedByBits omega)) =
        (fun _ : (A × B) → Bool ↦ False) := by
      funext omega
      apply propext
      constructor
      · intro hQ
        apply hQrange
        intro T hTQ
        have hTres := hQ hTQ
        rw [linkReservoirTriangles_eq_map] at hTres
        exact (Finset.map_subset_map.2
          (subset_univ (FiniteLaw.selectedByBits omega))) hTres
      · exact False.elim
    rw [hfalse]
    simp

/-- Weighted form of the Bernoulli reservoir joint-inclusion estimate.  Its
point weight vanishes away from triples that this link can sample. -/
theorem independentBits_probability_subset_linkReservoir_le_weight
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (Q : TripleSystemOn V) :
    (FiniteLaw.independentBits (fun _ : A × B ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun omega ↦
        Q ⊆ linkReservoirTriangles center left right hcenterLeft
          hcenterRight hleftRight (FiniteLaw.selectedByBits omega)) ≤
      setWeight (linkReservoirPointWeight center left right hcenterLeft
        hcenterRight hleftRight sigma) Q := by
  classical
  let Full := linkReservoirTriangles center left right hcenterLeft
    hcenterRight hleftRight (univ : Finset (A × B))
  by_cases hQ : Q ⊆ Full
  · rw [setWeight_linkReservoirPointWeight_of_subset
      center left right hcenterLeft hcenterRight hleftRight sigma Q hQ]
    exact independentBits_probability_subset_linkReservoir_le
      center left right hcenterLeft hcenterRight hleftRight sigma hsigma Q
  · rw [setWeight_linkReservoirPointWeight_eq_zero_of_not_subset
      center left right hcenterLeft hcenterRight hleftRight sigma Q hQ]
    have himpossible : ∀ omega : A × B → Bool,
        ¬ Q ⊆ linkReservoirTriangles center left right hcenterLeft
          hcenterRight hleftRight (FiniteLaw.selectedByBits omega) := by
      intro omega hsub
      apply hQ
      apply hsub.trans
      unfold Full
      rw [linkReservoirTriangles_eq_map, linkReservoirTriangles_eq_map]
      exact Finset.map_subset_map.2 (subset_univ _)
    calc
      (FiniteLaw.independentBits (fun _ : A × B ↦ sigma)
          (fun _ ↦ hsigma)).probability (fun omega ↦
            Q ⊆ linkReservoirTriangles center left right hcenterLeft
              hcenterRight hleftRight (FiniteLaw.selectedByBits omega)) ≤
          (FiniteLaw.independentBits (fun _ : A × B ↦ sigma)
            (fun _ ↦ hsigma)).probability (fun _ ↦ False) := by
            apply FiniteLaw.probability_mono
            intro omega homega
            exact himpossible omega homega
      _ = 0 := FiniteLaw.probability_false _

end

end Erdos207

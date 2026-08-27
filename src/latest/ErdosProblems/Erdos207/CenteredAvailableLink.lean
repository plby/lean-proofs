/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredHallCandidates
import ErdosProblems.Erdos207.SharpPairedBisection

/-! # Source-correct balanced Hall candidates in a genuine available link -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem card_ambientLinkSubtype_degree
    {V : Type*} [Fintype V] [DecidableEq V] (center : V) (A : TripleSystemOn V)
    (W : Finset V) (x : W) :
    (relationNeighborsIn (fun a b : W ↦ ambientLinkRelation center A a.1 b.1) univ x).card =
      (ambientLinkNeighborsIn center A W x.1).card := by
  let S := relationNeighborsIn (fun a b : W ↦ ambientLinkRelation center A a.1 b.1) univ x
  have heq : S.image Subtype.val = ambientLinkNeighborsIn center A W x.1 := by
    ext y
    constructor
    · intro hy
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
      exact mem_ambientLinkNeighborsIn_iff.mpr ⟨v.2, ((mem_relationNeighborsIn_iff _).mp hv).2⟩
    · intro hy
      have hh := mem_ambientLinkNeighborsIn_iff.mp hy
      exact mem_image.mpr ⟨⟨y, hh.1⟩, (mem_relationNeighborsIn_iff _).mpr ⟨mem_univ _, hh.2⟩, rfl⟩
  rw [← heq, card_image_of_injective _ Subtype.val_injective]

theorem card_ambientLinkSubtype_codegree
    {V : Type*} [Fintype V] [DecidableEq V] (center : V) (A : TripleSystemOn V)
    (W : Finset V) (x y : W) :
    (relationCommonNeighbors (fun a b : W ↦ ambientLinkRelation center A a.1 b.1) x y).card =
      (ambientLinkCommonNeighborsIn center A W x.1 y.1).card := by
  let S := relationCommonNeighbors (fun a b : W ↦ ambientLinkRelation center A a.1 b.1) x y
  have heq : S.image Subtype.val = ambientLinkCommonNeighborsIn center A W x.1 y.1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hz
      have hh := (mem_relationCommonNeighbors_iff _).mp hv
      exact mem_ambientLinkCommonNeighborsIn_iff.mpr ⟨v.2, hh.1, hh.2⟩
    · intro hz
      have hh := mem_ambientLinkCommonNeighborsIn_iff.mp hz
      exact mem_image.mpr ⟨⟨z, hh.1⟩, (mem_relationCommonNeighbors_iff _).mpr hh.2, rfl⟩
  rw [← heq, card_image_of_injective _ Subtype.val_injective]

theorem link_orientedSmallHall_candidates_of_centered
    {V : Type*} [Fintype V] [DecidableEq V] (K : BipartiteLink V) (A : TripleSystemOn V)
    (W : Finset V) (hleft : K.left ⊆ W) (hright : K.right ⊆ W) (hbalanced : K.left.card = K.right.card)
    (rho xi error : ℝ) (hrho : 0 ≤ rho) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (herror : 0 ≤ error)
    (hdegree : ∀ v ∈ W,
      (1-xi)*rho*W.card ≤ ((ambientLinkNeighborsIn K.center A W v).card : ℝ) ∧
      ((ambientLinkNeighborsIn K.center A W v).card : ℝ) ≤ (1+xi)*rho*W.card)
    (hcodegree : ∀ v ∈ W, ∀ w ∈ W, v ≠ w →
      ((ambientLinkCommonNeighborsIn K.center A W v w).card : ℝ) ≤ (1+xi)*rho^2*W.card)
    (hbudget : 2*rho*W.card+3*xi*rho^2*(W.card : ℝ)^2 ≤ error^2)
    (d c : ℕ) (hleftDegree : ∀ a, d ≤ (relationNeighborsIn (linkAvailableRelation K A) univ a).card)
    (hrightDegree : ∀ b, d ≤ (relationNeighborsIn (transposeRelation (linkAvailableRelation K A)) univ b).card)
    (hscalar : (c : ℝ)+rho*((K.left.card+1)/2 : ℕ)+error ≤ d) :
    ∀ o : OrientedSmallHallObstruction ↥K.left ↥K.right,
      c*orientedSmallHallSize o ≤ (orientedSmallHallCandidates (linkAvailableRelation K A) o).card := by
  let R := fun a b : W ↦ ambientLinkRelation K.center A a.1 b.1
  let f : ↥K.left ↪ W := ⟨fun a ↦ ⟨a.1, hleft a.2⟩, fun _ _ h ↦ Subtype.ext (congrArg (fun v : W ↦ v.1) h)⟩
  let g : ↥K.right ↪ W := ⟨fun b ↦ ⟨b.1, hright b.2⟩, fun _ _ h ↦ Subtype.ext (congrArg (fun v : W ↦ v.1) h)⟩
  apply orientedSmallHall_linear_candidates_of_centered (linkAvailableRelation K A) R f g
    (fun _ _ ↦ linkAvailableRelation_iff_ambient) (fun _ _ ↦ ambientLinkRelation_symm)
    (by simpa only [Fintype.card_coe] using hbalanced) rho xi error hrho hxi hxi1 herror
    _ _ _ d c hleftDegree hrightDegree (by simpa only [Fintype.card_coe] using hscalar)
  · intro v
    simpa only [R, Fintype.card_coe, card_ambientLinkSubtype_degree] using hdegree v.1 v.2
  · intro v w hvw
    simpa only [R, Fintype.card_coe, card_ambientLinkSubtype_codegree] using
      hcodegree v.1 v.2 w.1 w.2 (fun h ↦ hvw (Subtype.ext h))
  · simpa only [Fintype.card_coe] using hbudget

theorem exists_balancedLink_centered_candidates
    {V : Type*} [Fintype V] [DecidableEq V] (center : V) (A : TripleSystemOn V) (W : Finset V)
    (hcenter : center ∉ W) (heven : Even W.card)
    (rho xi error : ℝ) (hrho : 0 ≤ rho) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (herror : 0 ≤ error)
    (hdegree : ∀ v ∈ W,
      (1-xi)*rho*W.card ≤ ((ambientLinkNeighborsIn center A W v).card : ℝ) ∧
      ((ambientLinkNeighborsIn center A W v).card : ℝ) ≤ (1+xi)*rho*W.card)
    (hcodegree : ∀ v ∈ W, ∀ w ∈ W, v ≠ w →
      ((ambientLinkCommonNeighborsIn center A W v w).card : ℝ) ≤ (1+xi)*rho^2*W.card)
    (hbudget : 2*rho*W.card+3*xi*rho^2*(W.card : ℝ)^2 ≤ error^2)
    (m d c : ℕ) (hmin : ∀ v ∈ W, m ≤ (ambientLinkNeighborsIn center A W v).card)
    (hsmall : (W.card : ℝ≥0)*(2*(2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(m-2)) < 1)
    (hscalar : (c : ℝ)+rho*((W.card/2+1)/2 : ℕ)+error ≤ d) :
    ∃ K : BipartiteLink V, K.center = center ∧ K.left ∪ K.right = W ∧ K.left.card = K.right.card ∧
      (∀ a, d ≤ (relationNeighborsIn (linkAvailableRelation K A) univ a).card) ∧
      (∀ b, d ≤ (relationNeighborsIn (transposeRelation (linkAvailableRelation K A)) univ b).card) ∧
      ∀ o : OrientedSmallHallObstruction ↥K.left ↥K.right,
        c*orientedSmallHallSize o ≤ (orientedSmallHallCandidates (linkAvailableRelation K A) o).card := by
  let B : BalancedBisection V W := Classical.choice (BalancedBisection.nonempty_of_even W heven)
  obtain ⟨ω, hω⟩ := B.exists_pairedBisection_minCrossDegree_of_sharp (ambientLinkRelation center A) m d hmin hsmall
  let K := (B.pairedBisection ω).toBipartiteLink center hcenter
  have hpart := B.pairedBisection_isResidualPartition ω center hcenter
  have hKL : K.left ⊆ W := by intro v hv; rw [← hpart.2.1]; exact mem_union_left _ hv
  have hKR : K.right ⊆ W := by intro v hv; rw [← hpart.2.1]; exact mem_union_right _ hv
  have hleftDegree : ∀ a, d ≤ (relationNeighborsIn (linkAvailableRelation K A) univ a).card := by
    intro a
    rw [← B.pairedCrossDegree_eq_left_linkDegree ω center hcenter A a]
    exact hω a.1 (hKL a.2)
  have hrightDegree : ∀ b, d ≤ (relationNeighborsIn (transposeRelation (linkAvailableRelation K A)) univ b).card := by
    intro b
    rw [← B.pairedCrossDegree_eq_right_linkDegree ω center hcenter A b]
    exact hω b.1 (hKR b.2)
  have hcard : K.left.card = W.card/2 := by
    have hc := (B.pairedBisection ω).twice_card
    change 2*K.left.card = W.card at hc
    omega
  refine ⟨K, hpart.1, hpart.2.1, hpart.2.2, hleftDegree, hrightDegree, ?_⟩
  exact link_orientedSmallHall_candidates_of_centered K A W hKL hKR hpart.2.2 rho xi error hrho hxi hxi1 herror
    hdegree hcodegree hbudget d c hleftDegree hrightDegree (by simpa only [hcard] using hscalar)

end

end Erdos207

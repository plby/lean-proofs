/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairWitnessSampling
import ErdosProblems.Erdos207.SampledCandidateSimultaneousCover

/-! # Actual inner-edge collision blocks for simultaneous sampled links -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def simultaneousLinkInnerEdge
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V)
    (x : SimultaneousLinkPair O V K) : Sym2 V :=
  s((K x.1).leftEmbedding x.2.1, (K x.1).rightEmbedding x.2.2)

def otherLinkCoordinates
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (x : SimultaneousLinkPair O V K) : Finset (SimultaneousLinkPair O V K) :=
  univ.filter fun y ↦ y.1 ≠ x.1 ∧ r y.1 y.2.1 y.2.2 ∧
    simultaneousLinkInnerEdge K y = simultaneousLinkInnerEdge K x

theorem not_mem_otherLinkCoordinates
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (x : SimultaneousLinkPair O V K) : x ∉ otherLinkCoordinates K r x := by
  simp [otherLinkCoordinates]

theorem otherLinkCoordinates_block_innerEdge
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    {x y : SimultaneousLinkPair O V K}
    (hy : y ∈ insert x (otherLinkCoordinates K r x)) :
    simultaneousLinkInnerEdge K y = simultaneousLinkInnerEdge K x := by
  rcases mem_insert.mp hy with rfl | hy
  · rfl
  · exact (mem_filter.mp hy).2.2.2

theorem otherLinkCoordinates_pairwiseDisjoint
    {O V J : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (key : J → SimultaneousLinkPair O V K)
    (hinj : Function.Injective (fun j ↦ simultaneousLinkInnerEdge K (key j)))
    (S : Finset J) :
    (S : Set J).PairwiseDisjoint (fun j ↦ insert (key j) (otherLinkCoordinates K r (key j))) := by
  intro a _ b _ hab
  apply disjoint_left.mpr
  intro x hxa hxb
  exact hab (hinj ((otherLinkCoordinates_block_innerEdge K r hxa).symm.trans
    (otherLinkCoordinates_block_innerEdge K r hxb)))

theorem simultaneousLinkInnerEdge_left_injective
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V)
    (o : O) (a : ↥(K o).left) :
    Function.Injective (fun b : ↥(K o).right ↦ simultaneousLinkInnerEdge K ⟨o, (a, b)⟩) := by
  intro b c hbc
  exact (K o).rightEmbedding.injective (Sym2.congr_right.mp hbc)

theorem simultaneousLinkInnerEdge_right_injective
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V)
    (o : O) (b : ↥(K o).right) :
    Function.Injective (fun a : ↥(K o).left ↦ simultaneousLinkInnerEdge K ⟨o, (a, b)⟩) := by
  intro a c hac
  exact (K o).leftEmbedding.injective (Sym2.congr_left.mp hac)

def sampledLinkCollisions
    {O V J : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [DecidableEq J]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (key : J → SimultaneousLinkPair O V K) (S : Finset J)
    (omega : SimultaneousLinkPair O V K → Bool) : Finset J :=
  pairWitnesses key (fun j ↦ otherLinkCoordinates K r (key j)) S omega

theorem independentBits_sampledLinkCollisions_tail
    {O V J : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [DecidableEq J]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (key : J → SimultaneousLinkPair O V K) (S : Finset J)
    (hinj : Function.Injective (fun j ↦ simultaneousLinkInnerEdge K (key j)))
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (M : ℕ)
    (hM : ∀ j ∈ S, (otherLinkCoordinates K r (key j)).card ≤ M)
    (s R : ℕ) (hR : 0 < R) (hs : 2 * s ≤ R) :
    (FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
      (fun omega ↦ R ≤ (sampledLinkCollisions K r key S omega).card) ≤
        (2 * (S.card : ℝ≥0) * M * sigma ^ 2 / R) ^ s := by
  apply FiniteLaw.probability_pairWitnesses_card_ge_le _ sigma _ key
    (fun j ↦ otherLinkCoordinates K r (key j)) S
    (fun j _ ↦ not_mem_otherLinkCoordinates K r (key j))
    (otherLinkCoordinates_pairwiseDisjoint K r key hinj S) M hM s R hR hs
  intro A
  simp only [FiniteLaw.independentBits_probability_forall_true, prod_const, le_refl]

theorem independentBits_sampledLinkCollisions_tail_dyadic
    {O V J : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [DecidableEq J]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (key : J → SimultaneousLinkPair O V K) (S : Finset J)
    (hinj : Function.Injective (fun j ↦ simultaneousLinkInnerEdge K (key j)))
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (M : ℕ)
    (hM : ∀ j ∈ S, (otherLinkCoordinates K r (key j)).card ≤ M)
    (s R : ℕ) (hR : 0 < R) (hs : 2 * s ≤ R)
    (hmean : 4 * (S.card : ℝ≥0) * M * sigma ^ 2 ≤ R) :
    (FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
      (fun omega ↦ R ≤ (sampledLinkCollisions K r key S omega).card) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  apply FiniteLaw.probability_pairWitnesses_card_ge_le_dyadic _ sigma _ key
    (fun j ↦ otherLinkCoordinates K r (key j)) S
    (fun j _ ↦ not_mem_otherLinkCoordinates K r (key j))
    (otherLinkCoordinates_pairwiseDisjoint K r key hinj S) M hM s R hR hs hmean
  intro A
  simp only [FiniteLaw.independentBits_probability_forall_true, prod_const, le_refl]

end

end Erdos207

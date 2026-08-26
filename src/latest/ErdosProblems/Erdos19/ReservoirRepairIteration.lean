import ErdosProblems.Erdos19.BlockMatchingRepair
import ErdosProblems.Erdos19.MatchingRequestLoads
import Mathlib.Data.Fin.Tuple.Basic

/-! # The complete finite iteration of blockwise matching repairs

Requests are fixed before the iteration. Every new edge meets a required
vertex, and the other endpoints lie in a disjoint buffer. The request count
therefore bounds the used degree at every vertex that still needs coverage.
No bound on the load at buffer vertices is needed for the next matching.
-/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V]

theorem exists_reservoir_repair_family (G used : _root_.SimpleGraph V)
    (U Y : Set V) (hUY : Disjoint U Y) (X : I → Set V)
    (hX : Pairwise fun i j ↦ Disjoint (X i) (X j)) (hXcover : ∀ v, ∃ i, v ∈ X i)
    (missing initialLoad requests : ℕ)
    (hused : ∀ u ∈ U, (used.neighborSet u).ncard ≤ initialLoad) (m : ℕ) :
    ∀ (A : Fin m → Set V) (B : Fin m → I → Set V),
      (∀ i, A i ⊆ U) → (∀ i j, B i j ⊆ Y) → (∀ i j, B i j ⊆ X j) →
      (∀ i j, missing + initialLoad + requests ≤ (B i j).ncard) →
      (∀ i j u, u ∈ A i ∩ X j →
        (((A i ∩ X j) ∪ B i j) \ G.neighborSet u).ncard ≤ missing) →
      (∀ v, (∑ i : Fin m, if v ∈ A i then 1 else 0) ≤ requests) →
      ∃ M : Fin m → G.Subgraph,
        (∀ i, (M i).IsMatching ∧ A i ⊆ (M i).verts ∧
          (M i).verts ⊆ A i ∪ ⋃ j, B i j ∧
          (M i).verts.ncard ≤ 2 * (A i).ncard ∧ Disjoint used (M i).spanningCoe) ∧
        Pairwise fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe := by
  classical
  induction m with
  | zero =>
    intro A B _ _ _ _ _ _
    exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ m ih =>
    intro A B hAU hBY hBX hBsize hmissing hrequests
    let A₀ : Fin m → Set V := fun i ↦ A i.castSucc
    let B₀ : Fin m → I → Set V := fun i ↦ B i.castSucc
    have hrequests₀ : ∀ v, (∑ i : Fin m, if v ∈ A₀ i then 1 else 0) ≤ requests := by
      intro v
      have h := hrequests v
      rw [Fin.sum_univ_castSucc] at h
      dsimp only [A₀]
      omega
    obtain ⟨M, hM, hdis⟩ := ih A₀ B₀ (fun i ↦ hAU i.castSucc)
      (fun i ↦ hBY i.castSucc) (fun i ↦ hBX i.castSucc)
      (fun i ↦ hBsize i.castSucc) (fun i ↦ hmissing i.castSucc) hrequests₀
    let P := ⨆ i : Fin m, (M i).spanningCoe
    let used' := used ⊔ P
    let A' : I → Set V := fun j ↦ A (Fin.last m) ∩ X j
    let B' : I → Set V := B (Fin.last m)
    have hMverts : ∀ i, (M i).verts ⊆ A₀ i ∪ Y := by
      intro i v hv
      rcases (hM i).2.2.1 hv with hv | hv
      · exact Or.inl hv
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hv
        exact Or.inr (hBY i.castSucc j hj)
    have hPload : ∀ u ∈ U, (P.neighborSet u).ncard ≤ requests := by
      intro u hu
      exact matching_family_load_at_required_vertex G M (fun i ↦ (hM i).1) hdis A₀ U Y
        hUY hMverts requests hrequests₀ u hu
    have hblocks : Pairwise fun j k ↦ Disjoint (A' j ∪ B' j) (A' k ∪ B' k) := by
      intro j k hjk
      apply (hX hjk).mono
      · exact Set.union_subset Set.inter_subset_right (hBX _ j)
      · exact Set.union_subset Set.inter_subset_right (hBX _ k)
    have hAB : ∀ j, Disjoint (A' j) (B' j) := by
      intro j
      exact hUY.mono (Set.inter_subset_left.trans (hAU _))
        (hBY _ j)
    have hbuffer : ∀ j, missing + (initialLoad + requests) ≤ (B' j).ncard := by
      intro j
      have hsize := hBsize (Fin.last m) j
      change missing + (initialLoad + requests) ≤ (B (Fin.last m) j).ncard
      omega
    have hmiss : ∀ j u, u ∈ A' j →
        ((A' j ∪ B' j) \ G.neighborSet u).ncard ≤ missing := by
      exact hmissing (Fin.last m)
    have hload : ∀ j u, u ∈ A' j →
        (used'.neighborSet u).ncard ≤ initialLoad + requests := by
      intro j u hu
      have huU := hAU (Fin.last m) hu.1
      change ((used ⊔ P).neighborSet u).ncard ≤ _
      rw [neighborSet_sup]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add (hused u huU) (hPload u huU))
    obtain ⟨N, hN, hcoverN, hvertsN, hcardN, hdisN, _⟩ :=
      exists_disjoint_block_matching_repair G used' A' B' missing (initialLoad + requests)
        hblocks hAB hbuffer hmiss hload
    have hAunion : (⋃ j, A' j) = A (Fin.last m) := by
      ext v
      constructor
      · intro hv
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hv
        exact hj.1
      · intro hv
        obtain ⟨j, hj⟩ := hXcover v
        exact Set.mem_iUnion.mpr ⟨j, hv, hj⟩
    rw [hAunion] at hcoverN hcardN
    have hNverts : N.verts ⊆ A (Fin.last m) ∪ ⋃ j, B (Fin.last m) j := by
      intro v hv
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hvertsN hv)
      rcases hj with hj | hj
      · exact Or.inl hj.1
      · exact Or.inr (Set.mem_iUnion.mpr ⟨j, hj⟩)
    have husedN : Disjoint used N.spanningCoe := hdisN.mono_left le_sup_left
    have hMN : ∀ i, Disjoint (M i).spanningCoe N.spanningCoe := by
      intro i
      exact hdisN.mono_left ((le_iSup (fun j ↦ (M j).spanningCoe) i).trans le_sup_right)
    refine ⟨Fin.snoc M N, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last =>
        simpa only [Fin.snoc_last] using ⟨hN, hcoverN, hNverts, hcardN, husedN⟩
      | cast i =>
        simpa only [Fin.snoc_castSucc, A₀, B₀] using hM i
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact (hij rfl).elim
        | cast j => simpa only [Fin.snoc_last, Fin.snoc_castSucc] using (hMN j).symm
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hMN i
        | cast j =>
          simpa only [Fin.snoc_castSucc] using
            hdis (fun heq ↦ hij (congrArg Fin.castSucc heq))

#print axioms exists_reservoir_repair_family

end Erdos19

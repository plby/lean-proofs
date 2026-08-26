import ErdosProblems.Erdos19.BufferedMatchingRepair
import ErdosProblems.Erdos19.MatchingFamilyDegrees
import Mathlib.Data.Fin.Tuple.Basic

/-! # Packing buffer-assisted matchings around a short family of forbidden sets -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem exists_buffered_matching_family (G used : _root_.SimpleGraph V)
    (U Y : Set V) (hUY : Disjoint U Y) (d load : ℕ)
    (hmissing : ∀ u ∈ U, (G.neighborSet u)ᶜ.ncard ≤ d)
    (hused : ∀ u ∈ U, (used.neighborSet u).ncard ≤ load) (m : ℕ) :
    ∀ C : Fin m → Set V, (∀ i, d + load + m ≤ (Y \ C i).ncard) →
    ∃ M : Fin m → G.Subgraph,
      (∀ i, (M i).IsMatching ∧ U \ C i ⊆ (M i).verts ∧
        (M i).verts ⊆ (U ∪ Y) \ C i ∧
        (M i).verts.ncard ≤ 2 * (U \ C i).ncard ∧ Disjoint used (M i).spanningCoe) ∧
      Pairwise fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe := by
  classical
  induction m with
  | zero =>
    intro C _
    exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ m ih =>
    intro C hbuffer
    let C₀ : Fin m → Set V := fun i ↦ C i.castSucc
    obtain ⟨M, hM, hdis⟩ := ih C₀ (fun i ↦ by
      dsimp only [C₀]
      have := hbuffer i.castSucc
      omega)
    let P := ⨆ i : Fin m, (M i).spanningCoe
    let used' := used ⊔ P
    let A := U \ C (Fin.last m)
    let B := Y \ C (Fin.last m)
    have hPdegree (v : V) : (P.neighborSet v).ncard ≤ m := by
      rw [matching_family_degree G M (fun i ↦ (hM i).1) hdis v]
      calc
        _ ≤ ∑ _i : Fin m, 1 := by
          apply sum_le_sum
          intro i _
          split_ifs <;> omega
        _ = m := by simp
    have hload : ∀ u ∈ A, (used'.neighborSet u).ncard ≤ load + m := by
      intro u hu
      have hcard : (used'.neighborSet u).ncard ≤
          (used.neighborSet u).ncard + (P.neighborSet u).ncard := by
        change ((used ⊔ P).neighborSet u).ncard ≤ _
        rw [neighborSet_sup]
        exact Set.ncard_union_le _ _
      exact hcard.trans (Nat.add_le_add (hused u hu.1) (hPdegree u))
    have hmiss : ∀ u ∈ A, ((A ∪ B) \ G.neighborSet u).ncard ≤ d := by
      intro u hu
      exact (Set.ncard_le_ncard (show (A ∪ B) \ G.neighborSet u ⊆
        (G.neighborSet u)ᶜ from fun _ h ↦ h.2)).trans (hmissing u hu.1)
    have hAB : Disjoint A B := hUY.mono Set.sdiff_subset Set.sdiff_subset
    have hB : d + (load + m) ≤ B.ncard := by
      have h := hbuffer (Fin.last m)
      change d + load + (m + 1) ≤ B.ncard at h
      omega
    obtain ⟨N, hN, hAN, hNB, hNcard, hdisN, _⟩ :=
      exists_buffered_matching_repair G used' A B d (load + m) hAB hB hmiss hload
    have hNverts : N.verts ⊆ (U ∪ Y) \ C (Fin.last m) := by
      intro v hv
      rcases hNB hv with hv | hv
      · exact ⟨Or.inl hv.1, hv.2⟩
      · exact ⟨Or.inr hv.1, hv.2⟩
    have husedN : Disjoint used N.spanningCoe := hdisN.mono_left le_sup_left
    have hMN : ∀ i, Disjoint (M i).spanningCoe N.spanningCoe := by
      intro i
      exact hdisN.mono_left ((le_iSup (fun j ↦ (M j).spanningCoe) i).trans le_sup_right)
    refine ⟨Fin.snoc M N, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last =>
        simpa only [Fin.snoc_last] using ⟨hN, hAN, hNverts, hNcard, husedN⟩
      | cast i =>
        simpa only [Fin.snoc_castSucc, C₀] using hM i
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

#print axioms exists_buffered_matching_family

end Erdos19

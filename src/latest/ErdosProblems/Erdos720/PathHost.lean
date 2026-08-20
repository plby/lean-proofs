import ErdosProblems.Erdos720.Analytic

open Finset
open scoped SimpleGraph

noncomputable section

namespace Erdos720

open SimpleGraph

lemma two_crossing_subsets {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (U W A D : Finset V)
    (hUW : Disjoint U W) (hU : U.card = 3 * k) (hW : W.card = 3 * k)
    (hAD : Disjoint A D) (hA : A.card = (5 * k) / 2) (hD : D.card = (5 * k) / 2)
    (hAsub : A ⊆ U ∪ W) (hDsub : D ⊆ U ∪ W) :
    (∃ X Y : Finset V, X ⊆ A ∩ U ∧ Y ⊆ D ∩ W ∧ X.card = k ∧ Y.card = k) ∨
    (∃ X Y : Finset V, X ⊆ A ∩ W ∧ Y ⊆ D ∩ U ∧ X.card = k ∧ Y.card = k) := by
  classical
  have hAU_AW : Disjoint (A ∩ U) (A ∩ W) := by
    rw [Finset.disjoint_left]
    intro x hxU hxW
    exact Finset.disjoint_left.mp hUW (Finset.mem_inter.mp hxU).2 (Finset.mem_inter.mp hxW).2
  have hDU_DW : Disjoint (D ∩ U) (D ∩ W) := by
    rw [Finset.disjoint_left]
    intro x hxU hxW
    exact Finset.disjoint_left.mp hUW (Finset.mem_inter.mp hxU).2 (Finset.mem_inter.mp hxW).2
  have hAunion : (A ∩ U) ∪ (A ∩ W) = A := by
    ext x
    simp only [mem_union, mem_inter]
    constructor
    · tauto
    · intro hx
      have := hAsub hx
      simp only [mem_union] at this
      tauto
  have hDunion : (D ∩ U) ∪ (D ∩ W) = D := by
    ext x
    simp only [mem_union, mem_inter]
    constructor
    · tauto
    · intro hx
      have := hDsub hx
      simp only [mem_union] at this
      tauto
  have hAcard : (A ∩ U).card + (A ∩ W).card = (5 * k) / 2 := by
    rw [← Finset.card_union_of_disjoint hAU_AW, hAunion, hA]
  have hDcard : (D ∩ U).card + (D ∩ W).card = (5 * k) / 2 := by
    rw [← Finset.card_union_of_disjoint hDU_DW, hDunion, hD]
  have hcapU : (A ∩ U).card + (D ∩ U).card ≤ 3 * k := by
    have hd : Disjoint (A ∩ U) (D ∩ U) :=
      Finset.disjoint_left.mpr fun x hxA hxD ↦
        Finset.disjoint_left.mp hAD (Finset.mem_inter.mp hxA).1 (Finset.mem_inter.mp hxD).1
    rw [← Finset.card_union_of_disjoint hd, ← hU]
    exact Finset.card_le_card (by intro x hx; simp only [mem_union, mem_inter] at hx; tauto)
  have hcapW : (A ∩ W).card + (D ∩ W).card ≤ 3 * k := by
    have hd : Disjoint (A ∩ W) (D ∩ W) :=
      Finset.disjoint_left.mpr fun x hxA hxD ↦
        Finset.disjoint_left.mp hAD (Finset.mem_inter.mp hxA).1 (Finset.mem_inter.mp hxD).1
    rw [← Finset.card_union_of_disjoint hd, ← hW]
    exact Finset.card_le_card (by intro x hx; simp only [mem_union, mem_inter] at hx; tauto)
  by_cases hAU : k ≤ (A ∩ U).card
  · by_cases hDW : k ≤ (D ∩ W).card
    · left
      obtain ⟨X, hX, hXcard⟩ := Finset.exists_subset_card_eq (s := A ∩ U) hAU
      obtain ⟨Y, hY, hYcard⟩ := Finset.exists_subset_card_eq (s := D ∩ W) hDW
      exact ⟨X, Y, hX, hY, hXcard, hYcard⟩
    · have hDU : k ≤ (D ∩ U).card := by
        by_contra h
        omega
      have hAW : k ≤ (A ∩ W).card := by
        by_contra h
        omega
      right
      obtain ⟨X, hX, hXcard⟩ := Finset.exists_subset_card_eq (s := A ∩ W) hAW
      obtain ⟨Y, hY, hYcard⟩ := Finset.exists_subset_card_eq (s := D ∩ U) hDU
      exact ⟨X, Y, hX, hY, hXcard, hYcard⟩
  · by_cases hDU : k ≤ (D ∩ U).card
    · have hAW : k ≤ (A ∩ W).card := by
        by_contra h
        omega
      right
      obtain ⟨X, hX, hXcard⟩ := Finset.exists_subset_card_eq (s := A ∩ W) hAW
      obtain ⟨Y, hY, hYcard⟩ := Finset.exists_subset_card_eq (s := D ∩ U) hDU
      exact ⟨X, Y, hX, hY, hXcard, hYcard⟩
    · have hDW : k ≤ (D ∩ W).card := by
        by_contra h
        omega
      have hAW : k ≤ (A ∩ W).card := by
        by_contra h
        omega
      exfalso
      omega

lemma sparse_noHole_arrows_path (k : ℕ) (hk : 16 ≤ k) :
    ∃ H : SimpleGraph (Fin (7 * k)), Nat.card H.edgeSet ≤ 3136 * k ∧
      Arrows H (pathGraph k) := by
  classical
  obtain ⟨H, hHedges, hhole⟩ := exists_sparse_noHole_graph k hk
  refine ⟨H, hHedges, ?_⟩
  intro R hRH
  by_cases hRpath : pathGraph k ⊑ R
  · exact Or.inl hRpath
  by_cases hBpath : pathGraph k ⊑ H \ R
  · exact Or.inr hBpath
  exfalso
  have hkpos : 0 < k := by omega
  obtain ⟨U, W, hUcard, hWcard, hUW, hred⟩ :=
    exists_anticomplete_sets_of_path_free R (3 * k) k hkpos (by simp; omega) hRpath
  let T : Set (Fin (7 * k)) := ↑(U ∪ W)
  let B : SimpleGraph T := (H \ R).induce T
  have hBfree : ¬ pathGraph k ⊑ B := by
    intro hpath
    exact hBpath (hpath.trans (SimpleGraph.Embedding.induce (G := H \ R) T).isContained)
  have hcardT : Fintype.card T = 6 * k := by
    simp [T, Finset.card_union_of_disjoint hUW, hUcard, hWcard]
    omega
  have hsepSize : 2 * ((5 * k) / 2) + k ≤ Fintype.card T + 1 := by
    rw [hcardT]
    omega
  obtain ⟨A₀, D₀, hA₀card, hD₀card, hA₀D₀, hblue₀⟩ :=
    exists_anticomplete_sets_of_path_free B ((5 * k) / 2) k hkpos hsepSize hBfree
  let valEmb : T ↪ Fin (7 * k) := ⟨Subtype.val, Subtype.val_injective⟩
  let A := A₀.map valEmb
  let D := D₀.map valEmb
  have hAcard : A.card = (5 * k) / 2 := by simp [A, hA₀card]
  have hDcard : D.card = (5 * k) / 2 := by simp [D, hD₀card]
  have hAD : Disjoint A D := by
    simp only [A, D, Finset.disjoint_map]
    exact hA₀D₀
  have hAsub : A ⊆ U ∪ W := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨x, hxA, rfl⟩
    exact x.property
  have hDsub : D ⊆ U ∪ W := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨x, hxD, rfl⟩
    exact x.property
  have hblue : ∀ a ∈ A, ∀ d ∈ D, ¬ (H \ R).Adj a d := by
    intro a ha d hd
    rcases Finset.mem_map.mp ha with ⟨a₀, ha₀, rfl⟩
    rcases Finset.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    simpa [B, SimpleGraph.induce, valEmb] using hblue₀ a₀ ha₀ d₀ hd₀
  rcases two_crossing_subsets k U W A D hUW hUcard hWcard hAD hAcard hDcard hAsub hDsub with
    ⟨X, Y, hX, hY, hXcard, hYcard⟩ | ⟨X, Y, hX, hY, hXcard, hYcard⟩
  · obtain ⟨x, hx, y, hy, hHxy⟩ := hhole X Y hXcard hYcard (by
      exact hUW.mono (hX.trans Finset.inter_subset_right) (hY.trans Finset.inter_subset_right))
    have hxmem := Finset.mem_inter.mp (hX hx)
    have hymem := Finset.mem_inter.mp (hY hy)
    have hxA : x ∈ A := hxmem.1
    have hyD : y ∈ D := hymem.1
    have hnR : ¬ R.Adj x y := hred x hxmem.2 y hymem.2
    have hnB : ¬ (H \ R).Adj x y := hblue x hxA y hyD
    exact hnB ((SimpleGraph.sdiff_adj H R x y).2 ⟨hHxy, hnR⟩)
  · obtain ⟨x, hx, y, hy, hHxy⟩ := hhole X Y hXcard hYcard (by
      exact hUW.symm.mono (hX.trans Finset.inter_subset_right) (hY.trans Finset.inter_subset_right))
    have hxmem := Finset.mem_inter.mp (hX hx)
    have hymem := Finset.mem_inter.mp (hY hy)
    have hxA : x ∈ A := hxmem.1
    have hyD : y ∈ D := hymem.1
    have hnR : ¬ R.Adj x y := fun hxy ↦ hred y hymem.2 x hxmem.2 hxy.symm
    have hnB : ¬ (H \ R).Adj x y := hblue x hxA y hyD
    exact hnB ((SimpleGraph.sdiff_adj H R x y).2 ⟨hHxy, hnR⟩)

lemma sizeRamsey_path_le (k : ℕ) (hk : 16 ≤ k) :
    sizeRamsey (pathGraph k) ≤ 3136 * k := by
  obtain ⟨H, hE, hA⟩ := sparse_noHole_arrows_path k hk
  exact (sizeRamsey_le_of_witness
    ⟨7 * k, H, rfl, hA⟩).trans hE

end Erdos720

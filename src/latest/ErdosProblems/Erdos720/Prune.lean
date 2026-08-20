import ErdosProblems.Erdos720.Connector

namespace Erdos720

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def subtypeFinset {Z : Finset V} (S : Finset {v // v ∈ Z}) : Finset V :=
  S.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] lemma mem_subtypeFinset {Z : Finset V} {S : Finset {v // v ∈ Z}} {v : V} :
    v ∈ subtypeFinset S ↔ ∃ h : v ∈ Z, (⟨v, h⟩ : {v // v ∈ Z}) ∈ S := by
  classical
  simp [subtypeFinset]

lemma card_subtypeFinset {Z : Finset V} (S : Finset {v // v ∈ Z}) :
    (subtypeFinset S).card = S.card := by
  classical
  simp [subtypeFinset]

lemma subtypeFinset_subset {Z : Finset V} (S : Finset {v // v ∈ Z}) :
    subtypeFinset S ⊆ Z := by
  intro v hv
  simpa using (mem_subtypeFinset.mp hv).choose

lemma induced_neighbors_map {G : SimpleGraph V} {Z : Finset V}
    (S : Finset {v // v ∈ Z}) :
    subtypeFinset (setNeighbors (G.induce (↑Z : Set V)) S) =
      setNeighbors G (subtypeFinset S) ∩ Z := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨hvZ, hvN⟩ := mem_subtypeFinset.mp hv
    obtain ⟨x, hxS, hxv⟩ := mem_setNeighbors.mp hvN
    apply mem_inter.mpr
    refine ⟨mem_setNeighbors.mpr ?_, hvZ⟩
    exact ⟨x.1, mem_subtypeFinset.mpr ⟨x.2, hxS⟩, hxv⟩
  · intro hv
    obtain ⟨hvN, hvZ⟩ := mem_inter.mp hv
    obtain ⟨x, hxS, hxv⟩ := mem_setNeighbors.mp hvN
    obtain ⟨hxZ, hxSub⟩ := mem_subtypeFinset.mp hxS
    apply mem_subtypeFinset.mpr
    refine ⟨hvZ, mem_setNeighbors.mpr ?_⟩
    exact ⟨⟨x, hxZ⟩, hxSub, hxv⟩

lemma card_induced_neighbors {G : SimpleGraph V} {Z : Finset V}
    (S : Finset {v // v ∈ Z}) :
    (setNeighbors (G.induce (↑Z : Set V)) S).card =
      (setNeighbors G (subtypeFinset S) ∩ Z).card := by
  rw [← induced_neighbors_map S, card_subtypeFinset]

/-- Deleting one maximal poorly expanding set leaves a large induced
4-expander.  The constants are chosen for the later double-binary-tree
connector. -/
lemma prune_bipartite_no_hole (G : SimpleGraph V) (X Y : Finset V) (m : ℕ)
    (hm : 1 ≤ m) (hXY : Disjoint X Y) (hcover : X ∪ Y = univ)
    (hXcard : X.card = 128 * m) (hYcard : Y.card = 128 * m)
    (hnoHole : ∀ A B : Finset V, A ⊆ X → B ⊆ Y →
      A.card = m → B.card = m → ∃ a ∈ A, ∃ b ∈ B, G.Adj a b) :
    ∃ Z : Finset V, 118 * m ≤ Z.card ∧ Nonempty {v // v ∈ Z} ∧
      ∀ S : Finset {v // v ∈ Z}, S.card ≤ 18 * m →
        4 * S.card ≤ (setNeighbors (G.induce (↑Z : Set V)) S).card := by
  classical
  let candidates : Finset (Finset V) := Finset.univ.filter fun W =>
    W = ∅ ∨ (W.card ≤ 20 * m ∧ (setNeighbors G W).card < 4 * W.card)
  have hempty : ∅ ∈ candidates := by simp [candidates]
  let sizes : Finset ℕ := candidates.image Finset.card
  have hsizes : sizes.Nonempty := ⟨0, by
    exact mem_image.mpr ⟨∅, hempty, by simp⟩⟩
  let q := sizes.max' hsizes
  have hqmem : q ∈ sizes := max'_mem _ _
  obtain ⟨W, hWcand, hWcard⟩ := mem_image.mp hqmem
  have hmax : ∀ U ∈ candidates, U.card ≤ W.card := by
    intro U hU
    have hUc : U.card ∈ sizes := mem_image.mpr ⟨U, hU, rfl⟩
    rw [hWcard]
    exact le_max' sizes U.card hUc
  have hWdescr : W = ∅ ∨
      (W.card ≤ 20 * m ∧ (setNeighbors G W).card < 4 * W.card) := by
    simpa [candidates] using hWcand
  have hWsmall : W.card < 2 * m := by
    rcases hWdescr with rfl | hbad
    · simpa using (show 0 < 2 * m by omega)
    · by_contra hnot
      have htwo : 2 * m ≤ W.card := Nat.le_of_not_gt hnot
      have hWXUY : W = (W ∩ X) ∪ (W ∩ Y) := by
        ext v
        constructor
        · intro hvW
          have hvcover : v ∈ X ∪ Y := hcover.symm ▸ mem_univ v
          rcases mem_union.mp hvcover with hvX | hvY
          · exact mem_union_left _ (mem_inter.mpr ⟨hvW, hvX⟩)
          · exact mem_union_right _ (mem_inter.mpr ⟨hvW, hvY⟩)
        · intro hv
          rcases mem_union.mp hv with hv | hv
          · exact (mem_inter.mp hv).1
          · exact (mem_inter.mp hv).1
      have hparts : W.card = (W ∩ X).card + (W ∩ Y).card := by
        calc
          W.card = ((W ∩ X) ∪ (W ∩ Y)).card := congrArg card hWXUY
          _ = (W ∩ X).card + (W ∩ Y).card :=
            card_union_of_disjoint (hXY.mono inter_subset_right inter_subset_right)
      have hside : m ≤ (W ∩ X).card ∨ m ≤ (W ∩ Y).card := by omega
      have hN80 : (setNeighbors G W).card < 80 * m := by omega
      rcases hside with hside | hside
      · obtain ⟨A, hA, hAcard⟩ := exists_subset_card_eq hside
        have htarget : m ≤ (Y \ setNeighbors G W).card := by
          rw [Finset.card_sdiff]
          have hinter : (setNeighbors G W ∩ Y).card ≤ (setNeighbors G W).card :=
            card_le_card inter_subset_left
          rw [hYcard]
          omega
        obtain ⟨B, hB, hBcard⟩ := exists_subset_card_eq htarget
        obtain ⟨a, ha, b, hb, hab⟩ := hnoHole A B
          (hA.trans inter_subset_right) (hB.trans sdiff_subset) hAcard hBcard
        have haW : a ∈ W := inter_subset_left (hA ha)
        have hbnot : b ∉ setNeighbors G W := (mem_sdiff.mp (hB hb)).2
        exact hbnot (mem_setNeighbors.mpr ⟨a, haW, hab⟩)
      · obtain ⟨B, hB, hBcard⟩ := exists_subset_card_eq hside
        have htarget : m ≤ (X \ setNeighbors G W).card := by
          rw [Finset.card_sdiff]
          have hinter : (setNeighbors G W ∩ X).card ≤ (setNeighbors G W).card :=
            card_le_card inter_subset_left
          rw [hXcard]
          omega
        obtain ⟨A, hA, hAcard⟩ := exists_subset_card_eq htarget
        obtain ⟨a, ha, b, hb, hab⟩ := hnoHole A B
          (hA.trans sdiff_subset) (hB.trans inter_subset_right) hAcard hBcard
        have hbW : b ∈ W := inter_subset_left (hB hb)
        have hanot : a ∉ setNeighbors G W := (mem_sdiff.mp (hA ha)).2
        exact hanot (mem_setNeighbors.mpr ⟨b, hbW, (G.adj_comm _ _).mp hab⟩)
  have hNW : (setNeighbors G W).card ≤ 4 * W.card := by
    rcases hWdescr with rfl | hbad
    · simp
    · exact Nat.le_of_lt hbad.2
  let Z := univ \ (W ∪ setNeighbors G W)
  have hremoved : (W ∪ setNeighbors G W).card < 10 * m := by
    calc
      (W ∪ setNeighbors G W).card
          ≤ W.card + (setNeighbors G W).card := card_union_le _ _
      _ ≤ W.card + 4 * W.card := Nat.add_le_add_left hNW _
      _ < 10 * m := by omega
  have hVcard : Fintype.card V = 256 * m := by
    rw [← card_univ, ← hcover, card_union_of_disjoint hXY, hXcard, hYcard]
    omega
  have hZcard : 118 * m ≤ Z.card := by
    rw [show Z = univ \ (W ∪ setNeighbors G W) by rfl,
      card_sdiff_of_subset (subset_univ _), card_univ, hVcard]
    omega
  have hZnonempty : Nonempty {v // v ∈ Z} := by
    have : 0 < Z.card := by omega
    obtain ⟨z, hz⟩ := card_pos.mp this
    exact ⟨⟨z, hz⟩⟩
  refine ⟨Z, hZcard, hZnonempty, ?_⟩
  intro S hScard
  rw [card_induced_neighbors]
  let U := subtypeFinset S
  have hUcard : U.card = S.card := card_subtypeFinset S
  by_contra hfail
  have hbadrem : (setNeighbors G U ∩ Z).card < 4 * U.card := by
    have hraw : (setNeighbors G (subtypeFinset S) ∩ Z).card < 4 * S.card := by
      omega
    simpa [U, hUcard] using hraw
  have hUW : Disjoint U W := by
    rw [Finset.disjoint_left]
    intro v hvU hvW
    have hvZ := subtypeFinset_subset S hvU
    exact (mem_sdiff.mp hvZ).2 (mem_union_left _ hvW)
  let T := W ∪ U
  have hTcard : T.card = W.card + U.card := by
    rw [show T = W ∪ U by rfl, card_union_of_disjoint hUW.symm]
  have hTsmall : T.card ≤ 20 * m := by
    rw [hTcard, hUcard]
    omega
  have hNsub : setNeighbors G T ⊆
      setNeighbors G W ∪ (setNeighbors G U ∩ Z) := by
    intro v hv
    rw [show T = W ∪ U by rfl, setNeighbors_union] at hv
    rcases mem_union.mp hv with hvW | hvU
    · exact mem_union_left _ hvW
    · by_cases hvZ : v ∈ Z
      · exact mem_union_right _ (mem_inter.mpr ⟨hvU, hvZ⟩)
      · have hvRemoved : v ∈ W ∪ setNeighbors G W := by
          have : v ∈ (univ \ Z) := mem_sdiff.mpr ⟨mem_univ _, hvZ⟩
          simpa [Z] using this
        rcases mem_union.mp hvRemoved with hvWin | hvNW
        · exfalso
          obtain ⟨u, hu, huv⟩ := mem_setNeighbors.mp hvU
          have huZ := subtypeFinset_subset S hu
          exact (mem_sdiff.mp huZ).2 (mem_union_right _
            (mem_setNeighbors.mpr ⟨v, hvWin, (G.adj_comm _ _).mp huv⟩))
        · exact mem_union_left _ hvNW
  have hTbad : (setNeighbors G T).card < 4 * T.card := by
    have hc := card_le_card hNsub
    have hu := card_union_le (setNeighbors G W) (setNeighbors G U ∩ Z)
    rw [hTcard]
    omega
  have hTcand : T ∈ candidates := by
    exact mem_filter.mpr ⟨mem_univ _, Or.inr ⟨hTsmall, hTbad⟩⟩
  have hUpos : 0 < U.card := by
    by_contra hzero
    have : U = ∅ := card_eq_zero.mp (Nat.eq_zero_of_not_pos hzero)
    rw [this, setNeighbors_empty, empty_inter] at hbadrem
    simp at hbadrem
  have hlarger : W.card < T.card := by rw [hTcard]; omega
  exact (not_lt_of_ge (hmax T hTcand)) hlarger

end Erdos720

import ErdosProblems.Erdos577.JointThreeOldCounts

/-! The two triangle-gain constructions exclude the first adjacent old-terminal row. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma triple_last_split (v : Quadrilateral G) (a b c : V)
    (ha : a ∉ v.support) (hb : b ∉ v.support) (hc : c ∉ v.support)
    (hab : a ≠ b) (hac : a ≠ c) :
    Disjoint ({a, v 2, v 3} : Finset V) {b, c, v 0, v 1} ∧
      ({a, v 2, v 3} : Finset V) ∪ {b, c, v 0, v 1} = insert a ({b, c} ∪ v.support) := by
  obtain ⟨hd, he⟩ := triple_edge_split (v.rotate 3) a b c
    (by rwa [Quadrilateral.rotate_support]) (by rwa [Quadrilateral.rotate_support])
    (by rwa [Quadrilateral.rotate_support]) hab hac
  change Disjoint ({a, v 3, v 2} : Finset V) {b, c, v 0, v 1} at hd
  change ({a, v 3, v 2} : Finset V) ∪ {b, c, v 0, v 1} =
    insert a ({b, c} ∪ (v.rotate 3).support) at he
  rw [pair_comm (v 3) (v 2)] at hd he
  rw [Quadrilateral.rotate_support] at he
  exact ⟨hd, he⟩

lemma triple_first_split (v : Quadrilateral G) (a b c : V)
    (ha : a ∉ v.support) (hb : b ∉ v.support) (hc : c ∉ v.support)
    (hab : a ≠ b) (hac : a ≠ c) :
    Disjoint ({a, v 0, v 1} : Finset V) {b, c, v 2, v 3} ∧
      ({a, v 0, v 1} : Finset V) ∪ {b, c, v 2, v 3} = insert a ({b, c} ∪ v.support) := by
  obtain ⟨hd, he⟩ := triple_edge_split (v.rotate 1) a b c
    (by rwa [Quadrilateral.rotate_support]) (by rwa [Quadrilateral.rotate_support])
    (by rwa [Quadrilateral.rotate_support]) hab hac
  change Disjoint ({a, v 1, v 0} : Finset V) {b, c, v 2, v 3} at hd
  change ({a, v 1, v 0} : Finset V) ∪ {b, c, v 2, v 3} =
    insert a ({b, c} ∪ (v.rotate 1).support) at he
  rw [pair_comm (v 1) (v 0)] at hd he
  rw [Quadrilateral.rotate_support] at he
  exact ⟨hd, he⟩

variable [DecidableRel G.Adj]

theorem FinalRows.three_old_first_false {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3)
    (hxrow : ∀ i : Fin 4, G.Adj x (v i) ↔ (3 : ℕ).testBit i.val = true) : False := by
  obtain ⟨_, hw3, hwchoice, _, _, hyrow⟩ := h.three_old_counts hz hxrow
  have hdiag := h.toPairRows.three_low_diagonal_absent hz
  obtain ⟨_, hxz, hxw, hyz, hyw, hzw⟩ := JointCore.four_distinct h.distinct
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hx0 := (hxrow 0).mpr (by decide)
  have hx1 := (hxrow 1).mpr (by decide)
  have hrep : QuadOn G (insert w (v.support.erase (v 1))) := by
    rcases hwchoice with hw0 | hw2
    · have hyo : y ∉ ({z, v 1, v 2} : Finset V) := by
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨hyz, fun he ↦ h.y_out (he.symm ▸ hm 1), fun he ↦ h.y_out (he.symm ▸ hm 2)⟩
      obtain ⟨hquad, hfive⟩ := shared_pair_five z y (v 1) (v 2) hyo
        (h.three 1 (by decide)) (h.three 2 (by decide)) (v.adjacent 1)
        ((hyrow 1).mpr (by decide)) ((hyrow 2).mpr (by decide))
      have ht : G.IsNClique 3 {w, v 0, v 3} :=
        SimpleGraph.is3Clique_triple_iff.mpr ⟨hw0, hw3, (v.adjacent 3).symm⟩
      obtain ⟨hdis, hcover⟩ := triple_edge_split v w z y h.w_out h.z_out h.y_out hzw.symm hyw.symm
      have hcover' : ({w, v 0, v 3} : Finset V) ∪ {z, y, v 1, v 2} =
          insert y ({z, w} ∪ v.support) := by
        rw [hcover]
        simp only [insert_union, singleton_union]
        rw [insert_comm z y, insert_comm w y, insert_comm w z]
      have hhigh := h.high_diagonal_of_gain hdiag y (Or.inr rfl) ht hquad hdis hcover' hfive
      exact v.replace_using_path w h.w_out 1 0 2 3 (by decide) (by decide)
        hw0 hhigh (v.adjacent 2) hw3
    · have hzo : z ∉ ({x, v 0, v 1} : Finset V) := by
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨hxz.symm, fun he ↦ h.z_out (he.symm ▸ hm 0), fun he ↦ h.z_out (he.symm ▸ hm 1)⟩
      obtain ⟨hquad, hfive⟩ := shared_pair_five x z (v 0) (v 1) hzo
        hx0 hx1 (v.adjacent 0) (h.three 0 (by decide)) (h.three 1 (by decide))
      have ht : G.IsNClique 3 {w, v 2, v 3} :=
        SimpleGraph.is3Clique_triple_iff.mpr ⟨hw2, hw3, v.adjacent 2⟩
      obtain ⟨hdis, hcover⟩ := triple_last_split v w x z h.w_out h.x_out h.z_out hxw.symm hzw.symm
      have hcover' : ({w, v 2, v 3} : Finset V) ∪ {x, z, v 0, v 1} =
          insert x ({z, w} ∪ v.support) := by
        rw [hcover]
        simp only [insert_union, singleton_union]
        rw [insert_comm w x, insert_comm w z]
      have hhigh := h.high_diagonal_of_gain hdiag x (Or.inl rfl) ht hquad hdis hcover' hfive
      exact v.replace_using_path w h.w_out 1 2 0 3 (by decide) (by decide)
        hw2 hhigh.symm (v.adjacent 3).symm hw3
  exact h.no_xz_w ⟨v 1, hm 1, hx1, h.three 1 (by decide), hrep⟩

end Erdos577.JointFinal

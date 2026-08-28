import ErdosProblems.Erdos577.FullLeafHeavyLeafRowBounds

/-! A marked-leaf contact forces equality in the center and second-side bounds. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem marked_common_false (q : Quadrilateral G) (t : Finset V) (ht : t.card = 5)
    (hd : Disjoint t q.support) (hsixteen : 16 ≤ contacts G t q.support)
    (leaf center : V) (hcontact : G.Adj leaf (q 0)) (hcenter : 4 ≤ degreeIn G center t)
    (hforbidden : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → G.Adj v center →
      ¬CommonReplacement G leaf v u q.support) :
    ∀ v ∈ t, G.Adj v center → ¬G.Adj v (q 0) := by
  intro v hv hvc hv0
  have hmem : q 0 ∈ q.support := (q.mem_support _).mpr ⟨0, rfl⟩
  have hno (u : V) (hu : u ∈ t) (huv : u ≠ v) : ¬(G.Adj u (q 1) ∧ G.Adj u (q 3)) := by
    rintro ⟨hu1, hu3⟩
    exact hforbidden u hu v hv huv hvc ⟨q 0, hmem, hcontact, hv0,
      JointFinal.low_pair_replace q u (fun hh ↦ disjoint_left.mp hd hu hh) hu1 hu3 0 (Or.inl rfl)⟩
  have hrows (u : V) (hu : u ∈ t) (huv : u ≠ v) : degreeIn G u q.support ≤ 3 := by
    have hb := degree_le_two_add_first_of_no_low_pair q u (hno u hu huv)
    split_ifs at hb <;> omega
  have hfull := full_of_other_rows_three q t ht hsixteen hv hrows
  have hlarge : 1 < (t.filter (G.Adj center)).card := by
    change 1 < degreeIn G center t
    omega
  obtain ⟨u, hu, huv⟩ := exists_mem_ne hlarge v
  obtain ⟨hut, hcu⟩ := mem_filter.mp hu
  have hu3 := row_ge_three_of_other_rows_three q t ht hsixteen hv hrows hut huv
  have hu0 : G.Adj u (q 0) := by
    by_contra hnot
    have hb := degree_le_two_add_first_of_no_low_pair q u (hno u hut huv)
    rw [if_neg hnot] at hb
    omega
  have hrep := (show QuadOn G q.support from ⟨q, rfl⟩).replace_of_degree_four
    (fun hh ↦ disjoint_left.mp hd hv hh) hfull hmem
  exact hforbidden v hv u hut huv.symm hcu.symm ⟨q 0, hmem, hcontact, hu0, hrep⟩

theorem marked_contact_center_eq_four (q : Quadrilateral G) (t : Finset V) (ht : t.card = 5)
    (hd : Disjoint t q.support) (hsixteen : 16 ≤ contacts G t q.support)
    (leaf center : V) (hcontact : G.Adj leaf (q 0)) (hcenter : 4 ≤ degreeIn G center t)
    (hforbidden : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → G.Adj v center →
      ¬CommonReplacement G leaf v u q.support) :
    degreeIn G center t = 4 ∧ contacts G t q.support = 16 := by
  have hno := marked_common_false q t ht hd hsixteen leaf center hcontact hcenter hforbidden
  have hdis : Disjoint (t.filter (G.Adj center)) (t.filter (G.Adj (q 0))) := by
    apply disjoint_left.mpr
    intro v hv hv0
    obtain ⟨hvt, hcv⟩ := mem_filter.mp hv
    exact hno v hvt hcv.symm (mem_filter.mp hv0).2.symm
  have hb : ((t.filter (G.Adj center)) ∪ (t.filter (G.Adj (q 0)))).card ≤ 5 :=
    (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans_eq ht
  rw [card_union_of_disjoint hdis] at hb
  change degreeIn G center t + degreeIn G (q 0) t ≤ 5 at hb
  have h1 := degreeIn_le_card G (q 1) t
  have h2 := degreeIn_le_card G (q 2) t
  have h3 := degreeIn_le_card G (q 3) t
  rw [ht] at h1 h2 h3
  have hsum := columns_sum q t
  exact ⟨by omega, by omega⟩

theorem marked_positive_center_eq_four (q : Quadrilateral G) (t : Finset V) (ht : t.card = 5)
    (hd : Disjoint t q.support) (hsixteen : 16 ≤ contacts G t q.support)
    (leaf center : V) (hpositive : 1 ≤ degreeIn G leaf q.support)
    (hcenter : 4 ≤ degreeIn G center t)
    (hforbidden : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → G.Adj v center →
      ¬CommonReplacement G leaf v u q.support) :
    degreeIn G center t = 4 ∧ contacts G t q.support = 16 := by
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (q.support.filter (G.Adj leaf)).card by
    change 0 < degreeIn G leaf q.support
    omega)
  obtain ⟨hvq, hlv⟩ := mem_filter.mp hv
  obtain ⟨i, rfl⟩ := (q.mem_support v).mp hvq
  have hh := marked_contact_center_eq_four (q.rotate i) t ht
    (by rwa [q.rotate_support]) (by rwa [q.rotate_support]) leaf center
    (by simpa only [Quadrilateral.rotate_apply, zero_add] using hlv) hcenter
    (by simpa only [q.rotate_support] using hforbidden)
  simpa only [q.rotate_support] using hh

end Erdos577.FullLeafHeavy

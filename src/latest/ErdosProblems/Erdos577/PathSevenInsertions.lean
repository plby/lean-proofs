import ErdosProblems.Erdos577.CliqueReplacementObstructions
import ErdosProblems.Erdos577.PathSaturatedRows

/-! The seven insertion prohibitions of pattern (19) bound the paired path count by sixteen. -/

namespace Erdos577.PathBlock

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Rows correspond, in order, to the seven explicit local path partitions. -/
structure SevenInsertionsExcluded (p : FourPath G) (s : Finset V) (x y : V) : Prop where
  row1 : ¬CommonReplacement G (p.vertices 2) (p.vertices 1) (p.vertices 3) s
  row2 : ¬CommonReplacement G (p.vertices 3) (p.vertices 1) x s
  row3 : ¬CommonReplacement G (p.vertices 0) (p.vertices 2) y s
  row4 : ¬CommonReplacement G x (p.vertices 0) (p.vertices 1) s
  row5 : ¬CommonReplacement G x (p.vertices 2) (p.vertices 1) s
  row6 : ¬CommonReplacement G x (p.vertices 3) (p.vertices 2) s
  row7 : ¬CommonReplacement G y (p.vertices 3) (p.vertices 2) s

variable [DecidableRel G.Adj]

lemma PatternA.seven_insertions_bound (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hcl : G.IsNClique 4 q.support)
    (h : PatternA p q) (hh : 9 ≤ contacts G p.support q.support)
    (hmax : contacts G p.support q.support ≤ 10) (x y : V) (hy : y ∉ q.support)
    (hn : SevenInsertionsExcluded p q.support x y) :
    contacts G p.support q.support + degreeIn G (p.vertices 3) q.support +
      degreeIn G (p.vertices 2) q.support + degreeIn G x q.support +
        degreeIn G y q.support ≤ 16 := by
  have hcout : p.vertices 1 ∉ q.support := by
    intro hv
    exact disjoint_left.mp hd ((p.mem_support _).mpr ⟨1, rfl⟩) hv
  have hsum := p.contacts_support q.support
  have hXw := no_common_replacement_degree_sum hcl x (p.vertices 0) (p.vertices 1)
    hcout h.2.1 hn.row4
  have hXr := no_common_replacement_degree_sum hcl x (p.vertices 2) (p.vertices 1)
    hcout h.2.1 hn.row5
  have hr : degreeIn G (p.vertices 2) q.support ≤ 3 := by
    have hbits : ∀ j : Fin 4, j ≠ 3 → (7 : ℕ).testBit j.val = true := by decide +kernel
    have hb := q.degree_le_mask (p.vertices 2) 7 (fun j hj ↦ hbits j (h.1 j (Or.inr hj)))
    have he : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
    rwa [he] at hb
  have hzero := h.2.2.2
  have hcmax := h.2.2.1
  have hwr : 4 < degreeIn G (p.vertices 0) q.support + degreeIn G (p.vertices 2) q.support := by
    omega
  have hbound : ((q.support.filter (G.Adj (p.vertices 0))) ∪
      (q.support.filter (G.Adj (p.vertices 2)))).card ≤ 4 := by
    exact (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans
      (le_of_eq q.card_support)
  have hcommon := common_neighbor_of_union_bound (p.vertices 0) (p.vertices 2)
    q.support 4 hbound hwr
  have hY := no_common_replacement_degree_le_two hcl (p.vertices 0) (p.vertices 2) y hy
    hn.row3 hcommon
  omega

lemma PatternB.seven_insertions_bound (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hcl : G.IsNClique 4 q.support)
    (h : PatternB p q) (hh : 9 ≤ contacts G p.support q.support)
    (x y : V) (hx : x ∉ q.support) (hy : y ∉ q.support)
    (hn : SevenInsertionsExcluded p q.support x y) :
    contacts G p.support q.support + degreeIn G (p.vertices 3) q.support +
      degreeIn G (p.vertices 2) q.support + degreeIn G x q.support +
        degreeIn G y q.support ≤ 16 := by
  have hout (i : Fin 4) : p.vertices i ∉ q.support := by
    intro hv
    exact disjoint_left.mp hd ((p.mem_support _).mpr ⟨i, rfl⟩) hv
  obtain ⟨h0, h1, h2, h3⟩ := h.row_bounds p q
  have hsum := p.contacts_support q.support
  have hnot : ¬(degreeIn G (p.vertices 1) q.support = 3 ∧
      degreeIn G (p.vertices 2) q.support = 3 ∧ degreeIn G (p.vertices 3) q.support = 2) := by
    rintro ⟨hc, hr, hleaf⟩
    have hcv := h.full_middle_adj p q 1 hc 2 (by decide)
    have hrv := h.full_middle_adj p q 2 hr 2 (by decide)
    have hvq : q 2 ∈ q.support := (q.mem_support _).mpr ⟨2, rfl⟩
    have hxv : ¬G.Adj (p.vertices 3) (q 2) := by
      intro hbad
      have hh := h.1 2 (Or.inr hbad)
      omega
    have he := degreeIn_erase_add G (p.vertices 3) (q 2) hvq
    rw [if_neg hxv] at he
    have hrep : QuadOn G (insert (p.vertices 3) (q.support.erase (q 2))) :=
      (clique_replace_iff_two_contacts hcl (hout 3) hvq).mpr (by omega)
    exact hn.row1 ⟨q 2, hvq, hrv, hcv, hrep⟩
  have htotal : contacts G p.support q.support = 9 := by omega
  have hw : degreeIn G (p.vertices 0) q.support = 2 := by omega
  have hxc := common_neighbor_of_union_bound (p.vertices 3) (p.vertices 1) q.support 3
    (h.union_le_three p q 3 1) (by omega)
  have hwr := common_neighbor_of_union_bound (p.vertices 0) (p.vertices 2) q.support 3
    (h.union_le_three p q 0 2) (by omega)
  have hy2 := no_common_replacement_degree_le_two hcl (p.vertices 0) (p.vertices 2) y hy
    hn.row3 hwr
  obtain ⟨u, hu, hxu, hcu⟩ := hxc
  by_cases hc : degreeIn G (p.vertices 1) q.support = 3
  · have hwu := h.full_endpoint_contains p q 0 3 (Or.inl rfl) (Or.inr rfl) hw u hu hxu
    have hXu : ¬G.Adj x u := by
      intro hhx
      exact hn.row4 ⟨u, hu, hhx, hwu,
        clique_replace_of_degree_three hcl (hout 1) (by omega) hu⟩
    have hx1 := no_common_replacement_degree_le_one hcl (p.vertices 3) (p.vertices 1) x hx
      hn.row2 u hu hxu hcu hXu
    omega
  · have hr : degreeIn G (p.vertices 2) q.support = 3 := by omega
    have hleaf : degreeIn G (p.vertices 3) q.support = 2 := by omega
    have hXu : ¬G.Adj x u := by
      intro hhx
      exact hn.row6 ⟨u, hu, hhx, hxu,
        clique_replace_of_degree_three hcl (hout 2) (by omega) hu⟩
    have hx1 := no_common_replacement_degree_le_one hcl (p.vertices 3) (p.vertices 1) x hx
      hn.row2 u hu hxu hcu hXu
    obtain ⟨v, hv, hwv, hrv⟩ := hwr
    have hxv := h.full_endpoint_contains p q 3 0 (Or.inr rfl) (Or.inl rfl) hleaf v hv hwv
    have hYv : ¬G.Adj y v := by
      intro hhy
      exact hn.row7 ⟨v, hv, hhy, hxv,
        clique_replace_of_degree_three hcl (hout 2) (by omega) hv⟩
    have hy1 := no_common_replacement_degree_le_one hcl (p.vertices 0) (p.vertices 2) y hy
      hn.row3 v hv hwv hrv hYv
    omega

lemma Classified.seven_insertions_bound (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hcl : G.IsNClique 4 q.support)
    (h : Classified p q) (hh : 9 ≤ contacts G p.support q.support)
    (x y : V) (hx : x ∉ q.support) (hy : y ∉ q.support)
    (hn : SevenInsertionsExcluded p q.support x y) :
    contacts G p.support q.support + degreeIn G (p.vertices 3) q.support +
      degreeIn G (p.vertices 2) q.support + degreeIn G x q.support +
        degreeIn G y q.support ≤ 16 := by
  obtain ⟨hmax, rev, q', hq', ha | hb⟩ := h
  · cases rev
    · have ht := ha.1.seven_insertions_bound p q' (hq'.symm ▸ hd) (hq'.symm ▸ hcl)
        (hq'.symm ▸ hh) (hq'.symm ▸ hmax) x y (hq'.symm ▸ hy) (hq'.symm ▸ hn)
      simpa only [hq'] using ht
    · have hc := ha.2 0 1 2 (by decide) (by decide) (by decide)
      change CommonReplacement G (p.vertices 2) (p.vertices 1) (p.vertices 3) q'.support at hc
      exact False.elim (hn.row1 (hq' ▸ hc))
  · have hb' : PatternB p q' := by
      cases rev
      · exact hb.1
      · exact (PatternB.reverse_iff p q').mp hb.1
    have ht := hb'.seven_insertions_bound p q' (hq'.symm ▸ hd) (hq'.symm ▸ hcl)
      (hq'.symm ▸ hh) x y (hq'.symm ▸ hx) (hq'.symm ▸ hy) (hq'.symm ▸ hn)
    simpa only [hq'] using ht

end Erdos577.PathBlock

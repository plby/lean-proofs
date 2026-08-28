import ErdosProblems.Erdos577.WeightedFifteenThird
import ErdosProblems.Erdos577.WeightedFifteenDenseFactors
import ErdosProblems.Erdos577.PathPatternARows

/-! The forced complete second block and its exact six specified rows in pattern (15). -/

namespace Erdos577.WeightedFifteen

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def DenseRows (p : Paw G) (q v : Quadrilateral G) : Prop :=
  (∀ j : Fin 4, G.Adj p.leaf (v j)) ∧
    (∀ j : Fin 4, G.Adj p.center (v j) ↔ j ≠ 3) ∧
    (∀ j : Fin 4, G.Adj (q 0) (v j) ↔ j ≠ 3) ∧
    (∀ j : Fin 4, ¬G.Adj (p.vertices 3) (v j)) ∧
    (∀ j : Fin 4, ¬G.Adj (q 1) (v j)) ∧ (∀ j : Fin 4, ¬G.Adj (q 3) (v j))

variable [Fintype V] [DecidableRel G.Adj]

theorem dense_rows {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hcl : G.IsNClique 4 v.support) (hA : PathBlock.PatternA (path false p q hd h).reverse v)
    (hheavy : 9 ≤ contacts G (path false p q hd h).support v.support)
    (hpair : 17 ≤ contacts G (path false p q hd h).support v.support +
      contacts G (path true p q hd h).support v.support) : DenseRows p q v := by
  let R := (path false p q hd h).reverse
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  have hxout : p.leaf ∉ v.support := fun he ↦ disjoint_left.mp hdis
    (mem_union_left _ ((mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩)) he
  have hrout : p.center ∉ v.support := fun he ↦ disjoint_left.mp hdis
    (mem_union_left _ ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩)) he
  have hyout : q 0 ∉ v.support := fun he ↦ disjoint_left.mp hdis
    (mem_union_right _ ((q.mem_support _).mpr ⟨0, rfl⟩)) he
  obtain ⟨hrmax, hxmin, hxmax, hymax, hwzero⟩ := hA.row_bounds R v
  change degreeIn G p.center v.support ≤ 3 at hrmax
  change 3 ≤ degreeIn G p.leaf v.support at hxmin
  change degreeIn G p.leaf v.support ≤ 4 at hxmax
  change degreeIn G (q 0) v.support ≤ 3 at hymax
  change degreeIn G (q 3) v.support = 0 at hwzero
  have hsum := (path false p q hd h).contacts_support v.support
  change contacts G (path false p q hd h).support v.support = degreeIn G (q 3) v.support +
    degreeIn G (q 0) v.support + degreeIn G p.leaf v.support + degreeIn G p.center v.support at hsum
  have hother := (path true p q hd h).contacts_support v.support
  change contacts G (path true p q hd h).support v.support = degreeIn G (q 1) v.support +
    degreeIn G (p.vertices 3) v.support + degreeIn G p.center v.support +
      degreeIn G p.leaf v.support at hother
  have hrmin : 2 ≤ degreeIn G p.center v.support := by omega
  have hymin : 2 ≤ degreeIn G (q 0) v.support := by omega
  have hnr : ¬G.Adj p.center (v 3) := hA.outer_nonadjacent R v 0 (Or.inl rfl)
  have hny : ¬G.Adj (q 0) (v 3) := hA.outer_nonadjacent R v 2 (Or.inr rfl)
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab
  have hRc : ¬CommonReplacement G p.center (p.vertices 3) p.leaf v.support := by
    rw [hv]; exact hno 0
  have hRz : ¬CommonReplacement G p.center (q 1) p.leaf v.support := by
    rw [hv]; exact hno 9
  have hxc : ¬CommonReplacement G p.leaf (p.vertices 3) (q 0) v.support := by
    rw [hv]; exact hno 5
  have hxz : ¬CommonReplacement G p.leaf (q 1) p.center v.support := by
    rw [hv]; exact hno 1
  have hmiss (z : V) (hnoz : ¬CommonReplacement G p.center z p.leaf v.support)
      (u : V) (hu : u ∈ v.support) (hzu : G.Adj z u) : ¬G.Adj p.center u := by
    intro hru
    exact hnoz ⟨u, hu, hru, hzu, clique_replace_of_degree_three hcl hxout hxmin hu⟩
  by_cases hr2 : degreeIn G p.center v.support = 2
  · have hx4 : degreeIn G p.leaf v.support = 4 := by omega
    have hy3 : degreeIn G (q 0) v.support = 3 := by omega
    have hc0 : degreeIn G (p.vertices 3) v.support = 0 := by
      apply (degreeIn_eq_zero_iff (G := G) _ _).mpr
      intro u hu hcu
      exact hxc ⟨u, hu, v.adj_of_degree_four p.leaf hx4 u hu, hcu,
        clique_replace_of_degree_three hcl hyout (by omega) hu⟩
    have hz0 : degreeIn G (q 1) v.support = 0 := by
      apply (degreeIn_eq_zero_iff (G := G) _ _).mpr
      intro u hu hzu
      have hnru := hmiss (q 1) hRz u hu hzu
      have he := degreeIn_erase_add G p.center u hu
      rw [if_neg hnru] at he
      exact hxz ⟨u, hu, v.adj_of_degree_four p.leaf hx4 u hu, hzu,
        (clique_replace_iff_two_contacts hcl hrout hu).mpr (by omega)⟩
    omega
  · have hr3 : degreeIn G p.center v.support = 3 := by omega
    have hRrow := v.adj_iff_ne_three p.center hr3 hnr
    have hzero (second : Bool) (j : Fin 4) :
        ¬G.Adj (if second then q 1 else p.vertices 3) (v j) := by
      intro hj
      have hnoz : ¬CommonReplacement G p.center (if second then q 1 else p.vertices 3)
          p.leaf v.support := by cases second <;> assumption
      have hrj := hmiss _ hnoz (v j) ((v.mem_support _).mpr ⟨j, rfl⟩) hj
      have hj3 : j = 3 := by
        by_contra hne
        exact hrj ((hRrow j).mpr hne)
      subst j
      have hu : v 3 ∈ v.support := (v.mem_support _).mpr ⟨3, rfl⟩
      have hnx : ¬G.Adj p.leaf (v 3) := by
        intro hxv
        cases second
        · have he := degreeIn_erase_add G (q 0) (v 3) hu
          rw [if_neg hny] at he
          exact hxc ⟨v 3, hu, hxv, hj,
            (clique_replace_iff_two_contacts hcl hyout hu).mpr (by omega)⟩
        · have he := degreeIn_erase_add G p.center (v 3) hu
          rw [if_neg hnr] at he
          exact hxz ⟨v 3, hu, hxv, hj,
            (clique_replace_iff_two_contacts hcl hrout hu).mpr (by omega)⟩
      have hx3 : degreeIn G p.leaf v.support = 3 := by
        have ht := v.degree_le_three_of_nonadjacent p.leaf 3 hnx
        omega
      have hy3 : degreeIn G (q 0) v.support = 3 := by omega
      have hrows (i : Fin 4) (hi : i ≠ 3) :
          G.Adj p.leaf (v i) ∧ G.Adj p.center (v i) ∧ G.Adj (q 0) (v i) :=
        ⟨(v.adj_iff_ne_three p.leaf hx3 hnx i).mpr hi, (hRrow i).mpr hi,
          (v.adj_iff_ne_three (q 0) hy3 hny i).mpr hi⟩
      exact no_dense_exception hcard hn p hp hb q hq hd h ha hab v hv hcl hrows second hj
    have hc0 : degreeIn G (p.vertices 3) v.support = 0 := by
      apply (degreeIn_eq_zero_iff (G := G) _ _).mpr
      intro u hu
      obtain ⟨j, rfl⟩ := (v.mem_support u).mp hu
      exact hzero false j
    have hz0 : degreeIn G (q 1) v.support = 0 := by
      apply (degreeIn_eq_zero_iff (G := G) _ _).mpr
      intro u hu
      obtain ⟨j, rfl⟩ := (v.mem_support u).mp hu
      exact hzero true j
    have hx4 : degreeIn G p.leaf v.support = 4 := by omega
    have hy3 : degreeIn G (q 0) v.support = 3 := by omega
    refine ⟨fun j ↦ v.adj_of_degree_four p.leaf hx4 (v j) ((v.mem_support _).mpr ⟨j, rfl⟩),
      hRrow, v.adj_iff_ne_three (q 0) hy3 hny, hzero false, hzero true, ?_⟩
    intro j
    exact (degreeIn_eq_zero_iff (G := G) (q 3) v.support).mp hwzero
      (v j) ((v.mem_support _).mpr ⟨j, rfl⟩)

theorem exists_dense_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q) :
    ∃ a ∈ c.blocks, a ≠ b ∧ ∃ v : Quadrilateral G,
      v.support = a ∧ G.IsNClique 4 v.support ∧ DenseRows p q v := by
  obtain ⟨a, ha, hab, h9, _, h17⟩ := heavy_third_block hc hcard hdeg hn p hp hb q hq hd h
  obtain ⟨hcl, _, v, hv, hA, _⟩ := third_patternA hc hcard hdeg hn p hp hb q hq hd h ha hab h9 h17
  refine ⟨a, ha, hab, v, hv, hv.symm ▸ hcl, ?_⟩
  exact dense_rows hcard hn p hp hb q hq hd h ha hab v hv (hv.symm ▸ hcl) hA
    (by rw [hv]; exact h9) (by rw [hv]; exact h17)

end Erdos577.WeightedFifteen

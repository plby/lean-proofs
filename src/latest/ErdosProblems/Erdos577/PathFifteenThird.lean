import ErdosProblems.Erdos577.CliqueReplacementObstructions
import ErdosProblems.Erdos577.PathSaturatedRows

/-! Restrictions at the third path of pattern (15); the B case has paired count at most sixteen. -/

namespace Erdos577.PathBlock

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Subscripts retain the row numbers of the ten-insertion table for pattern (15). -/
structure ThirdInsertionsExcluded (p : FourPath G) (s : Finset V) (c z : V) : Prop where
  row1 : ¬CommonReplacement G (p.vertices 3) c (p.vertices 2) s
  row2 : ¬CommonReplacement G (p.vertices 2) z (p.vertices 3) s
  row4 : ¬CommonReplacement G (p.vertices 1) (p.vertices 3) c s
  row6 : ¬CommonReplacement G (p.vertices 2) c (p.vertices 1) s
  row7 : ¬CommonReplacement G (p.vertices 3) (p.vertices 0) (p.vertices 2) s
  row8 : ¬CommonReplacement G (p.vertices 3) (p.vertices 1) z s
  row9 : ¬CommonReplacement G (p.vertices 1) (p.vertices 0) (p.vertices 2) s
  row10 : ¬CommonReplacement G (p.vertices 3) z (p.vertices 2) s

lemma ThirdInsertionsExcluded.not_forward_A (p : FourPath G) (q : Quadrilateral G) (c z : V)
    (hn : ThirdInsertionsExcluded p q.support c z) : ¬CommonA p q := by
  intro h
  have hc := h 2 1 0 (by decide) (by decide) (by decide)
  change CommonReplacement G (p.vertices 1) (p.vertices 0) (p.vertices 2) q.support at hc
  exact hn.row9 hc

variable [DecidableRel G.Adj]

lemma PatternB.third_paired_bound (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hcl : G.IsNClique 4 q.support)
    (h : PatternB p q) (hh : 9 ≤ contacts G p.support q.support)
    (c z : V) (hc : c ∉ q.support) (hz : z ∉ q.support)
    (hn : ThirdInsertionsExcluded p q.support c z) :
    contacts G p.support q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support + degreeIn G c q.support +
        degreeIn G z q.support ≤ 16 := by
  have hout (i : Fin 4) : p.vertices i ∉ q.support := by
    intro hv
    exact disjoint_left.mp hd ((p.mem_support _).mpr ⟨i, rfl⟩) hv
  obtain ⟨h0, h1, h2, h3⟩ := h.row_bounds p q
  have hsum := p.contacts_support q.support
  have hleaf : degreeIn G (p.vertices 2) q.support ≤ 2 := by
    by_contra! hbig
    have he : degreeIn G (p.vertices 2) q.support = 3 := by omega
    exact hn.row7 (h.common_for_middle p q hd hcl hh 2 (Or.inr rfl) he
      3 0 (by decide) (by decide) (by decide))
  have he : contacts G p.support q.support = 9 := by omega
  have hy : degreeIn G (p.vertices 1) q.support = 3 := by omega
  have hw : degreeIn G (p.vertices 0) q.support = 2 := by omega
  have hr : degreeIn G (p.vertices 3) q.support = 2 := by omega
  have hleaf2 : degreeIn G (p.vertices 2) q.support = 2 := by omega
  have hu : q 0 ∈ q.support := (q.mem_support _).mpr ⟨0, rfl⟩
  have hru := h.full_endpoint_adj p q 3 (Or.inr rfl) hr 0 (Or.inl rfl)
  have hwu := h.full_endpoint_adj p q 0 (Or.inl rfl) hw 0 (Or.inl rfl)
  have hyu := h.full_middle_adj p q 1 hy 0 (by decide)
  have hlu : G.Adj (p.vertices 2) (q 0) := by
    by_contra hnlu
    have hsmall := no_common_replacement_degree_le_one hcl (p.vertices 3) (p.vertices 0)
      (p.vertices 2) (hout 2) hn.row7 (q 0) hu hru hwu hnlu
    omega
  have hncu : ¬G.Adj c (q 0) := by
    intro hcu
    exact hn.row6 ⟨q 0, hu, hlu, hcu,
      clique_replace_of_degree_three hcl (hout 1) (by omega) hu⟩
  have hc1 := no_common_replacement_degree_le_one hcl (p.vertices 1) (p.vertices 3) c hc
    hn.row4 (q 0) hu hyu hru hncu
  have hz2 := no_common_replacement_degree_le_two hcl (p.vertices 3) (p.vertices 1) z hz
    hn.row8 ⟨q 0, hu, hru, hyu⟩
  omega

end Erdos577.PathBlock

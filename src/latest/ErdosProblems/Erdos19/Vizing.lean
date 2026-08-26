import ErdosProblems.Erdos19.VizingAugmentation

/-! # Vizing's theorem for finite simple graphs -/

namespace Erdos19.Vizing

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Every finite simple graph of maximum degree at most `D` has a proper
edge labeling with `D + 1` colors. This theorem has no unproved input. -/
theorem exists_proper_edgeLabeling (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) :
    ∃ c : G.EdgeLabeling (Fin (D + 1)),
      ∀ x y z (hxy : G.Adj x y) (hxz : G.Adj x z),
        c.get x y hxy = c.get x z hxz → y = z := by
  obtain ⟨C, hC, hcomplete⟩ := exists_complete_proper_coloring G D hdegree
  let c : G.EdgeLabeling (Fin (D + 1)) := fun e ↦ (C e.val).getD 0
  refine ⟨c, ?_⟩
  intro x y z hxy hxz hsame
  obtain ⟨a, ha⟩ := hcomplete x y hxy
  obtain ⟨b, hb⟩ := hcomplete x z hxz
  have hab : a = b := by simpa only [c, SimpleGraph.EdgeLabeling.get, ha, hb,
    Option.getD_some] using hsame
  exact hC hxy hxz ha (hab ▸ hb)

/-- A proper edge labeling decomposes the graph into edge-disjoint graphs
of maximum degree one, namely its matching color classes. -/
theorem exists_matching_color_decomposition (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) :
    ∃ M : Fin (D + 1) → SimpleGraph V,
      (∀ a v, (M a).degree v ≤ 1) ∧
      (Pairwise fun a b ↦ Disjoint (M a) (M b)) ∧ (⨆ a, M a) = G := by
  classical
  obtain ⟨c, hc⟩ := exists_proper_edgeLabeling G D hdegree
  refine ⟨c.labelGraph, ?_, c.pairwise_disjoint_labelGraph, c.iSup_labelGraph⟩
  intro a v
  rw [SimpleGraph.degree]
  apply card_le_one.mpr
  intro x hx y hy
  have hxadj : (c.labelGraph a).Adj v x := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx
  have hyadj : (c.labelGraph a).Adj v y := by
    simpa only [SimpleGraph.mem_neighborFinset] using hy
  obtain ⟨hvx, hcx⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj v x).mp hxadj
  obtain ⟨hvy, hcy⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj v y).mp hyadj
  exact hc v x y hvx hvy (hcx.trans hcy.symm)

#print axioms exists_proper_edgeLabeling
#print axioms exists_matching_color_decomposition

end Erdos19.Vizing

import ErdosProblems.Erdos577.DensePairCommonTriple

/-! The two distinguished pairs share index two and use indices three and one, respectively. -/

namespace Erdos577.DenseObstruction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem PairConfig.reverse {c : TriangleChain G} {p : Paw G} {d : Quadrilateral G}
    {s : Finset V} {z : V} (h : PairConfig c p d s z)
    (hcenter : G.Adj p.center (d 1))
    (hsecondary : G.IsNClique 4 {p.vertices 2, p.vertices 3, d 0, d 3}) :
    PairConfig c p d.reverse s z := by
  have hdis : Disjoint p.support d.reverse.support := by
    rw [d.reverse_support]
    exact h.pair.disjoint
  refine ⟨h.paw, h.first, ?_, ?_, h.exposed, ?_, h.first_quad, h.first_score, h.second_quad⟩
  · rw [d.reverse_support]
    exact h.core
  · rw [d.reverse_support]
    exact h.different
  refine ⟨hdis, ?_, ?_, h.pair.center_first, hcenter, ?_⟩
  · rw [d.reverse_support]
    exact h.pair.complete
  · rw [d.reverse_support]
    exact h.pair.dense
  · rw [JointFinal.primary_support_eq p d.reverse hdis]
    exact hsecondary

theorem PairConfig.last_triangle_quad {c : TriangleChain G} {p : Paw G}
    {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z) :
    QuadOn G (insert (d 0) p.triangle) := by
  have hcl := h.pair.complement_clique.isClique
  have hcross (i : Fin 4) : p.vertices i ≠ d 0 := fun he ↦
    disjoint_left.mp h.pair.disjoint ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩)
      (he.symm ▸ (d.mem_support _).mpr ⟨0, rfl⟩)
  have hb : G.Adj (p.vertices 2) (d 0) := hcl (by simp) (by simp) (hcross 2)
  have hc : G.Adj (p.vertices 3) (d 0) := hcl (by simp) (by simp) (hcross 3)
  have hquad := QuadOn.of_vertices (hcross 1).symm p.edge23.ne
    hb.symm p.edge12.symm p.edge13 hc
  change QuadOn G {d 0, p.vertices 2, p.center, p.vertices 3} at hquad
  change QuadOn G {d 0, p.center, p.vertices 2, p.vertices 3}
  rwa [insert_comm (p.vertices 2) p.center] at hquad

end Erdos577.DenseObstruction

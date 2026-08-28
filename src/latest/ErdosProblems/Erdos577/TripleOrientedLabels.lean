import ErdosProblems.Erdos577.TripleFinalChain

/-! Property A retains the actual center and identifies the shared noncentral vertex. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.exists_triple_configuration_marked {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) :
    ∃ (p' : Paw G) (q : Quadrilateral G), p'.leaf = p.leaf ∧ p'.center = p.center ∧
      p'.triangle = p.triangle ∧ (p'.vertices 2 = p.vertices 2 ∨ p'.vertices 2 = p.vertices 3) ∧
      UniversalTriple.Configuration c p' q := by
  obtain ⟨p', q, hleaf, htri, hconfig⟩ :=
    hc.exists_triple_configuration hcard hdeg hn p hp
  have hnon := c.paw_nonadjacent hcard hn p hp
  have hcenter : p'.center = p.center := by
    have hm : p'.center ∈ p.triangle := htri ▸ p'.center_mem_triangle
    have he : G.Adj p'.leaf p'.center := p'.pendant
    rw [hleaf] at he
    simp only [Paw.triangle, mem_insert, mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact hm
    · rw [hm] at he
      exact False.elim (hnon.1 he)
    · rw [hm] at he
      exact False.elim (hnon.2 he)
  have hsecond : p'.vertices 2 = p.vertices 2 ∨ p'.vertices 2 = p.vertices 3 := by
    have hm : p'.vertices 2 ∈ p.triangle := htri ▸ (by simp [Paw.triangle])
    simp only [Paw.triangle, mem_insert, mem_singleton] at hm
    rcases hm with hm | hm | hm
    · have he : p'.vertices 2 = p'.center := hm.trans hcenter.symm
      exact False.elim (p'.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1) he)
    · exact Or.inl hm
    · exact Or.inr hm
  exact ⟨p', q, hleaf, hcenter, htri, hsecond, hconfig⟩

end Erdos577

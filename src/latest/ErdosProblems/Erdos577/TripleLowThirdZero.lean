import ErdosProblems.Erdos577.TripleLowThirdLabels

/-! The two explicit cycles exclude the remaining third-row neighbor. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V}

theorem LowCore.third_one_false (h : LowCore c p q a) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) (hthird : degreeIn G (p.vertices 3) a = 1) : False := by
  obtain ⟨z, v, s, t, ha, hza, hva, hsa, hta, hcz, hrv, hxv, hxs, hxt, hxz, hst⟩ :=
    h.third_one_labels hc hcard hdeg hn hthird
  have hout (i : Fin 4) (w : V) (hw : w ∈ a) : p.vertices i ≠ w := by
    intro he
    have hp : p.vertices i ∈ p.support := (mem_tupleSupport _ _).mpr ⟨i, rfl⟩
    exact disjoint_left.mp (h.toConfiguration.paw_disjoint_block h.core_block) hp
      (he.symm ▸ hw)
  have hzv : z ≠ v := fun he ↦ hxz (he.symm ▸ hxv)
  have hfirst : QuadOn G {p.center, p.vertices 3, z, v} :=
    QuadOn.of_vertices (hout 1 z hza) (hout 3 v hva) p.edge13 hcz
      (h.core_complete.isClique hza hva hzv) hrv.symm
  have hxy : p.leaf ≠ q 3 := by
    intro he
    apply h.toConfiguration.paw_outside 0
    change p.leaf ∈ q.support
    rw [he]
    exact (q.mem_support _).mpr ⟨3, rfl⟩
  have hsecond : QuadOn G {p.leaf, s, q 3, t} :=
    QuadOn.of_vertices hxy hst hxs (h.exposed_adj hsa).symm (h.exposed_adj hta) hxt.symm
  have hcover : ({p.center, p.vertices 3, z, v} ∪ {p.leaf, s, q 3, t} : Finset V) =
      insert (q 3) (p.support.erase (p.vertices 2) ∪ a) := by
    rw [p.erase_second_support, ha]
    ext w
    simp only [mem_union, mem_insert, mem_singleton]
    tauto
  have hdis : Disjoint ({p.center, p.vertices 3, z, v} : Finset V) {p.leaf, s, q 3, t} :=
    card_union_eq_card_add_card.mp (by
      rw [hcover, h.toConfiguration.partial_paw_card h.core_block h.core_ne,
        hfirst.card, hsecond.card])
  have hf := FullLeafSix.factor_of_two_quads hfirst hsecond hdis
  rw [hcover] at hf
  exact h.toConfiguration.no_missing_second_factor hcard hn h.core_block h.core_ne hf

theorem LowCore.third_zero (h : LowCore c p q a) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) : degreeIn G (p.vertices 3) a = 0 := by
  have hb := h.third_le_one hcard hn
  by_contra hz
  exact h.third_one_false hc hcard hdeg hn (by omega)

end Erdos577.UniversalTriple

import ErdosProblems.Erdos577.FirstPawSixUpper
import ErdosProblems.Erdos577.PawEdgeCount
import ErdosProblems.Erdos577.FirstPawFiveExcluded
import ErdosProblems.Erdos577.LocalChainSupport

/-! If all five essential contacts are present, an equal-score exchange produces pattern (5). -/

namespace Erdos577.FirstPawSix

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma essential_exchange_data (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern6 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3)) (he : Essential p q) :
    ∃ (l : LocalChain G (p.support ∪ q.support)) (p' : Paw G) (q' : Quadrilateral G),
      p'.support = l.remainder ∧ q'.support = l.block ∧ PawBlock.Pattern5 p' q' := by
  classical
  let f := essentialCopy p q hd h he
  let p' := essentialPaw.image f
  let q' : Quadrilateral G := f.comp essentialQuad
  let l := (essentialLocal.image f).withSupport (essentialCopy_image p q hd h he)
  have hp' : p'.support = l.remainder := by
    rw [Paw.image_support, Paw.support_eq, image_insert]
    rfl
  have hq' : q'.support = l.block := Quadrilateral.support_copy_comp _ _
  refine ⟨l, p', q', hp', hq', ?_⟩
  refine ⟨⟨f.toHom.map_rel' essential_first_diagonal, ?_⟩, ?_, ?_, ?_⟩
  · intro hadj
    exact essential_low_absent (adj_upper p q hd h hleaf _ _ hadj)
  · intro j hj
    apply essential_high_rows j
    rcases hj with h0 | h1
    · exact Or.inl (adj_upper p q hd h hleaf _ _ h0)
    · exact Or.inr (adj_upper p q hd h hleaf _ _ h1)
  · intro j hj
    exact essential_noncentral_two j (adj_upper p q hd h hleaf _ _ hj)
  · intro j hj
    exact essential_noncentral_three j (adj_upper p q hd h hleaf _ _ hj)

variable [Fintype V]

theorem not_essential {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern6 p q)
    (hheavy : 9 ≤ contacts G p.support q.support) : ¬Essential p q := by
  intro he
  have hleaf := c.paw_nonadjacent hcard hn p hp
  obtain ⟨l₀, p', q', hp', hq', h5⟩ := essential_exchange_data p q hd h hleaf he
  let l := l₀.withSupport (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  let d := c.replaceBlock b hb l
  have hqscore : edgeCount G q'.support = edgeCount G q.support := by
    rw [q'.edgeCount_eq, if_pos h5.1.1, if_neg h5.1.2, old_score p q h]
  have hdf : d.Feasible := hc.replaceBlock_feasible hb l
    ((congrArg (edgeCount G) hq').symm.trans (hqscore.trans (congrArg (edgeCount G) hq)))
  have hp'd : p'.support = d.remainder := hp'
  have hqmem : q'.support ∈ d.blocks := mem_union_right _ (mem_singleton.mpr hq')
  have hnewdis : Disjoint p'.support q'.support := by rw [hp', hq']; exact l₀.disjoint
  have hcover : p'.support ∪ q'.support = p.support ∪ q.support := by
    rw [hp', hq']
    exact l₀.cover
  have hp4 := p.edgeCount_of_nonadjacent hleaf
  have hp'4 : edgeCount G p'.support = 4 := p'.edgeCount_of_no_quad (by
    rw [hp'd]
    exact d.no_quad_remainder hcard hn)
  have hold := edgeCount_union G hd
  have hnew := edgeCount_union G hnewdis
  rw [hcover] at hnew
  have hnine : 9 ≤ contacts G p'.support q'.support := by omega
  exact hdf.not_first_paw_pattern5 hcard hdeg hn p' hp'd hqmem q' rfl hnine h5

end Erdos577.FirstPawSix

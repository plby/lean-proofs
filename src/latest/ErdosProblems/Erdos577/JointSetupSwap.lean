import ErdosProblems.Erdos577.JointSetupFactors

/-! The strong exchanged chain, its prescribed paw labeling, and all retained blocks. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def exposedPaw (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : CaseOne p q ∨ CaseTwo p q) : Paw G :=
  Paw.ofVertices (q 3) (p.vertices 2) (p.vertices 1) (p.vertices 3)
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩)
      (he ▸ (q.mem_support _).mpr ⟨3, rfl⟩))
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩)
      (he ▸ (q.mem_support _).mpr ⟨3, rfl⟩))
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩)
      (he ▸ (q.mem_support _).mpr ⟨3, rfl⟩))
    (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1))
    (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 3))
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 3))
    (first_rows p q h).2.symm p.edge12.symm p.edge23 p.edge13

lemma exposedPaw_leaf (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : CaseOne p q ∨ CaseTwo p q) : (exposedPaw p q hd h).leaf = q 3 := rfl

lemma exposedPaw_center (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : CaseOne p q ∨ CaseTwo p q) : (exposedPaw p q hd h).center = p.vertices 2 := rfl

lemma exposedPaw_triangle (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : CaseOne p q ∨ CaseTwo p q) : (exposedPaw p q hd h).triangle = p.triangle := by
  change ({p.vertices 2, p.center, p.vertices 3} : Finset V) = p.triangle
  ext u
  simp only [Paw.triangle, Paw.center, mem_insert, mem_singleton]
  tauto

lemma exposedPaw_support (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : CaseOne p q ∨ CaseTwo p q) : (exposedPaw p q hd h).support = insert (q 3) p.triangle := by
  rw [Paw.support_eq, exposedPaw_leaf, exposedPaw_triangle]

variable [Fintype V]

theorem exists_exposed_chain {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hd : Disjoint p.support q.support) (h : CaseOne p q ∨ CaseTwo p q) :
    ∃ d : TriangleChain G, d.Strong ∧ d.terminal = q 3 ∧ d.triangle = p.triangle ∧
      (exposedPaw p q hd h).support = d.remainder ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 3))} ∧
      ∀ a ∈ c.blocks, a ≠ s → a ∈ d.blocks := by
  obtain ⟨d, hstrong, ht, hT, he, hcomp, hblocks⟩ :=
    FullRow.exists_strong_first_swap hc hcard hn p hp hs q hq
      (first_rows p q h).1 (first_rows p q h).2
  have hp' : (exposedPaw p q hd h).support = d.remainder := by
    rw [exposedPaw_support]
    change insert (q 3) p.triangle = insert d.terminal d.triangle
    rw [ht, hT]
  refine ⟨d, hstrong, ht, hT, hp', he, hcomp, hblocks, ?_⟩
  intro a ha has
  rw [hblocks]
  exact mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)

theorem case_one_of_failed_replacement {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (h : CaseOne p q ∨ CaseTwo p q)
    (hfail : ¬QuadOn G (insert (p.vertices 2) (q.support.erase (q 3)))) : CaseOne p q := by
  rcases h with h | h
  · exact h
  · exact False.elim (hfail (case_two_universal hc p hp hs q hq h (q 3)
      ((q.mem_support _).mpr ⟨3, rfl⟩)))

end Erdos577.JointClaims

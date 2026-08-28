import ErdosProblems.Erdos577.ClaimTwoFive

/-! Two actual paw presentations with distinct leaves and interchanged centers. -/

namespace Erdos577.TwoExposed

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

structure PawPair (p p' : Paw G) : Prop where
  center : p'.center = p.vertices 2
  second : p'.vertices 2 = p.center
  third : p'.vertices 3 = p.vertices 3
  distinct : p.leaf ≠ p'.leaf

omit [DecidableEq V] in
lemma PawPair.symm {p p' : Paw G} (h : PawPair p p') : PawPair p' p :=
  ⟨h.second.symm, h.center.symm, h.third.symm, h.distinct.symm⟩

lemma PawPair.triangle {p p' : Paw G} (h : PawPair p p') : p'.triangle = p.triangle := by
  change ({p'.center, p'.vertices 2, p'.vertices 3} : Finset V) =
    {p.center, p.vertices 2, p.vertices 3}
  rw [h.center, h.second, h.third, insert_comm]

lemma PawPair.other_leaf_out {p p' : Paw G} (h : PawPair p p') : p'.leaf ∉ p.support := by
  rw [p.support_eq, mem_insert]
  exact not_or.mpr ⟨h.distinct.symm, fun hh ↦ p'.leaf_not_mem_triangle (h.triangle.symm ▸ hh)⟩

lemma PawPair.five_card {p p' : Paw G} (h : PawPair p p') :
    (insert p'.leaf p.support).card = 5 := by
  rw [card_insert_of_notMem h.other_leaf_out, p.card_support]

lemma PawPair.five_symm {p p' : Paw G} (h : PawPair p p') :
    insert p.leaf p'.support = insert p'.leaf p.support := by
  rw [p'.support_eq, p.support_eq, h.triangle, insert_comm]

variable [DecidableRel G.Adj]

lemma PawPair.five_contacts {p p' : Paw G} (h : PawPair p p') (a : Finset V) :
    contacts G (insert p'.leaf p.support) a =
      degreeIn G p.leaf a + degreeIn G p'.leaf a + contacts G p.triangle a := by
  rw [contacts, sum_insert h.other_leaf_out]
  change degreeIn G p'.leaf a + contacts G p.support a = _
  rw [p.contacts_support]
  omega

omit [DecidableRel G.Adj] in
def alternatePaw (p : Paw G) (z : V) (hz : z ∉ p.triangle)
    (hzb : G.Adj z (p.vertices 2)) : Paw G :=
  Paw.ofVertices z (p.vertices 2) p.center (p.vertices 3) hzb.ne
    (fun he ↦ hz (he.symm ▸ p.center_mem_triangle))
    (fun he ↦ hz (he.symm ▸ (show p.vertices 3 ∈ p.triangle by simp [Paw.triangle])))
    p.edge12.ne.symm p.edge23.ne p.edge13.ne hzb p.edge12.symm p.edge23 p.edge13

omit [DecidableRel G.Adj] in
lemma alternatePaw_apply (p : Paw G) (z : V) (hz : z ∉ p.triangle)
    (hzb : G.Adj z (p.vertices 2)) (i : Fin 4) :
    (alternatePaw p z hz hzb).vertices i = ![z, p.vertices 2, p.center, p.vertices 3] i := rfl

omit [DecidableRel G.Adj] in
lemma alternatePaw_pair (p : Paw G) (z : V) (hz : z ∉ p.triangle)
    (hzb : G.Adj z (p.vertices 2)) (hne : p.leaf ≠ z) : PawPair p (alternatePaw p z hz hzb) :=
  ⟨rfl, rfl, rfl, hne⟩

end Erdos577.TwoExposed

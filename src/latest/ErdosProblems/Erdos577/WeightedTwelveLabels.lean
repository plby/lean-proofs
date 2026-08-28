import ErdosProblems.Erdos577.WeightedTwelveRows

/-! The explicit local involution sends (X,r,b,c;Q) to (Y,c,b,r;Q-Y+X). -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def exposedPaw (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern12 p q) : Paw G :=
  Paw.ofVertices (q 3) (p.vertices 3) (p.vertices 2) (p.vertices 1)
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩)
      (he ▸ (q.mem_support _).mpr ⟨3, rfl⟩))
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩)
      (he ▸ (q.mem_support _).mpr ⟨3, rfl⟩))
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩)
      (he ▸ (q.mem_support _).mpr ⟨3, rfl⟩))
    (p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 2))
    (p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 1))
    (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1))
    (first_rows p q h).2.symm p.edge23.symm p.edge13.symm p.edge12.symm

lemma exposedPaw_apply (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern12 p q) (i : Fin 4) :
    (exposedPaw p q hd h).vertices i = ![q 3, p.vertices 3, p.vertices 2, p.vertices 1] i := rfl

lemma exposedPaw_triangle (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern12 p q) : (exposedPaw p q hd h).triangle = p.triangle := by
  change ({p.vertices 3, p.vertices 2, p.vertices 1} : Finset V) =
    {p.vertices 1, p.vertices 2, p.vertices 3}
  rw [insert_comm (p.vertices 3) (p.vertices 2), pair_comm (p.vertices 3) (p.vertices 1),
    insert_comm (p.vertices 2) (p.vertices 1)]

lemma exposedPaw_support (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern12 p q) :
    (exposedPaw p q hd h).support = insert (q 3) p.triangle := by
  rw [Paw.support_eq, exposedPaw_triangle]
  rfl

def exposedQuad (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern12 p q) : Quadrilateral G :=
  q.replaceAt 3 p.leaf
    (fun hh ↦ disjoint_left.mp hd (p.support_eq ▸ mem_insert_self _ _) hh)
    (fun i hi ↦ (first_rows p q h).1 i hi.ne.symm)

lemma exposedQuad_apply (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern12 p q) (i : Fin 4) :
    exposedQuad p q hd h i = if i = 3 then p.leaf else q i := by
  dsimp only [exposedQuad]
  split_ifs with hi
  · subst i
    exact q.replaceAt_apply 3 p.leaf _ _
  · exact q.replaceAt_apply_of_ne 3 p.leaf _ _ hi

lemma exposedQuad_support (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern12 p q) :
    (exposedQuad p q hd h).support = insert p.leaf (q.support.erase (q 3)) :=
  q.replaceAt_support 3 p.leaf _ _

end Erdos577.WeightedTwelve

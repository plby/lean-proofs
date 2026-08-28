import ErdosProblems.Erdos577.JointFirstSwap

/-! The exposed center-neighbor has the original ordered triangle and all its core labels. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def centerPaw (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hr : G.Adj p.center (q 1)) : Paw G where
  vertices := p.outsideTuple (q 1)
    (fun hh ↦ disjoint_left.mp hd hh ((q.mem_support _).mpr ⟨1, rfl⟩))
  pendant := by
    rw [Paw.outsideTuple_zero, Paw.outsideTuple_nonzero _ _ _ (by decide : (1 : Fin 4) ≠ 0)]
    exact hr.symm
  edge12 := by
    rw [Paw.outsideTuple_nonzero _ _ _ (by decide : (1 : Fin 4) ≠ 0),
      Paw.outsideTuple_nonzero _ _ _ (by decide : (2 : Fin 4) ≠ 0)]
    exact p.edge12
  edge13 := by
    rw [Paw.outsideTuple_nonzero _ _ _ (by decide : (1 : Fin 4) ≠ 0),
      Paw.outsideTuple_nonzero _ _ _ (by decide : (3 : Fin 4) ≠ 0)]
    exact p.edge13
  edge23 := by
    rw [Paw.outsideTuple_nonzero _ _ _ (by decide : (2 : Fin 4) ≠ 0),
      Paw.outsideTuple_nonzero _ _ _ (by decide : (3 : Fin 4) ≠ 0)]
    exact p.edge23

lemma centerPaw_leaf (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hr : G.Adj p.center (q 1)) : (centerPaw p q hd hr).leaf = q 1 := by
  exact p.outsideTuple_zero (q 1)
    (fun hh ↦ disjoint_left.mp hd hh ((q.mem_support _).mpr ⟨1, rfl⟩))

lemma centerPaw_nonzero (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hr : G.Adj p.center (q 1)) (i : Fin 4) (hi : i ≠ 0) :
    (centerPaw p q hd hr).vertices i = p.vertices i := by
  exact p.outsideTuple_nonzero (q 1)
    (fun hh ↦ disjoint_left.mp hd hh ((q.mem_support _).mpr ⟨1, rfl⟩)) hi

lemma centerPaw_triangle (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hr : G.Adj p.center (q 1)) : (centerPaw p q hd hr).triangle = p.triangle := by
  simp only [Paw.triangle, centerPaw_nonzero p q hd hr 1 (by decide),
    centerPaw_nonzero p q hd hr 2 (by decide), centerPaw_nonzero p q hd hr 3 (by decide)]

lemma centerPaw_support (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hr : G.Adj p.center (q 1)) : (centerPaw p q hd hr).support = insert (q 1) p.triangle := by
  rw [Paw.support_eq, centerPaw_leaf, centerPaw_triangle]

end Erdos577.JointFirst

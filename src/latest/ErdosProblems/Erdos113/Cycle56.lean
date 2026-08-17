import ErdosProblems.Erdos113.Cycles
import ErdosProblems.Erdos113.WalkFin
import ErdosProblems.Erdos113.Conflict

/-!
# Ordered homomorphic 56-cycles and closed walks
-/

open scoped SimpleGraph

namespace Erdos113Cycle56

open Erdos113Cycles

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Tuple56 (V : Type*) := Fin 56 → V

abbrev ClosedWalk56 (G : SimpleGraph V) :=
  Σ v : V, Conflict.FixedWalk G 56 v v

/-- Read the first 56 vertices of a length-56 closed walk. -/
def closedWalkTuple (G : SimpleGraph V) (P : ClosedWalk56 G) : Tuple56 V :=
  fun i ↦ P.2.1.getVert i.val

lemma closedWalkTuple_isHomCycle (G : SimpleGraph V) (P : ClosedWalk56 G) :
    IsHomCycle G (closedWalkTuple G P) := by
  intro i
  have hi : i.val < P.2.1.length := by simpa [P.2.2] using i.isLt
  have h := P.2.1.adj_getVert_succ hi
  by_cases hlast : i.val + 1 < 56
  · have hadd : (i + 1 : Fin 56).val = i.val + 1 :=
      Fin.val_add_eq_of_add_lt (by simpa using hlast)
    simpa [closedWalkTuple, hadd] using h
  · have hi55 : i.val = 55 := by omega
    have hend : P.2.1.getVert 56 = P.1 := by
      simpa [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    have hi' : i = (55 : Fin 56) := Fin.ext hi55
    subst i
    simpa [closedWalkTuple, hend, hstart] using h

/-- Append the initial vertex to a cyclic 56-tuple. -/
def closeSeq (x : Tuple56 V) (j : Fin 57) : V :=
  if h : j.val < 56 then x ⟨j.val, h⟩ else x 0

@[simp] lemma closeSeq_castSucc (x : Tuple56 V) (i : Fin 56) :
    closeSeq x i.castSucc = x i := by
  simp [closeSeq]

@[simp] lemma closeSeq_last (x : Tuple56 V) : closeSeq x (Fin.last 56) = x 0 := by
  simp [closeSeq]

lemma closeSeq_succ (x : Tuple56 V) (i : Fin 56) :
    closeSeq x i.succ = x (i + 1) := by
  by_cases h : i.val + 1 < 56
  · simp only [closeSeq, Fin.val_succ, h, ↓reduceDIte]
    congr 1
    apply Fin.ext
    symm
    exact Fin.val_add_eq_of_add_lt (by simpa using h)
  · have hi : i.val = 55 := by omega
    have hi' : i = (55 : Fin 56) := Fin.ext hi
    subst i
    simp [closeSeq]

lemma closeSeq_adj {G : SimpleGraph V} {x : Tuple56 V}
    (hx : IsHomCycle G x) (i : Fin 56) :
    G.Adj (closeSeq x i.castSucc) (closeSeq x i.succ) := by
  rw [closeSeq_castSucc, closeSeq_succ]
  exact hx i

/-- Turn a cyclic tuple into the corresponding closed walk. -/
def tupleClosedWalk {G : SimpleGraph V} (x : Tuple56 V) (hx : IsHomCycle G x) :
    ClosedWalk56 G := by
  let p := WF.walkOfFin 56 (closeSeq x) (closeSeq_adj hx)
  refine ⟨x 0, ⟨p.copy ?_ ?_, ?_⟩⟩
  · simp [p, closeSeq]
  · simp [p, closeSeq]
  · simp [p]

@[simp] lemma closedWalkTuple_tupleClosedWalk {G : SimpleGraph V}
    (x : Tuple56 V) (hx : IsHomCycle G x) :
    closedWalkTuple G (tupleClosedWalk x hx) = x := by
  funext i
  simp only [closedWalkTuple, tupleClosedWalk]
  rw [SimpleGraph.Walk.getVert_copy]
  simpa [closeSeq] using
    (WF.walkOfFin_getVert 56 (closeSeq x) (closeSeq_adj hx) i.val
      (Nat.le_of_lt i.isLt))

lemma closedWalkTuple_injective (G : SimpleGraph V) :
    Function.Injective (closedWalkTuple G) := by
  rintro ⟨p, P⟩ ⟨q, Q⟩ hPQ
  have hstart : p = q := by
    have h0 := congrFun hPQ 0
    simpa [closedWalkTuple] using h0
  subst q
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length
  · rw [P.2, Q.2]
  · intro i hiP
    by_cases hi : i < 56
    · have h := congrFun hPQ ⟨i, hi⟩
      simpa [closedWalkTuple] using h
    · have hiP' : i ≤ 56 := by simpa [P.2] using hiP
      have hi56 : i = 56 := by omega
      subst i
      have hp : P.1.getVert 56 = p := by
        simpa [P.2] using P.1.getVert_length
      have hq : Q.1.getVert 56 = p := by
        simpa [Q.2] using Q.1.getVert_length
      exact hp.trans hq.symm

noncomputable def closedWalkHomEquiv (G : SimpleGraph V) :
    ClosedWalk56 G ≃ {x : Tuple56 V // IsHomCycle G x} :=
  Equiv.ofBijective
    (fun P ↦ ⟨closedWalkTuple G P, closedWalkTuple_isHomCycle G P⟩)
    ⟨fun _ _ h ↦ closedWalkTuple_injective G (congrArg Subtype.val h), by
      intro x
      refine ⟨tupleClosedWalk x.1 x.2, ?_⟩
      apply Subtype.ext
      exact closedWalkTuple_tupleClosedWalk x.1 x.2⟩

lemma card_homCycle56_eq_closedWalkCount (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card {x : Tuple56 V // IsHomCycle G x} =
      Conflict.closedWalkCount G 56 := by
  rw [← Fintype.card_congr (closedWalkHomEquiv G)]
  simp only [Fintype.card_sigma, Conflict.closedWalkCount]
  rfl

end Erdos113Cycle56

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RawAlternatingDichotomy
import ErdosProblems.Erdos599.AlternatingMacroFlatten

/-!
# Concrete tools for finite macro routes

This is the finite counterpart of `AlternatingMacroFlatten`.  It records the
injectivity of a root-anchored finite macro orbit and selects concrete finite
representatives for all of its `Z`- and `Y`-members.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

namespace Walk

theorem support_length_eq_length_add_one {D : Digraph V} {a b : V}
    (p : Walk D a b) : p.support.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp only [DirectedPath.Walk.support_cons, List.length_cons,
        DirectedPath.Walk.length_cons, ih]

theorem adj_get_support_route {D : Digraph V} {a b : V}
    (p : Walk D a b) (j : ℕ) (hj : j + 1 < p.support.length) :
    D.Adj (p.support.get ⟨j, by omega⟩)
      (p.support.get ⟨j + 1, hj⟩) := by
  induction p generalizing j with
  | nil => simp at hj
  | @cons a c b h p ih =>
      cases j with
      | zero =>
          simp only [DirectedPath.Walk.support_cons, List.get_eq_getElem,
            List.getElem_cons_zero, List.getElem_cons_succ]
          have hpos : 0 < p.support.length :=
            List.length_pos_iff.mpr p.support_ne_nil
          simpa only [List.getElem_zero hpos, p.head_support] using h
      | succ j =>
          simp only [DirectedPath.Walk.support_cons, List.length_cons] at hj
          simp only [DirectedPath.Walk.support_cons, List.get_eq_getElem,
            List.getElem_cons_succ]
          simpa only [List.get_eq_getElem] using ih (j := j) (by omega)

theorem endpoints_eq_of_length_eq_zero {D : Digraph V} {a b : V}
    (p : Walk D a b) (h : p.length = 0) : a = b := by
  cases p with
  | nil => rfl
  | cons e p => simp at h

end Walk

namespace FiniteMacroRoute

variable {Z Y : Set Γ.DPath} (C : FiniteMacroRoute Γ Z Y)

/-- No `Z`-member repeats along a finite macro orbit rooted outside `Y`. -/
theorem z_injective (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y) :
    Function.Injective C.z := by
  have hne : ∀ (i : ℕ) (hi : i ≤ C.lastIndex)
      (j : ℕ) (hj : j ≤ C.lastIndex), i < j →
      C.z ⟨i, Nat.lt_succ_of_le hi⟩ ≠
        C.z ⟨j, Nat.lt_succ_of_le hj⟩ := by
    intro i
    induction i with
    | zero =>
        intro _hi j hj hij heq
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        have hk : k < C.lastIndex := by omega
        apply MacroStep.not_mem_range_of_initial_not_mem
          (C.z ⟨0, Nat.zero_lt_succ _⟩) hroot
        refine ⟨C.z ⟨k, by omega⟩, ?_⟩
        have hs := C.step ⟨k, hk⟩
        rw [← heq] at hs
        exact hs
    | succ i ih =>
        intro hi j hj hij heq
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        have hi' : i < C.lastIndex := by omega
        have hk' : k < C.lastIndex := by omega
        have hprev : C.z ⟨i, by omega⟩ = C.z ⟨k, by omega⟩ :=
          MacroStep.leftUnique hZ hY (C.step ⟨i, hi'⟩) (by
            simpa [heq] using C.step ⟨k, hk'⟩)
        exact ih (by omega) k (by omega) (by omega) hprev
  intro i j hij
  by_contra hneij
  rcases lt_or_gt_of_ne hneij with hij' | hji'
  · exact hne i.1 (Nat.le_of_lt_succ i.2) j.1
      (Nat.le_of_lt_succ j.2)
      hij' hij
  · exact hne j.1 (Nat.le_of_lt_succ j.2) i.1
      (Nat.le_of_lt_succ i.2)
      hji' hij.symm

/-- The intervening `Y`-members of a finite root-anchored route are also
pairwise distinct. -/
theorem y_injective (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y) :
    Function.Injective C.y := by
  have hz := C.z_injective hZ hY hroot
  intro i j hij
  have hzEq : (⟨i.1, by omega⟩ : Fin (C.lastIndex + 1)) =
      ⟨j.1, by omega⟩ := by
    apply hz
    apply Subtype.ext
    exact DWeb.IsWarp.eq_of_mem_support hZ
      (C.z ⟨i.1, by omega⟩).2 (C.z ⟨j.1, by omega⟩).2
      (Γ.terminal_mem_support (C.z_terminal i))
      (by
        have ht : C.terminal i = C.terminal j := Option.some.inj
          ((C.y_terminal i).symm.trans (hij ▸ C.y_terminal j))
        rw [ht]
        exact Γ.terminal_mem_support (C.z_terminal j))
  have hval : i.1 = j.1 := congrArg
    (fun x : Fin (C.lastIndex + 1) ↦ x.1) hzEq
  exact Fin.ext hval

theorem z_support_disjoint (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y)
    {i j : Fin (C.lastIndex + 1)} (hij : i ≠ j) :
    Disjoint (C.z i).1.support (C.z j).1.support := by
  exact DWeb.IsWarp.disjoint Γ hZ (C.z i).2 (C.z j).2
    (fun h ↦ hij ((C.z_injective hZ hY hroot) (Subtype.ext h)))

theorem y_support_disjoint (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y)
    {i j : Fin C.lastIndex} (hij : i ≠ j) :
    Disjoint (C.y i).1.support (C.y j).1.support := by
  exact DWeb.IsWarp.disjoint Γ hY (C.y i).2 (C.y j).2
    (fun h ↦ hij ((C.y_injective hZ hY hroot) (Subtype.ext h)))

/-- The concrete finite representative of a route's `Z`-member. -/
noncomputable def zFinite (hZfin : Γ.HasFiniteCharacter Z)
    (i : Fin (C.lastIndex + 1)) : FinitePath Γ.graph :=
  Classical.choose (hZfin (C.z i).2)

theorem z_eq_zFinite (hZfin : Γ.HasFiniteCharacter Z)
    (i : Fin (C.lastIndex + 1)) :
    (C.z i).1 = .inl (C.zFinite hZfin i) :=
  Classical.choose_spec (hZfin (C.z i).2)

/-- The concrete finite representative of a route's intervening `Y`-member. -/
noncomputable def yFinite (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin C.lastIndex) : FinitePath Γ.graph :=
  Classical.choose (hYfin (C.y i).2)

theorem y_eq_yFinite (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin C.lastIndex) :
    (C.y i).1 = .inl (C.yFinite hYfin i) :=
  Classical.choose_spec (hYfin (C.y i).2)

theorem zFinite_start (hZfin : Γ.HasFiniteCharacter Z)
    (i : Fin (C.lastIndex + 1)) :
    (C.zFinite hZfin i).start = (C.z i).1.initial :=
  (congrArg Path.initial (C.z_eq_zFinite hZfin i)).symm

theorem zFinite_finish_of_lt (hZfin : Γ.HasFiniteCharacter Z)
    (i : Fin C.lastIndex) :
    (C.zFinite hZfin ⟨i.1, by omega⟩).finish = C.terminal i := by
  have h := C.z_terminal i
  rw [C.z_eq_zFinite hZfin ⟨i.1, by omega⟩] at h
  exact Option.some.inj h

theorem yFinite_start (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin C.lastIndex) :
    (C.yFinite hYfin i).start =
      (C.z ⟨i.1 + 1, by omega⟩).1.initial :=
  (congrArg Path.initial (C.y_eq_yFinite hYfin i)).symm.trans (C.joins i)

theorem yFinite_finish (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin C.lastIndex) :
    (C.yFinite hYfin i).finish = C.terminal i := by
  have h := C.y_terminal i
  rw [C.y_eq_yFinite hYfin i] at h
  exact Option.some.inj h

theorem final_zFinite_finish (hZfin : Γ.HasFiniteCharacter Z) :
    (C.zFinite hZfin ⟨C.lastIndex, Nat.lt_succ_self _⟩).finish =
      C.finalTerminal := by
  have h := C.final_terminal
  rw [C.z_eq_zFinite hZfin ⟨C.lastIndex, Nat.lt_succ_self _⟩] at h
  exact Option.some.inj h

/-- The forward auxiliary walk carried by a finite route's `Z`-member. -/
noncomputable def zBlockWalk (hZfin : Γ.HasFiniteCharacter Z)
    (i : Fin (C.lastIndex + 1)) :
    Walk (macroDigraph Z Y) (C.zFinite hZfin i).start
      (C.zFinite hZfin i).finish :=
  Walk.into (MacroEdge Z Y) (C.zFinite hZfin i).walk (by
    intro x y hxy
    exact Or.inl (by
      simp only [familyEdges, Set.mem_iUnion]
      refine ⟨(C.z i).1, (C.z i).2, ?_⟩
      rw [C.z_eq_zFinite hZfin i]
      exact hxy))

@[simp]
theorem support_zBlockWalk (hZfin : Γ.HasFiniteCharacter Z)
    (i : Fin (C.lastIndex + 1)) :
    (C.zBlockWalk (Y := Y) hZfin i).support =
      (C.zFinite hZfin i).walk.support :=
  Walk.support_into _ _ _

/-- The backward auxiliary walk carried by an intervening `Y`-member. -/
noncomputable def yBlockWalk (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin C.lastIndex) :
    Walk (macroDigraph Z Y) (C.yFinite hYfin i).finish
      (C.yFinite hYfin i).start :=
  Walk.reverseInto (MacroEdge Z Y) (C.yFinite hYfin i).walk (by
    intro x y hxy
    exact Or.inr (by
      simp only [familyEdges, Set.mem_iUnion]
      refine ⟨(C.y i).1, (C.y i).2, ?_⟩
      rw [C.y_eq_yFinite hYfin i]
      exact hxy))

@[simp]
theorem support_yBlockWalk (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin C.lastIndex) :
    (C.yBlockWalk (Z := Z) hYfin i).support =
      (C.yFinite hYfin i).walk.support.reverse :=
  Walk.support_reverseInto _ _ _

/-- The full auxiliary walk realizing one nonfinal macro step. -/
noncomputable def stepBlockWalk
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin C.lastIndex) :
    Walk (macroDigraph Z Y)
      (C.z ⟨i.1, by omega⟩).1.initial
      (C.z ⟨i.1 + 1, by omega⟩).1.initial := by
  let f := C.zBlockWalk (Y := Y) hZfin ⟨i.1, by omega⟩
  let b := C.yBlockWalk (Z := Z) hYfin i
  exact Walk.castEndpoints (C.zFinite_start hZfin _)
    (C.yFinite_start hYfin i)
    (f.append (Walk.castEndpoints
      ((C.yFinite_finish hYfin i).trans
        (C.zFinite_finish_of_lt hZfin i).symm) rfl b))

@[simp]
theorem support_stepBlockWalk
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin C.lastIndex) :
    (C.stepBlockWalk hZfin hYfin i).support =
      (C.zFinite hZfin ⟨i.1, by omega⟩).walk.support ++
        (C.yFinite hYfin i).walk.support.dropLast.reverse := by
  unfold stepBlockWalk
  rw [Walk.support_castEndpoints, Walk.support_append,
    Walk.support_castEndpoints]
  simp

/-- The concatenation of the first `n` complete macro steps. -/
noncomputable def prefixWalk
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    (n : ℕ) → (hn : n ≤ C.lastIndex) →
      Walk (macroDigraph Z Y)
        (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial
        (C.z ⟨n, Nat.lt_succ_of_le hn⟩).1.initial
  | 0, _ => .nil
  | n + 1, hn => by
      exact (prefixWalk hZfin hYfin n (by omega)).append
        (C.stepBlockWalk hZfin hYfin ⟨n, by omega⟩)

@[simp]
theorem prefixWalk_zero
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    C.prefixWalk hZfin hYfin 0 (Nat.zero_le _) = .nil :=
  rfl

/-- The full raw auxiliary walk of a finite macro route, including the final
forward `Z`-member. -/
noncomputable def routeWalk
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    Walk (macroDigraph Z Y)
      (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial C.finalTerminal :=
  (C.prefixWalk hZfin hYfin C.lastIndex le_rfl).append
    (Walk.castEndpoints (C.zFinite_start hZfin _)
      (C.final_zFinite_finish hZfin)
      (C.zBlockWalk (Y := Y) hZfin
        ⟨C.lastIndex, Nat.lt_succ_self _⟩))

/-- Raw vertices of the finite route, indexed from zero through the number
of raw edges. -/
noncomputable def routeRawVertex
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    Fin ((C.routeWalk hZfin hYfin).length + 1) → V :=
  fun i ↦ (C.routeWalk hZfin hYfin).support.get ⟨i.1, by
    rw [Walk.support_length_eq_length_add_one]
    exact i.2⟩

@[simp]
theorem routeRawVertex_zero
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    C.routeRawVertex hZfin hYfin ⟨0, Nat.zero_lt_succ _⟩ =
      (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial := by
  unfold routeRawVertex
  calc
    (C.routeWalk hZfin hYfin).support.get ⟨0, by
        rw [Walk.support_length_eq_length_add_one]
        omega⟩ =
        (C.routeWalk hZfin hYfin).support.head
          (C.routeWalk hZfin hYfin).support_ne_nil := by
            rw [List.get_eq_getElem, List.head_eq_getElem_zero]
    _ = _ := (C.routeWalk hZfin hYfin).head_support

@[simp]
theorem routeRawVertex_last
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    C.routeRawVertex hZfin hYfin
      ⟨(C.routeWalk hZfin hYfin).length, Nat.lt_succ_self _⟩ =
      C.finalTerminal := by
  unfold routeRawVertex
  have hlast := (C.routeWalk hZfin hYfin).getLast_support
  rw [List.getLast_eq_getElem] at hlast
  have hspos : 0 < (C.routeWalk hZfin hYfin).support.length :=
    List.length_pos_iff.mpr (C.routeWalk hZfin hYfin).support_ne_nil
  let j : Fin (C.routeWalk hZfin hYfin).support.length :=
    ⟨(C.routeWalk hZfin hYfin).support.length - 1, by omega⟩
  have hindex :
      (⟨(C.routeWalk hZfin hYfin).length, by
        rw [Walk.support_length_eq_length_add_one]
        omega⟩ : Fin (C.routeWalk hZfin hYfin).support.length) = j := by
    apply Fin.ext
    dsimp only [j]
    rw [Walk.support_length_eq_length_add_one]
    omega
  change (C.routeWalk hZfin hYfin).support.get _ = C.finalTerminal
  rw [hindex, List.get_eq_getElem]
  exact hlast

theorem routeRawVertex_adj
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin (C.routeWalk hZfin hYfin).length) :
    MacroEdge Z Y
      (C.routeRawVertex hZfin hYfin ⟨i.1, by omega⟩)
      (C.routeRawVertex hZfin hYfin ⟨i.1 + 1, by omega⟩) := by
  unfold routeRawVertex
  exact Walk.adj_get_support_route (C.routeWalk hZfin hYfin) i.1 (by
    rw [Walk.support_length_eq_length_add_one]
    omega)

theorem routeWalk_length_pos
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    {u : V} (hp₀ : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial = u)
    (huT : u ∉ Γ.terminalFrontier Z) :
    0 < (C.routeWalk hZfin hYfin).length := by
  by_contra hnot
  have hzero : (C.routeWalk hZfin hYfin).length = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hend : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial = C.finalTerminal :=
    Walk.endpoints_eq_of_length_eq_zero (C.routeWalk hZfin hYfin) hzero
  have hfinal : C.finalTerminal = u := hend.symm.trans hp₀
  apply huT
  refine ⟨(C.z ⟨C.lastIndex, Nat.lt_succ_self _⟩).1,
    (C.z ⟨C.lastIndex, Nat.lt_succ_self _⟩).2, ?_⟩
  simpa [hfinal] using C.final_terminal

end FiniteMacroRoute

end Alternating
end Erdos599

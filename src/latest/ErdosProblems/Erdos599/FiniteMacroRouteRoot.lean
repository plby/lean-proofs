/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteMacroRouteTools

/-!
# Root uniqueness in a finite macro route

The chronological erasure of a finite macro route must retain its prescribed
initial vertex.  This file proves the required raw occurrence statement: the
root occurs only at position zero of the concrete route walk.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

namespace FiniteMacroRoute

variable {Z Y : Set Γ.DPath} (C : FiniteMacroRoute Γ Z Y)

/-- The root is absent from the tail of every nonfinal step block. -/
theorem root_not_mem_stepBlockWalk_tail
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y)
    (i : Fin C.lastIndex) :
    (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉
      (C.stepBlockWalk hZfin hYfin i).support.tail := by
  let r := (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial
  let zsupp := (C.zFinite hZfin ⟨i.1, by omega⟩).walk.support
  let ysupp := (C.yFinite hYfin i).walk.support.dropLast.reverse
  have hznonempty : zsupp ≠ [] :=
    (C.zFinite hZfin ⟨i.1, by omega⟩).walk.support_ne_nil
  have hzhead : zsupp.head hznonempty = (C.z ⟨i.1, by omega⟩).1.initial := by
    exact (C.zFinite hZfin ⟨i.1, by omega⟩).walk.head_support.trans
      (C.zFinite_start hZfin ⟨i.1, by omega⟩)
  have hzcons : zsupp =
      (C.z ⟨i.1, by omega⟩).1.initial :: zsupp.tail := by
    rw [← hzhead]
    exact (List.cons_head_tail hznonempty).symm
  rw [C.support_stepBlockWalk hZfin hYfin i]
  change r ∉ (zsupp ++ ysupp).tail
  rw [hzcons]
  simp only [List.cons_append, List.tail_cons, List.mem_append, not_or]
  constructor
  · intro hrzTail
    have hrz : r ∈ (C.z ⟨i.1, by omega⟩).1.support := by
      rw [C.z_eq_zFinite hZfin ⟨i.1, by omega⟩]
      exact List.mem_of_mem_tail hrzTail
    have hzEq : C.z ⟨i.1, by omega⟩ =
        C.z ⟨0, Nat.zero_lt_succ _⟩ := by
      apply Subtype.ext
      exact DWeb.IsWarp.eq_of_mem_support hZ
        (C.z ⟨i.1, by omega⟩).2
        (C.z ⟨0, Nat.zero_lt_succ _⟩).2 hrz
        (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial_mem_support
    have hi0 : i.1 = 0 := congrArg Fin.val
      ((C.z_injective hZ hY hroot) hzEq)
    have hrootHead : zsupp.head hznonempty = r := by
      rw [hzhead]
      exact congrArg (fun j : Fin (C.lastIndex + 1) ↦ (C.z j).1.initial)
        (Fin.ext hi0)
    have hnodup : zsupp.Nodup :=
      (C.zFinite hZfin ⟨i.1, by omega⟩).isPath
    rw [← hrootHead] at hrzTail
    have hnodup' :
        ((C.z ⟨i.1, by omega⟩).1.initial :: zsupp.tail).Nodup := by
      rw [← hzcons]
      exact hnodup
    exact (List.nodup_cons.mp hnodup').1 (hzhead ▸ hrzTail)
  · intro hry
    apply hroot
    rw [DWeb.mem_vertexSet]
    refine ⟨(C.y i).1, (C.y i).2, ?_⟩
    rw [C.y_eq_yFinite hYfin i]
    change r ∈ (C.yFinite hYfin i).walk.support.dropLast.reverse at hry
    exact List.mem_of_mem_dropLast (List.mem_reverse.mp hry)

/-- The root is absent from the tail of the final forward `Z` block. -/
theorem root_not_mem_final_zBlockWalk_tail
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y) :
    (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉
      (C.zBlockWalk (Y := Y) hZfin
        ⟨C.lastIndex, Nat.lt_succ_self _⟩).support.tail := by
  let i : Fin (C.lastIndex + 1) :=
    ⟨C.lastIndex, Nat.lt_succ_self _⟩
  let r := (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial
  rw [C.support_zBlockWalk hZfin i]
  intro hrTail
  have hrz : r ∈ (C.z i).1.support := by
    rw [C.z_eq_zFinite hZfin i]
    exact List.mem_of_mem_tail hrTail
  have hzEq : C.z i = C.z ⟨0, Nat.zero_lt_succ _⟩ := by
    apply Subtype.ext
    exact DWeb.IsWarp.eq_of_mem_support hZ (C.z i).2
      (C.z ⟨0, Nat.zero_lt_succ _⟩).2 hrz
      (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial_mem_support
  have hi0 : i.1 = 0 := congrArg Fin.val
    ((C.z_injective hZ hY hroot) hzEq)
  have hsupp := (C.zFinite hZfin i).isPath
  have hnonempty := (C.zFinite hZfin i).walk.support_ne_nil
  have hhead : (C.zFinite hZfin i).walk.support.head hnonempty = r := by
    calc
      _ = (C.z i).1.initial :=
        (C.zFinite hZfin i).walk.head_support.trans
          (C.zFinite_start hZfin i)
      _ = r := congrArg
        (fun j : Fin (C.lastIndex + 1) ↦ (C.z j).1.initial)
        (Fin.ext hi0)
  have hcons := List.cons_head_tail hnonempty
  rw [hhead] at hcons
  have hsupp' :
      (r :: (C.zFinite hZfin i).walk.support.tail).Nodup := by
    rw [hcons]
    exact hsupp
  exact (List.nodup_cons.mp hsupp').1 hrTail

/-- Appending the first `n` complete steps never reintroduces the root. -/
theorem root_not_mem_prefixWalk_tail
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y) :
    ∀ (n : ℕ) (hn : n ≤ C.lastIndex),
      (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉
        (C.prefixWalk hZfin hYfin n hn).support.tail := by
  intro n
  induction n with
  | zero =>
      intro hn
      simp [C.prefixWalk_zero hZfin hYfin]
  | succ n ih =>
      intro hn
      change (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉
        ((C.prefixWalk hZfin hYfin n (by omega)).append
          (C.stepBlockWalk hZfin hYfin ⟨n, by omega⟩)).support.tail
      rw [Walk.support_append]
      have hpne :
          (C.prefixWalk hZfin hYfin n (by omega)).support ≠ [] :=
        (C.prefixWalk hZfin hYfin n (by omega)).support_ne_nil
      rw [show (C.prefixWalk hZfin hYfin n (by omega)).support =
          (C.prefixWalk hZfin hYfin n (by omega)).support.head hpne ::
            (C.prefixWalk hZfin hYfin n (by omega)).support.tail by
        exact (List.cons_head_tail hpne).symm]
      simp only [List.cons_append, List.tail_cons, List.mem_append, not_or]
      exact ⟨ih (by omega), C.root_not_mem_stepBlockWalk_tail
        hZ hY hZfin hYfin hroot ⟨n, by omega⟩⟩

/-- The route root occurs only at the first raw vertex. -/
theorem routeRawVertex_root_unique
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y)
    (i : Fin ((C.routeWalk hZfin hYfin).length + 1))
    (hi : C.routeRawVertex hZfin hYfin i =
      C.routeRawVertex hZfin hYfin ⟨0, Nat.zero_lt_succ _⟩) :
    i.1 = 0 := by
  by_contra hi0
  have hmemTail :
      C.routeRawVertex hZfin hYfin i ∈
        (C.routeWalk hZfin hYfin).support.tail := by
    unfold routeRawVertex
    apply List.getElem_mem_tail _ hi0
  have hrootTail :
      (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∈
        (C.routeWalk hZfin hYfin).support.tail := by
    rwa [hi, C.routeRawVertex_zero hZfin hYfin] at hmemTail
  unfold routeWalk at hrootTail
  rw [Walk.support_append] at hrootTail
  have hpne :
      (C.prefixWalk hZfin hYfin C.lastIndex le_rfl).support ≠ [] :=
    (C.prefixWalk hZfin hYfin C.lastIndex le_rfl).support_ne_nil
  rw [show (C.prefixWalk hZfin hYfin C.lastIndex le_rfl).support =
      (C.prefixWalk hZfin hYfin C.lastIndex le_rfl).support.head hpne ::
        (C.prefixWalk hZfin hYfin C.lastIndex le_rfl).support.tail by
    exact (List.cons_head_tail hpne).symm] at hrootTail
  simp only [Walk.support_castEndpoints, List.cons_append, List.tail_cons,
    List.mem_append] at hrootTail
  exact hrootTail.elim
    (C.root_not_mem_prefixWalk_tail hZ hY hZfin hYfin hroot _ le_rfl)
    (C.root_not_mem_final_zBlockWalk_tail hZ hY hZfin hroot)

end FiniteMacroRoute

end Alternating
end Erdos599

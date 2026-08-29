/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingMacroChain

/-!
# Flattening the endpoint-pure macro chain

This file turns each path-level macro step into a concrete finite walk in the
auxiliary relation `MacroEdge`: first traverse the selected `Z`-path forward,
then traverse the selected `Y`-path backward.  It also records exact support
control.  The latter is the key input to the chronological loop-erasure
construction: injectivity of the macro paths implies that a vertex can occur
in only finitely many flattened blocks.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

/-- The auxiliary digraph whose edges go forward on `Z` and backward on
`Y`. -/
def macroDigraph (Z Y : Set Γ.DPath) : Digraph V :=
  ⟨MacroEdge Z Y⟩

namespace Walk

/-- Reinterpret a walk in any relation containing all its directed edge
occurrences. -/
def into {D : Digraph V} (E : V → V → Prop) {a b : V} :
    (p : Walk D a b) →
      (∀ ⦃x y⦄, (x, y) ∈ p.edgeSet → E x y) → Walk ⟨E⟩ a b
  | .nil, _ => .nil
  | .cons h p, hsub =>
      .cons (hsub (by simp [Walk.edgeSet_cons]))
        (into E p (fun _ _ hxy ↦ hsub (by
          simp only [Walk.edgeSet_cons, Set.mem_union,
            Set.mem_singleton_iff]
          exact Or.inr hxy)))

@[simp]
theorem support_into {D : Digraph V} (E : V → V → Prop) {a b : V}
    (p : Walk D a b) (hsub) :
    (into E p hsub).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp only [into, Walk.support_cons]
      rw [ih]

/-- Traverse a walk backwards in any relation containing all its reversed
edge occurrences. -/
def reverseInto {D : Digraph V} (E : V → V → Prop) {a b : V} :
    (p : Walk D a b) →
      (∀ ⦃x y⦄, (x, y) ∈ p.edgeSet → E y x) → Walk ⟨E⟩ b a
  | .nil, _ => .nil
  | .cons h p, hsub =>
      (reverseInto E p (fun _ _ hxy ↦ hsub (by
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff]
        exact Or.inr hxy))).concat
        (hsub (by simp [Walk.edgeSet_cons]))

@[simp]
theorem support_reverseInto {D : Digraph V} (E : V → V → Prop) {a b : V}
    (p : Walk D a b) (hsub) :
    (reverseInto E p hsub).support = p.support.reverse := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp only [reverseInto, Walk.support_concat, Walk.support_cons,
        List.reverse_cons]
      rw [ih]

/-- Transport both displayed endpoints of a walk along equalities. -/
def castEndpoints {D : Digraph V} {a b c d : V}
    (ha : a = c) (hb : b = d) (p : Walk D a b) : Walk D c d := by
  subst c
  subst d
  exact p

@[simp]
theorem support_castEndpoints {D : Digraph V} {a b c d : V}
    (ha : a = c) (hb : b = d) (p : Walk D a b) :
    (castEndpoints ha hb p).support = p.support := by
  subst c
  subst d
  rfl

end Walk

namespace MacroChain

variable {Z Y : Set Γ.DPath} (C : MacroChain Z Y)

/-- The chosen concrete finite representative of the `n`th `Z`-path. -/
noncomputable def zFinite (hZfin : Γ.HasFiniteCharacter Z) (n : ℕ) :
    FinitePath Γ.graph :=
  Classical.choose (hZfin (C.z n).2)

theorem z_eq_zFinite (hZfin : Γ.HasFiniteCharacter Z) (n : ℕ) :
    (C.z n).1 = .inl (C.zFinite hZfin n) :=
  Classical.choose_spec (hZfin (C.z n).2)

/-- The chosen concrete finite representative of the intervening `Y`-path. -/
noncomputable def yFinite (hYfin : Γ.HasFiniteCharacter Y) (n : ℕ) :
    FinitePath Γ.graph :=
  Classical.choose (hYfin (C.y n).2)

theorem y_eq_yFinite (hYfin : Γ.HasFiniteCharacter Y) (n : ℕ) :
    (C.y n).1 = .inl (C.yFinite hYfin n) :=
  Classical.choose_spec (hYfin (C.y n).2)

/-- The forward half of a macro block, retaining the concrete walk rather
than merely its reachability closure. -/
noncomputable def zBlockWalk (hZfin : Γ.HasFiniteCharacter Z) (n : ℕ) :
    Walk (macroDigraph Z Y) (C.zFinite hZfin n).start
      (C.zFinite hZfin n).finish :=
  Walk.into (MacroEdge Z Y) (C.zFinite hZfin n).walk (by
    intro x y hxy
    exact Or.inl (by
      simp only [familyEdges, Set.mem_iUnion]
      refine ⟨(C.z n).1, (C.z n).2, ?_⟩
      rw [C.z_eq_zFinite hZfin n]
      exact hxy))

@[simp]
theorem support_zBlockWalk (hZfin : Γ.HasFiniteCharacter Z) (n : ℕ) :
    (C.zBlockWalk (Y := Y) hZfin n).support =
      (C.zFinite hZfin n).walk.support := by
  exact Walk.support_into _ _ _

/-- The backward half of a macro block. -/
noncomputable def yBlockWalk (hYfin : Γ.HasFiniteCharacter Y) (n : ℕ) :
    Walk (macroDigraph Z Y) (C.yFinite hYfin n).finish
      (C.yFinite hYfin n).start :=
  Walk.reverseInto (MacroEdge Z Y) (C.yFinite hYfin n).walk (by
    intro x y hxy
    exact Or.inr (by
      simp only [familyEdges, Set.mem_iUnion]
      refine ⟨(C.y n).1, (C.y n).2, ?_⟩
      rw [C.y_eq_yFinite hYfin n]
      exact hxy))

@[simp]
theorem support_yBlockWalk (hYfin : Γ.HasFiniteCharacter Y) (n : ℕ) :
    (C.yBlockWalk (Z := Z) hYfin n).support =
      (C.yFinite hYfin n).walk.support.reverse := by
  exact Walk.support_reverseInto _ _ _

/-- The finite auxiliary walk realizing one full macro step. -/
noncomputable def blockWalk
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (n : ℕ) :
    Walk (macroDigraph Z Y) (C.z n).1.initial (C.z (n + 1)).1.initial := by
  let f := C.zBlockWalk (Y := Y) hZfin n
  let b := C.yBlockWalk (Z := Z) hYfin n
  have hfstart' : (C.zFinite hZfin n).start = (C.z n).1.initial := by
    exact (congrArg Path.initial (C.z_eq_zFinite hZfin n)).symm
  have hffinish : (C.zFinite hZfin n).finish = C.terminal n := by
    have h := C.z_terminal n
    rw [C.z_eq_zFinite hZfin n] at h
    exact Option.some.inj h
  have hbfinish : (C.yFinite hYfin n).finish = C.terminal n := by
    have h := C.y_terminal n
    rw [C.y_eq_yFinite hYfin n] at h
    exact Option.some.inj h
  have hjoin : (C.zFinite hZfin n).finish =
      (C.yFinite hYfin n).finish := hffinish.trans hbfinish.symm
  have hbstart : (C.yFinite hYfin n).start =
      (C.z (n + 1)).1.initial := by
    exact (congrArg Path.initial (C.y_eq_yFinite hYfin n)).symm.trans
      (C.joins n)
  exact Walk.castEndpoints hfstart' hbstart
    (f.append (Walk.castEndpoints hjoin.symm rfl b))

/-- The flattened support of a macro block is the forward carrier support
followed by the reversed backward-carrier support, with their common terminal
listed only once. -/
@[simp]
theorem support_blockWalk
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (n : ℕ) :
    (C.blockWalk hZfin hYfin n).support =
      (C.zFinite hZfin n).walk.support ++
        (C.yFinite hYfin n).walk.support.reverse.tail := by
  let f := C.zBlockWalk (Y := Y) hZfin n
  let b := C.yBlockWalk (Z := Z) hYfin n
  have hfstart' : (C.zFinite hZfin n).start = (C.z n).1.initial := by
    exact (congrArg Path.initial (C.z_eq_zFinite hZfin n)).symm
  have hffinish : (C.zFinite hZfin n).finish = C.terminal n := by
    have h := C.z_terminal n
    rw [C.z_eq_zFinite hZfin n] at h
    exact Option.some.inj h
  have hbfinish : (C.yFinite hYfin n).finish = C.terminal n := by
    have h := C.y_terminal n
    rw [C.y_eq_yFinite hYfin n] at h
    exact Option.some.inj h
  have hjoin : (C.zFinite hZfin n).finish =
      (C.yFinite hYfin n).finish := hffinish.trans hbfinish.symm
  have hbstart : (C.yFinite hYfin n).start =
      (C.z (n + 1)).1.initial := by
    exact (congrArg Path.initial (C.y_eq_yFinite hYfin n)).symm.trans
      (C.joins n)
  change (Walk.castEndpoints hfstart' hbstart
      (f.append (Walk.castEndpoints hjoin.symm rfl b))).support = _
  calc
    _ = (f.append (Walk.castEndpoints hjoin.symm rfl b)).support :=
      Walk.support_castEndpoints _ _ _
    _ = f.support ++ (Walk.castEndpoints hjoin.symm rfl b).support.tail :=
      Walk.support_append _ _
    _ = f.support ++ b.support.tail := by
      rw [Walk.support_castEndpoints]
    _ = _ := by
      rw [show f.support = (C.zFinite hZfin n).walk.support from
        C.support_zBlockWalk hZfin n]
      rw [show b.support = (C.yFinite hYfin n).walk.support.reverse from
        C.support_yBlockWalk hYfin n]

end MacroChain

end Alternating
end Erdos599

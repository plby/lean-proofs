/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingComponents
import ErdosProblems.Erdos599.AlternatingMacroChain

/-!
# Local finiteness and infinitude for the macro-edge relation

This file records the two graph-theoretic facts needed to pass from an
infinite path-level `MacroChain` to an infinite locally finite auxiliary
component.

* `MacroEdge Z Y` is locally finite when `Z` and `Y` are finite-character
  warps.
* Every `Z`-initial occurring in a macro chain is reachable from the first
  one.  Under the usual uncovered-root hypothesis these initials are
  pairwise distinct, so the reachable set is infinite.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The directed macro-edge relation is a subrelation of the symmetric
edge relation used by `AlternatingComponents`.  Hence finite-character
warps give finite outgoing macro-edge neighborhoods. -/
theorem finite_macroEdge_neighbors {Z Y : Set Gamma.DPath}
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z)
    (hYfinite : Gamma.HasFiniteCharacter Y) (x : V) :
    {y | MacroEdge Z Y x y}.Finite := by
  refine (AlternatingComponents.finite_edgeRel_neighbors
    hZ hY hZfinite hYfinite x).subset ?_
  intro y hxy
  rcases hxy with hxy | hyx
  · exact Or.inl (Or.inl hxy)
  · exact Or.inr (Or.inr hyx)

namespace MacroChain

/-- Every `Z`-initial in a macro chain is macro-edge reachable from the
initial vertex of the first `Z`-path. -/
theorem z_initial_reachable {Z Y : Set Gamma.DPath}
    (C : MacroChain Z Y)
    (hZfinite : Gamma.HasFiniteCharacter Z)
    (hYfinite : Gamma.HasFiniteCharacter Y) (n : ℕ) :
    Relation.ReflTransGen (MacroEdge Z Y)
      (C.z 0).1.initial (C.z n).1.initial := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      exact ih.trans (MacroStep.reachable hZfinite hYfinite (C.step n))

/-- Distinct indices of a macro chain have distinct `Z`-initials, provided
the chain starts outside `V[Y]`. -/
theorem z_initial_injective {Z Y : Set Gamma.DPath}
    (C : MacroChain Z Y)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hroot : (C.z 0).1.initial ∉ Gamma.vertexSet Y) :
    Function.Injective (fun n => (C.z n).1.initial) := by
  have hz : Function.Injective C.z := C.z_injective hZ hY hroot
  intro i j hij
  change (C.z i).1.initial = (C.z j).1.initial at hij
  apply hz
  apply Subtype.ext
  exact DWeb.IsWarp.eq_of_mem_support hZ (C.z i).2 (C.z j).2
    (C.z i).1.initial_mem_support
    (by rw [hij]; exact (C.z j).1.initial_mem_support)

/-- If the `Z`-initials of a macro chain are pairwise distinct, their
macro-edge reachable set is infinite.  This formulation is useful when
injectivity has already been established by a different invariant. -/
theorem macroEdge_reachable_infinite_of_z_initial_injective
    {Z Y : Set Gamma.DPath}
    (C : MacroChain Z Y)
    (hZfinite : Gamma.HasFiniteCharacter Z)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinj : Function.Injective (fun n => (C.z n).1.initial)) :
    {x | Relation.ReflTransGen (MacroEdge Z Y)
      (C.z 0).1.initial x}.Infinite := by
  exact Set.infinite_of_injective_forall_mem hinj
    (fun n => C.z_initial_reachable hZfinite hYfinite n)

/-- The standard uncovered-root hypotheses on a macro chain make its
macro-edge reachable set infinite. -/
theorem macroEdge_reachable_infinite {Z Y : Set Gamma.DPath}
    (C : MacroChain Z Y)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Gamma.vertexSet Y) :
    {x | Relation.ReflTransGen (MacroEdge Z Y)
      (C.z 0).1.initial x}.Infinite := by
  exact C.macroEdge_reachable_infinite_of_z_initial_injective
    hZfinite hYfinite (C.z_initial_injective hZ hY hroot)

end MacroChain

end Alternating
end Erdos599

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingMacroEdgeProvenance

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

namespace MacroChain

variable {Z Y : Set Γ.DPath} (C : MacroChain Z Y)

/-- Each tagged macro member occupies a finite half-open raw block interval.
This is the boundedness input showing that the loop-erased stream changes
colour infinitely often. -/
theorem streamEdgeTag_fiber_finite
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (a : EdgeTag) :
    {k | C.streamEdgeTag hZ hY hZfin hYfin hroot k = a}.Finite := by
  cases a with
  | inl n =>
      apply (Set.finite_Ico
        (C.streamBoundary hZ hY hZfin hYfin hroot n)
        (C.streamBoundary hZ hY hZfin hYfin hroot (n + 1))).subset
      intro k hk
      have hblock :
          C.streamEdgeBlock hZ hY hZfin hYfin hroot k = n := by
        change C.streamEdgeTag hZ hY hZfin hYfin hroot k = .inl n at hk
        dsimp only [streamEdgeTag] at hk
        split at hk <;> simp_all
      exact (C.streamEdgeBlock_eq_iff
        hZ hY hZfin hYfin hroot k n).mp hblock
  | inr n =>
      apply (Set.finite_Ico
        (C.streamBoundary hZ hY hZfin hYfin hroot n)
        (C.streamBoundary hZ hY hZfin hYfin hroot (n + 1))).subset
      intro k hk
      have hblock :
          C.streamEdgeBlock hZ hY hZfin hYfin hroot k = n := by
        change C.streamEdgeTag hZ hY hZfin hYfin hroot k = .inr n at hk
        dsimp only [streamEdgeTag] at hk
        split at hk <;> simp_all
      exact (C.streamEdgeBlock_eq_iff
        hZ hY hZfin hYfin hroot k n).mp hblock

end MacroChain

end Alternating
end Erdos599

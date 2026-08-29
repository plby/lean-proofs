/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint

/-!
# Degenerate witnesses for weak imaginary edges

The negation of strongness does not by itself make a separately selected
alternating path degenerate.  What it does say, exactly, is that every
successor-sized hammock witnessing the imaginary edge contains a degenerate
member.  This file records that source-level consequence without conflating
the hammock member with a later assigned contact interval.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {u₀ v : V}

/-- Every particular large hammock witnessing a weak imaginary edge has a
degenerate member. -/
theorem IsWeakImaginaryEdge.exists_degenerate_mem_of_hammock
    (hweak : IsWeakImaginaryEdge Gamma Y kappa u₀ v)
    {H : Set (AltPath Gamma.graph)}
    (hH : Hammock Gamma Y u₀ (.vertex v) H)
    (hcard : #H = succ kappa) :
    ∃ Q ∈ H, IsDegenerate Y Q (.vertex v) := by
  by_contra hnot
  push Not at hnot
  exact hweak.2 ⟨H, ⟨hH, hnot⟩, hcard⟩

/-- A weak imaginary edge admits a successor-sized hammock together with a
specific degenerate member of that same hammock. -/
theorem IsWeakImaginaryEdge.exists_hammock_with_degenerate_mem
    (hweak : IsWeakImaginaryEdge Gamma Y kappa u₀ v) :
    ∃ H : Set (AltPath Gamma.graph),
      Hammock Gamma Y u₀ (.vertex v) H ∧ #H = succ kappa ∧
        ∃ Q ∈ H, IsDegenerate Y Q (.vertex v) := by
  obtain ⟨H, hH, hcard⟩ := hweak.1
  exact ⟨H, hH, hcard,
    hweak.exists_degenerate_mem_of_hammock hH hcard⟩

end Erdos599.Blueprint

#print axioms Erdos599.Blueprint.IsWeakImaginaryEdge.exists_degenerate_mem_of_hammock
#print axioms Erdos599.Blueprint.IsWeakImaginaryEdge.exists_hammock_with_degenerate_mem

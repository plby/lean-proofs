/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92OuterInjectivityBridge

/-!
# Terminal constructor from a reduced body

This is the exact handoff from the minimal-rank Section 9.2 body to the
stable `ReducedOuterRealization` API.  The selected Section 3 Mahler
container is constructed internally, and bounded-body injectivity is
converted to injectivity on its `2s` dilation by the explicit containment
proved in `Section92OuterInjectivityBridge`.
-/

namespace Erdos186.CFP.Bilu.Section92ReducedOuterConstructor

open Module
open Mahler
open Section9ContainerIntegration Section94SortedContainerAssembly
open Section92OuterInjectivityBridge

noncomputable section

/-- Construct the complete terminal outer realization from the output of
the Section 9.2 minimal-rank body argument. -/
theorem exists_reducedOuterRealization_of_body
    {n s volumeConstant rankBound : ℕ} {A : Finset ℤ}
    (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (hfull : AdmitsIndependent p n 1)
    (phi : Mahler.IntegralPoint n →+ ℤ)
    (hinj : Set.InjOn phi
      {z : Mahler.IntegralPoint n |
        p (integralEmbed z) ≤ outerDilationBound n (2 * s)})
    (hlifts : ∀ a ∈ A, ∃ z : Mahler.IntegralPoint n,
      p (integralEmbed z) ≤ 1 ∧ phi z = a)
    (hvolume : ∀ D : MappedOuterContainer p phi,
      D.source.volume ≤ volumeConstant * A.card)
    (hrank : n ≤ rankBound) :
    Nonempty (ReducedOuterRealization s volumeConstant rankBound A) := by
  obtain ⟨D⟩ := exists_mappedOuterContainer hn p hp hfull phi
  exact ⟨{
    rank := n
    seminorm := p
    map := phi
    outer := D
    enlarged_injective :=
      enlarged_injective_of_injectiveOn_seminormBall D hp hfull hinj
    lifts := hlifts
    volume_le := hvolume D
    rank_le := hrank }⟩

end

end Erdos186.CFP.Bilu.Section92ReducedOuterConstructor

#print axioms Erdos186.CFP.Bilu.Section92ReducedOuterConstructor.exists_reducedOuterRealization_of_body

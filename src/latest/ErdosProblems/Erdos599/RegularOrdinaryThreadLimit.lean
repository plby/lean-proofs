/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CofinalChainLimit
import ErdosProblems.Erdos599.SliceSpliceConstructor

/-!
# Ordinary splice threads at a ladder limit

A cofinal growing chain made of literal accumulated-ladder prefixes has the
same thread limits as the ladder's own limit-stage chain.  Consequently each
ordinary splice thread limit is a member of the accumulated warp at the
limiting stage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

universe u v w

namespace DWeb.GrowingWarpChain

variable {V : Type u} {G : DWeb V}
variable {I : Type v} [LinearOrder I] [Nonempty I]
variable {J : Type w} [LinearOrder J]

/-- A cofinal stagewise embedding of growing warp chains sends every thread
limit of the first chain to the limit family of the second. -/
theorem threadLimit_mem_limitPaths_of_cofinal
    (C : G.GrowingWarpChain I) (E : G.GrowingWarpChain J)
    (stageIndex : I → J) (hmono : Monotone stageIndex)
    (hcofinal : ∀ j, ∃ i, j ≤ stageIndex i)
    (a : C.initialUnion)
    (hstage : ∀ i p, p ∈ C.stage i → p.initial = a.1 →
      p ∈ E.stage (stageIndex i)) :
    C.threadLimit G a ∈ E.limitPaths G := by
  obtain ⟨p₀, i₀, hp₀, hp₀initial⟩ := C.thread_nonempty G a
  have hp₀E : p₀ ∈ E.stage (stageIndex i₀) :=
    hstage i₀ p₀ hp₀ hp₀initial
  have haE : a.1 ∈ E.initialUnion :=
    Set.mem_iUnion.2 ⟨stageIndex i₀, p₀, hp₀E, hp₀initial⟩
  let b : E.initialUnion := ⟨a.1, haE⟩
  have hthreadSubset : C.thread G a.1 ⊆ E.thread G b.1 := by
    rintro p ⟨i, hpi, hpinitial⟩
    exact ⟨stageIndex i, hstage i p hpi hpinitial, hpinitial⟩
  have hthreadCofinal : ∀ q ∈ E.thread G b.1,
      ∃ p ∈ C.thread G a.1, G.Extends q p := by
    rintro q ⟨j, hqj, hqinitial⟩
    obtain ⟨i, hji⟩ := hcofinal j
    let k : I := max i i₀
    have hjk : j ≤ stageIndex k :=
      hji.trans (hmono (le_max_left i i₀))
    obtain ⟨r, hrk, hqr⟩ := E.grows hjk q hqj
    obtain ⟨p, hpk, hp₀p⟩ :=
      C.grows (show i₀ ≤ k from le_max_right i i₀) p₀ hp₀
    have hpinitial : p.initial = a.1 :=
      (G.extends_initial hp₀p).symm.trans hp₀initial
    have hpEk : p ∈ E.stage (stageIndex k) :=
      hstage k p hpk hpinitial
    have hrinitial : r.initial = a.1 :=
      (G.extends_initial hqr).symm.trans hqinitial
    have hrp : r = p :=
      DWeb.IsWarp.eq_of_initial_eq G (E.isWarp (stageIndex k)) hrk hpEk
        (hrinitial.trans hpinitial.symm)
    exact ⟨p, ⟨k, hpk, hpinitial⟩, hrp ▸ hqr⟩
  have hlimitEq : C.threadLimit G a = E.threadLimit G b :=
    DirectedPath.Path.chainLimit_eq_of_subset_of_cofinal
      (C.thread G a.1) (E.thread G b.1)
      (C.thread_nonempty G a) (E.thread_nonempty G b)
      (C.thread_isChain G a.1) (E.thread_isChain G b.1)
      hthreadSubset hthreadCofinal
  exact ⟨b, hlimitEq.symm⟩

end DWeb.GrowingWarpChain

namespace CardinalInduction.SliceSpliceConstructor

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- At a genuine limit stage, every cofinal growing chain consisting of
literal accumulated-ladder prefixes has its thread limits in that stage's
accumulated warp. -/
theorem threadLimit_mem_warpAt_of_cofinal_stagePrefix
    {L : Gamma.KappaLadder kappa} (hlimit : L.HasLimitStages)
    {I : Type v} [LinearOrder I] [Nonempty I]
    (C : Gamma.GrowingWarpChain I)
    (stageIndex : I → Ladder.Stage kappa)
    (beta : Ladder.Stage kappa) (hbeta : Order.IsSuccLimit beta.1)
    (hindex : ∀ i, stageIndex i < beta)
    (hmono : Monotone stageIndex)
    (hcofinal : ∀ b : Set.Iio beta.1,
      ∃ i, b.1 ≤ (stageIndex i).1)
    (a : C.initialUnion)
    (hprefix : ∀ i p, p ∈ C.stage i → p.initial = a.1 →
      SliceSplice.StagePrefix Gamma L (stageIndex i) p) :
    C.threadLimit Gamma a ∈ L.warpAt beta := by
  obtain ⟨E, hstageE, hlimitE⟩ :=
    hlimit (Ladder.Stage.toExtended beta) hbeta
  let f : I → Set.Iio beta.1 := fun i ↦
    ⟨(stageIndex i).1, hindex i⟩
  have hfmono : Monotone f := by
    intro i j hij
    exact hmono hij
  have hfcofinal : ∀ b, ∃ i, b ≤ f i := by
    intro b
    obtain ⟨i, hi⟩ := hcofinal b
    exact ⟨i, hi⟩
  have hfstage : ∀ i p, p ∈ C.stage i → p.initial = a.1 →
      p ∈ E.stage (f i) := by
    intro i p hp hpinitial
    obtain ⟨g, rfl, hgEssential, _hgfinish⟩ :=
      hprefix i p hp hpinitial
    rw [hstageE (f i)]
    exact hgEssential.1
  have hmem : C.threadLimit Gamma a ∈ E.limitPaths Gamma :=
    C.threadLimit_mem_limitPaths_of_cofinal E f hfmono hfcofinal a hfstage
  change C.threadLimit Gamma a ∈
    L.accumulated (Ladder.Stage.toExtended beta)
  rwa [hlimitE]

end CardinalInduction.SliceSpliceConstructor
end Erdos599

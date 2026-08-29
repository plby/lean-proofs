/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate

/-!
# Bounding exceptional members of a source star

If all but a small subfamily of the continuation row reconstruct ordinary
reference fragments, then all mavericks of the starred row inject into that
small exceptional continuation family.  The injection uses the unique
continuation at the old terminal.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularStarMaverickBound

universe u

variable {V : Type u}

theorem mk_sliceMavericks_star_lt
    {G : DWeb V} {kappa : Cardinal.{u}}
    {A C T : Set V} {W R Good Y : Set G.DPath}
    (hW : IsLinkageBetween G A C W)
    (hR : IsLinkageBetween G C T R)
    (hcompat : G.StarCompatible W R)
    (hGood : Good ⊆ R)
    (hbad : #(↥(R \ Good)) < kappa)
    (hordinary : ∀ (p : W) (q : G.DPath), q ∈ Good →
      G.terminal? p.1 = some q.initial →
        ControlledSlices.IsLadderFragment G Y (G.starPath hcompat p)) :
    #(ControlledSlices.sliceMavericks G Y (G.star hcompat)) < kappa := by
  classical
  let M := ControlledSlices.sliceMavericks G Y (G.star hcompat)
  let old (p : M) : W := Classical.choose p.2.1
  have hold (p : M) : G.starPath hcompat (old p) = p.1 :=
    Classical.choose_spec p.2.1
  let oldFinite (p : M) : DirectedPath.FinitePath G.graph :=
    Classical.choose (hW.finiteCharacter (old p).2)
  have holdFinite (p : M) :
      (old p).1 = .inl (oldFinite p) :=
    Classical.choose_spec (hW.finiteCharacter (old p).2)
  have hmatch (p : M) :
      ∃ q ∈ R, q.initial = (oldFinite p).finish := by
    have hterminal : (oldFinite p).finish ∈ G.terminalFrontier W :=
      ⟨(old p).1, (old p).2, by rw [holdFinite]; rfl⟩
    have hinitial : (oldFinite p).finish ∈ G.initialSet R := by
      rw [hR.initialSet_eq]
      exact hW.terminalFrontier_subset hterminal
    obtain ⟨q, hqR, hqInitial⟩ := hinitial
    exact ⟨q, hqR, hqInitial⟩
  let next (p : M) : G.DPath := Classical.choose (hmatch p)
  have hnextR (p : M) : next p ∈ R :=
    (Classical.choose_spec (hmatch p)).1
  have hnextInitial (p : M) :
      (next p).initial = (oldFinite p).finish :=
    (Classical.choose_spec (hmatch p)).2
  have hnextBad (p : M) : next p ∈ R \ Good := by
    refine ⟨hnextR p, ?_⟩
    intro hgood
    apply p.2.2
    rw [← hold p]
    apply hordinary (old p) (next p) hgood
    rw [holdFinite p]
    exact congrArg some (hnextInitial p).symm
  let badNext (p : M) : ↥(R \ Good) := ⟨next p, hnextBad p⟩
  have hnextSupport (p : M) : (next p).initial ∈ p.1.support := by
    rw [← hold p]
    change (next p).initial ∈
      (G.starPath hcompat (old p)).support
    let old' : W := ⟨.inl (oldFinite p), by
      simpa only [← holdFinite p] using (old p).2⟩
    have holdOld : old p = old' := Subtype.ext (holdFinite p)
    rw [holdOld]
    dsimp only [old', DWeb.starPath]
    rw [dif_pos (hmatch p)]
    let q := Classical.choose (hmatch p)
    have hqR : q ∈ R := (Classical.choose_spec (hmatch p)).1
    have hqInitial : q.initial = (oldFinite p).finish :=
      (Classical.choose_spec (hmatch p)).2
    have hqNext : q = next p := by
      by_contra hne
      exact Set.disjoint_left.1 (hR.isWarp hqR (hnextR p) hne)
        q.initial_mem_support
        (hqInitial.trans (hnextInitial p).symm ▸
          (next p).initial_mem_support)
    have hinter : (oldFinite p).support ∩ q.support ⊆
        {(oldFinite p).finish} := by
      intro x hx
      have hx' := hcompat (.inl (oldFinite p))
        (by simpa only [holdFinite p] using (old p).2)
        q hqR x hx.1 hx.2
      exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
    change (next p).initial ∈
      (DirectedPath.Path.appendFinite (oldFinite p) q
        hqInitial hinter).support
    rw [DirectedPath.Path.support_appendFinite]
    exact Or.inr (hqNext ▸ (next p).initial_mem_support)
  have hinjective : Function.Injective badNext := by
    intro p q hpq
    apply Subtype.ext
    by_contra hpne
    have hnextEq : next p = next q := congrArg Subtype.val hpq
    exact Set.disjoint_left.1
      (G.isWarp_star hW.isWarp hR.isWarp hcompat p.2.1 q.2.1 hpne)
      (hnextSupport p)
      (by simpa only [hnextEq] using hnextSupport q)
  exact (Cardinal.mk_le_of_injective hinjective).trans_lt hbad

end RegularStarMaverickBound
end CardinalInduction
end Erdos599

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualRootedOutput
import ErdosProblems.Erdos599.GroundingSourceRootTransfer

/-!
# The untouched hanging-component obstruction in the equal branch

The stationary equal subwarp need not target every hanging component of the
limiting ladder.  This file records the exact obstruction that results.  If
the inserted forward edges do not touch a hanging limiting component, then
the repaired relation cannot root its terminal at an original source.

Thus the source-rooted premise isolated by `GroundingEqualRootedOutput`
requires a whole-family coverage argument (or a larger relation); it does
not follow merely from stationarity and collision-free thinning.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open GroundingEqualActiveSelection
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev EqualInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :=
  L.popularAuxiliaryInput hL.legal

/-- Under the standard source normalization, a hanging path contains no
original source vertex at all. -/
theorem support_disjoint_source_of_hanging
    (p : Gamma.DPath)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p) :
    Disjoint p.support Gamma.source := by
  rw [Set.disjoint_left]
  intro x hxp hxsource
  have hno : ¬ Alternating.HasIncoming
      (Alternating.familyEdges ({p} : Set Gamma.DPath)) x := by
    rintro ⟨y, hyx⟩
    exact hNoEnter
      (Alternating.familyEdges_subset_adj ({p} : Set Gamma.DPath) hyx)
      hxsource
  have hinitial : p.initial = x :=
    Alternating.initial_eq_of_mem_support_of_noIncoming
      (W := ({p} : Set Gamma.DPath)) (p := p) (by simp) hxp hno
  exact hhang (hinitial.symm ▸ hxsource)

/-- If no inserted forward edge is incident with a limiting-ladder member,
then every repaired edge entering its support came from that same member. -/
theorem repairedEdge_tail_mem_of_head_mem_of_forward_avoids
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    {p : Gamma.DPath} (hpLimit : p ∈ L.limitWarp)
    (hforward : ∀ e ∈ canonicalErasedForwardEdges (EqualInput L hL) Q,
      e.1 ∉ p.support ∧ e.2 ∉ p.support)
    {x y : V} (hy : y ∈ p.support)
    (hxy : (x, y) ∈
      canonicalErasedRepairedEdges (EqualInput L hL) Q) :
    x ∈ p.support := by
  rcases hxy with hbase | hinserted
  · obtain ⟨q, hqLimit, hxyQ⟩ := hbase.1.1
    have hyQ : y ∈ q.support := (q.edgeSet_subset_support_prod hxyQ).2
    have hpq : p = q :=
      Alternating.DWeb.IsWarp.eq_of_mem_support
        (hL.legal.warpStages (Ladder.finalStage kappa))
        hpLimit hqLimit hy hyQ
    rw [hpq]
    exact (q.edgeSet_subset_support_prod hxyQ).1
  · exact False.elim ((hforward (x, y) hinserted).2 hy)

/-- Consequently, any repaired-relation root of a point on the untouched
component must itself lie on that component. -/
theorem root_mem_support_of_reaches_of_forward_avoids
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    {p : Gamma.DPath} (hpLimit : p ∈ L.limitWarp)
    (hforward : ∀ e ∈ canonicalErasedForwardEdges (EqualInput L hL) Q,
      e.1 ∉ p.support ∧ e.2 ∉ p.support)
    {a b : V}
    (hab : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈
        canonicalErasedRepairedEdges (EqualInput L hL) Q) a b)
    (hb : b ∈ p.support) :
    a ∈ p.support := by
  induction hab with
  | refl => exact hb
  | @tail x y hax hxy ih =>
      apply ih
      exact repairedEdge_tail_mem_of_head_mem_of_forward_avoids
        L hL Q hpLimit hforward hb hxy

/-- Machine-checked form of the untouched hanging-component obstruction:
the terminal of such a component has no original-source root in the
canonical repaired relation. -/
theorem not_sourceRooted_terminal_of_hanging_of_forward_avoids
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {p : Gamma.DPath} (hpLimit : p ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p)
    {b : V} (hpterminal : Gamma.terminal? p = some b)
    (hforward : ∀ e ∈ canonicalErasedForwardEdges (EqualInput L hL) Q,
      e.1 ∉ p.support ∧ e.2 ∉ p.support) :
    ¬ ∃ a ∈ Gamma.source, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈
        canonicalErasedRepairedEdges (EqualInput L hL) Q) a b := by
  rintro ⟨a, haSource, hab⟩
  have hbSupport : b ∈ p.support := Gamma.terminal_mem_support hpterminal
  have haSupport : a ∈ p.support :=
    root_mem_support_of_reaches_of_forward_avoids
      L hL Q hpLimit hforward hab hbSupport
  exact Set.disjoint_left.1
    (support_disjoint_source_of_hanging p hNoEnter hhang)
    haSupport haSource

end KappaLadder
end DWeb
end Erdos599

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.ClosedJordanSimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Planar domains without bounded complementary components

This file isolates the purely topological reduction used in the simple-connectivity argument.
A set has no bounded complementary component when every connected component of its complement
is unbounded.  Such a set contains the bounded side of every Jordan curve that it contains.
Consequently, the standard Jordan-enclosure theorem for open connected plane domains reduces
simple connectivity to this no-bounded-component condition.
-/

open Bornology Set

namespace Schoenflies

/-- A plane set has no bounded complementary component. -/
def HasNoBoundedComplementComponents (D : Set Plane) : Prop :=
  ∀ x ∈ Dᶜ, ¬ IsBounded (connectedComponentIn Dᶜ x)

/-- A plane set has Jordan enclosures if every compact connected subset is contained in a
closed Jordan disc whose boundary is carried by the set. -/
def HasJordanEnclosures (D : Set Plane) : Prop :=
  ∀ K : Set Plane, IsCompact K → IsConnected K → K ⊆ D →
    ∃ C : Set Plane, IsJordanCurve C ∧ K ⊆ C ∪ inside C ∧ C ⊆ D

/-- If `D` has no bounded complementary component, then it contains the bounded side of every
Jordan curve carried by `D`.

Indeed, a complementary component of `D` meeting the Jordan interior stays in the corresponding
component of the complement of the curve, hence is bounded. -/
theorem inside_subset_of_hasNoBoundedComplementComponents {D C : Set Plane}
    (hD : HasNoBoundedComplementComponents D) (hC : IsJordanCurve C) (hCD : C ⊆ D) :
    inside C ⊆ D := by
  intro x hx
  by_contra hxD
  have hxDc : x ∈ Dᶜ := hxD
  have hcompl : Dᶜ ⊆ Cᶜ := compl_subset_compl.mpr hCD
  have hcomponent : connectedComponentIn Dᶜ x ⊆ connectedComponentIn Cᶜ x :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxDc)
      ((connectedComponentIn_subset Dᶜ x).trans hcompl)
  have hsep := jordan_curve_theorem hC
  have hbounded : IsBounded (connectedComponentIn Dᶜ x) :=
    hsep.isBounded_inside.subset (by
      rwa [hsep.connectedComponentIn_eq_inside hx] at hcomponent)
  exact hD x hxDc hbounded

/-- The exact topological reduction: Jordan enclosure plus absence of bounded complementary
components makes an open connected plane domain simply connected. -/
theorem isSimplyConnected_of_hasNoBoundedComplementComponents
    {D : Set Plane} (hopen : IsOpen D) (hconnected : IsConnected D)
    (hholes : HasNoBoundedComplementComponents D) (henclose : HasJordanEnclosures D) :
    IsSimplyConnected D := by
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  refine ⟨hopen.isConnected_iff_isPathConnected.mp hconnected, ?_⟩
  intro x p hp
  have hcompact : IsCompact (range p) := _root_.isCompact_range p.continuous
  have hconn : IsConnected (range p) := _root_.isConnected_range p.continuous
  have hsub : range p ⊆ D := by
    rintro _ ⟨t, rfl⟩
    exact hp t
  obtain ⟨C, hC, hpC, hCD⟩ := henclose (range p) hcompact hconn hsub
  have hin : inside C ⊆ D :=
    inside_subset_of_hasNoBoundedComplementComponents hholes hC hCD
  have hdisc : C ∪ inside C ⊆ D := union_subset hCD hin
  have hsimply := hC.isSimplyConnected_union_inside
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem] at hsimply
  obtain ⟨F, hF⟩ := hsimply.2 x p (fun t ↦ hpC (mem_range_self t))
  exact ⟨F, fun z ↦ hdisc (hF z)⟩

end Schoenflies

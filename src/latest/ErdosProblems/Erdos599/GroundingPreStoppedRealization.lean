/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedOutput
import ErdosProblems.Erdos599.GroundingReservedFrontierOutput
import ErdosProblems.Erdos599.GroundingSourceRootTransfer

/-!
# Realizing the pre-stopped Assertion 8.22 relation

This file studies the reserved simultaneous switch *before* any boundary
stopping.  Isolated boundary vertices can be added explicitly; all other
boundary vertices are covered by incidence with the realized relation.

The literal `BB` need not be a reachability antichain, and stopping every
departure from `BB` can strand a later boundary point.  The sound compilers
below therefore keep those issues explicit.  They also give total
clean-output/obstruction dichotomies: a construction-specific exchange
argument may turn an unrooted point or an ordered boundary collision directly
into a hindrance, without pretending that either obstruction is absent.
-/

noncomputable section

open Set

namespace Erdos599

open _root_.Erdos599.DirectedPath

namespace GroundingPreStoppedRealization

universe u

variable {V : Type u} {Gamma : DWeb V}

/-! ## Ordered reachability inside one directed path -/

theorem walk_start_reaches_of_mem_support
    {D : Digraph V} : ∀ {a b : V} (p : Walk D a b) {x : V},
    x ∈ p.support →
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ p.edgeSet) a x
  | a, _, .nil, x, hx => by
      have hxa : x = a := by simpa using hx
      subst x
      exact .refl
  | a, _, .cons h p, x, hx => by
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact .refl
      · have htail := walk_start_reaches_of_mem_support p hx
        have htail' : Relation.ReflTransGen
            (fun u v ↦ (u, v) ∈ (Walk.cons h p).edgeSet) _ x :=
          Relation.ReflTransGen.mono
            (r := fun u v ↦ (u, v) ∈ p.edgeSet)
            (p := fun u v ↦ (u, v) ∈ (Walk.cons h p).edgeSet)
            (by
              intro u v huv
              exact Set.mem_union_right _ huv) _ x htail
        exact htail'.head (by simp)

theorem walk_support_reachability_total
    {D : Digraph V} : ∀ {a b : V} (p : Walk D a b) {x y : V},
    x ∈ p.support → y ∈ p.support →
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ p.edgeSet) x y ∨
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ p.edgeSet) y x
  | a, _, .nil, x, y, hx, hy => by
      have hxa : x = a := by simpa using hx
      have hya : y = a := by simpa using hy
      subst x
      subst y
      exact Or.inl .refl
  | a, _, .cons h p, x, y, hx, hy => by
      simp only [Walk.support_cons, List.mem_cons] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact Or.inl .refl
      · exact Or.inl (walk_start_reaches_of_mem_support
          (Walk.cons h p) (by simp [hy]))
      · exact Or.inr (walk_start_reaches_of_mem_support
          (Walk.cons h p) (by simp [hx]))
      · rcases walk_support_reachability_total p hx hy with hxy | hyx
        · exact Or.inl (Relation.ReflTransGen.mono
            (r := fun u v ↦ (u, v) ∈ p.edgeSet)
            (p := fun u v ↦ (u, v) ∈ (Walk.cons h p).edgeSet)
            (by
              intro u v huv
              exact Set.mem_union_right _ huv) x y hxy)
        · exact Or.inr (Relation.ReflTransGen.mono
            (r := fun u v ↦ (u, v) ∈ p.edgeSet)
            (p := fun u v ↦ (u, v) ∈ (Walk.cons h p).edgeSet)
            (by
              intro u v huv
              exact Set.mem_union_right _ huv) y x hyx)

theorem ray_reaches_of_le
    {D : Digraph V} (r : Ray D) {m n : ℕ} (hmn : m ≤ n) :
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ r.edgeSet) (r m) (r n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => exact .refl
  | succ d ih =>
      apply ih.tail
      refine ⟨m + d, ?_⟩
      simp [Nat.add_assoc]

theorem path_support_reachability_total
    {D : Digraph V} (p : Path D) {x y : V}
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ p.edgeSet) x y ∨
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ p.edgeSet) y x := by
  rcases p with p | r
  · exact walk_support_reachability_total p.walk hx hy
  · obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    rcases Nat.le_total m n with hmn | hnm
    · exact Or.inl (ray_reaches_of_le r hmn)
    · exact Or.inr (ray_reaches_of_le r hnm)

/-- A reachability antichain meets every component of an exact path-family
realization in at most one vertex. -/
theorem component_inter_subsingleton_of_realized_reachabilityAntichain
    {S : Alternating.SwitchData Gamma} {W : Set Gamma.DPath}
    (hR : S.RealizedBy W) {B : Set V}
    (hanti : GroundingRootedReachabilityWarp.IsReachabilityAntichain
      S.edges B) {p : Gamma.DPath} (hp : p ∈ W) :
    (p.support ∩ B).Subsingleton := by
  intro x hx y hy
  rcases path_support_reachability_total p hx.1 hy.1 with hxy | hyx
  · apply hanti hx.2 hy.2
    exact Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈ p.edgeSet)
      (p := fun u v ↦ (u, v) ∈ S.edges)
      (by
        intro u v huv
        rw [← hR.2.1]
        exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, huv⟩⟩)
      x y hxy
  · symm
    apply hanti hy.2 hx.2
    exact Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈ p.edgeSet)
      (p := fun u v ↦ (u, v) ∈ S.edges)
      (by
        intro u v huv
        rw [← hR.2.1]
        exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, huv⟩⟩)
      y x hyx

end GroundingPreStoppedRealization

namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode
open GroundingPreStoppedRealization

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The reserved simultaneous relation before any boundary stopping.  The
empty stopping set retains every forward edge and deletes no residual
boundary departure. -/
abbrev assertion822ReservedPreStoppedEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) : Set (V × V) :=
  L.assertion822ReservedSwitchedEdgesAt hL S R ∅

/-- Exact switch data for the pre-stopped relation.  A point of `BB` which
is not incident with a relation edge is retained as a singleton component. -/
def assertion822ReservedPreStoppedSwitchData
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) : SwitchData Gamma where
  edges := L.assertion822ReservedPreStoppedEdges hL S R
  edges_in_graph :=
    L.assertion822ReservedSwitchedEdgesAt_subset_adj hL S R ∅
  isolated := GroundingCut.BB
      (L.popularAuxiliaryInput hL.legal) S.cut \
    RelationDecomposition.IncidentVertices
      (L.assertion822ReservedPreStoppedEdges hL S R)

/-- The only global decomposition premises not supplied by local
bi-uniqueness: the pre-stopped relation has neither a directed cycle nor a
reverse directed ray. -/
structure Assertion822PreStoppedCompatible
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) : Prop where
  noDirectedCycle : ¬ ContainsDirectedCycle
    (L.assertion822ReservedPreStoppedEdges hL S R)
  noReverseDirectedRay : ¬ ContainsReverseDirectedRay
    (L.assertion822ReservedPreStoppedEdges hL S R)

/-- Sound flexible-frontier compiler for the pre-stopped relation.  Unlike
the earlier `T`-stopped construction, the relation itself is independent of
`T`; hence choosing an orthogonal separating sub-boundary cannot strand a
later frontier point by deleting an upstream departure. -/
theorem assertion822Output_of_preStoppedFrontierGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) (T : Set V)
    (hTsubset : T ⊆
      GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)
    (hTseparator : Popular.IsSeparator Gamma T)
    (hanti : GroundingRootedReachabilityWarp.IsReachabilityAntichain
      (L.assertion822ReservedPreStoppedEdges hL S R) T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  apply GroundingAssertion822Output.exists_of_rootedReachability
    (L.popularAuxiliaryInput hL.legal) S.cut
    (L.assertion822ReservedPreStoppedEdges hL S R)
    (Gamma.source \ {R.record.initial}) T
    (L.assertion822ReservedSwitchedEdgesAt_subset_adj hL S R ∅)
    (L.assertion822ReservedSwitchedEdgesAt_biUnique hL S R ∅)
    Set.sdiff_subset hTsubset hTseparator hanti hroot
    R.record.initial R.record_initial_mem_source
  simp

/-- Finite rooted components suffice for Assertion 8.22; components of the
pre-stopped relation which do not meet `BB` need not be decomposed at all.
Thus no global acyclicity or reverse-ray premise is needed once the literal
`BB` antichain and rooted-reachability statements are known. -/
theorem assertion822Output_of_preStoppedRootedGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (hanti : GroundingRootedReachabilityWarp.IsReachabilityAntichain
      (L.assertion822ReservedPreStoppedEdges hL S R)
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut))
    (hroot : ∀ b ∈ GroundingCut.BB
        (L.popularAuxiliaryInput hL.legal) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R) a b) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  apply GroundingAssertion822Output.exists_of_rootedReachability
    (L.popularAuxiliaryInput hL.legal) S.cut
    (L.assertion822ReservedPreStoppedEdges hL S R)
    (Gamma.source \ {R.record.initial})
    (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)
    (L.assertion822ReservedSwitchedEdgesAt_subset_adj hL S R ∅)
    (L.assertion822ReservedSwitchedEdgesAt_biUnique hL S R ∅)
    Set.sdiff_subset Subset.rfl
    (GroundingAssertion818Decoder.assertion8_18
      L hL.legal S.cut S.separates)
    hanti hroot R.record.initial R.record_initial_mem_source
  simp

/-- A concrete obstruction to using the literal bookkeeping boundary as the
frontier of the pre-stopped switch: two distinct boundary points occur in
the same directed switched component, in this order.  Keeping this witness
explicit is useful because the grounding argument can handle some such
collisions directly, instead of incorrectly treating `BB` as an automatic
reachability antichain. -/
structure Assertion822PreStoppedBoundaryObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) where
  earlier : V
  later : V
  earlier_mem : earlier ∈
    GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut
  later_mem : later ∈
    GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut
  distinct : earlier ≠ later
  reaches : Relation.ReflTransGen
    (fun x y ↦
      (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R) earlier later

/-- A literal boundary point for which the reserved pre-stopped relation has
no root in the allowed part of the original source. -/
structure Assertion822PreStoppedRootObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) where
  boundary : V
  boundary_mem : boundary ∈
    GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut
  not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
    Relation.ReflTransGen
      (fun x y ↦
        (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R) a boundary

/-- Exact clean-output/obstruction dichotomy for the pre-stopped relation.
Once every literal boundary point is rooted away from the reserved source,
either Assertion 8.22 follows, or there is a displayed ordered collision of
two distinct `BB` points.  The latter is the precise input needed by the
construction-specific exchange branch. -/
theorem assertion822Output_or_preStoppedBoundaryObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (hroot : ∀ b ∈ GroundingCut.BB
        (L.popularAuxiliaryInput hL.legal) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R) a b) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      Nonempty (L.Assertion822PreStoppedBoundaryObstruction hL S R) := by
  classical
  by_cases hanti : GroundingRootedReachabilityWarp.IsReachabilityAntichain
      (L.assertion822ReservedPreStoppedEdges hL S R)
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)
  · exact Or.inl
      (L.assertion822Output_of_preStoppedRootedGeometry hL S R hanti hroot)
  · right
    by_contra hnone
    apply hanti
    intro b hb c hc hbc
    by_contra hne
    exact hnone ⟨{
      earlier := b
      later := c
      earlier_mem := hb
      later_mem := hc
      distinct := hne
      reaches := hbc }⟩

/-- Total reduction for the pre-stopped construction.  For fixed reserved
controls, either Assertion 8.22 is already obtained, a literal boundary
point has no allowed source root, or two distinct literal boundary points
are ordered in one switched component.  These are exactly the two honest
construction-specific exchange obligations; no false global antichain or
rootedness premise is hidden in the statement. -/
theorem assertion822Output_or_preStoppedObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      Nonempty (L.Assertion822PreStoppedRootObstruction hL S R) ∨
      Nonempty (L.Assertion822PreStoppedBoundaryObstruction hL S R) := by
  classical
  by_cases hroot : ∀ b ∈ GroundingCut.BB
      (L.popularAuxiliaryInput hL.legal) S.cut,
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦
          (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R) a b
  · rcases L.assertion822Output_or_preStoppedBoundaryObstruction
        hL S R hroot with houtput | hboundary
    · exact Or.inl houtput
    · exact Or.inr (Or.inr hboundary)
  · right
    left
    by_contra hnone
    apply hroot
    intro b hb
    by_contra hnotRooted
    exact hnone ⟨{
      boundary := b
      boundary_mem := hb
      not_rooted := hnotRooted }⟩

/-- Compile construction-specific repairs of the two pre-stopped
obstructions into the disjunction consumed by the final grounding theorem.
The repair callbacks may return a hindrance directly; they are not forced
to manufacture an Assertion 8.22 warp in a configuration where the literal
boundary is not an antichain. -/
theorem assertion822Output_or_hindrance_of_preStoppedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (repairRoot : L.Assertion822PreStoppedRootObstruction hL S R →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary :
      L.Assertion822PreStoppedBoundaryObstruction hL S R →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  rcases L.assertion822Output_or_preStoppedObstruction hL S R with
      houtput | hroot | hboundary
  · exact Or.inl houtput
  · exact Or.inr (repairRoot hroot.some)
  · exact Or.inr (repairBoundary hboundary.some)

/-- Unreserved wrapper for the preceding repair compiler.  Stationarity
chooses the reserved grounded record before the two construction-specific
callbacks are invoked. -/
theorem assertion822Output_or_hindrance_of_preStoppedRepairs'
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ R : L.UnusedGroundedRecord hL S,
      L.Assertion822PreStoppedRootObstruction hL S R →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ R : L.UnusedGroundedRecord hL S,
      L.Assertion822PreStoppedBoundaryObstruction hL S R →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  let R := (L.exists_unusedGroundedRecord hL S).some
  exact L.assertion822Output_or_hindrance_of_preStoppedRepairs hL S R
    (repairRoot R) (repairBoundary R)

/-! ## Alternative reduction through the literal-boundary-stopped switch -/

/-- A literal boundary point stranded by stopping every departure from
`BB`.  This is the sole obstruction in the stopped construction, since its
boundary is automatically a reachability antichain. -/
structure Assertion822StoppedRootObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) where
  boundary : V
  boundary_mem : boundary ∈
    GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut
  not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ L.assertion822ReservedSwitchedEdgesAt
        hL S R (GroundingCut.BB
          (L.popularAuxiliaryInput hL.legal) S.cut)) a boundary

/-- Total reduction for the switch stopped at the complete literal
boundary.  If every boundary point remains rooted, the reserved frontier
compiler gives Assertion 8.22; otherwise the displayed stranded point is
the exact construction-specific exchange witness. -/
theorem assertion822Output_or_stoppedRootObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      Nonempty (L.Assertion822StoppedRootObstruction hL S R) := by
  classical
  let B := GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut
  by_cases hroot : ∀ b ∈ B,
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedSwitchedEdgesAt hL S R B) a b
  · left
    apply L.assertion822Output_of_reservedFrontierGeometry hL S R B
      Subset.rfl
    · exact GroundingAssertion818Decoder.assertion8_18
        L hL.legal S.cut S.separates
    · exact hroot
  · right
    by_contra hnone
    apply hroot
    intro b hb
    by_contra hnotRooted
    exact hnone ⟨{
      boundary := b
      boundary_mem := hb
      not_rooted := hnotRooted }⟩

/-- Repair compiler for the literal-boundary-stopped construction. -/
theorem assertion822Output_or_hindrance_of_stoppedRootRepair
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repair : ∀ R : L.UnusedGroundedRecord hL S,
      L.Assertion822StoppedRootObstruction hL S R →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  let R := (L.exists_unusedGroundedRecord hL S).some
  rcases L.assertion822Output_or_stoppedRootObstruction hL S R with
      houtput | hobstruction
  · exact Or.inl houtput
  · exact Or.inr (repair R hobstruction.some)

/-- Compatibility gives an honest original-web warp realizing the complete
pre-stopped relation and all isolated `BB` points. -/
theorem Assertion822PreStoppedCompatible.exists_realization
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (h : L.Assertion822PreStoppedCompatible hL S R) :
    ∃ W : Set Gamma.DPath,
      (L.assertion822ReservedPreStoppedSwitchData hL S R).RealizedBy W := by
  apply
    Alternating.RayCompatibleRelationDecomposition.exists_warp_realizing_biUnique_with_isolated
    Gamma (L.assertion822ReservedPreStoppedEdges hL S R)
    ((L.assertion822ReservedPreStoppedSwitchData hL S R).isolated)
    (L.assertion822ReservedSwitchedEdgesAt_subset_adj hL S R ∅)
    (L.assertion822ReservedSwitchedEdgesAt_biUnique hL S R ∅)
    h.noDirectedCycle h.noReverseDirectedRay
  intro x hx y
  constructor
  · intro hxy
    exact hx.2 ⟨y, Or.inl hxy⟩
  · intro hyx
    exact hx.2 ⟨y, Or.inr hyx⟩

/-- Relation-level completion of Assertion 8.22.  Compatibility constructs
the pre-stopped warp; incidence/singleton coverage is automatic.  The two
remaining source arguments are exactly the source-root and one-boundary-hit
claims for the pre-stopped relation. -/
theorem assertion822Output_of_preStoppedRelationGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (hcompat : L.Assertion822PreStoppedCompatible hL S R)
    (hanti : GroundingRootedReachabilityWarp.IsReachabilityAntichain
      (L.assertion822ReservedPreStoppedEdges hL S R)
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut))
    (hroot : ∀ b ∈ GroundingCut.BB
        (L.popularAuxiliaryInput hL.legal) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R) a b ∧
        ¬ HasIncoming (L.assertion822ReservedPreStoppedEdges hL S R) a) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  classical
  obtain ⟨W, hR⟩ := hcompat.exists_realization
  apply L.assertion822Output_of_preStoppedWarpGeometry hL S R W hR.1
  · intro p hpW hpBB
    exact Alternating.SwitchData.component_initial_mem_of_rooted_reachability
      (L.assertion822ReservedPreStoppedSwitchData hL S R)
      hR (Gamma.source \ {R.record.initial})
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)
      hroot hpW hpBB
  · apply GroundingBBGeometry.subset_vertexSet_of_realized_isolated_or_incident
      hR
    intro b hb
    by_cases hincident : b ∈ RelationDecomposition.IncidentVertices
        (L.assertion822ReservedPreStoppedEdges hL S R)
    · exact Or.inr hincident
    · exact Or.inl ⟨hb, hincident⟩
  · intro p hpW
    exact component_inter_subsingleton_of_realized_reachabilityAntichain
      hR hanti hpW

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_of_preStoppedRelationGeometry
#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_of_preStoppedRootedGeometry
#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_of_preStoppedFrontierGeometry
#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_or_preStoppedBoundaryObstruction
#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_or_preStoppedObstruction
#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedRepairs'
#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_stoppedRootRepair

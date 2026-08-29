/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating
import ErdosProblems.Erdos599.FracturedDuplication
import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.Blueprint
import ErdosProblems.Erdos599.SafeSwitching

/-!
# The closure step in Assertion 9.31

This file isolates Claim 2 in the proof of Aharoni--Berger Assertion 9.31.
The point of the closing-up construction is that a safe alternating path
which is not already contained in the closed set can be adjoined to the
chosen maximal hammock.  Hence the ``large hammock'' branch of maximality
must hold.  For a finite prescribed endpoint this gives an imaginary edge;
for the endpoint at infinity it gives popularity.

The lemma is deliberately stated for the exact `HammockClosedUpTo`
interface constructed in `HalfwayClause.lean`; it does not assume the
large hammock as an extra input.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Γ : DWeb V} {Y : Set Γ.DPath}

/-! ## Extracting the two induction witnesses used by 9.31 -/

/-- Apply the lower-cardinal induction hypothesis to an auxiliary
unhindered web.  Assertion 9.31 uses this form after passing to a quotient
or deletion whose distinguished source set has cardinality `μ < κ`. -/
theorem exists_lower_halfwayLinkage
    {κ μ : Cardinal.{u}} (hμ : μ < κ) (hμInfinite : aleph0 ≤ μ)
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V κ)
    (Δ : DWeb V) (hΔ : Δ.IsUnhindered)
    (A₀ : Set V) (hA₀ : A₀ ⊆ Δ.source) (hcard : #A₀ = μ) :
    ∃ W : Set Δ.DPath,
      CardinalInduction.IsHalfwayLinkageOfAltitude Δ A₀ μ W := by
  exact (hlower μ hμ Δ hΔ).halfway hμInfinite A₀ hA₀ hcard

/-- Apply the already established current-cardinal extension clause to an
auxiliary unhindered web.  The input linkage is only for the complementary
sources; the output is a full linkage, exactly as in the source proof's
construction of the `T_α`--`T_β` linkage. -/
theorem exists_current_linkage
    {κ : Cardinal.{u}}
    (hext : CardinalInduction.UniversalExtensionClauseAt V κ)
    (Δ : DWeb V) (hΔ : Δ.IsUnhindered)
    (A₀ : Set V) (hA₀ : A₀ ⊆ Δ.source) (hcard : #A₀ = κ)
    (hcomplement : ∃ F : Set Δ.DPath,
      CardinalInduction.IsLinkageBetween Δ (Δ.source \ A₀) Δ.target F) :
    ∃ L : Set Δ.DPath,
      CardinalInduction.IsLinkageBetween Δ Δ.source Δ.target L := by
  exact hext Δ hΔ A₀ hA₀ hcard hcomplement

/-- Adjoining one compatible safe alternating path preserves the hammock
conditions.  Compatibility is needed only for the interiors, since all
members already have the prescribed endpoints. -/
theorem Hammock.insert {u : V} {e : AltEnd V}
    {H : Set (AltPath Γ.graph)} {Q : AltPath Γ.graph}
    (hH : Hammock Γ Y u e H)
    (hQsafe : IsSafe Y Q) (hQinitial : Q.initial = u)
    (hQend : HasEnd Q e)
    (hQdisjoint : ∀ R ∈ H,
      Disjoint (hammockInterior u e Q) (hammockInterior u e R)) :
    Hammock Γ Y u e (insert Q H) := by
  refine ⟨?_, ?_⟩
  · intro R hR
    rcases hR with rfl | hR
    · exact ⟨hQsafe, hQinitial, hQend⟩
    · exact hH.1 R hR
  · intro R hR S hS hRS
    rcases hR with rfl | hR <;> rcases hS with rfl | hS
    · exact (hRS rfl).elim
    · exact hQdisjoint S hS
    · exact (hQdisjoint R hR).symm
    · exact hH.2 hR hS hRS

/-- A path whose interior avoids a set also has interior disjoint from every
hammock contained in that set. -/
theorem disjoint_hammockInterior_of_contained
    {u : V} {e : AltEnd V} {H : Set (AltPath Γ.graph)}
    {Q : AltPath Γ.graph} {X : Set V}
    (hHX : HammockContained H X)
    (hQX : Disjoint (hammockInterior u e Q) X) :
    ∀ R ∈ H,
      Disjoint (hammockInterior u e Q) (hammockInterior u e R) := by
  intro R hR
  apply hQX.mono Set.Subset.rfl
  intro x hx
  exact hHX (Set.mem_iUnion.2 ⟨R, Set.mem_iUnion.2 ⟨hR, hx.1⟩⟩)

/-- Claim 2, common finite/infinite endpoint form.  A closed-up maximal
hammock and a compatible safe path outside the closure force a hammock of
successor size. -/
theorem exists_large_hammock_of_closed
    {X ZBefore innerRoof roof : Set V} {κ : Cardinal.{u}}
    {u : V} {e : AltEnd V} {Q : AltPath Γ.graph}
    (hclosed : HammockClosedUpTo Γ Y X ZBefore innerRoof roof κ)
    (heligible : HammockEligible ZBefore innerRoof roof u e)
    (hQsafe : IsSafe Y Q) (hQinitial : Q.initial = u)
    (hQend : HasEnd Q e)
    (hQX : Disjoint (hammockInterior u e Q) X)
    (hQoutside : ¬ Q.vertexSet ⊆ X) :
    HasHammockCard Γ Y u e (succ κ) := by
  obtain ⟨H, hHmax, hHX⟩ := hclosed u e heligible
  have hHinsert : Hammock Γ Y u e (insert Q H) :=
    hHmax.isHammock.insert hQsafe hQinitial hQend
      (disjoint_hammockInterior_of_contained hHX hQX)
  rcases hHmax with hsmall | hlarge
  · have hEq : H = insert Q H :=
      hsmall.2.1.eq_of_subset hHinsert (Set.subset_insert Q H)
    have hinsert_subset : insert Q H ⊆ H := hEq.symm.subset
    have hQH : Q ∈ H := hinsert_subset (Set.mem_insert Q H)
    exact False.elim <| hQoutside fun x hxQ ↦
      hHX (Set.mem_iUnion.2 ⟨Q, Set.mem_iUnion.2 ⟨hQH, hxQ⟩⟩)
  · exact ⟨hlarge.2.2.choose, hlarge.2.2.choose_spec.1,
      hlarge.2.2.choose_spec.2⟩

/-- Finite-endpoint form of Claim 2: the assigned safe path certifies an
edge of the imaginary graph. -/
theorem isImaginaryEdge_of_closed
    {X ZBefore innerRoof roof : Set V} {κ : Cardinal.{u}}
    {u v : V} {Q : AltPath Γ.graph}
    (hclosed : HammockClosedUpTo Γ Y X ZBefore innerRoof roof κ)
    (heligible : HammockEligible ZBefore innerRoof roof u (.vertex v))
    (hQsafe : IsSafe Y Q) (hQinitial : Q.initial = u)
    (hQend : Q.terminal? = some v)
    (hQX : Disjoint (hammockInterior u (.vertex v) Q) X)
    (hQoutside : ¬ Q.vertexSet ⊆ X) :
    IsImaginaryEdge Γ Y κ u v :=
  exists_large_hammock_of_closed hclosed heligible hQsafe hQinitial
    hQend hQX hQoutside

/-- Removing at most `κ` degenerate members from a size-`κ⁺` hammock leaves
a size-`κ⁺` nondegenerate hammock.  The infinitude hypothesis is exactly the
cardinal arithmetic used in Section 9. -/
theorem hasNondegenerateHammockCard_of_large
    {κ : Cardinal.{u}} (hκ : aleph0 ≤ κ) {u : V} {e : AltEnd V}
    (hlarge : HasHammockCard Γ Y u e (succ κ))
    (hdegenerate : ∀ K : Set (AltPath Γ.graph),
      Hammock Γ Y u e K →
      #{Q : K // IsDegenerate Y Q.1 e} ≤ κ) :
    HasNondegenerateHammockCard Γ Y u e (succ κ) := by
  obtain ⟨K, hK, hKcard⟩ := hlarge
  let bad : Set (AltPath Γ.graph) := {Q | Q ∈ K ∧ IsDegenerate Y Q e}
  let good : Set (AltPath Γ.graph) := K \ bad
  have hgoodK : good ⊆ K := Set.sdiff_subset
  have hgoodH : Hammock Γ Y u e good := hK.subset hgoodK
  have hbadcard : #bad ≤ κ := by
    let f : bad → {Q : K // IsDegenerate Y Q.1 e} :=
      fun Q ↦ ⟨⟨Q.1, Q.2.1⟩, Q.2.2⟩
    exact (Cardinal.mk_le_of_injective (f := f) (by
      intro Q R h
      exact Subtype.ext (congrArg (fun x ↦ (x.1 : AltPath Γ.graph)) h))).trans
        (hdegenerate K hK)
  have hgoodcard : #good = succ κ := by
    apply le_antisymm
    · rw [← hKcard]
      exact Cardinal.mk_le_mk_of_subset hgoodK
    · apply le_of_not_gt
      intro hlt
      have hgoodle : #good ≤ κ := (lt_succ_iff.mp hlt)
      have hKle : #K ≤ κ := by
        calc
          #K ≤ #(K \ bad : Set (AltPath Γ.graph)) + #bad :=
            Cardinal.le_mk_sdiff_add_mk K bad
          _ = #good + #bad := rfl
          _ ≤ κ := Cardinal.add_le_of_le hκ hgoodle hbadcard
      have hs : succ κ ≤ κ := by simpa only [hKcard] using hKle
      exact (not_le_of_gt (lt_succ κ)) hs
  refine ⟨good, ⟨hgoodH, ?_⟩, hgoodcard⟩
  intro Q hQgood hQdegenerate
  exact hQgood.2 ⟨hQgood.1, hQdegenerate⟩

/-- Strong finite-endpoint form of Claim 2.  The separate bound on
degenerate members is the exact content supplied by the source's
degeneracy lemma (Definition 4.10 and the following switching argument). -/
theorem isStrongImaginaryEdge_of_closed
    {X ZBefore innerRoof roof : Set V} {κ : Cardinal.{u}}
    (hκ : aleph0 ≤ κ) {u v : V} {Q : AltPath Γ.graph}
    (hclosed : HammockClosedUpTo Γ Y X ZBefore innerRoof roof κ)
    (heligible : HammockEligible ZBefore innerRoof roof u (.vertex v))
    (hQsafe : IsSafe Y Q) (hQinitial : Q.initial = u)
    (hQend : Q.terminal? = some v)
    (hQX : Disjoint (hammockInterior u (.vertex v) Q) X)
    (hQoutside : ¬ Q.vertexSet ⊆ X)
    (hdegenerate : ∀ K : Set (AltPath Γ.graph),
      Hammock Γ Y u (.vertex v) K →
      #{R : K // IsDegenerate Y R.1 (.vertex v)} ≤ κ) :
    IsStrongImaginaryEdge Γ Y κ u v := by
  apply hasNondegenerateHammockCard_of_large hκ
  · exact exists_large_hammock_of_closed hclosed heligible hQsafe
      hQinitial hQend hQX hQoutside
  · exact hdegenerate

/-- Infinite-endpoint form of Claim 2: the assigned ray certifies that its
initial vertex is popular. -/
theorem isPopular_of_closed_infinite
    {X ZBefore innerRoof roof persistent : Set V} {κ : Cardinal.{u}}
    {u : V} {Q : AltPath Γ.graph}
    (hclosed : HammockClosedUpTo Γ Y X ZBefore innerRoof roof κ)
    (heligible : HammockEligible ZBefore innerRoof roof u .infinity)
    (hQsafe : IsSafe Y Q) (hQinitial : Q.initial = u)
    (hQinfinite : Q.IsInfinite)
    (hQX : Disjoint (hammockInterior u .infinity Q) X)
    (hQoutside : ¬ Q.vertexSet ⊆ X) :
    IsPopular Γ Y persistent κ u := by
  exact Or.inr <| exists_large_hammock_of_closed hclosed heligible hQsafe
    hQinitial hQinfinite hQX hQoutside

/-! ## Applying Claim 2 to the fractured simultaneous assignment -/

/-- The exact closure facts about assigned alternating paths which are
proved from the outside-fragment construction in Assertion 9.31.  Unlike a
compiled path family, this structure mentions only the certificates returned
by Theorem 4.12 and the already constructed closed set. -/
structure AssignmentClosureContext
    {Zf : FracturedWarp Γ}
    (A : SimultaneousAssignment Zf.paths Y)
    (X ZBefore innerRoof roof : Set V) : Prop where
  eligible_finite : ∀ s v,
    (A.assigned s).terminal? = some v →
      HammockEligible ZBefore innerRoof roof s.1 (.vertex v)
  eligible_infinite : ∀ s, (A.assigned s).IsInfinite →
    HammockEligible ZBefore innerRoof roof s.1 .infinity
  interior_disjoint_finite : ∀ s v,
    (h : (A.assigned s).terminal? = some v) →
      Disjoint
        (hammockInterior s.1 (.vertex v) (A.assigned s)) X
  interior_disjoint_infinite : ∀ s,
    (A.assigned s).IsInfinite →
      Disjoint
        (hammockInterior s.1 .infinity (A.assigned s)) X
  outside : ∀ s, ¬(A.assigned s).vertexSet ⊆ X

/-- The simultaneous assignment and the closing-up Claim 2 together turn
every finite assigned endpoint into an imaginary edge and every infinite
assignment into a popular starting vertex.  This is the safe-assignment
half of Assertion 9.31, before the purely graph-theoretic fragment splicing.
-/
theorem classify_simultaneousAssignment_of_closed
    {Zf : FracturedWarp Γ}
    {X ZBefore innerRoof roof persistent : Set V} {κ : Cardinal.{u}}
    (hclosed : HammockClosedUpTo Γ Y X ZBefore innerRoof roof κ)
    (A : SimultaneousAssignment Zf.paths Y)
    (hA : AssignmentClosureContext A X ZBefore innerRoof roof) :
    (∀ s v, (A.assigned s).terminal? = some v →
        IsImaginaryEdge Γ Y κ s.1 v) ∧
      (∀ s, (A.assigned s).IsInfinite →
        IsPopular Γ Y persistent κ s.1) := by
  constructor
  · intro s v hterm
    exact isImaginaryEdge_of_closed hclosed (hA.eligible_finite s v hterm)
      (A.safe s) (A.starts_at s) hterm
      (hA.interior_disjoint_finite s v hterm) (hA.outside s)
  · intro s hinfinite
    exact isPopular_of_closed_infinite hclosed
      (hA.eligible_infinite s hinfinite) (A.safe s) (A.starts_at s)
      hinfinite (hA.interior_disjoint_infinite s hinfinite) (hA.outside s)

/-- Existential form used by Assertion 9.31.  The assignment is constructed
by the fractured version of Theorem 4.12; `closureFacts` contains only the
geometric facts tying that returned assignment to the closed set.
-/
theorem exists_classified_fracturedAssignment
    {Zf : FracturedWarp Γ}
    {X ZBefore innerRoof roof persistent : Set V} {κ : Cardinal.{u}}
    (hassignment : FracturedSimultaneousAssignmentStatement Γ)
    (hΓ : Γ.IsNormalized)
    (hsource : Γ.initialSet Zf.paths ⊆ Γ.source)
    (htarget : Γ.terminalFrontier Zf.paths ⊆ Γ.target)
    (hYwarp : Γ.IsWarp Y)
    (hZfinite : Γ.HasFiniteCharacter Zf.paths)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (hinitial : Γ.initialSet Y ⊆ Γ.initialSet Zf.paths)
    (hclosed : HammockClosedUpTo Γ Y X ZBefore innerRoof roof κ)
    (closureFacts : ∀ A : SimultaneousAssignment Zf.paths Y,
      AssignmentClosureContext A X ZBefore innerRoof roof) :
    ∃ A : SimultaneousAssignment Zf.paths Y,
      (∀ s v, (A.assigned s).terminal? = some v →
          IsImaginaryEdge Γ Y κ s.1 v) ∧
        (∀ s, (A.assigned s).IsInfinite →
          IsPopular Γ Y persistent κ s.1) := by
  let A := (hassignment hΓ Zf Y hsource htarget hYwarp hZfinite
    hYfinite hinitial).some
  exact ⟨A, classify_simultaneousAssignment_of_closed hclosed A
    (closureFacts A)⟩

/-! ### The finite assignment edge relation -/

/-- The endpoint information from a simultaneous fractured assignment which
the global 9.31 transaction actually consumes.

An outcome `some v` means that the source is compressed to the directed
edge `(s,v)`; `none` means that the source is retained as a terminal.  No
original-web alternating path is stored.  This is essential for Remark 4.20:
an occurrence-aware path in the duplicated web need not project to a safe
`AltPath` after connector edges are contracted, while its source, finite
exit, infinity alternative, and finite-exit injectivity remain meaningful. -/
structure CompressedFracturedAssignment (Zf : FracturedWarp Γ)
    (Y : Set Γ.DPath) where
  outcome : {s : V // s ∈ Γ.initialSet Zf.paths \ Γ.initialSet Y} → Option V
  finite_exit_mem : ∀ s v, outcome s = some v →
    v ∈ Γ.terminalFrontier Zf.paths \ Γ.vertexSet Y
  finite_exits_injective : ∀ s₁ s₂ v,
    outcome s₁ = some v → outcome s₂ = some v → s₁ = s₂

namespace CompressedFracturedAssignment

/-- Forget the alternating paths of an ordinary simultaneous assignment and
retain exactly its compressed endpoint transaction. -/
def ofSimultaneous {Zf : FracturedWarp Γ}
    (A : SimultaneousAssignment Zf.paths Y) :
    CompressedFracturedAssignment Zf Y where
  outcome s := (A.assigned s).terminal?
  finite_exit_mem s v hterminal := A.finite_terminal_mem s hterminal
  finite_exits_injective s₁ s₂ v h₁ h₂ :=
    A.finite_terminals_injective h₁ h₂

/-- Retain the projected endpoint data of an occurrence-aware assignment in
the duplicated web.  This does not contract or project its alternating
paths. -/
noncomputable def ofDuplicated {Zf : FracturedWarp Γ}
    (A : FracturedDuplication.DuplicatedFracturedAssignment Zf Y)
    (hYfinite : Γ.HasFiniteCharacter Y) :
    CompressedFracturedAssignment Zf Y where
  outcome := A.endAt hYfinite
  finite_exit_mem _s _v h := A.finite_exit_mem hYfinite h
  finite_exits_injective _s₁ _s₂ _v h₁ h₂ :=
    A.finite_exits_injective hYfinite h₁ h₂

/-- The occurrence-aware analogue of `AssignmentClosureContext`.

The endpoint summary alone is intentionally insufficient: connector
contraction can turn an arbitrary infinite split path into an unsafe forward
ray.  The actual outside-fragment construction therefore supplies, for each
split assignment, a projected path whose safeness and closure geometry are
proved from the fact that all holes come from one finite-character linkage
and all contracted joints lie in the closed set. -/
structure ProjectionClosureContext {Zf : FracturedWarp Γ}
    (A : FracturedDuplication.DuplicatedFracturedAssignment Zf Y)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (X ZBefore innerRoof roof : Set V) where
  projected : FracturedDuplication.AssignmentSource Zf Y → AltPath Γ.graph
  starts_at : ∀ s, (projected s).initial = s.1
  safe : ∀ s, IsSafe Y (projected s)
  finite_ends_at : ∀ s v, A.endAt hYfinite s = some v →
    (projected s).terminal? = some v
  infinite : ∀ s, A.endAt hYfinite s = none →
    (projected s).IsInfinite
  eligible_finite : ∀ s v, A.endAt hYfinite s = some v →
    HammockEligible ZBefore innerRoof roof s.1 (.vertex v)
  eligible_infinite : ∀ s, A.endAt hYfinite s = none →
    HammockEligible ZBefore innerRoof roof s.1 .infinity
  interior_disjoint_finite : ∀ s v,
    (h : A.endAt hYfinite s = some v) →
      Disjoint (hammockInterior s.1 (.vertex v) (projected s)) X
  interior_disjoint_infinite : ∀ s,
    (h : A.endAt hYfinite s = none) →
      Disjoint (hammockInterior s.1 .infinity (projected s)) X
  outside : ∀ s, ¬(projected s).vertexSet ⊆ X

/-- Whole-trace avoidance is the convenient output of the concrete
one-linkage projection theorem.  It implies both interior-disjointness
clauses and ensures that the projected route is not swallowed by the closed
set, so only endpoint preservation and hammock eligibility remain for the
Claim-2 handoff. -/
def ProjectionClosureContext.of_disjoint {Zf : FracturedWarp Γ}
    (A : FracturedDuplication.DuplicatedFracturedAssignment Zf Y)
    (hYfinite : Γ.HasFiniteCharacter Y)
    {X ZBefore innerRoof roof : Set V}
    (projected : FracturedDuplication.AssignmentSource Zf Y →
      AltPath Γ.graph)
    (starts_at : ∀ s, (projected s).initial = s.1)
    (safe : ∀ s, IsSafe Y (projected s))
    (finite_ends_at : ∀ s v, A.endAt hYfinite s = some v →
      (projected s).terminal? = some v)
    (infinite : ∀ s, A.endAt hYfinite s = none →
      (projected s).IsInfinite)
    (avoids : ∀ s, Disjoint (projected s).vertexSet X)
    (eligible_finite : ∀ s v, A.endAt hYfinite s = some v →
      HammockEligible ZBefore innerRoof roof s.1 (.vertex v))
    (eligible_infinite : ∀ s, A.endAt hYfinite s = none →
      HammockEligible ZBefore innerRoof roof s.1 .infinity) :
    ProjectionClosureContext A hYfinite X ZBefore innerRoof roof where
  projected := projected
  starts_at := starts_at
  safe := safe
  finite_ends_at := finite_ends_at
  infinite := infinite
  eligible_finite := eligible_finite
  eligible_infinite := eligible_infinite
  interior_disjoint_finite := by
    intro s v _hfinite
    apply Set.disjoint_of_subset_left _ (avoids s)
    exact fun _ hx ↦ hx.1
  interior_disjoint_infinite := by
    intro s _hinfinite
    apply Set.disjoint_of_subset_left _ (avoids s)
    exact fun _ hx ↦ hx.1
  outside := by
    intro s hsubset
    exact Set.disjoint_left.1 (avoids s)
      (projected s).initial_mem_vertexSet
      (hsubset (projected s).initial_mem_vertexSet)

/-- Apply Claim 2 to the genuine projected paths supplied by the concrete
one-linkage outside-fragment construction. -/
theorem classify_of_projectionClosureContext
    {Zf : FracturedWarp Γ}
    (A : FracturedDuplication.DuplicatedFracturedAssignment Zf Y)
    (hYfinite : Γ.HasFiniteCharacter Y)
    {X ZBefore innerRoof roof persistent : Set V} {κ : Cardinal.{u}}
    (hclosed : HammockClosedUpTo Γ Y X ZBefore innerRoof roof κ)
    (C : ProjectionClosureContext A hYfinite X ZBefore innerRoof roof) :
    (∀ s v, A.endAt hYfinite s = some v →
        IsImaginaryEdge Γ Y κ s.1 v) ∧
      (∀ s, A.endAt hYfinite s = none →
        IsPopular Γ Y persistent κ s.1) := by
  constructor
  · intro s v hfinite
    exact isImaginaryEdge_of_closed hclosed
      (C.eligible_finite s v hfinite) (C.safe s) (C.starts_at s)
      (C.finite_ends_at s v hfinite)
      (C.interior_disjoint_finite s v hfinite) (C.outside s)
  · intro s hinfinite
    exact isPopular_of_closed_infinite hclosed
      (C.eligible_infinite s hinfinite) (C.safe s) (C.starts_at s)
      (C.infinite s hinfinite)
      (C.interior_disjoint_infinite s hinfinite) (C.outside s)

/-- Compressed finite outcomes as an edge relation on the original vertex
type. -/
def finiteEdges {Zf : FracturedWarp Γ}
    (A : CompressedFracturedAssignment Zf Y) : Set (V × V) :=
  {e | ∃ s, A.outcome s = some e.2 ∧ s.1 = e.1}

theorem mem_finiteEdges_iff {Zf : FracturedWarp Γ}
    (A : CompressedFracturedAssignment Zf Y) {u v : V} :
    (u, v) ∈ A.finiteEdges ↔
      ∃ s, A.outcome s = some v ∧ s.1 = u :=
  Iff.rfl

/-- Sources whose duplicated assignment has an infinite outcome. -/
def infiniteSources {Zf : FracturedWarp Γ}
    (A : CompressedFracturedAssignment Zf Y) : Set V :=
  {u | ∃ s, s.1 = u ∧ A.outcome s = none}

/-- A compressed assignment is functional at its sources. -/
theorem finiteEdges_out_unique {Zf : FracturedWarp Γ}
    (A : CompressedFracturedAssignment Zf Y)
    {u v w : V} (huv : (u, v) ∈ A.finiteEdges)
    (huw : (u, w) ∈ A.finiteEdges) : v = w := by
  obtain ⟨s, hsv, hsu⟩ := huv
  obtain ⟨t, htw, htu⟩ := huw
  have hst : s = t := by
    apply Subtype.ext
    exact hsu.trans htu.symm
  subst t
  simpa [hsv] using htw

/-- Injectivity of finite exits makes the compressed edge relation
left-unique at its targets. -/
theorem finiteEdges_in_unique {Zf : FracturedWarp Γ}
    (A : CompressedFracturedAssignment Zf Y)
    {u v w : V} (huw : (u, w) ∈ A.finiteEdges)
    (hvw : (v, w) ∈ A.finiteEdges) : u = v := by
  obtain ⟨s, hsw, hsu⟩ := huw
  obtain ⟨t, htw, htv⟩ := hvw
  have hst : s = t := A.finite_exits_injective s t w hsw htw
  exact hsu.symm.trans (congrArg Subtype.val hst) |>.trans htv

theorem finiteEdges_biUnique {Zf : FracturedWarp Γ}
    (A : CompressedFracturedAssignment Zf Y) :
    Relator.BiUnique (fun u v ↦ (u, v) ∈ A.finiteEdges) := by
  constructor
  · intro u v w huw hvw
    exact A.finiteEdges_in_unique huw hvw
  · intro u v w huv huw
    exact A.finiteEdges_out_unique huv huw

/-- Finite outcomes classified by Claim 2 are edges of the imaginary
graph.  Classification is deliberately an explicit input: occurrence-aware
split paths cannot in general be projected to safe original-web paths. -/
theorem finiteEdges_subset_imaginaryGraph
    {Zf : FracturedWarp Γ} {κ : Cardinal.{u}}
    (A : CompressedFracturedAssignment Zf Y)
    (hfinite : ∀ s v, A.outcome s = some v →
      IsImaginaryEdge Γ Y κ s.1 v) :
    A.finiteEdges ⊆ {e | (imaginaryGraph Γ Y κ).Adj e.1 e.2} := by
  rintro ⟨u, v⟩ ⟨s, hterm, rfl⟩
  exact Or.inr (hfinite s v hterm)

/-- Infinite outcomes classified by Claim 2 are popular. -/
theorem infiniteSources_popular
    {Zf : FracturedWarp Γ} {persistent : Set V} {κ : Cardinal.{u}}
    (A : CompressedFracturedAssignment Zf Y)
    (hinfinite : ∀ s, A.outcome s = none →
      IsPopular Γ Y persistent κ s.1) :
    A.infiniteSources ⊆ {u | IsPopular Γ Y persistent κ u} := by
  rintro u ⟨s, rfl, hs⟩
  exact hinfinite s hs

end CompressedFracturedAssignment

/-- Compress each finite assigned alternating path to its ordered pair of
endpoints.  Infinite assignments deliberately contribute no edge: their
source becomes a terminal of the compiled blueprint. -/
def assignedFiniteEdges {Zf : FracturedWarp Γ}
    (A : SimultaneousAssignment Zf.paths Y) : Set (V × V) :=
  {e | ∃ s, (A.assigned s).terminal? = some e.2 ∧ s.1 = e.1}

theorem mem_assignedFiniteEdges_iff {Zf : FracturedWarp Γ}
    (A : SimultaneousAssignment Zf.paths Y) {u v : V} :
    (u, v) ∈ assignedFiniteEdges A ↔
      ∃ s, (A.assigned s).terminal? = some v ∧ s.1 = u :=
  Iff.rfl

/-- Claim 2 makes every compressed finite assignment an edge of `D ∪ IE`.
-/
theorem assignedFiniteEdges_subset_imaginaryGraph
    {Zf : FracturedWarp Γ} {κ : Cardinal.{u}}
    (A : SimultaneousAssignment Zf.paths Y)
    (hfinite : ∀ s v, (A.assigned s).terminal? = some v →
      IsImaginaryEdge Γ Y κ s.1 v) :
    assignedFiniteEdges A ⊆
      {e | (imaginaryGraph Γ Y κ).Adj e.1 e.2} := by
  rintro ⟨u, v⟩ ⟨s, hterm, rfl⟩
  exact Or.inr (hfinite s v hterm)

/-- A simultaneous assignment is functional at the sources after finite
paths are compressed to endpoint edges. -/
theorem assignedFiniteEdges_out_unique
    {Zf : FracturedWarp Γ} (A : SimultaneousAssignment Zf.paths Y)
    {u v w : V} (huv : (u, v) ∈ assignedFiniteEdges A)
    (huw : (u, w) ∈ assignedFiniteEdges A) : v = w := by
  obtain ⟨s, hsv, hsu⟩ := huv
  obtain ⟨t, htw, htu⟩ := huw
  have hst : s = t := by
    apply Subtype.ext
    exact hsu.trans htu.symm
  subst t
  simpa [hsv] using htw

/-- Pairwise distinct finite terminals make the compressed assignment
injective at its targets. -/
theorem assignedFiniteEdges_in_unique
    {Zf : FracturedWarp Γ} (A : SimultaneousAssignment Zf.paths Y)
    {u v w : V} (huw : (u, w) ∈ assignedFiniteEdges A)
    (hvw : (v, w) ∈ assignedFiniteEdges A) : u = v := by
  obtain ⟨s, hsw, hsu⟩ := huw
  obtain ⟨t, htw, htv⟩ := hvw
  have hst : s = t := A.finite_terminals_injective hsw htw
  exact hsu.symm.trans (congrArg Subtype.val hst) |>.trans htv

theorem assignedFiniteEdges_biUnique
    {Zf : FracturedWarp Γ} (A : SimultaneousAssignment Zf.paths Y) :
    Relator.BiUnique (fun u v ↦ (u, v) ∈ assignedFiniteEdges A) :=
  by
    constructor
    · intro u v w huw hvw
      exact assignedFiniteEdges_in_unique A huw hvw
    · intro u v w huv huw
      exact assignedFiniteEdges_out_unique A huv huw

/-- Sources whose assignments go to infinity. -/
def assignedInfiniteSources {Zf : FracturedWarp Γ}
    (A : SimultaneousAssignment Zf.paths Y) : Set V :=
  {u | ∃ s, s.1 = u ∧ (A.assigned s).IsInfinite}

theorem assignedInfiniteSources_popular
    {Zf : FracturedWarp Γ} {persistent : Set V} {κ : Cardinal.{u}}
    (A : SimultaneousAssignment Zf.paths Y)
    (hinfinite : ∀ s, (A.assigned s).IsInfinite →
      IsPopular Γ Y persistent κ s.1) :
    assignedInfiniteSources A ⊆
      {u | IsPopular Γ Y persistent κ u} := by
  rintro u ⟨s, rfl, hs⟩
  exact hinfinite s hs

@[simp] theorem CompressedFracturedAssignment.finiteEdges_ofSimultaneous
    {Zf : FracturedWarp Γ} (A : SimultaneousAssignment Zf.paths Y) :
    (CompressedFracturedAssignment.ofSimultaneous A).finiteEdges =
      assignedFiniteEdges A :=
  rfl

@[simp] theorem CompressedFracturedAssignment.infiniteSources_ofSimultaneous
    {Zf : FracturedWarp Γ} (A : SimultaneousAssignment Zf.paths Y) :
    (CompressedFracturedAssignment.ofSimultaneous A).infiniteSources =
      assignedInfiniteSources A := by
  ext u
  simp only [CompressedFracturedAssignment.infiniteSources,
    CompressedFracturedAssignment.ofSimultaneous, assignedInfiniteSources,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, rfl, hs⟩
    exact ⟨s, rfl, (A.assigned s).isInfinite_iff_terminal?_eq_none.mpr hs⟩
  · rintro ⟨s, rfl, hs⟩
    exact ⟨s, rfl, (A.assigned s).isInfinite_iff_terminal?_eq_none.mp hs⟩

/-! ## Compiling the assigned edge relation into an honest blueprint -/

open Alternating.RelationDecomposition

/-- The canonical path family of a forward-oriented functional relation.
This is the graph-theoretic splicing step: the paths are constructed as the
root orbits, rather than supplied as a proposed result blueprint. -/
def orientationBlueprint {κ : Cardinal.{u}}
    (O : ForwardOrientation (imaginaryGraph Γ Y κ)) :
    LinkageBlueprint Γ Y κ where
  paths := O.rootPaths
  isWarp := O.rootPaths_pairwiseDisjoint

@[simp] theorem orientationBlueprint_paths {κ : Cardinal.{u}}
    (O : ForwardOrientation (imaginaryGraph Γ Y κ)) :
    (orientationBlueprint O).paths = O.rootPaths := rfl

/-- The root-orbit decomposition covers exactly the carrier supplied to the
forward orientation.  The reverse inclusion includes the isolated
depth-zero vertices, which are invisible in the edge-set realization alone
but are essential for blueprint source coverage. -/
theorem orientationBlueprint_vertexSet {κ : Cardinal.{u}}
    (O : ForwardOrientation (imaginaryGraph Γ Y κ)) :
    (orientationBlueprint O).vertexSet = O.carrier := by
  have orbit_mem_carrier {r : V} (hr : O.IsRoot r) :
      ∀ {n : ℕ}, O.Alive r n → O.orbit r n ∈ O.carrier := by
    intro n halive
    cases n with
    | zero => simpa using hr.1
    | succ n =>
        exact (O.endpoints_mem _ (O.orbit_edge halive)).2
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, hxp⟩
    rcases hp with ⟨r, rfl⟩
    simp only [ForwardOrientation.rootPath] at hxp
    split at hxp <;> rename_i hstop
    · rcases hxp with ⟨n, hn⟩
      rw [← hn]
      exact orbit_mem_carrier r.2 (fun k _ ↦ hstop k)
    · change x ∈
        (O.orbitWalk r.1 (O.stoppingIndex hstop)
          (O.alive_stoppingIndex hstop)).support at hxp
      rw [O.orbitWalk_support] at hxp
      simp only [List.mem_ofFn] at hxp
      obtain ⟨i, rfl⟩ := hxp
      exact orbit_mem_carrier r.2
        (O.alive_mono (O.alive_stoppingIndex hstop) i.is_le)
  · intro x hx
    obtain ⟨hroot, halive, horbit⟩ := O.reachable_from_component x hx
    let r : O.Root := ⟨O.component x, hroot⟩
    have hxroot : x ∈ (O.rootPath r).support := by
      simp only [ForwardOrientation.rootPath]
      split <;> rename_i hstop
      · exact ⟨O.depth x, horbit⟩
      · change x ∈
          (O.orbitWalk r.1 (O.stoppingIndex hstop)
            (O.alive_stoppingIndex hstop)).support
        rw [O.orbitWalk_support]
        simp only [List.mem_ofFn]
        have hle : O.depth x ≤ O.stoppingIndex hstop := by
          by_contra hnot
          have hsucc : O.stoppingIndex hstop + 1 ≤ O.depth x := by omega
          have hstill : O.Alive r.1 (O.stoppingIndex hstop + 1) :=
            O.alive_mono halive hsucc
          exact O.not_hasNext_stoppingIndex hstop
            (O.alive_succ_iff.mp hstill).2
        exact ⟨⟨O.depth x, Nat.lt_succ_iff.mpr hle⟩, horbit⟩
    exact ⟨O.rootPath r, ⟨r, rfl⟩, hxroot⟩

/-- The canonical decomposition realizes exactly the assigned edge
relation. -/
theorem orientationBlueprint_edgeSet {κ : Cardinal.{u}}
    (O : ForwardOrientation (imaginaryGraph Γ Y κ)) :
    (orientationBlueprint O).edgeSet = O.edge := by
  exact O.rootPathEdges_eq

/-- A bi-unique acyclic splice relation with no reverse ray has an honest
path-family realization in the imaginary graph.  This combines the
well-founded orientation constructor with the root-orbit decomposition and
is the precise replacement for informally saying that the assigned
fragments "form a warp". -/
theorem exists_blueprint_realizing_relation
    {κ : Cardinal.{u}} (E : Set (V × V)) (carrier : Set V)
    (hgraph : E ⊆ {e | (imaginaryGraph Γ Y κ).Adj e.1 e.2})
    (hendpoints : ∀ e ∈ E, e.1 ∈ carrier ∧ e.2 ∈ carrier)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hcycle : ¬ ContainsDirectedCycle E)
    (hreverse : ¬ ContainsReverseDirectedRay E) :
    ∃ U : LinkageBlueprint Γ Y κ, U.edgeSet = E := by
  obtain ⟨O, hOE⟩ := ForwardOrientation.exists_forwardOrientation
    E carrier hgraph hendpoints hunique hcycle hreverse
  refine ⟨orientationBlueprint O, ?_⟩
  rw [orientationBlueprint_edgeSet, hOE]

/-- Strengthened orientation constructor retaining the exact carrier as a
named conclusion.  The underlying constructor already uses this carrier;
exposing the equality is essential when isolated vertices must survive an
edge deletion. -/
theorem exists_forwardOrientation_exact
    {D : Digraph V} (E : Set (V × V)) (carrier : Set V)
    (hgraph : E ⊆ {e | D.Adj e.1 e.2})
    (hendpoints : ∀ e ∈ E, e.1 ∈ carrier ∧ e.2 ∈ carrier)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hcycle : ¬ContainsDirectedCycle E)
    (hreverse : ¬ContainsReverseDirectedRay E) :
    ∃ O : ForwardOrientation D, O.edge = E ∧ O.carrier = carrier := by
  let hwf : WellFounded (fun x y ↦ (x, y) ∈ E) :=
    ForwardOrientation.predecessor_wellFounded E hcycle hreverse
  let O : ForwardOrientation D :=
    { edge := E
      carrier := carrier
      depth := ForwardOrientation.wellFoundedDepth E hwf
      component := ForwardOrientation.wellFoundedRoot E hwf
      edge_in_graph := hgraph
      endpoints_mem := hendpoints
      out_unique := fun hxy hxz ↦ hunique.2 hxy hxz
      in_unique := fun hxz hyz ↦ hunique.1 hxz hyz
      depth_step := fun hxy ↦
        ForwardOrientation.wellFoundedDepth_step E hunique hwf hxy
      component_step := fun hxy ↦
        ForwardOrientation.wellFoundedRoot_step E hunique hwf hxy
      root_label := fun _hx hdepth ↦
        ForwardOrientation.wellFoundedRoot_eq_self_of_depth_eq_zero
          E hwf hdepth
      predecessor := by
        intro x _hx hpos
        have hne : ForwardOrientation.wellFoundedDepth E hwf x ≠ 0 :=
          Nat.ne_of_gt hpos
        exact Classical.byContradiction fun hnot ↦
          hne ((ForwardOrientation.wellFoundedDepth_eq_zero_iff
            E hwf x).mpr hnot) }
  exact ⟨O, rfl, rfl⟩

private theorem ray_edgeSet_not_containsDirectedCycle
    {D : Digraph V} (r : DirectedPath.Ray D) :
    ¬ContainsDirectedCycle r.edgeSet := by
  rintro ⟨C, hC⟩
  let i₀ : Fin C.length := ⟨0, C.positive⟩
  obtain ⟨n₀, hn₀⟩ := hC ⟨i₀, rfl⟩
  have hzero : C.vertex i₀ = r n₀ := congrArg Prod.fst hn₀
  have hvertex : ∀ n : ℕ, ∀ hn : n < C.length,
      C.vertex ⟨n, hn⟩ = r (n₀ + n) := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa [i₀] using hzero
    | succ n ih =>
        intro hn
        have hn' : n < C.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        let i : Fin C.length := ⟨n, hn'⟩
        have hnext : C.next i = ⟨n + 1, hn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hn
        obtain ⟨m, hm⟩ := hC ⟨i, rfl⟩
        have hsource : C.vertex i = r m := congrArg Prod.fst hm
        have htarget : C.vertex (C.next i) = r (m + 1) :=
          congrArg Prod.snd hm
        have hm_eq : m = n₀ + n := by
          apply r.injective
          exact hsource.symm.trans (ih hn')
        rw [hnext, hm_eq] at htarget
        simpa [Nat.add_assoc] using htarget
  let last := C.length - 1
  have hlast : last < C.length := Nat.sub_lt C.positive (by omega)
  let iLast : Fin C.length := ⟨last, hlast⟩
  have hnextLast : C.next iLast = i₀ := by
    apply Fin.ext
    have hs : last + 1 = C.length := Nat.sub_add_cancel C.positive
    simp [DirectedCycle.next, iLast, i₀, hs]
  obtain ⟨m, hm⟩ := hC ⟨iLast, rfl⟩
  have hsource : C.vertex iLast = r m := congrArg Prod.fst hm
  have htarget : C.vertex (C.next iLast) = r (m + 1) :=
    congrArg Prod.snd hm
  have hm_eq : m = n₀ + last := by
    apply r.injective
    exact hsource.symm.trans (hvertex last hlast)
  have hreturn : r n₀ = r (n₀ + C.length) := by
    rw [hnextLast, hm_eq] at htarget
    rw [Nat.add_assoc, Nat.sub_add_cancel C.positive] at htarget
    exact hzero.symm.trans htarget
  have := r.injective hreturn
  omega

private theorem finitePath_edgeSet_not_containsReverseDirectedRay
    {D : Digraph V} (p : DirectedPath.FinitePath D) :
    ¬ContainsReverseDirectedRay p.edgeSet := by
  rintro ⟨R, hR⟩
  have hall : ∀ n : ℕ, R.vertex n ∈ p.support := by
    intro n
    cases n with
    | zero => exact (p.edgeSet_subset_support_prod (hR 0)).2
    | succ n => exact (p.edgeSet_subset_support_prod (hR n)).1
  exact p.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hall)

private theorem ray_edgeSet_not_containsReverseDirectedRay
    {D : Digraph V} (r : DirectedPath.Ray D) :
    ¬ContainsReverseDirectedRay r.edgeSet := by
  rintro ⟨R, hR⟩
  let f : ℕ → ℕ := fun n ↦ Classical.choose (hR n)
  have hf (n : ℕ) :
      (R.vertex (n + 1), R.vertex n) = (r (f n), r (f n + 1)) :=
    Classical.choose_spec (hR n)
  have hstep (n : ℕ) : f (n + 1) + 1 = f n := by
    apply r.injective
    exact (congrArg Prod.snd (hf (n + 1))).symm.trans
      (congrArg Prod.fst (hf n))
  have hsum : ∀ n : ℕ, f n + n = f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hstep n
        omega
  have := hsum (f 0 + 1)
  omega

private theorem path_edgeSet_not_containsDirectedCycle
    {D : Digraph V} (p : DirectedPath.Path D) :
    ¬ContainsDirectedCycle p.edgeSet := by
  rcases p with p | r
  · exact Alternating.FinitePath.edgeSet_not_containsDirectedCycle p
  · exact ray_edgeSet_not_containsDirectedCycle r

private theorem path_edgeSet_not_containsReverseDirectedRay
    {D : Digraph V} (p : DirectedPath.Path D) :
    ¬ContainsReverseDirectedRay p.edgeSet := by
  rcases p with p | r
  · exact finitePath_edgeSet_not_containsReverseDirectedRay p
  · exact ray_edgeSet_not_containsReverseDirectedRay r

/-- The edge relation represented by a linkage blueprint has no directed
cycle.  This is public because relation-limit constructions need the fact at
each finite stage, independently of imaginary-edge deletion. -/
theorem blueprint_edgeSet_not_containsDirectedCycle
    {κ : Cardinal.{u}} (W : LinkageBlueprint Γ Y κ) :
    ¬ContainsDirectedCycle W.edgeSet := by
  rintro ⟨C, hC⟩
  let i₀ : Fin C.length := ⟨0, C.positive⟩
  obtain ⟨p₀, hp₀W, hp₀edge⟩ :
      ∃ p₀ ∈ W.paths,
        (C.vertex i₀, C.vertex (C.next i₀)) ∈ p₀.edgeSet := by
    have hm := hC ⟨i₀, rfl⟩
    simp only [LinkageBlueprint.edgeSet, Set.mem_iUnion] at hm
    rcases hm with ⟨p₀, hp₀W, hp₀edge⟩
    exact ⟨p₀, hp₀W, hp₀edge⟩
  have hedgeNat : ∀ n : ℕ, ∀ hn : n < C.length,
      (C.vertex ⟨n, hn⟩, C.vertex (C.next ⟨n, hn⟩)) ∈
        p₀.edgeSet := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa [i₀] using hp₀edge
    | succ n ih =>
        intro hn
        have hn' : n < C.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        have hnext : C.next (⟨n, hn'⟩ : Fin C.length) =
            ⟨n + 1, hn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hn
        have hm := hC ⟨⟨n + 1, hn⟩, rfl⟩
        simp only [LinkageBlueprint.edgeSet, Set.mem_iUnion] at hm
        rcases hm with ⟨p, hpW, hpedge⟩
        have hp₀shared : C.vertex ⟨n + 1, hn⟩ ∈ p₀.support := by
          rw [← hnext]
          exact (p₀.edgeSet_subset_support_prod (ih hn')).2
        have hpshared : C.vertex ⟨n + 1, hn⟩ ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).1
        have hp : p = p₀ :=
          DWeb.IsWarp.eq_of_mem_support W.isWarp hpW hp₀W hpshared hp₀shared
        exact hp ▸ hpedge
  have hCp₀ : C.EdgeSet ⊆ p₀.edgeSet := by
    rintro e ⟨i, rfl⟩
    exact hedgeNat i.1 i.2
  exact path_edgeSet_not_containsDirectedCycle p₀ ⟨C, hCp₀⟩

/-- The edge relation represented by a linkage blueprint has no reverse
directed ray.  Although a blueprint may contain forward rays, a reverse ray
cannot lie in one of them, and warp-disjointness forces every reverse ray in
the family union to lie in a single member. -/
theorem blueprint_edgeSet_not_containsReverseDirectedRay
    {κ : Cardinal.{u}} (W : LinkageBlueprint Γ Y κ) :
    ¬ContainsReverseDirectedRay W.edgeSet := by
  rintro ⟨R, hR⟩
  obtain ⟨p₀, hp₀W, hp₀edge⟩ :
      ∃ p₀ ∈ W.paths, (R.vertex 1, R.vertex 0) ∈ p₀.edgeSet := by
    have hm := hR 0
    simp only [LinkageBlueprint.edgeSet, Set.mem_iUnion] at hm
    simpa using hm
  have hedge : ∀ n : ℕ,
      (R.vertex (n + 1), R.vertex n) ∈ p₀.edgeSet := by
    intro n
    induction n with
    | zero => simpa using hp₀edge
    | succ n ih =>
        have hm := hR (n + 1)
        simp only [LinkageBlueprint.edgeSet, Set.mem_iUnion] at hm
        rcases hm with ⟨p, hpW, hpedge⟩
        have hp₀shared : R.vertex (n + 1) ∈ p₀.support :=
          (p₀.edgeSet_subset_support_prod ih).1
        have hpshared : R.vertex (n + 1) ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).2
        have hp : p = p₀ :=
          DWeb.IsWarp.eq_of_mem_support W.isWarp hpW hp₀W hpshared hp₀shared
        exact hp ▸ hpedge
  exact path_edgeSet_not_containsReverseDirectedRay p₀ ⟨R, hedge⟩

/-- Deleting one represented edge from a blueprint has an honest blueprint
realization which keeps every old vertex, including the two new isolated
endpoints when the deleted edge was a one-edge component.  This is the
concrete construction of the cut `W^u` used in Assertion 9.30.

The proof decomposes the remaining locally bi-functional relation into its
forward components.  Acyclicity and absence of reverse rays are inherited
from the original warp, while the explicit carrier `W.vertexSet` ensures
that edge deletion never silently discards vertices. -/
theorem exists_imaginaryEdgeDeletionAt
    {κ : Cardinal.{u}} (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet)
    (himaginary : IsImaginaryEdge Γ Y κ u v) :
    ∃ cut : LinkageBlueprint Γ Y κ,
      W.IsImaginaryEdgeDeletionAt cut u v := by
  let E : Set (V × V) := W.edgeSet \ {(u, v)}
  have hgraph : E ⊆
      {e | (imaginaryGraph Γ Y κ).Adj e.1 e.2} := by
    intro e he
    rcases Set.mem_iUnion.1 he.1 with ⟨p, he⟩
    rcases Set.mem_iUnion.1 he with ⟨hpW, hep⟩
    exact p.edgeSet_subset_adj hep
  have hendpoints : ∀ e ∈ E,
      e.1 ∈ W.vertexSet ∧ e.2 ∈ W.vertexSet := by
    intro e he
    rcases Set.mem_iUnion.1 he.1 with ⟨p, he⟩
    rcases Set.mem_iUnion.1 he with ⟨hpW, hep⟩
    exact ⟨⟨p, hpW, (p.edgeSet_subset_support_prod hep).1⟩,
      ⟨p, hpW, (p.edgeSet_subset_support_prod hep).2⟩⟩
  have hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    constructor
    · intro x y z hxz hyz
      exact (Alternating.IsWarp.familyEdges_leftUnique W.isWarp)
        hxz.1 hyz.1
    · intro x y z hxy hxz
      exact (Alternating.IsWarp.familyEdges_rightUnique W.isWarp)
        hxy.1 hxz.1
  have hcycle : ¬ContainsDirectedCycle E := by
    rintro ⟨C, hC⟩
    exact blueprint_edgeSet_not_containsDirectedCycle W
      ⟨C, hC.trans (fun _ he ↦ he.1)⟩
  have hreverse : ¬ContainsReverseDirectedRay E := by
    rintro ⟨R, hR⟩
    exact blueprint_edgeSet_not_containsReverseDirectedRay W
      ⟨R, fun n ↦ (hR n).1⟩
  obtain ⟨O, hOE, hOC⟩ := exists_forwardOrientation_exact
    E W.vertexSet hgraph hendpoints hunique hcycle hreverse
  refine ⟨orientationBlueprint O, huv, himaginary, ?_, ?_⟩
  · rw [orientationBlueprint_vertexSet, hOC]
  · rw [orientationBlueprint_edgeSet, hOE]

/-- Set-level inclusion of old vertices and old edges in the compiled
orientation gives source Definition 2.3 ordinary extension. -/
theorem ordinaryExtends_orientationBlueprint
    {κ : Cardinal.{u}} (W : LinkageBlueprint Γ Y κ)
    (O : ForwardOrientation (imaginaryGraph Γ Y κ))
    (hvertices : W.vertexSet ⊆ (orientationBlueprint O).vertexSet)
    (hedges : W.edgeSet ⊆ O.edge) :
    W.OrdinaryExtends (orientationBlueprint O) := by
  refine ⟨hvertices, ?_⟩
  change W.edgeSet ⊆ (orientationBlueprint O).edgeSet
  rw [orientationBlueprint_edgeSet]
  exact hedges

/-- A real path contained in the carrier and edge relation of the compiled
orientation becomes the real `z`--`B` certificate of Assertion 9.31. -/
theorem orientationBlueprint_realLinksTo
    {κ : Cardinal.{u}}
    (O : ForwardOrientation (imaginaryGraph Γ Y κ))
    {z : V} {B : Set V} (p : FinitePath Γ.graph)
    (hpstart : p.start = z) (hpfinish : p.finish ∈ B)
    (hpvertices : p.support ⊆ (orientationBlueprint O).vertexSet)
    (hpedges : p.edgeSet ⊆ O.edge) :
    (orientationBlueprint O).RealLinksTo z B := by
  refine ⟨p, hpstart, hpfinish, hpvertices, ?_⟩
  intro e he
  refine ⟨?_, p.edgeSet_subset_adj he⟩
  rw [orientationBlueprint_edgeSet]
  exact hpedges he

/-- The edge-relation compiler gives the full bare 9.31 conclusion once
the closure construction has supplied its terminal invariants.  Unlike the
earlier raw-family interface, the result blueprint is not an input: it is
the root-orbit decomposition of `O`. -/
theorem advanceConclusion_orientationBlueprint
    {κ : Cardinal.{u}} (W : LinkageBlueprint Γ Y κ)
    (O : ForwardOrientation (imaginaryGraph Γ Y κ))
    {z : V} {T persistent B : Set V}
    (hvertices : W.vertexSet ⊆ (orientationBlueprint O).vertexSet)
    (hedges : W.edgeSet ⊆ O.edge)
    (p : FinitePath Γ.graph)
    (hpstart : p.start = z) (hpfinish : p.finish ∈ B)
    (hpvertices : p.support ⊆ (orientationBlueprint O).vertexSet)
    (hpedges : p.edgeSet ⊆ O.edge)
    (hrealTerminals : W.realPart.terminals ⊆
      (orientationBlueprint O).realPart.terminals ∪ T)
    (hpersistent : W.terminalSet ∩ persistent ⊆
      (orientationBlueprint O).terminalSet ∪ {z}) :
    W.AdvanceConclusion (orientationBlueprint O) z T persistent B := by
  exact ⟨ordinaryExtends_orientationBlueprint W O hvertices hedges,
    orientationBlueprint_realLinksTo O p hpstart hpfinish hpvertices hpedges,
    hrealTerminals, hpersistent⟩

/-- Assemble the canonical root-orbit blueprint and all structural clauses
used by the endpoint-explicit Assertion 9.31 wrapper.  Keeping this theorem
below `AdvanceConclusion` avoids a dependency on the later `Advance931`
record while exposing exactly the data needed to construct it. -/
theorem exists_compiled_advance
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    (O : ForwardOrientation (imaginaryGraph Gamma Y kappa))
    {z : V} {T Z persistent B : Set V}
    (hroof : (orientationBlueprint O).vertexSet ⊆ Gamma.roof T)
    (hcover : Gamma.source ⊆
      (orientationBlueprint O).initialSet ∪
        (orientationBlueprint O).retainedReferenceInitials T)
    (hclosed : (orientationBlueprint O).vertexSet ⊆ Z)
    (hcard : #(orientationBlueprint O).paths ≤ kappa)
    (hstrong : (orientationBlueprint O).InfinitelyManyStrongEdges)
    (hpopular : (orientationBlueprint O).terminalSet ⊆
      {u | IsPopular Gamma Y persistent kappa u} ∪ T)
    (hstable : (orientationBlueprint O).Stable T persistent)
    (hvertices : current.vertexSet ⊆
      (orientationBlueprint O).vertexSet)
    (hedges : current.edgeSet ⊆ O.edge)
    (p : FinitePath Gamma.graph)
    (hpstart : p.start = z) (hpfinish : p.finish ∈ B)
    (hpvertices : p.support ⊆ (orientationBlueprint O).vertexSet)
    (hpedges : p.edgeSet ⊆ O.edge)
    (hrealTerminals : current.realPart.terminals ⊆
      (orientationBlueprint O).realPart.terminals ∪ T)
    (hpersistent : current.terminalSet ∩ persistent ⊆
      (orientationBlueprint O).terminalSet ∪ {z})
    (hpreserves : current.realPart.terminals \ {z} ⊆
      (orientationBlueprint O).realPart.terminals)
    (hinherited : ∀ x, x ∈ ancestor.terminalSet →
      x ∈ current.terminalSet → x ≠ z →
        x ∈ (orientationBlueprint O).terminalSet) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      U.IsLinkageBlueprint T Z persistent ∧
      U.Stable T persistent ∧
      current.AdvanceConclusion U z T persistent B ∧
      current.familyGraph.Extends U.familyGraph ∧
      current.realPart.Extends U.realPart ∧
      current.realPart.terminals \ {z} ⊆ U.realPart.terminals ∧
      (∀ x, x ∈ ancestor.terminalSet → x ∈ current.terminalSet →
        x ≠ z → x ∈ U.terminalSet) := by
  let U := orientationBlueprint O
  have hordinary : current.OrdinaryExtends U := by
    exact ordinaryExtends_orientationBlueprint current O hvertices hedges
  refine ⟨U, ?_, hstable, ?_, hordinary, hordinary.realPart_extends,
    hpreserves, hinherited⟩
  · exact {
      vertices_roofed := hroof
      covers_source := hcover
      vertices_closed := hclosed
      card_paths := hcard
      infinitely_many_strong := hstrong
      terminals_popular := hpopular }
  · exact ⟨hordinary,
      orientationBlueprint_realLinksTo O p hpstart hpfinish hpvertices hpedges,
      hrealTerminals, hpersistent⟩

end Blueprint
end Erdos599

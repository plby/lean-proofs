/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularExactFrontierContinuation
import ErdosProblems.Erdos599.SingularLiteralColumnContinuation
import ErdosProblems.Erdos599.SingularTargetRowMachine
import ErdosProblems.Erdos599.HalfwayExactFrontierInduction
import ErdosProblems.Erdos599.HalfwayExactFrontierClause

/-!
# Exact-frontier lower clauses imply the singular extension clause

`SingularExactFrontierContinuation` proves the geometric successor used in
Assertion 9.17: ordinary quotient continuation preserves an exact terminal
frontier.  This file performs the remaining simultaneous cardinal
bookkeeping and iterates that successor as a `TargetRowMachine`.

The result identifies the precise producer theorem still required from the
lower half-way construction.  At every smaller infinite cardinal and in
every unhindered auxiliary web, it must expose a qualified half-way linkage
together with a stop-over equal to its terminal frontier.  No safe-deletion,
residual-unhinderedness, or arbitrary-row successor hypothesis remains.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularExactFrontierMatrix

open SingularBoundarySplit SingularContinuation SingularExactFrontierContinuation
  SingularExtension SingularLiteralColumnContinuation SingularMatrix
  SingularTargetRowMachine SingularTargetLinkTransfer

universe u

variable {V : Type u}

/-- The source-faithful strengthening of the half-way clause needed by the
literal singular recursion. -/
def ExactFrontierHalfwayClauseAt
    (G : DWeb V) (rho : Cardinal.{u}) : Prop :=
  ∀ A : Set V, A ⊆ G.source → #A = rho →
    ∃ (W : Set G.DPath) (C : Set V),
      IsHalfwayLinkageOfAltitude G A rho W ∧
      ExactFrontierStopover G W C

/-- Uniform exact-frontier half-way clauses at all smaller infinite
cardinals, including every quotient auxiliary web. -/
def UniversalExactFrontierHalfwayBelow
    (V : Type u) (kappa : Cardinal.{u}) : Prop :=
  ∀ rho : Cardinal.{u}, rho < kappa →
    ∀ G : DWeb V, G.IsUnhindered → aleph0 ≤ rho →
      ExactFrontierHalfwayClauseAt G rho

/-- The exact-frontier simultaneous induction hypothesis supplies the
matrix-facing exact lower clause. -/
theorem universalExactFrontierHalfwayBelow_of_inductionBelow
    {kappa : Cardinal.{u}}
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa) :
    UniversalExactFrontierHalfwayBelow V kappa := by
  intro rho hrho G hG hrhoInfinite A hA hAcard
  obtain ⟨W, C, hC, hfrontier, hlinks, hheight⟩ :=
    (hlower rho hrho G hG).exactHalfway hrhoInfinite A hA hAcard
  have hqualified : IsHalfwayLinkageOfAltitude G A rho W :=
    halfwayLinkageOfAltitude_of_stopover hC hlinks hheight
  have hexact : ExactFrontierStopover G W C :=
    ⟨⟨hC, hC.separator⟩, hfrontier⟩
  exact ⟨W, C, hqualified, hexact⟩

/-- The exact-frontier clause already exported by the half-way construction
implies the matrix-facing formulation above.  The only conversion is from
the retained height witness to `IsHalfwayLinkageOfAltitude`. -/
theorem exactFrontierHalfwayClauseAt_of_halfwayConstruction
    {G : DWeb V} {rho : Cardinal.{u}}
    (h : CardinalInduction.ExactFrontierHalfwayClauseAt G rho) :
    ExactFrontierHalfwayClauseAt G rho := by
  intro A hA hcard
  obtain ⟨W, C, hC, hfrontier, hlinks, hheight⟩ := h A hA hcard
  exact ⟨W, C,
    halfwayLinkageOfAltitude_of_stopover hC hlinks hheight,
    ⟨⟨hC, hC.separator⟩, hfrontier⟩⟩

/-- Uniform source-construction exact clauses below `kappa` imply the
matrix-facing uniform hypothesis. -/
theorem universalExactFrontierHalfwayBelow_of_halfwayConstruction
    {kappa : Cardinal.{u}}
    (h : ∀ rho : Cardinal.{u}, rho < kappa →
      ∀ G : DWeb V, G.IsUnhindered → aleph0 ≤ rho →
        CardinalInduction.ExactFrontierHalfwayClauseAt G rho) :
    UniversalExactFrontierHalfwayBelow V kappa := by
  intro rho hrho G hG hinfinite
  exact exactFrontierHalfwayClauseAt_of_halfwayConstruction
    (h rho hrho G hG hinfinite)

/-- One simultaneous row with exact-frontier certificates and the cardinal
invariant required for the next competitor step. -/
structure ExactFrontierTargetRowStage
    (G : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular) where
  row : TargetRowStage G (Index kappa)
  boundary : Index kappa → Set V
  exact : ∀ i, ExactFrontierStopover G (row.paths i) (boundary i)
  source_spec : ∀ i,
    row.sources i ⊆ G.source ∧
      #(row.sources i) = scale kappa hkappa hsingular i

/-- Exact lower half-way clauses construct the zeroth simultaneous row on
the prescribed singular source layers. -/
theorem exists_initialExactFrontierTargetRowStage
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    (hexact : UniversalExactFrontierHalfwayBelow V kappa) :
    ∃ S : ExactFrontierTargetRowStage G kappa hkappa hsingular,
      S.row.sources = sourceLayer A₀ kappa hcard hkappa hsingular := by
  let A : Index kappa → Set V :=
    sourceLayer A₀ kappa hcard hkappa hsingular
  have hsource : ∀ i, A i ⊆ G.source ∧
      #(A i) = scale kappa hkappa hsingular i := by
    intro i
    exact ⟨(sourceLayer_subset A₀ kappa hcard hkappa hsingular i).trans hA₀,
      sourceLayer_card A₀ kappa hcard hkappa hsingular i⟩
  have hcolumns : ∀ i : Index kappa,
      ∃ (W : Set G.DPath) (C : Set V),
        IsHalfwayLinkageOfAltitude G (A i)
          (scale kappa hkappa hsingular i) W ∧
        ExactFrontierStopover G W C := by
    intro i
    exact hexact (scale kappa hkappa hsingular i)
      (scale_below kappa hkappa hsingular i) G hG
      (scale_infinite kappa hkappa hsingular i)
      (A i) (hsource i).1 (hsource i).2
  choose paths boundary hqualified hexactStop using hcolumns
  let R : TargetRowStage G (Index kappa) :=
    { sources := A
      paths := paths
      isWarp := fun i ↦ (hexactStop i).linkage.isWarp
      finiteCharacter := fun i ↦ (hexactStop i).linkage.finiteCharacter
      initialSet := fun i ↦ (hexactStop i).linkage.initialSet_eq
      links := fun i ↦ (hqualified i).2.1 }
  refine ⟨⟨R, boundary, ?_, ?_⟩, rfl⟩
  · exact hexactStop
  · exact hsource

/-- One simultaneous exact-frontier successor.  Each column changes the
next ambient request to its current terminal coordinates, applies the exact
lower clause in the quotient, and uses literal source-star continuation. -/
theorem exists_nextExactFrontierTargetRowStage
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hexact : UniversalExactFrontierHalfwayBelow V kappa)
    (S : ExactFrontierTargetRowStage G kappa hkappa hsingular) :
    ∃ T : ExactFrontierTargetRowStage G kappa hkappa hsingular,
      T.row.sources = nextTargetSources G fixed S.row ∧
      ∀ i, G.ForwardExtension (S.row.paths i) (T.row.paths i) := by
  have hnextSource : ∀ i,
      nextTargetSources G fixed S.row i ⊆ G.source ∧
        #(nextTargetSources G fixed S.row i) =
          scale kappa hkappa hsingular i := by
    intro i
    let rho := scale kappa hkappa hsingular i
    have hrho : aleph0 ≤ rho := scale_infinite kappa hkappa hsingular i
    have hI : #(Index kappa) ≤ rho :=
      scale_index_le kappa hkappa hsingular i
    exact ⟨nextTargetSources_subset_source hfixedInitial S.row
      (fun j ↦ (S.source_spec j).1) i,
      mk_nextTargetSources_eq hfixedWarp S.row hrho hI i
        (S.source_spec i).2⟩
  have hcolumns : ∀ i : Index kappa,
      ∃ (P : Set G.DPath) (E : Set V),
        ExactFrontierStopover G P E ∧
        G.ForwardExtension (S.row.paths i) P ∧
        LinksToTarget G P (nextTargetSources G fixed S.row i) := by
    intro i
    let rho := scale kappa hkappa hsingular i
    let B := nextTargetSources G fixed S.row i
    let A := requestedFrontier G (S.row.paths i) B
    let D := S.boundary i
    have hD : ExactFrontierStopover G (S.row.paths i) D := S.exact i
    have hBsource : B ⊆ G.source := (hnextSource i).1
    have hBcard : #B = rho := (hnextSource i).2
    have hAsource : A ⊆ (G.quotient D).source := by
      rw [hD.separating.quotient_source_eq]
      rintro x ⟨p, hp, hpx⟩
      exact hD.linkage.terminalFrontier_subset ⟨p, hp.1, hpx⟩
    have hAcard : #A = rho := by
      dsimp only [A]
      rw [terminalRequest_card hD.separating hBsource, hBcard]
    obtain ⟨U, E, hU, hE⟩ :=
      hexact rho (scale_below kappa hkappa hsingular i)
        (G.quotient D) hD.quotient_unhindered
        (scale_infinite kappa hkappa hsingular i)
        A hAsource hAcard
    let P : Set G.DPath := continuation G hD.linkage
      hD.separating.separator hD.separating.stopover.minimal
        hD.terminalCleanAt U hE.linkage.initialSet_eq
    have hresult := continuation_exactFrontierStopover_linksToTarget
      hNorm hD hAsource hBsource
      (routes_terminalRequest hD.separating hBsource)
      hE hU.2.1
    dsimp only at hresult
    exact ⟨P, E, hresult.1, hresult.2.1, hresult.2.2⟩
  choose paths boundary hexactStop hforward hlinks using hcolumns
  let R : TargetRowStage G (Index kappa) :=
    { sources := nextTargetSources G fixed S.row
      paths := paths
      isWarp := fun i ↦ (hexactStop i).linkage.isWarp
      finiteCharacter := fun i ↦ (hexactStop i).linkage.finiteCharacter
      initialSet := fun i ↦ (hexactStop i).linkage.initialSet_eq
      links := hlinks }
  refine ⟨⟨R, boundary, ?_, ?_⟩, rfl, ?_⟩
  · exact hexactStop
  · exact hnextSource
  · exact hforward

/-- Choose the initial exact row. -/
noncomputable def initialExactFrontierTargetRowStage
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    (hexact : UniversalExactFrontierHalfwayBelow V kappa) :
    ExactFrontierTargetRowStage G kappa hkappa hsingular :=
  Classical.choose (exists_initialExactFrontierTargetRowStage
    hkappa hsingular hG hA₀ hcard hexact)

theorem initialExactFrontierTargetRowStage_sources
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    (hexact : UniversalExactFrontierHalfwayBelow V kappa) :
    (initialExactFrontierTargetRowStage
      hkappa hsingular hG hA₀ hcard hexact).row.sources =
      sourceLayer A₀ kappa hcard hkappa hsingular :=
  Classical.choose_spec (exists_initialExactFrontierTargetRowStage
    hkappa hsingular hG hA₀ hcard hexact)

/-- Choose one exact simultaneous successor. -/
noncomputable def nextExactFrontierTargetRowStage
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hexact : UniversalExactFrontierHalfwayBelow V kappa)
    (S : ExactFrontierTargetRowStage G kappa hkappa hsingular) :
    ExactFrontierTargetRowStage G kappa hkappa hsingular :=
  Classical.choose (exists_nextExactFrontierTargetRowStage
    hkappa hsingular hNorm hfixedWarp hfixedInitial hexact S)

theorem nextExactFrontierTargetRowStage_spec
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hexact : UniversalExactFrontierHalfwayBelow V kappa)
    (S : ExactFrontierTargetRowStage G kappa hkappa hsingular) :
    let T := nextExactFrontierTargetRowStage
      hkappa hsingular hNorm hfixedWarp hfixedInitial hexact S
    T.row.sources = nextTargetSources G fixed S.row ∧
      ∀ i, G.ForwardExtension (S.row.paths i) (T.row.paths i) :=
  Classical.choose_spec (exists_nextExactFrontierTargetRowStage
    hkappa hsingular hNorm hfixedWarp hfixedInitial hexact S)

/-- Exact-frontier lower clauses furnish the complete future-proof row
machine consumed by the already-formalized singular matrix limit. -/
noncomputable def exactFrontierTargetRowMachine
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed)
    (hexact : UniversalExactFrontierHalfwayBelow V kappa) :
    TargetRowMachine G fixed
      (sourceLayer A₀ kappa hcard hkappa hsingular) where
  State := ExactFrontierTargetRowStage G kappa hkappa hsingular
  row S := S.row
  initial := initialExactFrontierTargetRowStage
    hkappa hsingular hG hA₀ hcard hexact
  next S := nextExactFrontierTargetRowStage hkappa hsingular hNorm
    hfixed.isWarp (hfixed.initialSet_eq.le.trans Set.sdiff_subset) hexact S
  sources_initial := initialExactFrontierTargetRowStage_sources
    hkappa hsingular hG hA₀ hcard hexact
  sources_next S := (nextExactFrontierTargetRowStage_spec
    hkappa hsingular hNorm hfixed.isWarp
      (hfixed.initialSet_eq.le.trans Set.sdiff_subset)
      hexact S).1
  forward_next S i := (nextExactFrontierTargetRowStage_spec
    hkappa hsingular hNorm hfixed.isWarp
      (hfixed.initialSet_eq.le.trans Set.sdiff_subset)
      hexact S).2 i

/-- Exact lower half-way clauses are sufficient for the singular extension
clause.  This is the precise Assertion 9.17-to-9.18 reduction: all column
continuations, simultaneous choices, omega iteration, competitor closure,
and normalization are discharged in the proof. -/
theorem singularExtensionClauseAt_of_lowerExactFrontierHalfway
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hexact : UniversalExactFrontierHalfwayBelow V kappa) :
    ExtensionClauseAt Gamma kappa := by
  apply singularExtensionClauseAt_of_normalizedTargetRowMachine
    kappa hkappa hsingular Gamma
  intro A₀ hA₀ hcard fixed hfixed
  exact exactFrontierTargetRowMachine hkappa hsingular
    hGamma.normalized Gamma.normalized_isNormalized
      hA₀ hcard hfixed hexact

/-- Source-faithful public singular step from the exact simultaneous lower
induction hypothesis. -/
theorem singularExtensionClauseAt_of_exactFrontierInductionBelow
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered) :
    ExtensionClauseAt Gamma kappa :=
  singularExtensionClauseAt_of_lowerExactFrontierHalfway
    kappa hkappa hsingular Gamma hGamma
      (universalExactFrontierHalfwayBelow_of_inductionBelow hlower)

/-- Public producer-facing form: exact-frontier clauses returned by the
half-way construction at every lower infinite cardinal directly imply the
singular extension clause. -/
theorem singularExtensionClauseAt_of_lowerConstructionExactFrontier
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hexact : ∀ rho : Cardinal.{u}, rho < kappa →
      ∀ G : DWeb V, G.IsUnhindered → aleph0 ≤ rho →
        CardinalInduction.ExactFrontierHalfwayClauseAt G rho) :
    ExtensionClauseAt Gamma kappa := by
  exact singularExtensionClauseAt_of_lowerExactFrontierHalfway
    kappa hkappa hsingular Gamma hGamma
      (universalExactFrontierHalfwayBelow_of_halfwayConstruction hexact)

/-- An exact-frontier half-way *step* reconstructs the strong lower clause
from the ordinary simultaneous induction hypotheses.  This is the adapter
used by the final public induction: at `rho < kappa`, the hypotheses below
`rho` are obtained by transitivity and the extension clause at `rho` is the
extension projection of the ordinary lower result. -/
theorem singularExtensionClauseAt_of_ordinaryBelow_of_exactHalfwayStep
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hexactStep : ∀ rho : Cardinal.{u},
      UniversalCardinalInductionBelow V rho →
      UniversalExtensionClauseAt V rho → aleph0 ≤ rho →
      ∀ G : DWeb V, G.IsUnhindered →
        CardinalInduction.ExactFrontierHalfwayClauseAt G rho)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered) :
    ExtensionClauseAt Gamma kappa := by
  apply singularExtensionClauseAt_of_lowerConstructionExactFrontier
    kappa hkappa hsingular Gamma hGamma
  intro rho hrho G hG hrhoInfinite
  let hlowerRho : UniversalCardinalInductionBelow V rho :=
    fun sigma hsigma ↦ hlower sigma (hsigma.trans hrho)
  let hextRho : UniversalExtensionClauseAt V rho :=
    fun H hH ↦ (hlower rho hrho H hH).extension
  exact hexactStep rho hlowerRho hextRho hrhoInfinite G hG

#print axioms exists_initialExactFrontierTargetRowStage
#print axioms exists_nextExactFrontierTargetRowStage
#print axioms exactFrontierTargetRowMachine
#print axioms singularExtensionClauseAt_of_lowerExactFrontierHalfway
#print axioms singularExtensionClauseAt_of_exactFrontierInductionBelow
#print axioms singularExtensionClauseAt_of_lowerConstructionExactFrontier
#print axioms
  singularExtensionClauseAt_of_ordinaryBelow_of_exactHalfwayStep

end SingularExactFrontierMatrix
end CardinalInduction
end Erdos599

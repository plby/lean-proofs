/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularEventualRows
import ErdosProblems.Erdos599.SingularClosedTargetRows

/-!
# The coinductive kernel of globally admissible singular rows

A maximal-chain argument cannot use the false assertion that every bounded
row has a successor.  The exact global replacement is the serial kernel of
the row transition relation: a row is viable when it belongs to some set of
rows in which every member has a later member that simultaneously

* enlarges every source column,
* absorbs the current simultaneous competitors, and
* forward-extends every path column.

Membership in this greatest post-fixed point is enough for dependent choice
to produce an omega chain.  Conversely, the range of any omega chain is a
serial family, so viability is exactly the non-well-founded part of the row
tree.  This is the condition a Zorn, club, or game argument must establish;
maximality alone does not imply it because terminal rows exist.

The construction below targets `EventualRows`, not the stronger exact
successor equation.  Thus source columns may jump over arbitrarily many
intermediate closures and intervening dead rows never have to be selected.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularCofinalViability

open SingularExtension SingularMatrix SingularEventualRows
  SingularClosedTargetRows

universe u

variable {V : Type u}

/-- One simultaneous target row with the exact scale bounds used by the
singular cardinal bookkeeping. -/
structure BoundedStage
    (G : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular) where
  row : TargetRowStage G (Index kappa)
  sources_subset : ∀ i, row.sources i ⊆ G.source
  sources_card : ∀ i,
    #(row.sources i) = scale kappa hkappa hsingular i

namespace BoundedStage

variable {G : DWeb V} {kappa : Cardinal.{u}}
variable {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}

abbrev sources (S : BoundedStage G kappa hkappa hsingular)
    (i : Index kappa) : Set V := S.row.sources i

abbrev paths (S : BoundedStage G kappa hkappa hsingular)
    (i : Index kappa) : Set G.DPath := S.row.paths i

end BoundedStage

/-- A later bounded row is admissible after `S` when it absorbs the
competitors created by `S` and forward-extends all columns.  Equality with
one immediate competitor step is deliberately not required. -/
def CofinalStep
    (G : DWeb V) (fixed : Set G.DPath)
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (S T : BoundedStage G kappa hkappa hsingular) : Prop :=
  (∀ i, S.sources i ⊆ T.sources i) ∧
  (∀ i,
    G.competitorClosure (fixed ∪ ⋃ j, S.paths j) (S.sources i) ⊆
      T.sources i) ∧
  ∀ i, G.ForwardExtension (S.paths i) (T.paths i)

/-- An actual infinite branch of bounded simultaneous rows, rooted at a
specified initial stage.  This is the choice object whose existence a
club/Zorn argument would have to produce. -/
structure CofinalSchedule
    (G : DWeb V) (fixed : Set G.DPath)
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (initial : BoundedStage G kappa hkappa hsingular) where
  stage : ℕ → BoundedStage G kappa hkappa hsingular
  stage_zero : stage 0 = initial
  step : ∀ n, CofinalStep G fixed (stage n) (stage (n + 1))

/-- A family of bounded stages with no terminal member. -/
def IsSerial
    (G : DWeb V) (fixed : Set G.DPath)
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (X : Set (BoundedStage G kappa hkappa hsingular)) : Prop :=
  ∀ S ∈ X, ∃ T ∈ X, CofinalStep G fixed S T

/-- The greatest post-fixed point of the predecessor operator, written in
its elementary union-of-post-fixed-sets form. -/
def Viable
    (G : DWeb V) (fixed : Set G.DPath)
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (S : BoundedStage G kappa hkappa hsingular) : Prop :=
  ∃ X : Set (BoundedStage G kappa hkappa hsingular),
    S ∈ X ∧ IsSerial G fixed X

theorem Viable.exists_step
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    {S : BoundedStage G kappa hkappa hsingular}
    (hS : Viable G fixed S) :
    ∃ T, CofinalStep G fixed S T ∧ Viable G fixed T := by
  obtain ⟨X, hSX, hserial⟩ := hS
  obtain ⟨T, hTX, hST⟩ := hserial S hSX
  exact ⟨T, hST, X, hTX, hserial⟩

/-- Every post-fixed family is contained in the viable kernel. -/
theorem viable_of_mem_serial
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    {X : Set (BoundedStage G kappa hkappa hsingular)}
    (hX : IsSerial G fixed X) {S} (hSX : S ∈ X) :
    Viable G fixed S :=
  ⟨X, hSX, hX⟩

/-- The collection of all viable stages is itself serial. -/
theorem isSerial_viable
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular} :
    IsSerial G fixed
      {S : BoundedStage G kappa hkappa hsingular | Viable G fixed S} := by
  intro S hS
  obtain ⟨T, hST, hT⟩ := hS.exists_step
  exact ⟨T, hT, hST⟩

/-- Elementary greatest-fixed-point equation for viability.  Its reverse
direction adjoins one predecessor to a serial certificate for the chosen
successor. -/
theorem viable_iff_exists_step_viable
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    {S : BoundedStage G kappa hkappa hsingular} :
    Viable G fixed S ↔
      ∃ T, CofinalStep G fixed S T ∧ Viable G fixed T := by
  constructor
  · exact Viable.exists_step
  · rintro ⟨T, hST, X, hTX, hserial⟩
    refine ⟨insert S X, Set.mem_insert S X, ?_⟩
    intro U hU
    rcases Set.mem_insert_iff.1 hU with rfl | hUX
    · exact ⟨T, Set.mem_insert_of_mem U hTX, hST⟩
    · obtain ⟨Z, hZX, hUZ⟩ := hserial U hUX
      exact ⟨Z, Set.mem_insert_of_mem S hZX, hUZ⟩

/-- A viable stage, retaining its coinductive certificate so recursive
choice remains definitionally total. -/
def ViableStage
    (G : DWeb V) (fixed : Set G.DPath)
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular) :=
  {S : BoundedStage G kappa hkappa hsingular // Viable G fixed S}

namespace ViableStage

variable {G : DWeb V} {fixed : Set G.DPath}
variable {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
variable {hsingular : kappa.IsSingular}

/-- One chosen successor inside the serial kernel. -/
noncomputable def next
    (S : ViableStage G fixed kappa hkappa hsingular) :
    ViableStage G fixed kappa hkappa hsingular :=
  ⟨Classical.choose S.property.exists_step,
    (Classical.choose_spec S.property.exists_step).2⟩

theorem step_next
    (S : ViableStage G fixed kappa hkappa hsingular) :
    CofinalStep G fixed S.1 S.next.1 :=
  (Classical.choose_spec S.property.exists_step).1

/-- The omega chain selected from a viable initial row. -/
noncomputable def chain
    (S : ViableStage G fixed kappa hkappa hsingular) :
    ℕ → ViableStage G fixed kappa hkappa hsingular
  | 0 => S
  | n + 1 => (chain S n).next

@[simp] theorem chain_zero
    (S : ViableStage G fixed kappa hkappa hsingular) :
    S.chain 0 = S := rfl

@[simp] theorem chain_succ
    (S : ViableStage G fixed kappa hkappa hsingular) (n : ℕ) :
    S.chain (n + 1) = (S.chain n).next := rfl

theorem chain_step
    (S : ViableStage G fixed kappa hkappa hsingular) (n : ℕ) :
    CofinalStep G fixed (S.chain n).1 (S.chain (n + 1)).1 := by
  rw [S.chain_succ]
  exact (S.chain n).step_next

end ViableStage

/-- Dependent choice inside the serial kernel, exposed as an ordinary
omega schedule. -/
noncomputable def cofinalScheduleOfViable
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (S : BoundedStage G kappa hkappa hsingular)
    (hS : Viable G fixed S) :
    CofinalSchedule G fixed S where
  stage n := (ViableStage.chain ⟨S, hS⟩ n).1
  stage_zero := rfl
  step n := ViableStage.chain_step ⟨S, hS⟩ n

/-- Conversely, the range of a schedule is a serial family. -/
theorem viable_of_cofinalSchedule
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    {S : BoundedStage G kappa hkappa hsingular}
    (C : CofinalSchedule G fixed S) : Viable G fixed S := by
  refine ⟨Set.range C.stage, ?_, ?_⟩
  · refine ⟨0, ?_⟩
    exact C.stage_zero
  · rintro T ⟨n, rfl⟩
    exact ⟨C.stage (n + 1), ⟨n + 1, rfl⟩, C.step n⟩

/-- Viability is exactly existence of an infinite cofinal branch, rather
than a local successor assertion about all bounded rows. -/
theorem viable_iff_nonempty_cofinalSchedule
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    {S : BoundedStage G kappa hkappa hsingular} :
    Viable G fixed S ↔ Nonempty (CofinalSchedule G fixed S) := by
  constructor
  · intro hS
    exact ⟨cofinalScheduleOfViable S hS⟩
  · rintro ⟨C⟩
    exact viable_of_cofinalSchedule C

/-- There is a globally admissible omega chain whose first row contains
the canonical singular source layers.  This is the direct existence
statement that a Zorn or club construction of cofinal rows must establish.
Unlike `InitialViability`, it mentions no auxiliary coinductive kernel. -/
def HasSeededCofinalSchedule
    (G : DWeb V) (fixed : Set G.DPath)
    (A₀ : Set V) (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hcard : #A₀ = kappa) : Prop :=
  ∃ S : BoundedStage G kappa hkappa hsingular,
    (∀ i,
      sourceLayer A₀ kappa hcard hkappa hsingular i ⊆ S.sources i) ∧
    Nonempty (CofinalSchedule G fixed S)

/-- A viable seed row yields the weaker eventual-row interface directly.
Every selected transition is already a simultaneous forward comparison, so
`n + 1` witnesses eventual coherence. -/
noncomputable def eventualRowsOfViable
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (S : ViableStage G fixed kappa hkappa hsingular)
    (hseed : ∀ i,
      sourceLayer A₀ kappa hcard hkappa hsingular i ⊆
        S.1.sources i) :
    EventualRows G fixed A₀ kappa hkappa hsingular hcard where
  sources i n := (S.chain n).1.sources i
  paths i n := (S.chain n).1.paths i
  seed := by simpa only [ViableStage.chain_zero] using hseed
  sources_subset i n := (S.chain n).1.sources_subset i
  sources_card i n := (S.chain n).1.sources_card i
  sources_mono i m n hmn := by
    induction n, hmn using Nat.le_induction with
    | base => exact Set.Subset.rfl
    | succ n _ ih =>
        exact ih.trans ((S.chain_step n).1 i)
  isWarp i n := (S.chain n).1.row.isWarp i
  finiteCharacter i n := (S.chain n).1.row.finiteCharacter i
  initialSet i n := (S.chain n).1.row.initialSet i
  links i n := (S.chain n).1.row.links i
  close i n := by
    simpa only [DWeb.matrixStageFamily] using (S.chain_step n).2.1 i
  eventualForward n :=
    ⟨n + 1, Nat.lt_succ_self n, (S.chain_step n).2.2⟩

/-- The selected cofinal subsequence of any eventual-row system is itself
a schedule in the bounded-stage relation. -/
noncomputable def cofinalScheduleOfEventualRows
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (R : EventualRows G fixed A₀ kappa hkappa hsingular hcard) :
    CofinalSchedule G fixed
      { row :=
          { sources := fun i ↦ R.sources i 0
            paths := fun i ↦ R.paths i 0
            isWarp := fun i ↦ R.isWarp i 0
            finiteCharacter := fun i ↦ R.finiteCharacter i 0
            initialSet := fun i ↦ R.initialSet i 0
            links := fun i ↦ R.links i 0 }
        sources_subset := fun i ↦ R.sources_subset i 0
        sources_card := fun i ↦ R.sources_card i 0 } where
  stage n :=
    { row :=
        { sources := fun i ↦ R.sources i (R.stageAt n)
          paths := fun i ↦ R.paths i (R.stageAt n)
          isWarp := fun i ↦ R.isWarp i (R.stageAt n)
          finiteCharacter := fun i ↦ R.finiteCharacter i (R.stageAt n)
          initialSet := fun i ↦ R.initialSet i (R.stageAt n)
          links := fun i ↦ R.links i (R.stageAt n) }
      sources_subset := fun i ↦ R.sources_subset i (R.stageAt n)
      sources_card := fun i ↦ R.sources_card i (R.stageAt n) }
  stage_zero := rfl
  step n := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact R.sources_mono i (R.stageAt_le_succ n)
    · intro i x hx
      have hxNext : x ∈ R.sources i (R.stageAt n + 1) := by
        apply R.close i (R.stageAt n)
        simpa only [DWeb.matrixStageFamily] using hx
      exact R.sources_mono i (R.stageAt_succ_le n) hxNext
    · intro i
      simpa only [EventualRows.stageAt_succ] using
        R.forward_nextStage (R.stageAt n) i

/-- The exact initial global-admissibility condition.  It asks only for one
seeded point in the serial kernel, not for successors of arbitrary rows. -/
def InitialViability
    (G : DWeb V) (fixed : Set G.DPath)
    (A₀ : Set V) (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hcard : #A₀ = kappa) : Prop :=
  ∃ S : BoundedStage G kappa hkappa hsingular,
    (∀ i,
      sourceLayer A₀ kappa hcard hkappa hsingular i ⊆ S.sources i) ∧
    Viable G fixed S

/-- Eventual rows already contain a viable seeded bounded stage: take their
chosen cofinal subsequence and use its range as the serial certificate. -/
theorem initialViability_of_eventualRows
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (R : EventualRows G fixed A₀ kappa hkappa hsingular hcard) :
    InitialViability G fixed A₀ kappa hkappa hsingular hcard := by
  let S : BoundedStage G kappa hkappa hsingular :=
    { row :=
        { sources := fun i ↦ R.sources i 0
          paths := fun i ↦ R.paths i 0
          isWarp := fun i ↦ R.isWarp i 0
          finiteCharacter := fun i ↦ R.finiteCharacter i 0
          initialSet := fun i ↦ R.initialSet i 0
          links := fun i ↦ R.links i 0 }
      sources_subset := fun i ↦ R.sources_subset i 0
      sources_card := fun i ↦ R.sources_card i 0 }
  refine ⟨S, R.seed, ?_⟩
  exact viable_of_cofinalSchedule (cofinalScheduleOfEventualRows R)

theorem exists_eventualRows_of_initialViability
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (h : InitialViability G fixed A₀ kappa hkappa hsingular hcard) :
    Nonempty (EventualRows G fixed A₀ kappa
      hkappa hsingular hcard) := by
  obtain ⟨S, hseed, hviable⟩ := h
  exact ⟨eventualRowsOfViable ⟨S, hviable⟩ hseed⟩

/-- The serial-kernel condition loses no information: it is equivalent to
the exact eventual-row interface consumed by the matrix limit. -/
theorem initialViability_iff_nonempty_eventualRows
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa} :
    InitialViability G fixed A₀ kappa hkappa hsingular hcard ↔
      Nonempty (EventualRows G fixed A₀ kappa
        hkappa hsingular hcard) := by
  constructor
  · exact exists_eventualRows_of_initialViability
  · rintro ⟨R⟩
    exact initialViability_of_eventualRows R

/-- The coinductive packaging and the literal seeded omega-chain
formulation have exactly the same strength. -/
theorem initialViability_iff_hasSeededCofinalSchedule
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa} :
    InitialViability G fixed A₀ kappa hkappa hsingular hcard ↔
      HasSeededCofinalSchedule G fixed A₀ kappa
        hkappa hsingular hcard := by
  constructor
  · rintro ⟨S, hseed, hviable⟩
    exact ⟨S, hseed,
      (viable_iff_nonempty_cofinalSchedule).1 hviable⟩
  · rintro ⟨S, hseed, hschedule⟩
    exact ⟨S, hseed,
      (viable_iff_nonempty_cofinalSchedule).2 hschedule⟩

/-! ## Exact strength of the serial kernel -/

/-- A genuine post-choice fixed point gives eventual rows by repeating its
paths and omega-closed sources.  This direction is useful for auditing any
proposed fixed-point or maximal-chain construction. -/
noncomputable def eventualRowsOfOmegaFixedPoint
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed)
    (R : OmegaFixedPointRows G fixed A₀ kappa
      hkappa hsingular hcard) :
    EventualRows G fixed A₀ kappa hkappa hsingular hcard where
  sources i _ := R.sources i
  paths i _ := R.paths i
  seed i := G.subset_omegaCompetitorClosure
    (fixed ∪ ⋃ j, R.paths j)
    (sourceLayer A₀ kappa hcard hkappa hsingular i)
  sources_subset i _ := by
    apply G.omegaCompetitorClosure_minimal
    · exact (sourceLayer_subset A₀ kappa hcard hkappa hsingular i).trans
        hA₀
    · rintro b ⟨_a, _ha, _p, _hp, _hpa, q, hq, hqb, _hpq⟩
      rw [← hqb]
      rcases hq with hqFixed | hqRows
      · have hqInitial : q.initial ∈ G.source \ A₀ := by
          rw [← hfixed.initialSet_eq]
          exact ⟨q, hqFixed, rfl⟩
        exact hqInitial.1
      · obtain ⟨j, hqRow⟩ := Set.mem_iUnion.1 hqRows
        rw [← R.initialSet j]
        exact ⟨q, hqRow, rfl⟩
  sources_card i _ := R.mk_sources_eq hfixed.isWarp i
  sources_mono _ _ _ _ := Set.Subset.rfl
  isWarp i _ := R.isWarp i
  finiteCharacter i _ := R.finiteCharacter i
  initialSet i _ := R.initialSet i
  links i _ := R.linksClosure i
  close i _ := G.competitorClosure_omega_subset
    (fixed ∪ ⋃ j, R.paths j)
    (sourceLayer A₀ kappa hcard hkappa hsingular i)
  eventualForward n :=
    ⟨n + 1, Nat.lt_succ_self n, fun i ↦
      G.forwardExtension_refl (R.paths i)⟩

/-- For a fixed complementary linkage, finding a viable seeded row is
already equivalent to linkability of the whole web.  Thus Zorn maximality
or a club argument must prove a graph-theoretic compactness statement; the
serial-kernel packaging alone cannot supply it. -/
theorem initialViability_iff_isLinkable
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    InitialViability G fixed A₀ kappa hkappa hsingular hcard ↔
      IsLinkable G := by
  constructor
  · intro hviable
    obtain ⟨R⟩ := exists_eventualRows_of_initialViability hviable
    exact SingularExtension.isLinkable_of_targetRows
      R.toTargetRows hA₀ hfixed
  · intro hG
    let R : OmegaFixedPointRows G fixed A₀ kappa
        hkappa hsingular hcard :=
      OmegaFixedPointRows.ofIsLinkable hA₀ hfixed hG
    exact initialViability_of_eventualRows
      (eventualRowsOfOmegaFixedPoint hA₀ hfixed R)

/-- The exact eventual-row interface is itself equivalent to whole-web
linkability once the complementary linkage is fixed.  Therefore producing
eventual rows is not a set-theoretic compactness lemma left after the graph
argument; it already contains the missing graph argument. -/
theorem nonempty_eventualRows_iff_isLinkable
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    Nonempty (EventualRows G fixed A₀ kappa
        hkappa hsingular hcard) ↔
      IsLinkable G := by
  rw [← initialViability_iff_nonempty_eventualRows,
    initialViability_iff_isLinkable hA₀ hfixed]

/-- Likewise, existence of a literal globally admissible seeded cofinal
chain is equivalent to the desired linkage.  This is the sharp boundary
for a proposed Zorn/club argument on simultaneous rows. -/
theorem hasSeededCofinalSchedule_iff_isLinkable
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    HasSeededCofinalSchedule G fixed A₀ kappa
        hkappa hsingular hcard ↔
      IsLinkable G := by
  rw [← initialViability_iff_hasSeededCofinalSchedule,
    initialViability_iff_isLinkable hA₀ hfixed]

/-! ## Unconditional existence of bounded seed rows -/

/-- Lower induction always supplies a bounded row with the canonical source
layers.  The unresolved global issue is whether some such row belongs to
the serial kernel. -/
theorem exists_initialBoundedStage
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa) :
    ∃ S : BoundedStage G kappa hkappa hsingular,
      ∀ i, S.sources i =
        sourceLayer A₀ kappa hcard hkappa hsingular i := by
  let R := initialTargetRowStage hA₀ hcard hkappa hsingular
    hlower hG hNorm
  refine ⟨
    { row := R
      sources_subset := ?_
      sources_card := ?_ }, ?_⟩
  · intro i
    exact (sourceLayer_subset A₀ kappa hcard hkappa hsingular i).trans
      hA₀
  · intro i
    exact sourceLayer_card A₀ kappa hcard hkappa hsingular i
  · intro i
    rfl

/-- Initial viability in every normalized singular extension instance is
sufficient for the complete extension clause. -/
theorem singularExtensionClauseAt_of_normalizedInitialViability
    (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V)
    (hselect : ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      (hcard : #A₀ = kappa) →
      ∀ fixed : Set Gamma.normalized.DPath,
        IsLinkageBetween Gamma.normalized
            (Gamma.normalized.source \ A₀) Gamma.normalized.target fixed →
        InitialViability Gamma.normalized fixed A₀ kappa
          hkappa hsingular hcard) :
    ExtensionClauseAt Gamma kappa := by
  apply singularExtensionClauseAt_of_normalizedEventualRows
    kappa hkappa hsingular Gamma
  intro A₀ hA₀ hcard fixed hfixed
  exact Classical.choice (exists_eventualRows_of_initialViability
    (hselect A₀ hA₀ hcard fixed hfixed))

#print axioms eventualRowsOfViable
#print axioms viable_iff_nonempty_cofinalSchedule
#print axioms initialViability_iff_nonempty_eventualRows
#print axioms initialViability_iff_hasSeededCofinalSchedule
#print axioms initialViability_iff_isLinkable
#print axioms nonempty_eventualRows_iff_isLinkable
#print axioms hasSeededCofinalSchedule_iff_isLinkable
#print axioms exists_initialBoundedStage
#print axioms singularExtensionClauseAt_of_normalizedInitialViability

end SingularCofinalViability
end CardinalInduction
end Erdos599

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularExtension

/-!
# Eventual coherence is enough for the singular matrix

The direct-limit proof of Assertion 9.18 does not intrinsically require
that every displayed row extend the immediately following displayed row.
It is enough that every simultaneous row have *some strictly later*
simultaneous row which forward-extends all of its columns.  Recursively
choosing such later rows gives a cofinal forward chain.

This is a genuinely weaker and construction-specific replacement for the
false arbitrary-row successor rule.  In particular, intervening rows are
allowed to be dead ends.  The source sets attached to the ambient sequence
only need to be monotone and to absorb the competitors created at their own
row.  The selected cofinal subsequence then contains the canonical matrix
source recursion, so its target-link certificates can be restricted to the
sources actually consumed by Assertion 9.18.

The remaining selection problem is therefore precise: construct an
eventually coherent sequence.  Independent from-scratch lower-cardinal
rows do not provide the `eventualForward` field.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularEventualRows

open SingularExtension SingularMatrix

universe u

variable {V : Type u}

/-- A possibly non-coherent omega sequence of simultaneous target rows,
together with enough later forward comparisons to extract a coherent
cofinal subsequence. -/
structure EventualRows
    (G : DWeb V) (fixed : Set G.DPath)
    (A₀ : Set V) (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hcard : #A₀ = kappa) where
  sources : Index kappa → ℕ → Set V
  paths : Index kappa → ℕ → Set G.DPath
  seed : ∀ i,
    sourceLayer A₀ kappa hcard huncountable hsingular i ⊆ sources i 0
  sources_subset : ∀ i n, sources i n ⊆ G.source
  sources_card : ∀ i n,
    #(sources i n) = scale kappa huncountable hsingular i
  sources_mono : ∀ i, Monotone (sources i)
  isWarp : ∀ i n, G.IsWarp (paths i n)
  finiteCharacter : ∀ i n, G.HasFiniteCharacter (paths i n)
  initialSet : ∀ i n, G.initialSet (paths i n) = G.source
  links : ∀ i n, LinksToTarget G (paths i n) (sources i n)
  close : ∀ i n,
    G.competitorClosure (G.matrixStageFamily fixed paths n) (sources i n) ⊆
      sources i (n + 1)
  eventualForward : ∀ n, ∃ m, n < m ∧
    ∀ i, G.ForwardExtension (paths i n) (paths i m)

namespace EventualRows

variable {G : DWeb V} {fixed : Set G.DPath}
variable {A₀ : Set V} {kappa : Cardinal.{u}}
variable {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
variable {hcard : #A₀ = kappa}

/-- One chosen strictly later simultaneous forward extension. -/
noncomputable def nextStage
    (R : EventualRows G fixed A₀ kappa
      huncountable hsingular hcard) (n : ℕ) : ℕ :=
  Classical.choose (R.eventualForward n)

theorem lt_nextStage
    (R : EventualRows G fixed A₀ kappa
      huncountable hsingular hcard) (n : ℕ) :
    n < R.nextStage n :=
  (Classical.choose_spec (R.eventualForward n)).1

theorem forward_nextStage
    (R : EventualRows G fixed A₀ kappa
      huncountable hsingular hcard) (n : ℕ) (i : Index kappa) :
    G.ForwardExtension (R.paths i n) (R.paths i (R.nextStage n)) :=
  (Classical.choose_spec (R.eventualForward n)).2 i

/-- The cofinal sequence obtained by repeatedly jumping to a later
simultaneous extension. -/
noncomputable def stageAt
    (R : EventualRows G fixed A₀ kappa
      huncountable hsingular hcard) : ℕ → ℕ
  | 0 => 0
  | n + 1 => R.nextStage (stageAt R n)

@[simp] theorem stageAt_zero
    (R : EventualRows G fixed A₀ kappa
      huncountable hsingular hcard) :
    R.stageAt 0 = 0 := rfl

@[simp] theorem stageAt_succ
    (R : EventualRows G fixed A₀ kappa
      huncountable hsingular hcard) (n : ℕ) :
    R.stageAt (n + 1) = R.nextStage (R.stageAt n) := rfl

theorem stageAt_succ_le
    (R : EventualRows G fixed A₀ kappa
      huncountable hsingular hcard) (n : ℕ) :
    R.stageAt n + 1 ≤ R.stageAt (n + 1) := by
  rw [R.stageAt_succ]
  exact R.lt_nextStage (R.stageAt n)

theorem stageAt_le_succ
    (R : EventualRows G fixed A₀ kappa
      huncountable hsingular hcard) (n : ℕ) :
    R.stageAt n ≤ R.stageAt (n + 1) :=
  (Nat.le_succ (R.stageAt n)).trans (R.stageAt_succ_le n)

/-- Restrict a source-faithful target-link certificate to a smaller source
set. -/
theorem linksToTarget_mono_sources
    {W : Set G.DPath} {S T : Set V}
    (hTS : T ⊆ S) (hW : LinksToTarget G W S) :
    LinksToTarget G W T := by
  intro a ha
  obtain ⟨p, hpW, q, rfl, hpure, hsuffix⟩ := hW a (hTS ha)
  refine ⟨Sum.inl q, hpW, q, rfl, ?_, hsuffix⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxq, hxT⟩
    have hxS : x ∈ q.support ∩ S := ⟨hxq, hTS hxT⟩
    have hxa : x = a := Set.mem_singleton_iff.1 (hpure ▸ hxS)
    exact hxa ▸ Set.mem_singleton a
  · intro x hx
    have hxa : x = a := Set.mem_singleton_iff.1 hx
    subst x
    have haS : a ∈ ({a} : Set V) := Set.mem_singleton a
    have haq : a ∈ q.support := (hpure.symm ▸ haS).1
    exact ⟨haq, ha⟩

/-- The canonical matrix sources generated by the selected cofinal rows
remain inside the auxiliary monotone source sets at the selected stages. -/
theorem matrixSources_subset_selected
    (R : EventualRows G fixed A₀ kappa
      huncountable hsingular hcard) (i : Index kappa) : ∀ n,
    matrixSources G fixed
        (fun j m ↦ R.paths j (R.stageAt m))
        (sourceLayer A₀ kappa hcard huncountable hsingular) i n ⊆
      R.sources i (R.stageAt n) := by
  intro n
  induction n with
  | zero =>
      simpa only [matrixSources_zero, stageAt_zero] using R.seed i
  | succ n ih =>
      rw [matrixSources_succ]
      intro x hx
      rcases hx with hxOld | hxCompetitor
      · exact R.sources_mono i (R.stageAt_le_succ n) (ih hxOld)
      · have hxNext : x ∈ R.sources i (R.stageAt n + 1) := by
          apply R.close i (R.stageAt n)
          apply G.competitorClosure_mono_sources ih
          simpa only [DWeb.matrixStageFamily] using hxCompetitor
        exact R.sources_mono i (R.stageAt_succ_le n) hxNext

/-- Extract the cofinal coherent subsequence and forget the larger
auxiliary source sets.  This produces exactly the `TargetRows` consumed by
Assertion 9.18. -/
noncomputable def toTargetRows
    (R : EventualRows G fixed A₀ kappa
      huncountable hsingular hcard) :
    TargetRows G fixed A₀ kappa huncountable hsingular hcard where
  paths i n := R.paths i (R.stageAt n)
  isWarp i n := R.isWarp i (R.stageAt n)
  finiteCharacter i n := R.finiteCharacter i (R.stageAt n)
  initialSet i n := R.initialSet i (R.stageAt n)
  targetSegment i n a ha := by
    apply targetSegment_of_linksToTarget
      (linksToTarget_mono_sources
        (R.matrixSources_subset_selected i n)
        (R.links i (R.stageAt n)))
    exact ha
  forward i n := by
    simpa only [stageAt_succ] using
      R.forward_nextStage (R.stageAt n) i

end EventualRows

/-! The normalized public reduction corresponding to the weaker selection
interface. -/

theorem singularExtensionClauseAt_of_normalizedEventualRows
    (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V)
    (hrows : ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      (hcard : #A₀ = kappa) →
      ∀ fixed : Set Gamma.normalized.DPath,
        IsLinkageBetween Gamma.normalized
            (Gamma.normalized.source \ A₀) Gamma.normalized.target fixed →
        EventualRows Gamma.normalized fixed A₀ kappa
          hkappa hsingular hcard) :
    ExtensionClauseAt Gamma kappa := by
  apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
  apply singularExtensionClauseAt_of_targetRows
    kappa hkappa hsingular Gamma.normalized
  intro A₀ hA₀ hcard fixed hfixed
  exact (hrows A₀ hA₀ hcard fixed hfixed).toTargetRows

#print axioms EventualRows.toTargetRows
#print axioms singularExtensionClauseAt_of_normalizedEventualRows

end SingularEventualRows
end CardinalInduction
end Erdos599

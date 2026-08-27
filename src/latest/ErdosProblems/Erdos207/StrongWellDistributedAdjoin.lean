/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteJointBind
import ErdosProblems.Erdos207.StrongWellDistributed
import ErdosProblems.Erdos207.WeightSystem

/-!
# Adjoining a conditionally sampled family to the master law

The KSSS master step samples several new triangle families conditionally on
the old stage.  A prescribed later family is partitioned according to which
triangles came from the old later family and which came from the new sample.
This file proves that powerset decomposition exactly, before any asymptotic
parameter estimates are applied.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Retain the old initial family on a joint old/new outcome. -/
def jointInitial
    {Ω Ξ V : Type*} [DecidableEq V]
    (initial : Ω → TripleSystemOn V) (z : Ω × Ξ) : TripleSystemOn V :=
  initial z.1

/-- Adjoin the conditionally sampled family to the old later family. -/
def jointLater
    {Ω Ξ V : Type*} [DecidableEq V]
    (later : Ω → TripleSystemOn V)
    (added : Ω → Ξ → TripleSystemOn V) (z : Ω × Ξ) : TripleSystemOn V :=
  later z.1 ∪ added z.1 z.2

/-- Inclusion in `later ω ∪ added ω ξ` supplies a partition of the
prescribed family into an old part and a new part. -/
lemma strongDistributionEvent_jointLater_partition
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V] [DecidableEq V]
    (initial later : Ω → TripleSystemOn V)
    (added : Ω → Ξ → TripleSystemOn V)
    (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V))
    (z : Ω × Ξ)
    (hz : StrongDistributionEvent (jointInitial initial)
      (jointLater later added) Ifix Dfix Efix z) :
    ∃ S ∈ Dfix.powerset,
      StrongDistributionEvent initial later Ifix S Efix z.1 ∧
      Dfix \ S ⊆ added z.1 z.2 := by
  classical
  let S := Dfix ∩ later z.1
  refine ⟨S, mem_powerset.mpr inter_subset_left, ?_, ?_⟩
  · exact ⟨hz.1, inter_subset_right, hz.2.2⟩
  · intro T hT
    obtain ⟨hTD, hTnotS⟩ := mem_sdiff.mp hT
    have hTunion := hz.2.1 hTD
    rw [jointLater, mem_union] at hTunion
    exact hTunion.resolve_left fun hTl ↦ hTnotS (mem_inter.mpr ⟨hTD, hTl⟩)

/-- Exact powerset bound for adjoining a conditionally sampled family. -/
theorem FiniteLaw.jointBind_probability_strongDistributionEvent_adjoin_le
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (initial later : Ω → TripleSystemOn V)
    (added : Ω → Ξ → TripleSystemOn V)
    (addedBound : TripleSystemOn V → ℝ≥0)
    (hadded : ∀ ω Q,
      (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ) ≤ addedBound Q)
    (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (L.jointBind K).probability
        (StrongDistributionEvent (jointInitial initial)
          (jointLater later added) Ifix Dfix Efix) ≤
      ∑ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          L.probability
            (StrongDistributionEvent initial later Ifix S Efix) := by
  classical
  let Event : TripleSystemOn V → (Ω × Ξ) → Prop := fun S z ↦
    StrongDistributionEvent initial later Ifix S Efix z.1 ∧
      Dfix \ S ⊆ added z.1 z.2
  calc
    (L.jointBind K).probability
        (StrongDistributionEvent (jointInitial initial)
          (jointLater later added) Ifix Dfix Efix) ≤
        (L.jointBind K).probability
          (fun z ↦ ∃ S ∈ Dfix.powerset, Event S z) := by
      apply FiniteLaw.probability_mono
      intro z hz
      simpa only [Event] using
        strongDistributionEvent_jointLater_partition initial later added
          Ifix Dfix Efix z hz
    _ ≤ ∑ S ∈ Dfix.powerset,
        (L.jointBind K).probability (Event S) :=
      (L.jointBind K).probability_exists_le Dfix.powerset Event
    _ ≤ ∑ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          L.probability
            (StrongDistributionEvent initial later Ifix S Efix) := by
      apply sum_le_sum
      intro S hS
      apply FiniteLaw.jointBind_probability_and_le L K
        (StrongDistributionEvent initial later Ifix S Efix)
        (fun ω ξ ↦ Dfix \ S ⊆ added ω ξ) (addedBound (Dfix \ S))
      intro ω _hOld
      exact hadded ω (Dfix \ S)

/-- Strong well-distributedness of the old law, together with a uniform
conditional joint-inclusion bound for the new family, yields the exact
powerset estimate used in the master update. -/
theorem IsStronglyWellDistributed.jointBind_adjoin_le
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C b : ℝ≥0}
    (hstrong : IsStronglyWellDistributed L W k initial later p C b)
    (added : Ω → Ξ → TripleSystemOn V)
    (addedBound : TripleSystemOn V → ℝ≥0)
    (hadded : ∀ ω Q,
      (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ) ≤ addedBound Q)
    (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V))
    (hdisj : Disjoint Ifix Dfix) :
    (L.jointBind K).probability
        (StrongDistributionEvent (jointInitial initial)
          (jointLater later added) Ifix Dfix Efix) ≤
      ∑ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          (C ^ (Ifix.card + S.card + Efix.card) *
            (p ^ Efix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) := by
  apply (FiniteLaw.jointBind_probability_strongDistributionEvent_adjoin_le
    L K initial later added addedBound hadded Ifix Dfix Efix).trans
  apply sum_le_sum
  intro S hS
  gcongr
  apply hstrong Ifix S Efix
  apply Disjoint.mono_right (mem_powerset.mp hS)
  exact hdisj

/-- If every powerset-partition term fits one target strong-distribution
budget, the complete adjoin update fits the same budget after multiplying
the target constant by two.  Thus all analytic work is reduced to a single
partition term. -/
theorem IsStronglyWellDistributed.jointBind_adjoin
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ}
    {W : Vortex V ell} {k k' : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C b p' C' b' : ℝ≥0}
    (hstrong : IsStronglyWellDistributed L W k initial later p C b)
    (added : Ω → Ξ → TripleSystemOn V)
    (addedBound : TripleSystemOn V → ℝ≥0)
    (hadded : ∀ ω Q,
      (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ) ≤ addedBound Q)
    (hpartition : ∀ (Ifix Dfix : TripleSystemOn V)
      (Efix : Finset (Sym2 V)), Disjoint Ifix Dfix →
      ∀ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          (C ^ (Ifix.card + S.card + Efix.card) *
            (p ^ Efix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) ≤
          C' ^ (Ifix.card + Dfix.card + Efix.card) *
            (p' ^ Efix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k' p' Dfix + b')) :
    IsStronglyWellDistributed (L.jointBind K) W k'
      (jointInitial initial) (jointLater later added) p' (2 * C') b' := by
  intro Ifix Dfix Efix hdisj
  let m := Ifix.card + Dfix.card + Efix.card
  let X := p' ^ Efix.card *
    (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
      laterTriangleScale W k' p' Dfix + b'
  have hraw := hstrong.jointBind_adjoin_le added addedBound hadded
    Ifix Dfix Efix hdisj
  calc
    (L.jointBind K).probability
        (StrongDistributionEvent (jointInitial initial)
          (jointLater later added) Ifix Dfix Efix) ≤
        ∑ S ∈ Dfix.powerset,
          addedBound (Dfix \ S) *
            (C ^ (Ifix.card + S.card + Efix.card) *
              (p ^ Efix.card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p S + b)) := hraw
    _ ≤ ∑ _S ∈ Dfix.powerset, C' ^ m * X := by
      apply sum_le_sum
      intro S hS
      simpa only [m, X] using hpartition Ifix Dfix Efix hdisj S hS
    _ = (2 : ℝ≥0) ^ Dfix.card * (C' ^ m * X) := by simp
    _ ≤ (2 : ℝ≥0) ^ m * (C' ^ m * X) := by
      gcongr
      · norm_num
      · dsimp only [m]
        omega
    _ = (2 * C') ^
          (Ifix.card + Dfix.card + Efix.card) *
            (p' ^ Efix.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k' p' Dfix + b') := by
      rw [mul_pow]
      dsimp only [m, X]
      ring

end

end Erdos207

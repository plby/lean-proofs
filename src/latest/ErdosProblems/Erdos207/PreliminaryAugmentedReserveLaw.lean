/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryAugmentedReserve

/-!
# Law update for the preliminary family and augmented reserve

This file is the exact finite probability bookkeeping behind KSSS
(8.7)--(8.13).  Prescribed later triangles split into old and preliminary
parts.  Independently, prescribed augmented-reserve edges split into sampled
and preliminary-uncovered parts.  A conditional joint bound for the latter
two parts therefore combines with reserve-aware strong distribution by two
powerset union bounds.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Exact two-powerset estimate before inserting the old strong-distribution
bound. -/
theorem FiniteLaw.jointBind_probability_preliminaryAugmentedReserve_le
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V]
    (L : FiniteLaw Omega) (K : Omega → FiniteLaw Xi)
    (initial later : Omega → TripleSystemOn V)
    (sampled : Omega → Finset (Sym2 V))
    (G : Omega → SimpleGraph V) (U : Finset V)
    (added : Omega → Xi → TripleSystemOn V)
    (preliminaryBound : TripleSystemOn V → Finset (Sym2 V) → ℝ≥0)
    (hpreliminary : ∀ omega Q E,
      (K omega).probability (fun xi ↦
        Q ⊆ added omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) U
          (added omega xi)) ≤ preliminaryBound Q E)
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V)) :
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added)
          (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
            (added z.1 z.2)) Ifix Dfix Efix Rfix) ≤
      ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        preliminaryBound (Dfix \ S) (Rfix \ T) *
          L.probability (ReserveStrongDistributionEvent
            initial later sampled Ifix S Efix T) := by
  classical
  let Event : TripleSystemOn V → Finset (Sym2 V) →
      (Omega × Xi) → Prop := fun S T z ↦
    ReserveStrongDistributionEvent initial later sampled
        Ifix S Efix T z.1 ∧
      (Dfix \ S ⊆ added z.1 z.2 ∧
        Rfix \ T ⊆ preliminaryResidualCrossingEdges
          (G z.1) U (added z.1 z.2))
  calc
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added)
          (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
            (added z.1 z.2)) Ifix Dfix Efix Rfix) ≤
        (L.jointBind K).probability (fun z ↦
          ∃ S ∈ Dfix.powerset, ∃ T ∈ Rfix.powerset, Event S T z) := by
      apply FiniteLaw.probability_mono
      intro z hz
      simpa only [Event] using
        reserveStrongDistributionEvent_preliminary_partition
          initial later sampled G U added Ifix Dfix Efix Rfix z hz
    _ ≤ ∑ S ∈ Dfix.powerset,
        (L.jointBind K).probability (fun z ↦
          ∃ T ∈ Rfix.powerset, Event S T z) :=
      (L.jointBind K).probability_exists_le Dfix.powerset
        (fun S z ↦ ∃ T ∈ Rfix.powerset, Event S T z)
    _ ≤ ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        (L.jointBind K).probability (Event S T) := by
      apply sum_le_sum
      intro S hS
      exact (L.jointBind K).probability_exists_le Rfix.powerset (Event S)
    _ ≤ ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        preliminaryBound (Dfix \ S) (Rfix \ T) *
          L.probability (ReserveStrongDistributionEvent
            initial later sampled Ifix S Efix T) := by
      apply sum_le_sum
      intro S hS
      apply sum_le_sum
      intro T hT
      apply L.jointBind_probability_and_le K
        (ReserveStrongDistributionEvent initial later sampled
          Ifix S Efix T)
        (fun omega xi ↦
          Dfix \ S ⊆ added omega xi ∧
          Rfix \ T ⊆ preliminaryResidualCrossingEdges
            (G omega) U (added omega xi))
        (preliminaryBound (Dfix \ S) (Rfix \ T))
      intro omega hOld
      exact hpreliminary omega (Dfix \ S) (Rfix \ T)

/-- Support-sensitive version of the exact two-powerset estimate.  This is
the form needed for totalized state-dependent kernels: the sharp preliminary
bound is required only at old states which can actually occur. -/
theorem FiniteLaw.jointBind_probability_preliminaryAugmentedReserve_le_supported
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V]
    (L : FiniteLaw Omega) (K : Omega → FiniteLaw Xi)
    (initial later : Omega → TripleSystemOn V)
    (sampled : Omega → Finset (Sym2 V))
    (G : Omega → SimpleGraph V) (U : Finset V)
    (added : Omega → Xi → TripleSystemOn V)
    (preliminaryBound : TripleSystemOn V → Finset (Sym2 V) → ℝ≥0)
    (hpreliminary : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (K omega).probability (fun xi ↦
        Q ⊆ added omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) U
          (added omega xi)) ≤ preliminaryBound Q E)
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V)) :
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added)
          (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
            (added z.1 z.2)) Ifix Dfix Efix Rfix) ≤
      ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        preliminaryBound (Dfix \ S) (Rfix \ T) *
          L.probability (ReserveStrongDistributionEvent
            initial later sampled Ifix S Efix T) := by
  classical
  let Event : TripleSystemOn V → Finset (Sym2 V) →
      (Omega × Xi) → Prop := fun S T z ↦
    ReserveStrongDistributionEvent initial later sampled
        Ifix S Efix T z.1 ∧
      (Dfix \ S ⊆ added z.1 z.2 ∧
        Rfix \ T ⊆ preliminaryResidualCrossingEdges
          (G z.1) U (added z.1 z.2))
  calc
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added)
          (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
            (added z.1 z.2)) Ifix Dfix Efix Rfix) ≤
        (L.jointBind K).probability (fun z ↦
          ∃ S ∈ Dfix.powerset, ∃ T ∈ Rfix.powerset, Event S T z) := by
      apply FiniteLaw.probability_mono
      intro z hz
      simpa only [Event] using
        reserveStrongDistributionEvent_preliminary_partition
          initial later sampled G U added Ifix Dfix Efix Rfix z hz
    _ ≤ ∑ S ∈ Dfix.powerset,
        (L.jointBind K).probability (fun z ↦
          ∃ T ∈ Rfix.powerset, Event S T z) :=
      (L.jointBind K).probability_exists_le Dfix.powerset
        (fun S z ↦ ∃ T ∈ Rfix.powerset, Event S T z)
    _ ≤ ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        (L.jointBind K).probability (Event S T) := by
      apply sum_le_sum
      intro S hS
      exact (L.jointBind K).probability_exists_le Rfix.powerset (Event S)
    _ ≤ ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        preliminaryBound (Dfix \ S) (Rfix \ T) *
          L.probability (ReserveStrongDistributionEvent
            initial later sampled Ifix S Efix T) := by
      apply sum_le_sum
      intro S hS
      apply sum_le_sum
      intro T hT
      apply L.jointBind_probability_and_le_on_support K
        (ReserveStrongDistributionEvent initial later sampled
          Ifix S Efix T)
        (fun omega xi ↦
          Dfix \ S ⊆ added omega xi ∧
          Rfix \ T ⊆ preliminaryResidualCrossingEdges
            (G omega) U (added omega xi))
        (preliminaryBound (Dfix \ S) (Rfix \ T))
      intro omega hmass _hOld
      exact hpreliminary omega hmass (Dfix \ S) (Rfix \ T)

/-- The preceding exact decomposition with the old reserve-aware
strong-distribution estimate substituted in every summand. -/
theorem IsReserveStronglyWellDistributed.jointBind_preliminaryAugmentedReserve_le
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {sampled : Omega → Finset (Sym2 V)}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p reserveDensity C b : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k initial later sampled
      p reserveDensity C b)
    (added : Omega → Xi → TripleSystemOn V)
    (preliminaryBound : TripleSystemOn V → Finset (Sym2 V) → ℝ≥0)
    (hpreliminary : ∀ omega Q E,
      (K omega).probability (fun xi ↦
        Q ⊆ added omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) U
          (added omega xi)) ≤ preliminaryBound Q E)
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V))
    (hdisj : Disjoint Ifix Dfix) :
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added)
          (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
            (added z.1 z.2)) Ifix Dfix Efix Rfix) ≤
      ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        preliminaryBound (Dfix \ S) (Rfix \ T) *
          (C ^ (Ifix.card + S.card + Efix.card + T.card) *
            (p ^ Efix.card * reserveDensity ^ T.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p S + b)) := by
  apply (FiniteLaw.jointBind_probability_preliminaryAugmentedReserve_le
    L K initial later sampled G U added preliminaryBound hpreliminary
      Ifix Dfix Efix Rfix).trans
  apply sum_le_sum
  intro S hS
  apply sum_le_sum
  intro T hT
  gcongr
  exact hstrong Ifix S Efix T
    (Disjoint.mono_right (mem_powerset.mp hS) hdisj)

/-- Insert the old reserve-aware estimate into the support-sensitive
two-powerset decomposition. -/
theorem IsReserveStronglyWellDistributed.jointBind_preliminaryAugmentedReserve_le_supported
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {sampled : Omega → Finset (Sym2 V)}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p reserveDensity C b : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k initial later sampled
      p reserveDensity C b)
    (added : Omega → Xi → TripleSystemOn V)
    (preliminaryBound : TripleSystemOn V → Finset (Sym2 V) → ℝ≥0)
    (hpreliminary : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (K omega).probability (fun xi ↦
        Q ⊆ added omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) U
          (added omega xi)) ≤ preliminaryBound Q E)
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V))
    (hdisj : Disjoint Ifix Dfix) :
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added)
          (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
            (added z.1 z.2)) Ifix Dfix Efix Rfix) ≤
      ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        preliminaryBound (Dfix \ S) (Rfix \ T) *
          (C ^ (Ifix.card + S.card + Efix.card + T.card) *
            (p ^ Efix.card * reserveDensity ^ T.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p S + b)) := by
  apply (FiniteLaw.jointBind_probability_preliminaryAugmentedReserve_le_supported
    L K initial later sampled G U added preliminaryBound hpreliminary
      Ifix Dfix Efix Rfix).trans
  apply sum_le_sum
  intro S hS
  apply sum_le_sum
  intro T hT
  gcongr
  exact hstrong Ifix S Efix T
    (Disjoint.mono_right (mem_powerset.mp hS) hdisj)

/-- Factor-absorption form of the preliminary update.  All analytic work is
isolated in the displayed per-partition inequality; the two powersets cost
one factor `2` in the output multiplicative constant. -/
theorem IsReserveStronglyWellDistributed.jointBind_preliminaryAugmentedReserve
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {sampled : Omega → Finset (Sym2 V)}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p reserveDensity C b p' reserveDensity' C' b' : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k initial later sampled
      p reserveDensity C b)
    (added : Omega → Xi → TripleSystemOn V)
    (preliminaryBound : TripleSystemOn V → Finset (Sym2 V) → ℝ≥0)
    (hpreliminary : ∀ omega Q E,
      (K omega).probability (fun xi ↦
        Q ⊆ added omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) U
          (added omega xi)) ≤ preliminaryBound Q E)
    (hpartition : ∀ (Ifix Dfix : TripleSystemOn V)
      (Efix Rfix : Finset (Sym2 V)), Disjoint Ifix Dfix →
      ∀ S ∈ Dfix.powerset, ∀ T ∈ Rfix.powerset,
        preliminaryBound (Dfix \ S) (Rfix \ T) *
          (C ^ (Ifix.card + S.card + Efix.card + T.card) *
            (p ^ Efix.card * reserveDensity ^ T.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p S + b)) ≤
        C' ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
          (p' ^ Efix.card * reserveDensity' ^ Rfix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W next p' Dfix + b')) :
    IsReserveStronglyWellDistributed (L.jointBind K) W next
      (jointInitial initial) (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
        (added z.1 z.2)) p' reserveDensity' (2 * C') b' := by
  intro Ifix Dfix Efix Rfix hdisj
  let m := Ifix.card + Dfix.card + Efix.card + Rfix.card
  let X := p' ^ Efix.card * reserveDensity' ^ Rfix.card *
    (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
      laterTriangleScale W next p' Dfix + b'
  have hraw := hstrong.jointBind_preliminaryAugmentedReserve_le
    added preliminaryBound hpreliminary Ifix Dfix Efix Rfix hdisj
  calc
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added)
          (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
            (added z.1 z.2)) Ifix Dfix Efix Rfix) ≤
      ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        preliminaryBound (Dfix \ S) (Rfix \ T) *
          (C ^ (Ifix.card + S.card + Efix.card + T.card) *
            (p ^ Efix.card * reserveDensity ^ T.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p S + b)) := hraw
    _ ≤ ∑ _S ∈ Dfix.powerset, ∑ _T ∈ Rfix.powerset,
        C' ^ m * X := by
      apply sum_le_sum
      intro S hS
      apply sum_le_sum
      intro T hT
      simpa only [m, X] using
        hpartition Ifix Dfix Efix Rfix hdisj S hS T hT
    _ = (2 : ℝ≥0) ^ (Dfix.card + Rfix.card) * (C' ^ m * X) := by
      simp [pow_add, mul_assoc]
    _ ≤ (2 : ℝ≥0) ^ m * (C' ^ m * X) := by
      gcongr
      · norm_num
      · dsimp only [m]
        omega
    _ = (2 * C') ^
          (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
        (p' ^ Efix.card * reserveDensity' ^ Rfix.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
          laterTriangleScale W next p' Dfix + b') := by
      rw [mul_pow]
      dsimp only [m, X]
      ring

/-- Factor-absorption form with a preliminary estimate required only on the
positive-mass support of the old law. -/
theorem IsReserveStronglyWellDistributed.jointBind_preliminaryAugmentedReserve_supported
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {sampled : Omega → Finset (Sym2 V)}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p reserveDensity C b p' reserveDensity' C' b' : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k initial later sampled
      p reserveDensity C b)
    (added : Omega → Xi → TripleSystemOn V)
    (preliminaryBound : TripleSystemOn V → Finset (Sym2 V) → ℝ≥0)
    (hpreliminary : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (K omega).probability (fun xi ↦
        Q ⊆ added omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) U
          (added omega xi)) ≤ preliminaryBound Q E)
    (hpartition : ∀ (Ifix Dfix : TripleSystemOn V)
      (Efix Rfix : Finset (Sym2 V)), Disjoint Ifix Dfix →
      ∀ S ∈ Dfix.powerset, ∀ T ∈ Rfix.powerset,
        preliminaryBound (Dfix \ S) (Rfix \ T) *
          (C ^ (Ifix.card + S.card + Efix.card + T.card) *
            (p ^ Efix.card * reserveDensity ^ T.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p S + b)) ≤
        C' ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
          (p' ^ Efix.card * reserveDensity' ^ Rfix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W next p' Dfix + b')) :
    IsReserveStronglyWellDistributed (L.jointBind K) W next
      (jointInitial initial) (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
        (added z.1 z.2)) p' reserveDensity' (2 * C') b' := by
  intro Ifix Dfix Efix Rfix hdisj
  let m := Ifix.card + Dfix.card + Efix.card + Rfix.card
  let X := p' ^ Efix.card * reserveDensity' ^ Rfix.card *
    (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
      laterTriangleScale W next p' Dfix + b'
  have hraw := hstrong.jointBind_preliminaryAugmentedReserve_le_supported
    added preliminaryBound hpreliminary Ifix Dfix Efix Rfix hdisj
  calc
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added)
          (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
            (added z.1 z.2)) Ifix Dfix Efix Rfix) ≤
      ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        preliminaryBound (Dfix \ S) (Rfix \ T) *
          (C ^ (Ifix.card + S.card + Efix.card + T.card) *
            (p ^ Efix.card * reserveDensity ^ T.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p S + b)) := hraw
    _ ≤ ∑ _S ∈ Dfix.powerset, ∑ _T ∈ Rfix.powerset,
        C' ^ m * X := by
      apply sum_le_sum
      intro S hS
      apply sum_le_sum
      intro T hT
      simpa only [m, X] using
        hpartition Ifix Dfix Efix Rfix hdisj S hS T hT
    _ = (2 : ℝ≥0) ^ (Dfix.card + Rfix.card) * (C' ^ m * X) := by
      simp [pow_add, mul_assoc]
    _ ≤ (2 : ℝ≥0) ^ m * (C' ^ m * X) := by
      gcongr
      · norm_num
      · dsimp only [m]
        omega
    _ = (2 * C') ^
          (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
        (p' ^ Efix.card * reserveDensity' ^ Rfix.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
          laterTriangleScale W next p' Dfix + b') := by
      rw [mul_pow]
      dsimp only [m, X]
      ring

end

end Erdos207

import ErdosProblems.Erdos520.ConcreteThinBlockMaximum
import ErdosProblems.Erdos520.RescaledScheduledSmallEnergy

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Concrete high-moment block maximum on a shifted schedule

This file joins the complete equation-(16) proof, conditional Markov, the
finite thin-block union, the exact small-energy estimate, and Borel--Cantelli.
The analytic scale is `ell + S`, as in the gap-free integer geometry.

The sole deep input below is the displayed eventual initial `2/3` moment.
Everything after that input, including the reciprocal `K/2` power in the
maximal block energy, is proved here.
-/

/-- The exact small-energy crossing level on a fixed shifted schedule. -/
noncomputable def concreteShiftedEnergyLevel
    (S K ell : ℕ) : ℝ :=
  caichToExactEnergyConstant *
    caichMaximalEnergyThreshold (ell + S) K
      (caichSmallEnergyT1 (ell + S))

theorem concreteShiftedEnergyLevel_pos
    {S K ell : ℕ} (hS : 2 ≤ S) :
    0 < concreteShiftedEnergyLevel S K ell := by
  exact mul_pos caichToExactEnergyConstant_pos
    (caichMaximalEnergyThreshold_pos (K := K)
      (show 0 < ell + S by omega) (caichSmallEnergyT1_add_pos hS))

/-- Complete maximal-block conclusion for any concrete schedule whose
energy is Caich's normalized energy at the shifted analytic scale.

`Kblocks` is allowed to differ from `K`: the aligned schedule has block-count
degree `K+1`, while the reciprocal energy gain is `K/2`. -/
theorem exists_ae_eventually_concreteShiftedBlockEnergyMax_le
    (s : ConcreteThinBlockSchedule) {S K Kblocks : ℕ} {D C : ℝ}
    (hS : 2 ≤ S) (hC : 0 ≤ C)
    (hJ : ∀ ell, (s.J ell : ℝ) ≤ D * (ell : ℝ) ^ Kblocks)
    (hI : ∀ ell j,
      s.I ell j =
        caichNormalizedEnergy (ell + S) K
          (s.y ell 0) (s.y ell j))
    (hmoment : ∀ᶠ ell : ℕ in atTop,
      (∫ omega,
        caichNormalizedEnergy (ell + S) K
          (s.y ell 0) (s.y ell 0) omega ^ ((2 : ℝ) / 3) ∂μ) ≤
        caichInitialEnergyMomentBudget (ell + S) K C) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
        caichBlockEnergyMax s.J s.toThinBlockData.U ell omega ≤
          B * caichMaximalEnergyThreshold (ell + S) K
            (caichSmallEnergyT1 (ell + S)) := by
  let d : ThinBlockData Omega := s.toThinBlockData
  have hImeas : ∀ ell j,
      StronglyMeasurable[d.filtration ell (j - 1)]
        (d.I ell (j - 1)) := by
    intro ell j
    change StronglyMeasurable[Filtration.piFinset
      ((s.y ell (j - 1) + 1).primesBelow)]
      (s.I ell (j - 1))
    rw [hI]
    exact stronglyMeasurable_caichNormalizedEnergy
      (ell + S) K (s.y ell 0) (s.y ell (j - 1))
  have hInonneg : ∀ ell j omega, 0 ≤ d.I ell j omega := by
    intro ell j omega
    change 0 ≤ s.I ell j omega
    rw [hI]
    exact caichNormalizedEnergy_nonneg
      (lt_of_lt_of_le Nat.one_lt_two (s.two_le_y ell j)) omega
  have hbase : ∀ ell omega, d.U ell 0 omega ≤ d.I ell 0 omega := by
    intro ell omega
    change realSmoothBlockEnergy (s.y ell 0) (s.y ell 0) omega ≤
      s.I ell 0 omega
    rw [hI]
    exact realSmoothBlockEnergy_self_le_caichInitial
      (ell := ell + S) (K := K) (s.two_le_y ell 0) omega
  obtain ⟨C0, hC0, htail⟩ :=
    exists_localizedThinBlockTailConstant_allScales
      d hImeas hInonneg s.thinPrimeBlockMomentBound
  let B0 : ℝ := max 1 (2 * C0)
  have hB0 : 1 ≤ B0 := le_max_left _ _
  have hB0pos : 0 < B0 := zero_lt_one.trans_le hB0
  have hC0B0 : 2 * C0 ≤ B0 := le_max_right _ _
  let A : ℕ → ℝ := fun ell => concreteShiftedEnergyLevel S K ell
  have hA : ∀ ell, 0 ≤ A ell := fun ell =>
    (concreteShiftedEnergyLevel_pos (K := K) (ell := ell) hS).le
  have hschedule : Summable fun ell => μ.real
      (caichRescaledScheduledEnergyFailure (fun n => n + S) K s.J s.y
        caichSmallEnergyT1 ell) := by
    apply summable_measureReal_caichShiftedScheduledEnergyFailure
      hS s.J s.y hC s.y_monotone (fun ell => s.two_le_y ell 0)
    exact hmoment
  have henergySet (ell : ℕ) :
      {omega | A ell ≤ caichBlockEnergyMax d.J d.I ell omega} =
        caichRescaledScheduledEnergyFailure (fun n => n + S) K
          s.J s.y caichSmallEnergyT1 ell := by
    ext omega
    change A ell ≤ caichBlockEnergyMax s.J s.I ell omega ↔ _
    unfold caichRescaledScheduledEnergyFailure
    simp only [Set.mem_setOf_eq]
    have hmax : caichBlockEnergyMax s.J s.I ell omega =
        caichBlockEnergyMax s.J
          (caichRescaledScheduledEnergy (fun n => n + S) K s.y)
          ell omega := by
      unfold caichBlockEnergyMax
      apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
      intro j hj
      rw [hI]
      rfl
    rw [← hmax]
    rfl
  have henergy : Summable fun ell =>
      μ.real {omega | A ell ≤ caichBlockEnergyMax d.J d.I ell omega} := by
    apply hschedule.congr
    intro ell
    rw [henergySet]
  have hsmall : Summable fun ell =>
      μ.real (thinBlockMaximumSmallFailure d ell (A ell) B0) :=
    summable_measureReal_thinBlockMaximumSmallFailure_of_energyMax
      μ d A B0 hA hB0 hbase henergy
  have hthin : ∀ ell j, j ∈ Finset.range (d.J ell) →
      μ.real (localizedThinBlockBad d ell (j + 1) (A ell) B0) ≤
        (1 / 2 : ℝ) ^ ell := by
    intro ell j hj
    exact htail ell (j + 1) (by omega) (by simpa using! hj)
      (A ell) B0
      (concreteShiftedEnergyLevel_pos (K := K) (ell := ell) hS)
      hB0pos hC0B0
  have hmax := ae_eventually_caichBlockEnergyMax_le
    d A B0 D Kblocks hJ hsmall hthin
  refine ⟨B0 * caichToExactEnergyConstant,
    mul_pos hB0pos caichToExactEnergyConstant_pos, ?_⟩
  filter_upwards [hmax] with omega homega
  filter_upwards [homega] with ell hell
  exact hell.trans_eq (by
    unfold A concreteShiftedEnergyLevel
    ring)

end Problem520
end Erdos

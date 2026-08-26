import ErdosProblems.Erdos520.AlignedClampedSchedule
import ErdosProblems.Erdos520.ConcreteThinBlockMaximum
import ErdosProblems.Erdos520.RescaledScheduledSmallEnergy

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Concrete high-moment block maximum on a clamped schedule

This is the clamped-scale counterpart of `ConcreteRescaledBlockMaximum`.
Since `clampedAlignedScale S ell = ell` eventually, the small-energy budget
is unchanged outside a finite set and the resulting block estimate is
eventually indexed by the literal outer scale.
-/

/-- The exact small-energy crossing level at the clamped analytic scale. -/
noncomputable def concreteClampedEnergyLevel
    (S K ell : ℕ) : ℝ :=
  caichToExactEnergyConstant *
    caichMaximalEnergyThreshold (clampedAlignedScale S ell) K
      (caichSmallEnergyT1 (clampedAlignedScale S ell))

theorem concreteClampedEnergyLevel_pos
    {S K ell : ℕ} (hS : 2 ≤ S) :
    0 < concreteClampedEnergyLevel S K ell := by
  have hL : 2 ≤ clampedAlignedScale S ell :=
    hS.trans (le_clampedAlignedScale_left S ell)
  exact mul_pos caichToExactEnergyConstant_pos
    (caichMaximalEnergyThreshold_pos (K := K) (by omega)
      (caichSmallEnergyT1_pos hL))

/-- Clamping the argument of the scalar small-energy budget only changes
finitely many terms. -/
theorem summable_caichSmallEnergyT1_budget_clamped
    (S : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    Summable fun ell : ℕ =>
      caichSmallEnergyT1 (clampedAlignedScale S ell) ^ (-(1 : ℝ) / 4) +
        C * caichSmallEnergyT1 (clampedAlignedScale S ell) ^
          (-(1 : ℝ) / 6) := by
  apply (summable_caichSmallEnergyT1_budget hC).congr_atTop
  filter_upwards [eventually_clampedAlignedScale_eq S] with ell hell
  simp only [hell]

/-- Fully specialized clamped-scale small-energy summability theorem. -/
theorem summable_measureReal_caichClampedScheduledEnergyFailure
    {K S : ℕ} (hS : 2 ≤ S) (J : ℕ → ℕ) (y : ℕ → ℕ → ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hy : ∀ ell, Monotone (y ell))
    (hy₀ : ∀ ell, 2 ≤ y ell 0)
    (hmoment : ∀ᶠ ell : ℕ in atTop,
      (∫ omega,
        caichNormalizedEnergy (clampedAlignedScale S ell) K
            (y ell 0) (y ell 0) omega ^ ((2 : ℝ) / 3) ∂μ) ≤
          caichInitialEnergyMomentBudget
            (clampedAlignedScale S ell) K C) :
    Summable fun ell => μ.real
      (caichRescaledScheduledEnergyFailure (clampedAlignedScale S) K J y
        caichSmallEnergyT1 ell) := by
  apply summable_measureReal_caichRescaledScheduledEnergyFailure
    (clampedAlignedScale S) J y caichSmallEnergyT1 hy hy₀
  · filter_upwards with ell
    have hL := hS.trans (le_clampedAlignedScale_left S ell)
    omega
  · filter_upwards with ell
    exact caichSmallEnergyT1_pos
      (hS.trans (le_clampedAlignedScale_left S ell))
  · exact hmoment
  · exact summable_caichSmallEnergyT1_budget_clamped S (by positivity)

/-- Complete maximal-block conclusion for a concrete schedule whose
normalized energy is evaluated at the clamped analytic scale. -/
theorem exists_ae_eventually_concreteClampedBlockEnergyMax_le
    (s : ConcreteThinBlockSchedule) {S K Kblocks : ℕ} {D C : ℝ}
    (hS : 2 ≤ S) (hC : 0 ≤ C)
    (hJ : ∀ ell, (s.J ell : ℝ) ≤ D * (ell : ℝ) ^ Kblocks)
    (hI : ∀ ell j,
      s.I ell j =
        caichNormalizedEnergy (clampedAlignedScale S ell) K
          (s.y ell 0) (s.y ell j))
    (hmoment : ∀ᶠ ell : ℕ in atTop,
      (∫ omega,
        caichNormalizedEnergy (clampedAlignedScale S ell) K
            (s.y ell 0) (s.y ell 0) omega ^ ((2 : ℝ) / 3) ∂μ) ≤
          caichInitialEnergyMomentBudget
            (clampedAlignedScale S ell) K C) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
        caichBlockEnergyMax s.J s.toThinBlockData.U ell omega ≤
          B * caichMaximalEnergyThreshold
            (clampedAlignedScale S ell) K
            (caichSmallEnergyT1 (clampedAlignedScale S ell)) := by
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
      (clampedAlignedScale S ell) K (s.y ell 0) (s.y ell (j - 1))
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
      (ell := clampedAlignedScale S ell) (K := K)
      (s.two_le_y ell 0) omega
  obtain ⟨C0, hC0, htail⟩ :=
    exists_localizedThinBlockTailConstant_allScales
      d hImeas hInonneg s.thinPrimeBlockMomentBound
  let B0 : ℝ := max 1 (2 * C0)
  have hB0 : 1 ≤ B0 := le_max_left _ _
  have hB0pos : 0 < B0 := zero_lt_one.trans_le hB0
  have hC0B0 : 2 * C0 ≤ B0 := le_max_right _ _
  let A : ℕ → ℝ := fun ell => concreteClampedEnergyLevel S K ell
  have hA : ∀ ell, 0 ≤ A ell := fun ell =>
    (concreteClampedEnergyLevel_pos (K := K) (ell := ell) hS).le
  have hschedule : Summable fun ell => μ.real
      (caichRescaledScheduledEnergyFailure (clampedAlignedScale S) K
        s.J s.y caichSmallEnergyT1 ell) := by
    apply summable_measureReal_caichClampedScheduledEnergyFailure
      hS s.J s.y hC s.y_monotone (fun ell => s.two_le_y ell 0)
    exact hmoment
  have henergySet (ell : ℕ) :
      {omega | A ell ≤ caichBlockEnergyMax d.J d.I ell omega} =
        caichRescaledScheduledEnergyFailure (clampedAlignedScale S) K
          s.J s.y caichSmallEnergyT1 ell := by
    ext omega
    change A ell ≤ caichBlockEnergyMax s.J s.I ell omega ↔ _
    unfold caichRescaledScheduledEnergyFailure
    simp only [Set.mem_setOf_eq]
    have hmax : caichBlockEnergyMax s.J s.I ell omega =
        caichBlockEnergyMax s.J
          (caichRescaledScheduledEnergy (clampedAlignedScale S) K s.y)
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
      (concreteClampedEnergyLevel_pos (K := K) (ell := ell) hS)
      hB0pos hC0B0
  have hmax := ae_eventually_caichBlockEnergyMax_le
    d A B0 D Kblocks hJ hsmall hthin
  refine ⟨B0 * caichToExactEnergyConstant,
    mul_pos hB0pos caichToExactEnergyConstant_pos, ?_⟩
  filter_upwards [hmax] with omega homega
  filter_upwards [homega] with ell hell
  exact hell.trans_eq (by
    unfold A concreteClampedEnergyLevel
    ring)

end Problem520
end Erdos

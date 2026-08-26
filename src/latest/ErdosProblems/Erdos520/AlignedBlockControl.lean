import ErdosProblems.Erdos520.AlignedIntegerGeometry
import ErdosProblems.Erdos520.ConcreteRescaledBlockMaximum
import ErdosProblems.Erdos520.HarperSpecialization

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# The complete repaired block maximum on the aligned schedule

This file specializes Harper's initial low moment to the gap-free aligned
integer schedule and feeds it through the fully concrete high-moment block
argument.  The endpoint is the reciprocal `ell^(-K/2)` maximal block-energy
bound used in the quadratic-variation reduction.

No version of Caich's disputed two-parameter maximal inequality occurs here.
The only non-elementary premise is `HarperRademacherInitialMomentStatement`,
the exact published low-moment theorem isolated in `HarperSpecialization`.
-/

/-- The harmless `K`-dependent enlargement of Harper's absolute moment
constant caused by starting the aligned thin schedule at `X_(L-2)`. -/
noncomputable def alignedHarperMomentConstant (C : ℝ) (K : ℕ) : ℝ :=
  C / (1 / (3 * (2 : ℝ) ^ K)) ^ ((1 : ℝ) / 3)

theorem alignedHarperMomentConstant_nonneg {C : ℝ} (hC : 0 ≤ C) (K : ℕ) :
    0 ≤ alignedHarperMomentConstant C K := by
  unfold alignedHarperMomentConstant
  positivity

/-- Harper's low moment has exactly the shifted Caich budget required at the
initial endpoint of the aligned schedule. -/
theorem integral_alignedThinInitialEnergy_twoThird_le_of_harperBound
    {C : ℝ} {Y K L : ℕ}
    (hC : 0 ≤ C) (hHarper : HarperRademacherInitialMomentBound C Y)
    (hK : 1 ≤ K) (hL : 5 ≤ L)
    (hY : Y ≤ alignedThinEndpoint K L 0) :
    (∫ omega,
        caichNormalizedEnergy L K
          (alignedThinEndpoint K L 0)
          (alignedThinEndpoint K L 0) omega ^ ((2 : ℝ) / 3) ∂μ) ≤
      caichInitialEnergyMomentBudget L K
        (alignedHarperMomentConstant C K) := by
  let cK : ℝ := 1 / (3 * (2 : ℝ) ^ K)
  let H : ℝ := 1 + logLogNat (alignedThinEndpoint K L 0)
  have hcK : 0 < cK := by dsimp [cK]; positivity
  have hLR : (0 : ℝ) < L := by positivity
  have hscale : cK * (L : ℝ) ^ K ≤ H := by
    simpa only [cK, H] using!
      (alignedThinInitial_harperScale_lower hK hL)
  have hH : 0 < H :=
    (mul_pos hcK (pow_pos hLR K)).trans_le hscale
  have hthird0 : 0 < cK ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hcK _
  have hLthird0 : 0 < (L : ℝ) ^ ((K : ℝ) / 3) :=
    Real.rpow_pos_of_pos hLR _
  have hscaledThird :
      cK ^ ((1 : ℝ) / 3) * (L : ℝ) ^ ((K : ℝ) / 3) ≤
        H ^ ((1 : ℝ) / 3) := by
    have hpowThird :
        ((L : ℝ) ^ K) ^ ((1 : ℝ) / 3) =
          (L : ℝ) ^ ((K : ℝ) / 3) := by
      symm
      rw [show (K : ℝ) / 3 = (K : ℝ) * ((1 : ℝ) / 3) by ring,
        Real.rpow_mul hLR.le, Real.rpow_natCast]
    have hr := Real.rpow_le_rpow
      (mul_nonneg hcK.le (pow_nonneg hLR.le K)) hscale
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    calc
      cK ^ ((1 : ℝ) / 3) * (L : ℝ) ^ ((K : ℝ) / 3) =
          (cK * (L : ℝ) ^ K) ^ ((1 : ℝ) / 3) := by
        rw [Real.mul_rpow hcK.le (pow_nonneg hLR.le K)]
        rw [hpowThird]
      _ ≤ H ^ ((1 : ℝ) / 3) := hr
  have hraw := integral_caichInitialEnergy_twoThird_le_of_harperBound
    (ell := L) (K := K) hHarper hY
      (two_le_alignedThinEndpoint K L 0)
  calc
    (∫ omega,
        caichNormalizedEnergy L K
          (alignedThinEndpoint K L 0)
          (alignedThinEndpoint K L 0) omega ^ ((2 : ℝ) / 3) ∂μ) ≤
        C / H ^ ((1 : ℝ) / 3) := by
      simpa only [H] using! hraw
    _ ≤ C /
        (cK ^ ((1 : ℝ) / 3) * (L : ℝ) ^ ((K : ℝ) / 3)) :=
      div_le_div_of_nonneg_left hC (mul_pos hthird0 hLthird0)
        hscaledThird
    _ = caichInitialEnergyMomentBudget L K
        (alignedHarperMomentConstant C K) := by
      unfold caichInitialEnergyMomentBudget alignedHarperMomentConstant
      dsimp [cK]
      field_simp

/-- Complete aligned maximal-block theorem.  It includes the concrete
schedule, equation (16), conditional Markov, the honest polynomial union,
small energy, and Borel--Cantelli. -/
theorem exists_alignedBlockEnergyMaxGood_of_harper
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement) :
    ∃ s : ConcreteThinBlockSchedule, ∃ S : ℕ, ∃ B : ℝ,
      5 ≤ S ∧
      s.J = shiftedAlignedThinBlockCount K S ∧
      s.y = (fun ell j => alignedThinEndpoint K (ell + S) j) ∧
      s.I = (fun ell j =>
        caichNormalizedEnergy (ell + S) K
          (alignedThinEndpoint K (ell + S) 0)
          (alignedThinEndpoint K (ell + S) j)) ∧
      0 < B ∧
      ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
        blockEnergyMaxGoodAtScale s.J s.toThinBlockData.U B K ell omega := by
  obtain ⟨C, hC, Y, hY, hHarperBound⟩ := hHarper
  obtain ⟨s, S, hS, hJ, hy, hI⟩ :=
    exists_alignedIntegerConcreteThinBlockSchedule K (by omega)
  let C' : ℝ := alignedHarperMomentConstant C K
  have hC' : 0 ≤ C' := alignedHarperMomentConstant_nonneg hC.le K
  have hmoment : ∀ᶠ ell : ℕ in atTop,
      (∫ omega,
        caichNormalizedEnergy (ell + S) K
          (s.y ell 0) (s.y ell 0) omega ^ ((2 : ℝ) / 3) ∂μ) ≤
        caichInitialEnergyMomentBudget (ell + S) K C' := by
    filter_upwards [eventually_ge_atTop Y] with ell hellY
    have hYendpoint : Y ≤ alignedThinEndpoint K (ell + S) 0 := by
      calc
        Y ≤ ell := hellY
        _ ≤ ell + S := Nat.le_add_right ell S
        _ ≤ alignedThinEndpoint K (ell + S) 0 :=
          scale_le_alignedThinEndpoint (by omega)
            (show 4 ≤ ell + S by omega)
    have hm := integral_alignedThinInitialEnergy_twoThird_le_of_harperBound
      hC.le hHarperBound (by omega) (show 5 ≤ ell + S by omega) hYendpoint
    simpa only [C', hy] using! hm
  have hJpoly : ∀ ell,
      (s.J ell : ℝ) ≤
        (((S + 1) ^ (K + 1) : ℕ) : ℝ) *
          (ell : ℝ) ^ (K + 1) := by
    intro ell
    rw [hJ]
    exact shiftedAlignedThinBlockCount_cast_le_all K S ell
  have hIpoint : ∀ ell j,
      s.I ell j = caichNormalizedEnergy (ell + S) K
        (s.y ell 0) (s.y ell j) := by
    intro ell j
    rw [hI, hy]
  obtain ⟨B, hB, hmax⟩ :=
    exists_ae_eventually_concreteShiftedBlockEnergyMax_le
      s (S := S) (K := K) (Kblocks := K + 1)
        (D := (((S + 1) ^ (K + 1) : ℕ) : ℝ))
        (C := C') (by omega) hC' hJpoly hIpoint hmoment
  refine ⟨s, S, B, hS, hJ, hy, hI, hB, ?_⟩
  filter_upwards [hmax] with omega homega
  filter_upwards [homega, eventually_ge_atTop (2 : ℕ)] with ell hell hell2
  unfold blockEnergyMaxGoodAtScale
  calc
    caichBlockEnergyMax s.J s.toThinBlockData.U ell omega ≤
        B * caichMaximalEnergyThreshold (ell + S) K
          (caichSmallEnergyT1 (ell + S)) := hell
    _ = B * alignedCaichBlockLevel K (ell + S) := by
      rw [caichMaximalEnergyThreshold_smallEnergyT1]
      rfl
    _ ≤ B * alignedCaichBlockLevel K ell :=
      mul_alignedCaichBlockLevel_add_le hB.le hK hell2
    _ = B * Real.sqrt
          ((ell : ℝ) ^ 10 /
            ((ell : ℝ) * Real.log (ell : ℝ))) /
          (ell : ℝ) ^ ((K : ℝ) / 2) := by
      unfold alignedCaichBlockLevel
      ring

end Problem520
end Erdos

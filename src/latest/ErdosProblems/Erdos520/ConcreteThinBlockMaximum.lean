import ErdosProblems.Erdos520.IntegerThinSchedule
import ErdosProblems.Erdos520.ThinBlockMaximum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set

namespace Erdos
namespace Problem520

/-!
# The base block in the maximal thin-block argument

The union in equation (27) includes `j = 0`, whereas the high-moment estimate
is needed only for the fresh blocks `1 ≤ j ≤ J`.  At `j = 0` the concrete
clamped maximum is constant and its energy is bounded directly by Caich's
initial normalized energy.  This file proves that bookkeeping fact.
-/

/-- With equal block endpoints, the clamped running maximum is exactly the
square of the old smooth sum. -/
theorem realSmoothBlockMaxSq_self (a : ℕ) (omega : Omega) (z : ℝ) :
    realSmoothBlockMaxSq a a omega z = |ΨReal omega z a| ^ 2 := by
  unfold realSmoothBlockMaxSq finiteRunningMax
  calc
    (Finset.range (a + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |ΨReal omega z (freshCutoff a a k)| ^ 2) =
      (Finset.range (a + 1)).sup' Finset.nonempty_range_add_one
        (fun _ => |ΨReal omega z a| ^ 2) := by
          apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
          intro k hk
          rw [freshCutoff_eq_a le_rfl]
          simpa only [Finset.mem_range, Nat.lt_add_one_iff] using! hk
    _ = |ΨReal omega z a| ^ 2 :=
      Finset.sup'_const Finset.nonempty_range_add_one _

/-- Consequently the `j = 0` block energy is the ordinary Parseval-side
smooth energy divided by `log a`. -/
theorem realSmoothBlockEnergy_self (a : ℕ) (omega : Omega) :
    realSmoothBlockEnergy a a omega =
      smoothEnergy omega a / Real.log (a : ℝ) := by
  unfold realSmoothBlockEnergy smoothEnergy
  simp_rw [realSmoothBlockMaxSq_self]
  ring

/-- At equal initial endpoints Caich's normalized energy dominates the base
block.  The factor `2 * pi` in his normalization makes this immediate. -/
theorem realSmoothBlockEnergy_self_le_caichInitial
    {ell K a : ℕ} (ha : 2 ≤ a) (omega : Omega) :
    realSmoothBlockEnergy a a omega ≤
      caichNormalizedEnergy ell K a a omega := by
  rw [realSmoothBlockEnergy_self]
  have hC :
      Real.exp
          (Real.log (Real.log (a : ℝ) / Real.log (a : ℝ)) /
            ((ell : ℝ) ^ K)) ≤
        (2 * Real.pi) * (1 : ℝ) := by
    have hloga : Real.log (a : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < a by omega))).ne'
    rw [div_self hloga, Real.log_one, zero_div, Real.exp_zero]
    nlinarith [Real.pi_gt_three]
  have h := smoothEnergy_div_log_le_caichNormalizedEnergy
    (ell := ell) (K := K) (y₀ := a) (a := a) (b := a) (C := 1)
    (show 1 < a by omega) le_rfl hC omega
  simpa using! h

/-- A concrete schedule whose initial `I` is Caich's normalized energy has
the base comparison needed by `ThinBlockMaximum`. -/
theorem ConcreteThinBlockSchedule.baseBlockEnergy_le_I_of_caich
    (s : ConcreteThinBlockSchedule) {K ell : ℕ}
    (hI0 : s.I ell 0 =
      caichNormalizedEnergy (ell + 1) K
        (s.y ell 0) (s.y ell 0)) (omega : Omega) :
    s.toThinBlockData.U ell 0 omega ≤
      s.toThinBlockData.I ell 0 omega := by
  change realSmoothBlockEnergy (s.y ell (0 - 1)) (s.y ell 0) omega ≤
    s.I ell 0 omega
  simp only [Nat.zero_sub]
  rw [hI0]
  exact realSmoothBlockEnergy_self_le_caichInitial
    (s.two_le_y ell 0) omega

/-- The exact integer schedule can be chosen with the moment bound and the
base-block comparison simultaneously.  Thus the only small-energy failure
left in equation (27) is the crossing of the scheduled energies `I_j`. -/
theorem exists_integerThinPrimeBlockMomentBound_with_baseControl (K : ℕ) :
    ∃ s : ConcreteThinBlockSchedule,
      s.J = integerThinBlockCount K ∧
      ThinPrimeBlockMomentBound μ s.toThinBlockData ∧
      ∀ ell omega,
        s.toThinBlockData.U ell 0 omega ≤
          s.toThinBlockData.I ell 0 omega := by
  obtain ⟨s, B, hB, hJ, hy, hI⟩ :=
    exists_integerConcreteThinBlockSchedule K
  refine ⟨s, hJ, s.thinPrimeBlockMomentBound, ?_⟩
  intro ell omega
  apply s.baseBlockEnergy_le_I_of_caich (K := K) (ell := ell)
  rw [hI, hy]

end Problem520
end Erdos

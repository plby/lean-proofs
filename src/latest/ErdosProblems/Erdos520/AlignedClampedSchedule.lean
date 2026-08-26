import ErdosProblems.Erdos520.AlignedIntegerGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# The aligned schedule with a clamped analytic scale

The original total packaging used the analytic scale `ell + S`.  That is
harmless for block estimates but does not literally agree with the outer
scale used by the test mesh.  Here the finite exceptional range is handled
instead by

`L(ell) = max S ell`.

Thus `L(ell) = ell` eventually.  The zeroth block count is set to zero, and
the remaining counts obey the all-scale polynomial bound with constant
`S^(K+1)`.
-/

/-- Analytic scale clamped above the finite threshold `S`. -/
def clampedAlignedScale (S ell : ℕ) : ℕ := max S ell

/-- Aligned block count at the clamped scale.  The value at zero is suppressed
so a positive-power polynomial bound is literally true at every scale. -/
def clampedAlignedThinBlockCount (K S ell : ℕ) : ℕ :=
  if ell = 0 then 0 else alignedThinBlockCount K (clampedAlignedScale S ell)

theorem le_clampedAlignedScale_left (S ell : ℕ) :
    S ≤ clampedAlignedScale S ell :=
  le_max_left _ _

theorem le_clampedAlignedScale_right (S ell : ℕ) :
    ell ≤ clampedAlignedScale S ell :=
  le_max_right _ _

/-- Beyond the clamp threshold, the analytic scale is definitionally equal
after simplification to the outer scale. -/
theorem clampedAlignedScale_eq_of_ge {S ell : ℕ} (h : S ≤ ell) :
    clampedAlignedScale S ell = ell :=
  max_eq_right h

theorem eventually_clampedAlignedScale_eq (S : ℕ) :
    ∀ᶠ ell : ℕ in atTop, clampedAlignedScale S ell = ell := by
  filter_upwards [eventually_ge_atTop S] with ell hell
  exact clampedAlignedScale_eq_of_ge hell

/-- For positive `S` and `ell`, the clamp is bounded by their product. -/
theorem clampedAlignedScale_le_mul
    {S ell : ℕ} (hS : 1 ≤ S) (hell : 1 ≤ ell) :
    clampedAlignedScale S ell ≤ S * ell := by
  apply max_le
  · calc
      S = S * 1 := by simp
      _ ≤ S * ell := Nat.mul_le_mul_left S hell
  · calc
      ell = 1 * ell := by simp
      _ ≤ S * ell := Nat.mul_le_mul_right ell hS

/-- Polynomial count bound at every positive scale. -/
theorem clamped_alignedThinBlockCount_cast_le
    {K S ell : ℕ} (hS : 1 ≤ S) (hell : 1 ≤ ell) :
    (alignedThinBlockCount K (clampedAlignedScale S ell) : ℝ) ≤
      ((S ^ (K + 1) : ℕ) : ℝ) * (ell : ℝ) ^ (K + 1 : ℕ) := by
  have hpow := Nat.pow_le_pow_left
    (clampedAlignedScale_le_mul hS hell) (K + 1)
  rw [alignedThinBlockCount]
  exact_mod_cast (hpow.trans_eq (mul_pow S ell (K + 1)))

/-- Literal all-scale polynomial bound, including `ell = 0`. -/
theorem clampedAlignedThinBlockCount_cast_le_all
    {K S : ℕ} (hS : 1 ≤ S) (ell : ℕ) :
    (clampedAlignedThinBlockCount K S ell : ℝ) ≤
      ((S ^ (K + 1) : ℕ) : ℝ) * (ell : ℝ) ^ (K + 1 : ℕ) := by
  by_cases hell : ell = 0
  · subst ell
    simp [clampedAlignedThinBlockCount]
  rw [clampedAlignedThinBlockCount, if_neg hell]
  exact clamped_alignedThinBlockCount_cast_le hS
    (Nat.one_le_iff_ne_zero.mpr hell)

/-! ## Concrete thin-block packaging -/

/-- The gap-free aligned schedule packaged at the clamped analytic scale.
All fields are total, while `clampedAlignedScale S ell = ell` eventually. -/
theorem exists_clampedAlignedIntegerConcreteThinBlockSchedule
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ s : ConcreteThinBlockSchedule, ∃ S : ℕ, 5 ≤ S ∧
      s.J = clampedAlignedThinBlockCount K S ∧
      s.y = (fun ell j =>
        alignedThinEndpoint K (clampedAlignedScale S ell) j) ∧
      s.I = (fun ell j =>
        caichNormalizedEnergy (clampedAlignedScale S ell) K
          (alignedThinEndpoint K (clampedAlignedScale S ell) 0)
          (alignedThinEndpoint K (clampedAlignedScale S ell) j)) := by
  obtain ⟨C, hC, N, hN, hP⟩ := exists_primeCountingUpperBound
  let S : ℕ := alignedScheduleShift N
  have hS5 : 5 ≤ S := five_le_alignedScheduleShift N
  have hNS : N ≤ S := self_le_alignedScheduleShift N
  let s : ConcreteThinBlockSchedule :=
    { J := clampedAlignedThinBlockCount K S
      y := fun ell j =>
        alignedThinEndpoint K (clampedAlignedScale S ell) j
      y_monotone := fun ell =>
        alignedThinEndpoint_mono K (clampedAlignedScale S ell)
      two_le_y := fun ell j =>
        two_le_alignedThinEndpoint K (clampedAlignedScale S ell) j
      I := fun ell j =>
        caichNormalizedEnergy (clampedAlignedScale S ell) K
          (alignedThinEndpoint K (clampedAlignedScale S ell) 0)
          (alignedThinEndpoint K (clampedAlignedScale S ell) j)
      I_nonneg := by
        intro ell j old
        apply caichNormalizedEnergy_nonneg
        exact lt_of_lt_of_le Nat.one_lt_two
          (two_le_alignedThinEndpoint K (clampedAlignedScale S ell) j)
      Cparseval := 2
      Cparseval_nonneg := by norm_num
      Crecip := 4 * C
      Crecip_nonneg := by positivity
      parseval_le := by
        intro ell _hell j hj hjJ old
        have hellne : ell ≠ 0 := by
          intro hell0
          subst ell
          simp [clampedAlignedThinBlockCount] at hjJ
          omega
        rw [clampedAlignedThinBlockCount, if_neg hellne] at hjJ
        let L : ℕ := clampedAlignedScale S ell
        let a : ℕ := alignedThinEndpoint K L (j - 1)
        let b : ℕ := alignedThinEndpoint K L j
        have hL5 : 5 ≤ L := by
          exact hS5.trans (le_clampedAlignedScale_left S ell)
        have ha : 1 < a := by
          exact lt_of_lt_of_le Nat.one_lt_two
            (two_le_alignedThinEndpoint K L (j - 1))
        have hab : a ≤ b := by
          exact alignedThinEndpoint_mono K L (Nat.sub_le j 1)
        have hjprev : j - 1 ≤ alignedThinBlockCount K L :=
          (Nat.sub_le j 1).trans hjJ
        have hdamp :
            Real.exp
                (Real.log
                    (Real.log (a : ℝ) /
                      Real.log (alignedThinEndpoint K L 0 : ℝ)) /
                  ((L : ℝ) ^ K)) ≤
              (2 * Real.pi) * 2 := by
          simpa only [a] using!
            (alignedThinEndpoint_caichDamping_le_four_pi
              hK (show 4 ≤ L by omega) hjprev)
        change smoothEnergy old a / Real.log (b : ℝ) ≤
          (2 : ℝ) *
            caichNormalizedEnergy L K
              (alignedThinEndpoint K L 0) a old
        exact smoothEnergy_div_log_le_caichNormalizedEnergy
          ha hab hdamp old
      reciprocal_le := by
        intro ell hell j hj hjJ
        have hellne : ell ≠ 0 := Nat.one_le_iff_ne_zero.mp hell
        rw [clampedAlignedThinBlockCount, if_neg hellne] at hjJ
        let L : ℕ := clampedAlignedScale S ell
        let a : ℕ := alignedThinEndpoint K L (j - 1)
        let b : ℕ := alignedThinEndpoint K L j
        have hL5 : 5 ≤ L :=
          hS5.trans (le_clampedAlignedScale_left S ell)
        have hNL : N ≤ L :=
          hNS.trans (le_clampedAlignedScale_left S ell)
        have hLa : L ≤ a := by
          exact scale_le_alignedThinEndpoint hK (show 4 ≤ L by omega)
        have hNa : N ≤ a := hNL.trans hLa
        have ha : 2 ≤ a := two_le_alignedThinEndpoint K L (j - 1)
        have hab : a ≤ b :=
          alignedThinEndpoint_mono K L (Nat.sub_le j 1)
        have hwidth : logLogNat b - logLogNat a ≤ 2 / (L : ℝ) := by
          have hstep := alignedThinEndpoint_logLog_width
            (K := K) (ell := L) (j := j - 1) hK
              (show 4 ≤ L by omega)
          simpa only [a, b, Nat.sub_add_cancel hj] using! hstep
        have hlarge : (L : ℝ) ≤ Real.log (a : ℝ) :=
          scale_le_log_alignedThinEndpoint hK hL5
        have hraw := freshReciprocalSum_le_of_primeCountingUpperBound
          hC.le hP hNa ha hab
        have hLR : (0 : ℝ) < L := by positivity
        have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
        have hellL : (ell : ℝ) ≤ L := by
          exact_mod_cast le_clampedAlignedScale_right S ell
        calc
          freshReciprocalSum a b ≤
              C * (logLogNat b - logLogNat a) +
                2 * C / Real.log (a : ℝ) := hraw
          _ ≤ C * (2 / (L : ℝ)) + 2 * C / (L : ℝ) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hwidth hC.le
            · exact div_le_div_of_nonneg_left (by positivity) hLR hlarge
          _ = 4 * C / (L : ℝ) := by ring
          _ ≤ 4 * C / (ell : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hellR hellL }
  exact ⟨s, S, hS5, rfl, rfl, rfl⟩

/-- The clamped schedule supplies the complete equation-(16) moment bound,
with the schedule/test outer scales eventually identical. -/
theorem exists_clampedAlignedIntegerThinPrimeBlockMomentBound
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ s : ConcreteThinBlockSchedule, ∃ S : ℕ, 5 ≤ S ∧
      s.J = clampedAlignedThinBlockCount K S ∧
      s.y = (fun ell j =>
        alignedThinEndpoint K (clampedAlignedScale S ell) j) ∧
      s.I = (fun ell j =>
        caichNormalizedEnergy (clampedAlignedScale S ell) K
          (alignedThinEndpoint K (clampedAlignedScale S ell) 0)
          (alignedThinEndpoint K (clampedAlignedScale S ell) j)) ∧
      ThinPrimeBlockMomentBound μ s.toThinBlockData := by
  obtain ⟨s, S, hS, hJ, hy, hI⟩ :=
    exists_clampedAlignedIntegerConcreteThinBlockSchedule K hK
  exact ⟨s, S, hS, hJ, hy, hI, s.thinPrimeBlockMomentBound⟩

end Problem520
end Erdos

import ErdosProblems.Erdos421.LogPowerNorm
import ErdosProblems.Erdos421.MonotoneWeights

/-! # Cancellation for the unweighted Dirichlet blocks used as zeta factors -/

namespace Erdos421

/-- A finite block of the ordinary zeta Dirichlet series. -/
noncomputable def zetaBlock (M N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, ((M + n : ℕ) : ℂ) ^ (-s)

theorem cpow_neg_eq_weighted_phase {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (-s) = ((x ^ (-s.re) : ℝ) : ℂ) *
      oscillatoryPhase (Real.log x) (-s.im) := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have he : -s = ((-s.re : ℝ) : ℂ) + Complex.I * ((-s.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [he, Complex.cpow_add _ _ hxc, ← Complex.ofReal_cpow hx.le]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hxc, ← Complex.ofReal_log hx.le]
  unfold oscillatoryPhase
  congr 1
  ring

theorem zetaBlock_eq_weighted_phases {M : ℕ} (hM : 0 < M) (N : ℕ) (s : ℂ) :
    zetaBlock M N s = ∑ n ∈ Finset.range N,
      ((M + n : ℕ) : ℝ) ^ (-s.re) •
        oscillatoryPhase (Real.log (M + n : ℕ)) (-s.im) := by
  apply Finset.sum_congr rfl
  intro n _
  have hx : (0 : ℝ) < (M + n : ℕ) := by exact_mod_cast Nat.add_pos_left hM n
  simpa only [Complex.real_smul, Complex.ofReal_natCast] using cpow_neg_eq_weighted_phase hx s

theorem zetaBlock_norm_le_of_prefix_bounds {M : ℕ} (hM : 0 < M) (N : ℕ)
    (s : ℂ) (hs : 0 ≤ s.re) {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ N, ‖logarithmicSum M n (-s.im)‖ ≤ B) :
    ‖zetaBlock M N s‖ ≤ (M : ℝ) ^ (-s.re) * B := by
  let w : ℕ → ℝ := fun n ↦ ((M + n : ℕ) : ℝ) ^ (-s.re)
  have hw : ∀ n, 0 ≤ w n := fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ha : Antitone w := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast Nat.add_pos_left hM i
    · exact_mod_cast Nat.add_le_add_left hij M
    · exact neg_nonpos.mpr hs
  have hb := norm_sum_antitone_weight_le w
    (fun n ↦ oscillatoryPhase (Real.log (M + n : ℕ)) (-s.im)) N hw ha hB hprefix
  rw [zetaBlock_eq_weighted_phases hM]
  simpa only [w, Nat.add_zero] using hb

/-- An unconditional power saving for an ordinary zeta factor throughout
an explicit polynomial range of imaginary parts. -/
theorem zetaBlock_uniform_norm_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (R K : ℕ) (hK : 2 * R + 4 ≤ K) (s : ℂ) (hs : 0 ≤ s.re)
    (hlo : (M : ℝ) ^ (2 / (K : ℝ)) ≤ |s.im|) (hhi : |s.im| ≤ (M : ℝ) ^ (R + 1)) :
    ‖zetaBlock M N s‖ ≤
      4 * (M : ℝ) ^ (1 - s.re) * logarithmicPowerSaving M R K := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hsave := logarithmicPowerSaving_pos hM R K
  have hprefix : ∀ n ≤ N, ‖logarithmicSum M n (-s.im)‖ ≤
      4 * M * logarithmicPowerSaving M R K := by
    intro n hn
    apply logarithmicSum_uniform_norm_bound hM (hn.trans hN) R K hK
    · simpa only [abs_neg] using hlo
    · simpa only [abs_neg] using hhi
  have hb := zetaBlock_norm_le_of_prefix_bounds hM N s hs (by positivity) hprefix
  have he : (M : ℝ) ^ (-s.re) * M = (M : ℝ) ^ (1 - s.re) := by
    rw [sub_eq_add_neg, Real.rpow_add hMp, Real.rpow_one]
    ring
  calc
    _ ≤ (M : ℝ) ^ (-s.re) * (4 * M * logarithmicPowerSaving M R K) := hb
    _ = 4 * ((M : ℝ) ^ (-s.re) * M) * logarithmicPowerSaving M R K := by ring
    _ = _ := by rw [he]

theorem zetaBlock_uniform_norm_bound_of_one_le_re {M N : ℕ}
    (hM : 0 < M) (hN : N ≤ M) (R K : ℕ) (hK : 2 * R + 4 ≤ K)
    (s : ℂ) (hs : 1 ≤ s.re)
    (hlo : (M : ℝ) ^ (2 / (K : ℝ)) ≤ |s.im|) (hhi : |s.im| ≤ (M : ℝ) ^ (R + 1)) :
    ‖zetaBlock M N s‖ ≤ 4 * logarithmicPowerSaving M R K := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hp : (M : ℝ) ^ (1 - s.re) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hM1 (sub_nonpos.mpr hs)
  have hb := zetaBlock_uniform_norm_bound hM hN R K hK s (by linarith) hlo hhi
  have hsave := logarithmicPowerSaving_pos hM R K
  nlinarith

end Erdos421

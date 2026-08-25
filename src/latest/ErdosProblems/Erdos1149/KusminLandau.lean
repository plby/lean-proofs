/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos587.Analytic

/-!
# A discrete Kusmin--Landau inequality

This file proves the first-derivative estimate for a finite exponential sum.
The formulation is entirely discrete: the consecutive increments of the real
phase are monotone and remain a distance at least `lambda` from the integers.

The proof is summation by parts.  For `e(x) = exp(2 * pi * I * x)`, put
`w(x) = (1 - e(x))⁻¹`.  On `0 < x < 1`, `w(x)` has real part `1/2` and
imaginary part `cot (pi*x) / 2`.  Thus `w` moves monotonically along a vertical
line when `x` is monotone.  Its total variation telescopes, while the elementary
chord estimate `4 * min(x,1-x) ≤ ‖1-e(x)‖` controls both endpoints.
-/

open scoped BigOperators

namespace Erdos1149

/-- The reciprocal chord used in the Kusmin--Landau summation-by-parts proof. -/
noncomputable def chordWeight (x : ℝ) : ℂ :=
  (1 - Erdos587.phase x)⁻¹

private lemma phase_ne_one_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Erdos587.phase x ≠ 1 := by
  intro h
  rw [Erdos587.phase, Real.fourierChar_apply] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have him := congrArg Complex.im hn
  norm_num at him
  have hxn : x = (n : ℝ) := by
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hp)
    simpa [mul_assoc, mul_left_comm, mul_comm] using him
  have hn0 : (0 : ℤ) < n := by
    exact_mod_cast (hxn ▸ hx.1)
  have hn1 : n < (1 : ℤ) := by
    exact_mod_cast (hxn ▸ hx.2)
  omega

/-- The reciprocal chord has real part `1/2` and imaginary part one half of a
cotangent on the fundamental interval. -/
private lemma chordWeight_eq_half_add_cot {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    chordWeight x = ⟨1 / 2, Real.cot (Real.pi * x) / 2⟩ := by
  have hphase : Erdos587.phase x ≠ 1 := phase_ne_one_of_mem_Ioo hx
  rw [chordWeight, Erdos587.phase, Real.fourierChar_apply]
  rw [show (↑(2 * Real.pi * x) : ℂ) * Complex.I =
      2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) by push_cast; ring]
  have hcot := Complex.cot_pi_eq_exp_ratio (x : ℂ)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cot] at hcot
  have hden : 1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ≠ 0 := by
    rw [sub_ne_zero]
    symm
    simpa [Erdos587.phase, Real.fourierChar_apply, mul_assoc, mul_left_comm, mul_comm] using hphase
  let E := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))
  let c : ℂ := Real.cot (Real.pi * x)
  have hcot' : c * Complex.I * (1 - E) = E + 1 := by
    have hIden : Complex.I * (1 - E) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by simpa [E] using hden)
    have := (eq_div_iff hIden).mp hcot
    simpa [E, c, mul_assoc] using this
  have hprod : ((1 / 2 : ℂ) + c / 2 * Complex.I) * (1 - E) = 1 := by
    calc
      ((1 / 2 : ℂ) + c / 2 * Complex.I) * (1 - E) =
          ((1 - E) + c * Complex.I * (1 - E)) / 2 := by ring
      _ = ((1 - E) + (E + 1)) / 2 := by rw [hcot']
      _ = 1 := by ring
  rw [show (⟨1 / 2, Real.cot (Real.pi * x) / 2⟩ : ℂ) =
      (1 / 2 : ℂ) + c / 2 * Complex.I by
        apply Complex.ext <;> norm_num [c] <;>
          rw [← Complex.ofReal_mul, ← Complex.ofReal_cot] <;> rfl]
  rw [← one_div, div_eq_iff hden]
  simpa [E, c, mul_assoc] using hprod.symm

private lemma chordWeight_re {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (chordWeight x).re = 1 / 2 := by
  rw [chordWeight_eq_half_add_cot hx]

private lemma chordWeight_im {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (chordWeight x).im = Real.cot (Real.pi * x) / 2 := by
  rw [chordWeight_eq_half_add_cot hx]

private lemma antitoneOn_cot_pi :
    AntitoneOn (fun x : ℝ => Real.cot (Real.pi * x)) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  change Real.cot (Real.pi * y) ≤ Real.cot (Real.pi * x)
  by_cases hxy' : x = y
  · simp [hxy']
  have hlt : x < y := lt_of_le_of_ne hxy hxy'
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  rw [div_le_div_iff₀]
  · rw [← sub_nonneg, mul_comm (Real.cos (Real.pi * x)),
        mul_comm (Real.cos (Real.pi * y)),
        mul_comm (Real.sin (Real.pi * x)) (Real.cos (Real.pi * y)), ← Real.sin_sub]
    have harg : Real.pi * y - Real.pi * x ∈ Set.Icc 0 Real.pi := by
      have hpx : 0 < Real.pi * x := mul_pos Real.pi_pos hx.1
      have hpy : Real.pi * y < Real.pi := by
        simpa using mul_lt_mul_of_pos_left hy.2 Real.pi_pos
      have hpxy : Real.pi * x ≤ Real.pi * y :=
        mul_le_mul_of_nonneg_left hxy Real.pi_pos.le
      constructor <;> nlinarith
    exact Real.sin_nonneg_of_mem_Icc harg
  · exact Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hy.1)
      (by simpa using mul_lt_mul_of_pos_left hy.2 Real.pi_pos)
  · exact Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx.1)
      (by simpa using mul_lt_mul_of_pos_left hx.2 Real.pi_pos)

private lemma antitoneOn_chordWeight_im :
    AntitoneOn (fun x : ℝ => (chordWeight x).im) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  change (chordWeight y).im ≤ (chordWeight x).im
  rw [chordWeight_im hx, chordWeight_im hy]
  exact div_le_div_of_nonneg_right (antitoneOn_cot_pi hx hy hxy) (by norm_num)

/-- If two reciprocal chords correspond to ordered frequencies in `(0,1)`,
their distance is the drop of their imaginary parts. -/
private lemma norm_chordWeight_sub_eq {x y : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hxy : x ≤ y) :
    ‖chordWeight y - chordWeight x‖ = (chordWeight x).im - (chordWeight y).im := by
  rw [Complex.norm_def]
  have hre : (chordWeight y - chordWeight x).re = 0 := by
    simp [chordWeight_re hx, chordWeight_re hy]
  have him : (chordWeight y).im ≤ (chordWeight x).im :=
    antitoneOn_chordWeight_im hx hy hxy
  rw [Complex.normSq_apply, hre, zero_mul, zero_add]
  rw [show (chordWeight y - chordWeight x).im * (chordWeight y - chordWeight x).im =
      (chordWeight y - chordWeight x).im ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonpos]
  · simp
  · simpa using sub_nonpos.mpr him

private lemma nearestIntDist_ge {x lam : ℝ} (hlam : 0 < lam)
    (hx : lam ≤ x) (hx' : x ≤ 1 - lam) :
    lam ≤ Erdos587.nearestIntDist x := by
  have hx0 : 0 ≤ x := hlam.le.trans hx
  have hx1 : x < 1 := by linarith
  rw [Erdos587.nearestIntDist, abs_sub_round_eq_min,
    Int.fract_eq_self.mpr ⟨hx0, hx1⟩]
  exact le_min hx (by linarith)

private lemma norm_chordWeight_le {x lam : ℝ} (hlam : 0 < lam)
    (hx : lam ≤ x) (hx' : x ≤ 1 - lam) :
    ‖chordWeight x‖ ≤ 1 / (4 * lam) := by
  have hdist := nearestIntDist_ge hlam hx hx'
  have hfour := Erdos587.four_mul_nearestIntDist_le_norm_fourierChar_sub_one x
  have hchord : 4 * lam ≤ ‖1 - Erdos587.phase x‖ := by
    calc
      4 * lam ≤ 4 * Erdos587.nearestIntDist x := by gcongr
      _ ≤ ‖Erdos587.phase x - 1‖ := hfour
      _ = ‖1 - Erdos587.phase x‖ := by rw [← norm_neg]; congr 1; ring
  have hlam4 : 0 < 4 * lam := mul_pos (by norm_num) hlam
  have hnorm : 0 < ‖1 - Erdos587.phase x‖ := hlam4.trans_le hchord
  rw [chordWeight, norm_inv, one_div]
  exact (inv_le_inv₀ hnorm hlam4).2 hchord

/-- A finite summation-by-parts identity adapted to consecutive differences. -/
private lemma sum_range_eq_boundary_add_variation (z w : ℕ → ℂ)
    (N : ℕ) (hzw : ∀ k < N + 1, z k = (z k - z (k + 1)) * w k) :
    ∑ k ∈ Finset.range (N + 1), z k =
      z 0 * w 0 - z (N + 1) * w N +
        ∑ k ∈ Finset.range N, z (k + 1) * (w (k + 1) - w k) := by
  induction N with
  | zero =>
      simp only [Nat.zero_add, Finset.sum_range_one, Finset.sum_range_zero, add_zero]
      exact (hzw 0 (by omega)).trans (by ring)
  | succ N ih =>
      have ih' := ih (fun k hk => hzw k (by omega))
      rw [Finset.sum_range_succ, ih', Finset.sum_range_succ]
      calc
        (z 0 * w 0 - z (N + 1) * w N +
              ∑ k ∈ Finset.range N, z (k + 1) * (w (k + 1) - w k)) + z (N + 1) =
            (z 0 * w 0 - z (N + 1) * w N +
              ∑ k ∈ Finset.range N, z (k + 1) * (w (k + 1) - w k)) +
              ((z (N + 1) - z (N + 1 + 1)) * w (N + 1)) := by
                exact congrArg _ (hzw (N + 1) (by omega))
        _ = z 0 * w 0 - z (N + 1 + 1) * w (N + 1) +
              (∑ k ∈ Finset.range N, z (k + 1) * (w (k + 1) - w k) +
                z (N + 1) * (w (N + 1) - w N)) := by ring

private lemma phase_difference_mul_chordWeight (g : ℕ → ℝ) (a k : ℕ)
    (hk : g (a + k + 1) - g (a + k) ∈ Set.Ioo (0 : ℝ) 1) :
    Erdos587.phase (g (a + k)) =
      (Erdos587.phase (g (a + k)) - Erdos587.phase (g (a + (k + 1)))) *
        chordWeight (g (a + k + 1) - g (a + k)) := by
  have hphase : Erdos587.phase (g (a + k + 1) - g (a + k)) ≠ 1 :=
    phase_ne_one_of_mem_Ioo hk
  have hnext :
      Erdos587.phase (g (a + (k + 1))) =
        Erdos587.phase (g (a + k)) *
          Erdos587.phase (g (a + k + 1) - g (a + k)) := by
    rw [← Erdos587.phase_add]
    congr 1
    ring
  rw [hnext, chordWeight]
  field_simp [sub_ne_zero.mpr hphase.symm]

/-- Discrete Kusmin--Landau inequality on a translated natural-number range.

The `N` sampled increments are required to be monotone and to lie in
`[λ, 1-λ]`.  The sum itself has `N` terms; asking for the last additional
increment makes the summation-by-parts boundary uniform, including `N = 0`.
-/
theorem norm_sum_phase_add_range_le_inv (g : ℕ → ℝ) (a N : ℕ) (lam : ℝ)
    (hlam : 0 < lam) (_hlamhalf : lam ≤ 1 / 2)
    (hinc : ∀ k < N, lam ≤ g (a + k + 1) - g (a + k) ∧
      g (a + k + 1) - g (a + k) ≤ 1 - lam)
    (hmono : MonotoneOn (fun k : ℕ => g (a + k + 1) - g (a + k)) (Set.Iio N)) :
    ‖∑ k ∈ Finset.range N, Erdos587.phase (g (a + k))‖ ≤ 1 / lam := by
  cases N with
  | zero => simp [hlam.le]
  | succ M =>
      let d : ℕ → ℝ := fun k => g (a + k + 1) - g (a + k)
      let z : ℕ → ℂ := fun k => Erdos587.phase (g (a + k))
      let w : ℕ → ℂ := fun k => chordWeight (d k)
      have hd (k : ℕ) (hk : k < M + 1) : lam ≤ d k ∧ d k ≤ 1 - lam := by
        simpa [d] using hinc k (by omega)
      have hdIoo (k : ℕ) (hk : k < M + 1) : d k ∈ Set.Ioo (0 : ℝ) 1 := by
        have h := hd k hk
        constructor <;> linarith
      have hzw : ∀ k < M + 1, z k = (z k - z (k + 1)) * w k := by
        intro k hk
        simpa [z, w, d] using phase_difference_mul_chordWeight g a k (hdIoo k hk)
      have hab := sum_range_eq_boundary_add_variation z w M hzw
      rw [show M + 1 = Nat.succ M by omega] at hab
      rw [hab]
      calc
        ‖z 0 * w 0 - z (M + 1) * w M +
              ∑ k ∈ Finset.range M, z (k + 1) * (w (k + 1) - w k)‖
            ≤ ‖z 0 * w 0‖ + ‖z (M + 1) * w M‖ +
                ∑ k ∈ Finset.range M, ‖z (k + 1) * (w (k + 1) - w k)‖ := by
              calc
                _ ≤ ‖z 0 * w 0 - z (M + 1) * w M‖ +
                    ‖∑ k ∈ Finset.range M, z (k + 1) * (w (k + 1) - w k)‖ := norm_add_le _ _
                _ ≤ (‖z 0 * w 0‖ + ‖z (M + 1) * w M‖) +
                    ∑ k ∈ Finset.range M, ‖z (k + 1) * (w (k + 1) - w k)‖ := by
                      gcongr
                      · exact norm_sub_le _ _
                      · exact norm_sum_le _ _
                _ = _ := by ring
        _ = ‖w 0‖ + ‖w M‖ +
              ∑ k ∈ Finset.range M, ((w k).im - (w (k + 1)).im) := by
            congr 1
            · simp [z, Erdos587.norm_phase]
            · apply Finset.sum_congr rfl
              intro k hk
              have hkM : k < M := Finset.mem_range.mp hk
              have hdk := hdIoo k (by omega)
              have hdks := hdIoo (k + 1) (by omega)
              have hle : d k ≤ d (k + 1) :=
                hmono (by simpa using (show k < M + 1 by omega))
                  (by simpa using (show k + 1 < M + 1 by omega)) (by omega)
              simp only [norm_mul, z, w, Erdos587.norm_phase, one_mul]
              exact norm_chordWeight_sub_eq hdk hdks hle
        _ = ‖w 0‖ + ‖w M‖ + ((w 0).im - (w M).im) := by
            rw [Finset.sum_range_sub']
        _ ≤ 2 * (‖w 0‖ + ‖w M‖) := by
            have h0 := Complex.abs_im_le_norm (w 0)
            have hM := Complex.abs_im_le_norm (w M)
            rw [abs_le] at h0 hM
            linarith
        _ ≤ 2 * (1 / (4 * lam) + 1 / (4 * lam)) := by
            gcongr
            · exact norm_chordWeight_le hlam (hd 0 (by omega)).1 (hd 0 (by omega)).2
            · exact norm_chordWeight_le hlam (hd M (by omega)).1 (hd M (by omega)).2
        _ = 1 / lam := by
            field_simp [hlam.ne']
            norm_num

/-- The reflected form of the discrete Kusmin--Landau inequality.  It is
useful when the consecutive increments are antitone and lie in
`[-1+lam,-lam]`. -/
theorem norm_sum_phase_add_range_le_inv_of_antitone (g : ℕ → ℝ) (a N : ℕ)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2)
    (hinc : ∀ k < N, -1 + lam ≤ g (a + k + 1) - g (a + k) ∧
      g (a + k + 1) - g (a + k) ≤ -lam)
    (hanti : AntitoneOn (fun k : ℕ => g (a + k + 1) - g (a + k)) (Set.Iio N)) :
    ‖∑ k ∈ Finset.range N, Erdos587.phase (g (a + k))‖ ≤ 1 / lam := by
  have hpos := norm_sum_phase_add_range_le_inv (fun n => -g n) a N lam hlam hlamhalf
    (fun k hk => by
      have h := hinc k hk
      constructor <;> linarith)
    (by
      intro i hi j hj hij
      have h := hanti hi hj hij
      dsimp at h ⊢
      linarith)
  simp only [Erdos587.phase_neg] at hpos
  rw [← map_sum] at hpos
  change ‖(starRingEnd ℂ) (∑ k ∈ Finset.range N, Erdos587.phase (g (a + k)))‖ ≤ 1 / lam at hpos
  rw [Complex.norm_conj] at hpos
  exact hpos

/-- Kusmin--Landau for positive, antitone increments.  Reversing the sampled
sequence turns these into negative, antitone increments; the one extra endpoint
increment is chosen as a repeat of the first original increment. -/
theorem norm_sum_phase_add_range_le_inv_of_antitone_pos (g : ℕ → ℝ) (a N : ℕ)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2)
    (hinc : ∀ k < N, lam ≤ g (a + k + 1) - g (a + k) ∧
      g (a + k + 1) - g (a + k) ≤ 1 - lam)
    (hanti : AntitoneOn (fun k : ℕ => g (a + k + 1) - g (a + k)) (Set.Iio N)) :
    ‖∑ k ∈ Finset.range N, Erdos587.phase (g (a + k))‖ ≤ 1 / lam := by
  cases N with
  | zero => simp [hlam.le]
  | succ M =>
      let r : ℕ → ℝ := fun k =>
        if k < M + 1 then g (a + (M - k))
        else g a - (g (a + 1) - g a)
      have hrinc (k : ℕ) (hk : k < M + 1) :
          r (k + 1) - r k =
            -(g (a + (M - (k + 1)) + 1) - g (a + (M - (k + 1)))) := by
        by_cases hkM : k < M
        · have hks : k + 1 < M + 1 := by omega
          simp only [r, if_pos hk, if_pos hks]
          rw [show M - k = M - (k + 1) + 1 by omega]
          ring
        · have hkEq : k = M := by omega
          subst k
          simp only [r, if_pos (by omega : M < M + 1), if_neg (by omega : ¬ M + 1 < M + 1)]
          simp
      have hrbound (k : ℕ) (hk : k < M + 1) :
          -1 + lam ≤ r (k + 1) - r k ∧ r (k + 1) - r k ≤ -lam := by
        rw [hrinc k hk]
        have h := hinc (M - (k + 1)) (by omega)
        constructor <;> linarith
      have hranti : AntitoneOn (fun k : ℕ => r (k + 1) - r k) (Set.Iio (M + 1)) := by
        intro i hi j hj hij
        change r (j + 1) - r j ≤ r (i + 1) - r i
        rw [hrinc i (by simpa using hi), hrinc j (by simpa using hj)]
        have hrev : M - (j + 1) ≤ M - (i + 1) := by omega
        have hold := hanti (show M - (j + 1) < M + 1 by omega)
          (show M - (i + 1) < M + 1 by omega) hrev
        linarith
      have hrev := norm_sum_phase_add_range_le_inv_of_antitone r 0 (M + 1)
        lam hlam hlamhalf (by simpa only [Nat.zero_add] using hrbound)
          (by simpa only [Nat.zero_add] using hranti)
      have hsum :
          (∑ k ∈ Finset.range (M + 1), Erdos587.phase (r (0 + k))) =
            ∑ k ∈ Finset.range (M + 1), Erdos587.phase (g (a + k)) := by
        calc
          (∑ k ∈ Finset.range (M + 1), Erdos587.phase (r (0 + k))) =
              ∑ k ∈ Finset.range (M + 1), Erdos587.phase (g (a + (M - k))) := by
                apply Finset.sum_congr rfl
                intro k hk
                simp only [Nat.zero_add, r, if_pos (Finset.mem_range.mp hk)]
          _ = ∑ k ∈ Finset.range (M + 1), Erdos587.phase (g (a + k)) := by
                simpa only [show M + 1 - 1 = M by omega] using
                  Finset.sum_range_reflect (fun k => Erdos587.phase (g (a + k))) (M + 1)
      rwa [hsum] at hrev

/-- Kusmin--Landau for negative, monotone increments.  Negating the phase
reduces this to `norm_sum_phase_add_range_le_inv_of_antitone_pos`. -/
theorem norm_sum_phase_add_range_le_inv_of_monotone_neg (g : ℕ → ℝ) (a N : ℕ)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2)
    (hinc : ∀ k < N, -1 + lam ≤ g (a + k + 1) - g (a + k) ∧
      g (a + k + 1) - g (a + k) ≤ -lam)
    (hmono : MonotoneOn (fun k : ℕ => g (a + k + 1) - g (a + k)) (Set.Iio N)) :
    ‖∑ k ∈ Finset.range N, Erdos587.phase (g (a + k))‖ ≤ 1 / lam := by
  have hpos := norm_sum_phase_add_range_le_inv_of_antitone_pos (fun n => -g n) a N
    lam hlam hlamhalf
    (fun k hk => by
      have h := hinc k hk
      constructor <;> linarith)
    (by
      intro i hi j hj hij
      have h := hmono hi hj hij
      dsimp at h ⊢
      linarith)
  simp only [Erdos587.phase_neg] at hpos
  rw [← map_sum] at hpos
  change ‖(starRingEnd ℂ) (∑ k ∈ Finset.range N, Erdos587.phase (g (a + k)))‖ ≤ 1 / lam at hpos
  rw [Complex.norm_conj] at hpos
  exact hpos

end Erdos1149

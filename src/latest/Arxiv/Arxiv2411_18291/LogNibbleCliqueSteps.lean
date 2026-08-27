import Arxiv.Arxiv2411_18291.LogNibbleIncrements
import Arxiv.Arxiv2411_18291.NibbleCliqueIncrements

/-! # Finite clique-count comparison steps for logarithmic tracking -/

noncomputable section

namespace Arxiv2411_18291

def logNibbleCliqueUpper (k : ℕ) (a g D p : ℝ) : ℝ :=
  nibbleCliqueMain k g D p + logNibbleCliqueError k a g D p

def logNibbleCliqueLower (k : ℕ) (a g D p : ℝ) : ℝ :=
  nibbleCliqueMain k g D p - logNibbleCliqueError k a g D p

theorem nibbleCliqueMain_increment_bounds {k : ℕ} (hk : 0 < k) {g D s p : ℝ}
    (hg : 0 < g) (hD : 0 ≤ D) (hs : 0 ≤ s) (hsp : s ≤ p)
    (hstep : p - s = (k : ℝ) / g) :
    -nibbleCliqueSlope k D p ≤ nibbleCliqueMain k g D s - nibbleCliqueMain k g D p ∧
      nibbleCliqueMain k g D s - nibbleCliqueMain k g D p ≤
        -nibbleCliqueSlope k D p + nibbleCliqueTaylor k g D p ∧
      nibbleCliqueMain k g D s - nibbleCliqueMain k g D p ≤ 0 := by
  have hC : 0 ≤ D * g / (k : ℝ) := by positivity
  have h := scaled_power_increment_bounds hs hsp hC k
  obtain ⟨hL, hT, _, _⟩ := nibbleClique_step_terms hk (a := 0) (D := D) hg.ne' hstep
  rw [hL, hT] at h
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hsp k) hC
  unfold nibbleCliqueMain
  ring_nf at h hm ⊢
  exact ⟨h.1, h.2, by linarith only [hm]⟩

theorem logNibbleCliqueError_step_bounds {k : ℕ} (hk : 0 < k) {a g D s p : ℝ}
    (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 ≤ D) (hs : 0 < s) (hsp : s ≤ p)
    (hp1 : p ≤ 1) (has : a ≤ s) (hstep : p - s = (k : ℝ) / g) :
    8 * nibbleLogFactor k p * (k : ℝ) ^ 2 * a ^ 3 * D / p ≤
        logNibbleCliqueError k a g D s - logNibbleCliqueError k a g D p ∧
      logNibbleCliqueError k a g D s - logNibbleCliqueError k a g D p ≤
        8 * (k : ℝ) ^ 3 * D := by
  obtain ⟨hlo, hhi⟩ := logNibbleCliqueError_increment_bounds k hs hsp hp1 ha hD hg.le
  rw [hstep] at hlo hhi
  have hLs := nibbleLogFactor_one_le k hs (hsp.trans hp1)
  have hLsp := nibbleLogFactor_mul_le_rank hk hs
  have hfactor : nibbleLogFactor k s * a ^ 3 / s ≤ k := by
    calc
      _ ≤ nibbleLogFactor k s * s ^ 3 / s :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ ha has 3) (by linarith only [hLs])) hs.le
      _ = (nibbleLogFactor k s * s) * s := by field_simp
      _ ≤ (k : ℝ) * s := mul_le_mul_of_nonneg_right hLsp hs.le
      _ ≤ k := by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hsp.trans hp1) (Nat.cast_nonneg k (α := ℝ))
  have hupper : 8 * nibbleLogFactor k s * k * a ^ 3 * D * g * ((k : ℝ) / g) / s ≤
      8 * (k : ℝ) ^ 3 * D := by
    have hh := mul_le_mul_of_nonneg_left hfactor
      (show 0 ≤ 8 * (k : ℝ) ^ 2 * D by positivity)
    convert! hh using 1 <;> field_simp
  refine ⟨?_, hhi.trans hupper⟩
  convert! hlo using 1
  field_simp

theorem logNibbleCliqueTaylor_le_error {k : ℕ} (hk : 2 ≤ k) {a g D p : ℝ}
    (hg : 0 < g) (hD : 0 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1)
    (hsteps : (k : ℝ) ≤ a ^ 3 * g) :
    nibbleCliqueTaylor k g D p ≤
      8 * nibbleLogFactor k p * (k : ℝ) ^ 2 * a ^ 3 * D / p := by
  have hL := nibbleLogFactor_one_le k hp hp1
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have ha3g : 0 ≤ a ^ 3 * g := hkR.trans hsteps
  have ha3 : 0 ≤ a ^ 3 := (mul_nonneg_iff_of_pos_right hg).mp ha3g
  have hκ : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hpow : p ^ (k - 1) ≤ 1 := pow_le_one₀ hp.le hp1
  have hnum : ((k - 1 : ℕ) : ℝ) * p ^ (k - 1) ≤ a ^ 3 * g := by
    apply le_trans _ (hκ.trans hsteps)
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (k - 1) (α := ℝ))
  have hpow' : p ^ (k - 2) * p = p ^ (k - 1) := by
    rw [← pow_succ, show k - 2 + 1 = k - 1 by omega]
  calc
    _ = (D * (k : ℝ) ^ 2 / (p * g)) * (((k - 1 : ℕ) : ℝ) * p ^ (k - 1)) := by
      unfold nibbleCliqueTaylor
      rw [← hpow']
      field_simp
    _ ≤ (D * (k : ℝ) ^ 2 / (p * g)) * (a ^ 3 * g) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = (k : ℝ) ^ 2 * a ^ 3 * D / p := by field_simp
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right (show 1 ≤ 8 * nibbleLogFactor k p by linarith)
        (show 0 ≤ (k : ℝ) ^ 2 * a ^ 3 * D / p by positivity)
      simpa only [one_mul, mul_div_assoc, mul_assoc] using hh

theorem logNibbleClique_comparison_step_control {k : ℕ} (hk : 3 ≤ k) {a g D s p : ℝ}
    (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 ≤ D) (hs : 0 < s) (hsp : s ≤ p)
    (hp1 : p ≤ 1) (has : a ≤ s) (hstep : p - s = (k : ℝ) / g)
    (hsteps : (k : ℝ) ≤ a ^ 3 * g) :
    let δu := logNibbleCliqueUpper k a g D s - logNibbleCliqueUpper k a g D p
    let δl := logNibbleCliqueLower k a g D s - logNibbleCliqueLower k a g D p;
    -nibbleCliqueSlope k D p ≤ δu ∧ δl ≤ -nibbleCliqueSlope k D p ∧
      |δu| ≤ 9 * (k : ℝ) ^ 3 * D ∧ |δl| ≤ 9 * (k : ℝ) ^ 3 * D := by
  have hk0 : 0 < k := by omega
  have hp := hs.trans_le hsp
  obtain ⟨hmlo, hmhi, hm0⟩ := nibbleCliqueMain_increment_bounds hk0 hg hD hs.le hsp hstep
  obtain ⟨helo, hehi⟩ := logNibbleCliqueError_step_bounds hk0 ha hg hD hs hsp hp1 has hstep
  have hT := logNibbleCliqueTaylor_le_error (by omega : 2 ≤ k) hg hD hp hp1 hsteps
  have hL := nibbleLogFactor_one_le k hp hp1
  have he0 : 0 ≤ 8 * nibbleLogFactor k p * (k : ℝ) ^ 2 * a ^ 3 * D / p := by positivity
  have hM0 : 0 ≤ nibbleCliqueSlope k D p := by unfold nibbleCliqueSlope; positivity
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hM : nibbleCliqueSlope k D p ≤ (k : ℝ) ^ 3 * D := by
    have hpow : p ^ (k - 1) ≤ 1 := pow_le_one₀ hp.le hp1
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (k : ℝ) * D by positivity)
    have hk3 : (k : ℝ) ≤ (k : ℝ) ^ 3 := by
      have hsq : 1 ≤ (k : ℝ) ^ 2 := by nlinarith only [hkR]
      have hh := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg k (α := ℝ))
      nlinarith only [hh]
    have hh' := mul_le_mul_of_nonneg_right hk3 hD
    unfold nibbleCliqueSlope
    nlinarith only [hh, hh']
  have hB : 0 ≤ (k : ℝ) ^ 3 * D := by positivity
  dsimp only [logNibbleCliqueUpper, logNibbleCliqueLower]
  refine ⟨?_, ?_, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    nlinarith only [hmlo, hmhi, hm0, helo, hehi, hT, he0, hM0, hM, hB]

end Arxiv2411_18291

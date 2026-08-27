import Arxiv.Arxiv2411_18291.LogNibbleScaleBounds

/-! # Clique-count overlap and variance margins for logarithmic tracking -/

namespace Arxiv2411_18291

theorem logNibbleCliqueError_ge_twice_width (k : ℕ) {a g D p : ℝ}
    (ha : 0 ≤ a) (hg : 0 ≤ g) (hD : 0 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1) :
    2 * (a ^ 3 * D * g) ≤ logNibbleCliqueError k a g D p := by
  have hL := nibbleLogFactor_one_le k hp hp1
  have hcoeff : 2 ≤ 4 * (nibbleLogFactor k p) ^ 2 := by nlinarith only [hL]
  have hh := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ a ^ 3 * D * g by positivity)
  unfold logNibbleCliqueError
  nlinarith only [hh]

theorem log_nibble_count_variance_bound {k : ℕ} (hk : 3 ≤ k) {a p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : a ≤ ((2 / 5 : ℝ) * p) ^ k) :
    9 * a ≤ (k : ℝ) * p ^ (k - 2) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hgeom : (2 / 5 : ℝ) ^ k ≤ (2 / 5 : ℝ) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have hc : 9 * (2 / 5 : ℝ) ^ k ≤ k := by norm_num at hgeom; linarith only [hgeom, hkR]
  have hpow : p ^ k = p ^ 2 * p ^ (k - 2) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : 2 ≤ k)]
  have hp2 : p ^ 2 ≤ 1 := pow_le_one₀ hp hp1
  have hp2' := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 9 * (2 / 5 : ℝ) ^ k by positivity)
  calc
    _ ≤ 9 * (((2 / 5 : ℝ) * p) ^ k) := mul_le_mul_of_nonneg_left ha (by norm_num)
    _ = (9 * (2 / 5 : ℝ) ^ k * p ^ 2) * p ^ (k - 2) := by
      rw [mul_pow, hpow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith only [hp2', hc]) (pow_nonneg hp _)

theorem log_nibble_count_overlap_margin (k : ℕ) {a g D p L : ℝ}
    (ha : 0 ≤ a) (hg : 0 ≤ g) (hD : 0 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1)
    (hL : L ≤ a ^ 3 * D) :
    (p * g) * L ≤ logNibbleCliqueError k a g D p - a ^ 3 * D * g := by
  have hv := logNibbleCliqueError_ge_twice_width k ha hg hD hp hp1
  have hw : 0 ≤ a ^ 3 * D * g := by positivity
  have hEL : (p * g) * L ≤ a ^ 3 * D * g := by
    calc
      _ ≤ (p * g) * (a ^ 3 * D) :=
        mul_le_mul_of_nonneg_left hL (mul_nonneg hp.le hg)
      _ = p * (a ^ 3 * D * g) := by ring
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 hw
  linarith only [hv, hEL]

theorem log_nibble_count_variance_margin {k : ℕ} (hk : 3 ≤ k) {a g D p : ℝ}
    (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    (hac : a ≤ ((2 / 5 : ℝ) * p) ^ k) :
    2 * (p * g) ^ 2 * logNibbleDegreeError k a D p ^ 2 ≤
      (k : ℝ) ^ 2 * (logNibbleCliqueError k a g D p - a ^ 3 * D * g) *
        nibbleCliqueMain k g D p := by
  have hk0 : 0 < k := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hvar := log_nibble_count_variance_bound hk hp.le hp1 hac
  let F := 4 * (nibbleLogFactor k p) ^ 2 * a ^ 3 * D ^ 2 * g ^ 2 * p ^ 2
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hmul := mul_le_mul_of_nonneg_left hvar hF
  have hpow : p ^ k = p ^ (k - 2) * p ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ k)]
  have hleft : 4 * (p * g) ^ 2 * logNibbleDegreeError k a D p ^ 2 = F * (9 * a) := by
    unfold logNibbleDegreeError
    dsimp only [F]
    ring
  have hright : (k : ℝ) ^ 2 * logNibbleCliqueError k a g D p *
      nibbleCliqueMain k g D p = F * ((k : ℝ) * p ^ (k - 2)) := by
    unfold logNibbleCliqueError nibbleCliqueMain
    rw [hpow]
    dsimp only [F]
    field_simp
  have hfour : 4 * (p * g) ^ 2 * logNibbleDegreeError k a D p ^ 2 ≤
      (k : ℝ) ^ 2 * logNibbleCliqueError k a g D p * nibbleCliqueMain k g D p := by
    rw [hleft, hright]
    exact hmul
  have hv := logNibbleCliqueError_ge_twice_width k ha hg.le hD.le hp hp1
  have hvprod := mul_le_mul_of_nonneg_right hv
    (mul_nonneg (sq_nonneg (k : ℝ)) (nibbleCliqueMain_pos hk0 hg hD hp).le)
  nlinarith only [hfour, hvprod]

end Arxiv2411_18291

import Arxiv.Arxiv2411_18291.LogNibbleScalars
import Arxiv.Arxiv2411_18291.FaceCriticalDrift

/-! # Relative degree, count, and face errors of the logarithmic comparisons -/

namespace Arxiv2411_18291

namespace LogNibbleScalarConditions

theorem degree_bounds {k : ℕ} {a D p : ℝ} (P : LogNibbleScalarConditions k a p)
    (hD : 0 ≤ D) :
    logNibbleDegreeError k a D p ≤ nibbleDegreeMain k D p / 8 ∧
      (logNibbleDegreeError k a D p) ^ 2 ≤ a ^ 2 * D * nibbleDegreeMain k D p / 8 := by
  have h₁ := mul_le_mul_of_nonneg_right P.degree hD
  have h₂ := mul_le_mul_of_nonneg_right P.degree_sq
    (show 0 ≤ a ^ 2 * D ^ 2 by positivity)
  unfold logNibbleDegreeError nibbleDegreeMain
  constructor <;> nlinarith only [h₁, h₂]

theorem count_bounds {k : ℕ} (hk : 0 < k) {a g D p : ℝ}
    (P : LogNibbleScalarConditions k a p) (hD : 0 ≤ D) (hg : 0 ≤ g) (hp : 0 ≤ p) :
    logNibbleCliqueError k a g D p ≤ nibbleCliqueMain k g D p / 64 ∧
      logNibbleCliqueError k a g D p * nibbleDegreeMain k D p ≤
        5 / 2 * (a ^ 2 * D) * nibbleCliqueMain k g D p := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h₁ := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right P.count (mul_nonneg hD hg)) hkR.le
  have h₂ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right P.coupling
    (show 0 ≤ a ^ 2 * D ^ 2 * g * p ^ (k - 1) by positivity)) hkR.le
  have hpow : p ^ (k - 1) * p = p ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  constructor
  · unfold logNibbleCliqueError nibbleCliqueMain
    convert! h₁ using 1 <;> field_simp
  · unfold logNibbleCliqueError nibbleDegreeMain nibbleCliqueMain
    convert! h₂ using 1
    · field_simp
    · rw [← hpow]
      ring

theorem face_bounds {k : ℕ} (hk : 0 < k) {a g D p : ℝ}
    (P : LogNibbleScalarConditions k a p) (ha : 0 ≤ a) (hD : 0 ≤ D) (hg : 0 ≤ g) :
    logNibbleDegreeError k a D p ≤ 3 / 4 * a * nibbleDegreeMain k D p ∧
      logNibbleCliqueError k a g D p ≤ a * nibbleCliqueMain k g D p / 4 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h₁ := mul_le_mul_of_nonneg_right P.face_degree (mul_nonneg ha hD)
  have h₂ := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right P.face_count (show 0 ≤ a * D * g by positivity)) hkR.le
  constructor
  · unfold logNibbleDegreeError nibbleDegreeMain
    nlinarith only [h₁]
  · unfold logNibbleCliqueError nibbleCliqueMain
    convert! h₂ using 1 <;> field_simp

end LogNibbleScalarConditions

theorem log_nibble_face_loss_lower {k : ℕ} (hk : 0 < k) {a g D p h n y d : ℝ}
    (P : LogNibbleScalarConditions k a p) (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 < D)
    (hp : 0 < p) (hp1 : p ≤ 1) (hh : 0 < h) (hn : 0 ≤ n)
    (hy : 0 ≤ y) (hyn : y ≤ n) (hdn : d ≤ n) (hcritical : y + a * n ≤ d)
    (hcount : |h - nibbleCliqueMain k g D p| ≤ logNibbleCliqueError k a g D p) :
    (nibbleDegreeMain k D p / nibbleCliqueMain k g D p) * y ≤
      d * (nibbleDegreeMain k D p - logNibbleDegreeError k a D p) / h := by
  have hL := nibbleLogFactor_one_le k hp hp1
  have hu : 0 ≤ logNibbleDegreeError k a D p := by
    unfold logNibbleDegreeError
    positivity
  obtain ⟨he, hc⟩ := P.face_bounds hk ha hD.le hg.le
  apply face_loss_lower_of_relative_errors (b := 3) (a := a / 4)
    (nibbleDegreeMain_pos hD hp).le hu hh (nibbleCliqueMain_pos hk hg hD hp)
    (by positivity) hn hy hyn hdn
  · nlinarith only [hcritical]
  · nlinarith only [he]
  · have hhhi := (abs_le.mp hcount).2
    nlinarith only [hhhi, hc]

end Arxiv2411_18291

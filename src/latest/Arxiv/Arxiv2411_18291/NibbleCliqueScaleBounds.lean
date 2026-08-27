import Arxiv.Arxiv2411_18291.NibbleDegreeScaleBounds

/-! # Clique-count error bounds and positivity of the lower comparison -/

namespace Arxiv2411_18291

theorem nibbleCliqueError_nonneg (k : ℕ) {a g D p : ℝ}
    (ha : 0 ≤ a) (hg : 0 ≤ g) (hD : 0 ≤ D) :
    0 ≤ nibbleCliqueError k a g D p := by
  unfold nibbleCliqueError
  positivity

theorem nibbleCliqueError_degree_product {k : ℕ} (hk : 0 < k) (a g D : ℝ)
    {p : ℝ} (hp : p ≠ 0) :
    nibbleCliqueError k a g D p * nibbleDegreeMain k D p =
      (16 * (k : ℝ) ^ 3 * a / p ^ 2) *
        (nibbleEdgeScale a D p * nibbleCliqueMain k g D p) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [nibble_main_relation hk]
  unfold nibbleCliqueError nibbleEdgeScale
  field_simp

theorem nibbleCliqueError_degree_le {k : ℕ} (hk : 0 < k) {a g D p : ℝ}
    (hg : 0 < g) (hD : 0 < D) (hp : 0 < p)
    (hden : 16 * (k : ℝ) ^ 3 * a ≤ p ^ 2) :
    nibbleCliqueError k a g D p * nibbleDegreeMain k D p ≤
      nibbleEdgeScale a D p * nibbleCliqueMain k g D p := by
  rw [nibbleCliqueError_degree_product hk a g D hp.ne']
  have hratio : 16 * (k : ℝ) ^ 3 * a / p ^ 2 ≤ 1 :=
    (div_le_iff₀ (pow_pos hp 2)).mpr (by simpa only [one_mul] using hden)
  have hnonneg := mul_nonneg (nibbleEdgeScale_nonneg (a := a) hD.le hp.le)
    (nibbleCliqueMain_pos hk hg hD hp).le
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio hnonneg

theorem nibbleCliqueError_le_scaled_main {k : ℕ} (hk : 0 < k) {a g D p : ℝ}
    (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 < D) (hp : 0 < p) (hap : a ≤ p ^ k)
    (hden : 16 * (k : ℝ) ^ 3 * a ≤ p ^ 2) :
    nibbleCliqueError k a g D p ≤ a * nibbleCliqueMain k g D p := by
  have hprod := nibbleCliqueError_degree_le hk hg hD hp hden
  have ht := mul_le_mul_of_nonneg_right (nibbleEdgeScale_le_scaled_main hk ha hD hp hap)
    (nibbleCliqueMain_pos hk hg hD hp).le
  apply le_of_mul_le_mul_right _ (nibbleDegreeMain_pos (k := k) hD hp)
  calc
    _ ≤ _ := hprod.trans ht
    _ = _ := by ring

theorem nibbleCliqueError_le_half_main {k : ℕ} (hk : 0 < k) {a g D p : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hg : 0 < g) (hD : 0 < D) (hp : 0 < p)
    (hap : a ≤ p ^ k) (hden : 16 * (k : ℝ) ^ 3 * a ≤ p ^ 2) :
    nibbleCliqueError k a g D p ≤ nibbleCliqueMain k g D p / 2 := by
  calc
    _ ≤ a * nibbleCliqueMain k g D p := nibbleCliqueError_le_scaled_main hk ha hg hD hp hap hden
    _ ≤ (1 / 2) * nibbleCliqueMain k g D p :=
      mul_le_mul_of_nonneg_right ha2 (nibbleCliqueMain_pos hk hg hD hp).le
    _ = _ := by ring

theorem nibbleCliqueLower_pos {k : ℕ} (hk : 0 < k) {a g D p : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hg : 0 < g) (hD : 0 < D) (hp : 0 < p)
    (hap : a ≤ p ^ k) (hden : 16 * (k : ℝ) ^ 3 * a ≤ p ^ 2) :
    0 < nibbleCliqueLower k a g D p := by
  have hh := nibbleCliqueMain_pos hk hg hD hp
  have he := nibbleCliqueError_le_half_main hk ha ha2 hg hD hp hap hden
  unfold nibbleCliqueLower
  linarith only [hh, he]

end Arxiv2411_18291

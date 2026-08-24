import ErdosProblems.Erdos587.CompactWeights

/-! Uniform separation of the critical root plateau from its support boundary. -/

open scoped SchwartzMap

namespace Erdos587

lemma sqrt_gap_of_square_gap {a b L δ : ℝ} (hL : 0 < L)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L ^ 2)
    (hgap : 2 * δ * L ^ 2 ≤ b - a) :
    Real.sqrt a + δ * L ≤ Real.sqrt b := by
  have hb0 := ha.trans hab
  have hsa : Real.sqrt a ≤ L := Real.sqrt_le_iff.mpr ⟨hL.le, hab.trans hb⟩
  have hsb : Real.sqrt b ≤ L := Real.sqrt_le_iff.mpr ⟨hL.le, hb⟩
  have hsab := Real.sqrt_le_sqrt hab
  have hsq : (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a) = b - a := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb0]
  have hh : (δ * L) * (2 * L) ≤ (Real.sqrt b - Real.sqrt a) * (2 * L) := by
    calc
      _ = 2 * δ * L ^ 2 := by ring
      _ ≤ b - a := hgap
      _ = (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a) := hsq.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hsab)
  have hcancel := (mul_le_mul_iff_left₀ (by positivity : 0 < 2 * L)).mp hh
  linarith

lemma critical_root_plateau_gaps {t U V L C : ℝ}
    (ht : 0 ≤ t) (hU : 0 ≤ U) (hV : 0 ≤ V) (hL : 0 < L) (hC : 0 < C)
    (hUV : U ≤ V) (hupper : t + U + V ≤ L ^ 2) (hspan : L ^ 2 ≤ C * (U + V)) :
    Real.sqrt (t + U / 4) + L / (128 * C) ≤ Real.sqrt (t + V / 8 + 5 * U / 32) ∧
    Real.sqrt (t + V / 2 + 7 * U / 32) + L / (128 * C) ≤ Real.sqrt (t + V) := by
  have hsize : L ^ 2 ≤ 2 * C * V := by
    nlinarith [mul_le_mul_of_nonneg_left hUV hC.le]
  have hgap₁ : L ^ 2 ≤ (64 * C) * ((t + V / 8 + 5 * U / 32) - (t + U / 4)) := by
    have hh : V / 32 ≤ (t + V / 8 + 5 * U / 32) - (t + U / 4) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 64 * C by positivity)]
  have hgap₂ : L ^ 2 ≤ (64 * C) * ((t + V) - (t + V / 2 + 7 * U / 32)) := by
    have hh : V / 32 ≤ (t + V) - (t + V / 2 + 7 * U / 32) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 64 * C by positivity)]
  have hscale (a b : ℝ) (hgap : L ^ 2 ≤ (64 * C) * (b - a)) :
      2 * (1 / (128 * C)) * L ^ 2 ≤ b - a := by
    have hh := (div_le_iff₀ (show 0 < 64 * C by positivity)).mpr
      (show L ^ 2 ≤ (b - a) * (64 * C) by nlinarith)
    calc
      _ = L ^ 2 / (64 * C) := by ring
      _ ≤ b - a := hh
  constructor
  · have hh := sqrt_gap_of_square_gap hL (by positivity : 0 ≤ t + U / 4)
      (show t + U / 4 ≤ t + V / 8 + 5 * U / 32 by linarith)
      (show t + V / 8 + 5 * U / 32 ≤ L ^ 2 by linarith)
      (hscale _ _ hgap₁)
    convert hh using 1 <;> ring
  · have hh := sqrt_gap_of_square_gap hL (by positivity : 0 ≤ t + V / 2 + 7 * U / 32)
      (show t + V / 2 + 7 * U / 32 ≤ t + V by linarith)
      (show t + V ≤ L ^ 2 by linarith) (hscale _ _ hgap₂)
    convert hh using 1 <;> ring

theorem exists_finite_critical_root_weights {C : ℝ} (hC : 0 < C) :
    ∃ F : Finset 𝓢(ℝ, ℂ),
      (∀ f ∈ F, (∀ x : ℝ, (f x).im = 0) ∧ (∀ x : ℝ, 0 ≤ (f x).re) ∧
        (∀ x : ℝ, (f x).re ≤ 1)) ∧
      ∀ t U V L : ℝ, 0 ≤ t → 0 ≤ U → 0 ≤ V → 0 < L → U ≤ V →
        t + U + V ≤ L ^ 2 → L ^ 2 ≤ C * (U + V) →
        ∃ f ∈ F,
          (∀ z : ℝ, f (L⁻¹ * z) ≠ 0 →
            0 < z ∧ t + U / 4 ≤ z ^ 2 ∧ z ^ 2 ≤ t + V) ∧
          (∀ z : ℝ, 0 ≤ z → t + V / 8 + 5 * U / 32 ≤ z ^ 2 →
            z ^ 2 ≤ t + V / 2 + 7 * U / 32 → f (L⁻¹ * z) = 1) := by
  let η : ℝ := 1 / (512 * C)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨F, hF, hcover⟩ := exists_finite_interval_weights hη
  refine ⟨F, hF, ?_⟩
  intro t U V L ht hU hV hL hUV hupper hspan
  let a := Real.sqrt (t + V / 8 + 5 * U / 32) / L
  let b := Real.sqrt (t + V / 2 + 7 * U / 32) / L
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hL.le
  have hab : a ≤ b := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hL.le
  have hb1 : b ≤ 1 := (div_le_one hL).mpr (Real.sqrt_le_iff.mpr ⟨hL.le, by linarith⟩)
  obtain ⟨f, hfF, hfpl, hfsupp⟩ := hcover a b ha0 hab hb1
  obtain ⟨hgap₁, hgap₂⟩ := critical_root_plateau_gaps ht hU hV hL hC hUV hupper hspan
  have hηgap : 3 * η * L < L / (128 * C) := by
    dsimp [η]
    apply (lt_div_iff₀ (show 0 < 128 * C by positivity)).mpr
    field_simp
    nlinarith
  have hmul (z : ℝ) : (L⁻¹ * z) * L = z := by field_simp
  have haL : a * L = Real.sqrt (t + V / 8 + 5 * U / 32) := by dsimp [a]; field_simp
  have hbL : b * L = Real.sqrt (t + V / 2 + 7 * U / 32) := by dsimp [b]; field_simp
  refine ⟨f, hfF, ?_, ?_⟩
  · intro z hz
    obtain ⟨hzlo, hzhi⟩ := hfsupp (L⁻¹ * z) hz
    have hlo := mul_lt_mul_of_pos_right hzlo hL
    have hhi := mul_lt_mul_of_pos_right hzhi hL
    rw [sub_mul, haL, hmul] at hlo
    rw [add_mul, hbL, hmul] at hhi
    have hrootlo : Real.sqrt (t + U / 4) < z := by linarith
    have hroothi : z < Real.sqrt (t + V) := by linarith
    have hzpos : 0 < z := (Real.sqrt_nonneg _).trans_lt hrootlo
    refine ⟨hzpos, ?_, ?_⟩
    · have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrootlo.le 2
      rwa [Real.sq_sqrt (by positivity)] at hh
    · have hh := pow_le_pow_left₀ hzpos.le hroothi.le 2
      rwa [Real.sq_sqrt (by positivity)] at hh
  · intro z hz0 hzlo hzhi
    apply hfpl
    have hlo : Real.sqrt (t + V / 8 + 5 * U / 32) ≤ z :=
      Real.sqrt_le_iff.mpr ⟨hz0, hzlo⟩
    have hhi : z ≤ Real.sqrt (t + V / 2 + 7 * U / 32) := by
      have hh := Real.sqrt_le_sqrt hzhi
      rwa [Real.sqrt_sq hz0] at hh
    constructor
    · change Real.sqrt (t + V / 8 + 5 * U / 32) / L ≤ L⁻¹ * z
      rw [div_le_iff₀ hL, hmul]
      exact hlo
    · change L⁻¹ * z ≤ Real.sqrt (t + V / 2 + 7 * U / 32) / L
      rw [le_div_iff₀ hL, hmul]
      exact hhi

end Erdos587

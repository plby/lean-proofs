import ErdosProblems.Erdos587.HooleyInnerBox

/-! # The inner lattice radii retain coordinate mass up to a fixed factor -/

namespace Erdos587.GeneralizedAP

lemma delta_ceil_mass_le_mul_inner_radius {b δ : ℝ} {s : ℕ} (hs : 0 < s) (hδ : 0 < δ)
    (hb : 2 * (s : ℝ) ≤ b) (hδb : δ ≤ 8 * b) :
    ⌈8 * b / δ⌉₊ ≤ ⌈32 * (s : ℝ) / δ⌉₊ * ⌊b / s⌋₊ := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hb0 : 0 ≤ b := by linarith
  have hx2 : 2 ≤ b / s := (le_div_iff₀ hsR).mpr hb
  have hfloor := Nat.lt_floor_add_one (b / s)
  have hhalf : b / (2 * s) ≤ (⌊b / s⌋₊ : ℝ) := by
    have hh : (b / s) / 2 ≤ (⌊b / s⌋₊ : ℝ) := by linarith
    exact (by ring : b / (2 * s) = (b / s) / 2).trans_le hh
  have hone : 1 ≤ 8 * b / δ := (le_div_iff₀ hδ).mpr (by simpa only [one_mul] using hδb)
  have hceil : (⌈8 * b / δ⌉₊ : ℝ) ≤ 8 * b / δ + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (by positivity) hδ.le)).le
  have hbound : (⌈8 * b / δ⌉₊ : ℝ) ≤ (⌈32 * (s : ℝ) / δ⌉₊ : ℝ) * (⌊b / s⌋₊ : ℝ) := by
    calc
      _ ≤ 8 * b / δ + 1 := hceil
      _ ≤ 8 * b / δ + 8 * b / δ := add_le_add le_rfl hone
      _ = 16 * b / δ := by ring
      _ = (32 * (s : ℝ) / δ) * (b / (2 * s)) := by field_simp; ring
      _ ≤ _ := mul_le_mul (Nat.le_ceil _) hhalf (by positivity) (by positivity)
  exact_mod_cast hbound

lemma delta_inner_radius_budgets {b δ : ℝ} {s m : ℕ} (hs : 0 < s) (hm : 0 < m)
    (hδ : 0 < δ) (hwidth : (m : ℝ) ≤ 8 * b / δ)
    (hlarge : 16 * (s : ℝ) ≤ δ * m) :
    m ≤ ⌈8 * b / δ⌉₊ ∧
      ⌈8 * b / δ⌉₊ ≤ ⌈32 * (s : ℝ) / δ⌉₊ * ⌊b / s⌋₊ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hprod : (m : ℝ) * δ ≤ 8 * b := (le_div_iff₀ hδ).mp hwidth
  have hb : 2 * (s : ℝ) ≤ b := by linarith
  have hδb : δ ≤ 8 * b := by nlinarith
  refine ⟨?_, delta_ceil_mass_le_mul_inner_radius hs hδ hb hδb⟩
  exact_mod_cast hwidth.trans (Nat.le_ceil _)

end Erdos587.GeneralizedAP

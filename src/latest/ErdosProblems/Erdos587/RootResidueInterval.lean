import ErdosProblems.Erdos587.ProgressionGeometry

/-! A positive root in every residue class of a sufficiently long real interval. -/

namespace Erdos587

theorem exists_positive_residue_in_real_interval {q : ℕ} (hq : 0 < q) (r : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hwidth : 2 * (q : ℝ) ≤ b - a) :
    ∃ z : ℕ, 0 < z ∧ a ≤ z ∧ (z : ℝ) ≤ b ∧ z ≡ r [MOD q] := by
  let n := ⌊a / (q : ℝ)⌋₊
  let z := r % q + q * (n + 1)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrem : ((r % q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt r hq
  have hfloor : (n : ℝ) ≤ a / q := Nat.floor_le (div_nonneg ha hqR.le)
  have hfloor' : a / q < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : a < (q : ℝ) * ((n : ℝ) + 1) := by
    have hh := (div_lt_iff₀ hqR).mp hfloor'
    nlinarith
  have hhi : (q : ℝ) * (n : ℝ) ≤ a := by
    have hh := (le_div_iff₀ hqR).mp hfloor
    nlinarith
  have hzR : (z : ℝ) = (r % q : ℕ) + (q : ℝ) * ((n : ℝ) + 1) := by
    simp only [z, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  refine ⟨z, by dsimp only [z]; positivity, ?_, ?_, ?_⟩
  · rw [hzR]
    have hh := Nat.cast_nonneg (α := ℝ) (r % q)
    linarith
  · rw [hzR]
    nlinarith
  · change z % q = r % q
    dsimp only [z]
    simp [Nat.add_mod]

lemma quadratic_residue_reduced_period {g u : ℕ} (_hu : 0 < u) {z r : ℕ}
    (hz : z ≡ r [MOD u / g.gcd u]) : g * z ^ 2 ≡ g * r ^ 2 [MOD u] := by
  let d := g.gcd u
  have hdu : d ∣ u := Nat.gcd_dvd_right g u
  have hdg : d ∣ g := Nat.gcd_dvd_left g u
  have huEq : d * (u / d) = u := Nat.mul_div_cancel' hdu
  have hgEq : d * (g / d) = g := Nat.mul_div_cancel' hdg
  change z ≡ r [MOD u / d] at hz
  have hh := (hz.pow 2).mul_left (g / d)
  have hscaled := hh.mul_left' d
  simpa only [← Nat.mul_assoc, hgEq, huEq] using hscaled

end Erdos587

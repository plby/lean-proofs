import ErdosProblems.Erdos380.SmoothDyadicSelection

/-! # A growing-parameter logarithmic lower bound for dyadic smooth numbers -/

open scoped BigOperators

namespace Erdos380

/-- The elementary dyadic construction gives the correct leading
logarithmic cost whenever `u` grows, `u/Y` tends to zero, and
`log Y / log u` tends to one.  The sufficient inequalities are retained
explicitly here. -/
theorem exists_smoothCount_dyadic_exponential_lower : ∃ Y₀ : ℕ,
    ∀ X Y : ℕ, Y₀ ≤ Y → ∀ ε u : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ u →
      (X : ℝ) = u * Y → 4 ≤ ε * Y → 8 * (X : ℝ) ≤ ε * (Y : ℝ) ^ 2 →
      Real.log (20 * Y : ℝ) ≤ (1 + ε) * Real.log u →
      (2 : ℝ) ^ X * Real.exp (-(1 + 3 * ε) * u * Real.log u) ≤
        (smoothCount (2 ^ X) (2 ^ Y) : ℝ) := by
  obtain ⟨b₀, hb₀⟩ := exists_smoothCount_all_dyadic_lower
  refine ⟨2 * b₀ + 2, ?_⟩
  intro X Y hY ε u hε hε1 hu hparam hsize hXY hlogs
  have hYpos : 0 < Y := by omega
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hYpos
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hlu : 0 ≤ Real.log u := Real.log_nonneg hu
  let K : ℕ := ⌊ε * Y / 2⌋₊
  have hKupper : (K : ℝ) ≤ ε * Y / 2 := Nat.floor_le (by positivity)
  have hKlower : ε * Y / 4 ≤ (K : ℝ) := by
    have hfloor : ε * Y / 2 < (K : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hKhalf : (K : ℝ) ≤ (Y : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hε1 hYR.le
    linarith
  have hKY : K ≤ Y := by exact_mod_cast (show (K : ℝ) ≤ Y by linarith)
  have hB : ((Y - K : ℕ) : ℝ) = (Y : ℝ) - K := Nat.cast_sub hKY
  have hBlower : (Y : ℝ) / 2 ≤ ((Y - K : ℕ) : ℝ) := by rw [hB]; linarith
  have hbase : b₀ ≤ Y - K := by
    have hbY : (2 * b₀ + 2 : ℝ) ≤ Y := by exact_mod_cast hY
    have hbB : (b₀ : ℝ) ≤ ((Y - K : ℕ) : ℝ) := by linarith
    exact_mod_cast hbB
  have hX : X ≤ K * (Y - K) := by
    have hprod := mul_le_mul hKlower hBlower (by positivity : (0 : ℝ) ≤ Y / 2) (Nat.cast_nonneg K)
    have hxR : (X : ℝ) ≤ (K : ℝ) * ((Y - K : ℕ) : ℝ) := by nlinarith
    exact_mod_cast hxR
  obtain ⟨k, hkK, hkX, hcount⟩ := hb₀ X Y K hKY hbase hX
  have hkupper : (k : ℝ) ≤ (1 + ε) * u := by
    have hkXR : (k : ℝ) * ((Y - K : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hkX
    have hBε : (1 - ε / 2) * (Y : ℝ) ≤ ((Y - K : ℕ) : ℝ) := by rw [hB]; linarith
    have hmul := mul_le_mul_of_nonneg_left hBε (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have hεpoly : 1 ≤ (1 + ε) * (1 - ε / 2) := by nlinarith
    have hfactor : 0 < (1 - ε / 2) * (Y : ℝ) := mul_pos (by linarith) hYR
    apply le_of_mul_le_mul_right _ hfactor
    have huY := mul_le_mul_of_nonneg_right hεpoly (mul_nonneg hu0.le hYR.le)
    rw [hparam] at hkXR
    nlinarith
  have hlogBase : 0 ≤ Real.log (20 * Y : ℝ) := by
    apply Real.log_nonneg
    have hYone : (1 : ℝ) ≤ Y := by exact_mod_cast hYpos
    linarith
  have hloss : (k : ℝ) * Real.log (20 * Y : ℝ) ≤ (1 + 3 * ε) * u * Real.log u := by
    calc
      (k : ℝ) * Real.log (20 * Y : ℝ) ≤ ((1 + ε) * u) * ((1 + ε) * Real.log u) :=
        mul_le_mul hkupper hlogs hlogBase (by positivity)
      _ ≤ _ := by
        have hεsq : (1 + ε) ^ 2 ≤ 1 + 3 * ε := by nlinarith
        have hmul := mul_le_mul_of_nonneg_right hεsq (mul_nonneg hu0.le hlu)
        nlinarith
  have hpow : (20 * Y : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (20 * Y : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hcount' : (2 : ℝ) ^ X ≤ Real.exp ((1 + 3 * ε) * u * Real.log u) *
      (smoothCount (2 ^ X) (2 ^ Y) : ℝ) := by
    rw [hpow] at hcount
    exact hcount.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hloss) (by positivity))
  have hmul := mul_le_mul_of_nonneg_right hcount'
    (Real.exp_pos (-(1 + 3 * ε) * u * Real.log u)).le
  have hcancel : Real.exp ((1 + 3 * ε) * u * Real.log u) *
      Real.exp (-(1 + 3 * ε) * u * Real.log u) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring_nf
  calc
    _ ≤ (Real.exp ((1 + 3 * ε) * u * Real.log u) *
        (smoothCount (2 ^ X) (2 ^ Y) : ℝ)) * Real.exp (-(1 + 3 * ε) * u * Real.log u) := hmul
    _ = (smoothCount (2 ^ X) (2 ^ Y) : ℝ) *
        (Real.exp ((1 + 3 * ε) * u * Real.log u) *
          Real.exp (-(1 + 3 * ε) * u * Real.log u)) := by ring
    _ = _ := by rw [hcancel, mul_one]

end Erdos380

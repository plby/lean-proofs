import ErdosProblems.Erdos633.Rationality

/-!
# Rationality in the two group-one shapes

The integer equations are the signed boundary invariants, and the area
equations are the normalized area ratios. Their algebraic consequences are
proved here. The geometric extraction of these hypotheses remains separate.

For U, both characters determine `L(2-s²)` and `Ls`. The identity
`N = (L(2-s²))² + L * (L(2-s²))` then makes `L` rational directly.
-/

namespace Erdos633

theorem groupOne_U_invariant_rational (s L : ℝ) (m n : ℤ)
    (hm : (m : ℝ) = L * (2 + s - s ^ 2))
    (hn : (n : ℝ) = L * (2 - s - s ^ 2)) :
    L * (2 - s ^ 2) ∈ rationalReals ∧ L * s ∈ rationalReals := by
  have hsum : ((m : ℝ) + n) / 2 = L * (2 - s ^ 2) := by rw [hm, hn]; ring
  have hdiff : ((m : ℝ) - n) / 2 = L * s := by rw [hm, hn]; ring
  constructor
  · rw [← hsum]
    exact rationalReals.div_mem
      (rationalReals.add_mem (rationalReals_int m) (rationalReals_int n))
      (rationalReals_nat 2)
  · rw [← hdiff]
    exact rationalReals.div_mem
      (rationalReals.sub_mem (rationalReals_int m) (rationalReals_int n))
      (rationalReals_nat 2)

/-- The U parameter and scale follow from the two integers and area alone;
no boundary-edge count hypothesis is required. -/
theorem groupOne_U_rational (s L : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (m n : ℤ) (hm : (m : ℝ) = L * (2 + s - s ^ 2))
    (hn : (n : ℝ) = L * (2 - s - s ^ 2)) (N : ℕ)
    (harea : (N : ℝ) = L ^ 2 * (2 - s ^ 2) * (3 - s ^ 2)) :
    s ∈ rationalReals ∧ L ∈ rationalReals := by
  obtain ⟨hXr, hYr⟩ := groupOne_U_invariant_rational s L m n hm hn
  have hfactor : 0 < 2 - s ^ 2 := by nlinarith only [hs0, hs1]
  have hX0 : L * (2 - s ^ 2) ≠ 0 := ne_of_gt (mul_pos hL hfactor)
  have hprod : (L * (2 - s ^ 2)) * L ∈ rationalReals := by
    have h := rationalReals.sub_mem (rationalReals_nat N) (rationalReals.pow_mem hXr 2)
    convert h using 1
    rw [harea]
    ring
  have hLr := rational_of_mul hXr hX0 hprod
  exact ⟨rational_of_mul hLr (ne_of_gt hL) hYr, hLr⟩

/-- In V, the single independent signed count first determines `s²`. -/
theorem groupOne_V_square_rational (s L : ℝ) (hL : 0 < L)
    (m : ℤ) (hm : (m : ℝ) = L * s) (N : ℕ)
    (harea : (N : ℝ) = L ^ 2 * (2 - s ^ 2)) :
    L ^ 2 ∈ rationalReals ∧ s ^ 2 ∈ rationalReals := by
  have hm2 : (m : ℝ) ^ 2 = L ^ 2 * s ^ 2 := by rw [hm]; ring
  have hLsq : L ^ 2 = ((N : ℝ) + (m : ℝ) ^ 2) / 2 := by
    nlinarith only [hm2, harea]
  have hLr : L ^ 2 ∈ rationalReals := by
    rw [hLsq]
    exact rationalReals.div_mem
      (rationalReals.add_mem (rationalReals_nat N)
        (rationalReals.pow_mem (rationalReals_int m) 2)) (rationalReals_nat 2)
  have hprod : L ^ 2 * s ^ 2 ∈ rationalReals := by
    rw [← hm2]
    exact rationalReals.pow_mem (rationalReals_int m) 2
  exact ⟨hLr, rational_of_mul hLr (pow_ne_zero 2 (ne_of_gt hL)) hprod⟩

/-- A positive unit-edge count rules out the irrational square root in V. -/
theorem groupOne_V_rational (s L : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (m : ℤ) (hm : (m : ℝ) = L * s) (N : ℕ)
    (harea : (N : ℝ) = L ^ 2 * (2 - s ^ 2))
    (p q r : ℕ) (hr : 0 < r) (hedge : L = p * s + q * (1 - s ^ 2) + r) :
    s ∈ rationalReals ∧ L ∈ rationalReals := by
  have hsq := (groupOne_V_square_rational s L hL m hm N harea).2
  have hsne := ne_of_gt hs0
  have hratio : L / s ∈ rationalReals := by
    have h := rationalReals.div_mem (rationalReals_int m) hsq
    have heq : (m : ℝ) / s ^ 2 = L / s := by
      rw [hm]
      field_simp
    rwa [heq] at h
  have hsrat : s ∈ rationalReals := by
    apply rational_of_positive_boundary
      (rationalReals.sub_mem hratio (rationalReals_nat p))
      (rationalReals.add_mem
        (rationalReals.mul_mem (rationalReals_nat q)
          (rationalReals.sub_mem rationalReals.one_mem hsq)) (rationalReals_nat r))
    · have hfactor : 0 < 1 - s ^ 2 := by nlinarith only [hs0, hs1]
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr
      positivity
    · field_simp
      nlinarith only [hedge]
  refine ⟨hsrat, ?_⟩
  have h := rationalReals.div_mem (rationalReals_int m) hsrat
  rw [hm] at h
  simpa [hsne] using h

end Erdos633

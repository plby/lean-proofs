import ErdosProblems.Erdos587.HooleyApproximationCount
import ErdosProblems.Erdos587.HooleyDivisorCounting
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.ZMod.Units

/-! # Reduced Dirichlet approximants and the exact nonzero error encoding -/

namespace Erdos587

theorem exists_delta_dirichlet_approximant (α : ℝ) {K : ℝ} (hK : 1 ≤ K) :
    ∃ (b : ℕ) (h : ℤ), 0 < b ∧ (b : ℝ) ≤ K ∧
      IsUnit (h : ZMod b) ∧ |α - (h : ℝ) / b| ≤ 1 / ((b : ℝ) * K) := by
  obtain ⟨r, herror, hden⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le α (Nat.floor_pos.mpr hK)
  have hb : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hcop : IsCoprime r.num (r.den : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using r.reduced)
  have hunit : IsUnit (r.num : ZMod r.den) := by
    apply isCoprime_zero_right.mp
    simpa using hcop.map (Int.castRingHom (ZMod r.den))
  refine ⟨r.den, r.num, r.pos,
    (show (r.den : ℝ) ≤ ⌊K⌋₊ by exact_mod_cast hden).trans (Nat.floor_le (by linarith)),
    hunit, ?_⟩
  have hcast : (r : ℝ) = (r.num : ℝ) / r.den := Rat.cast_def r
  rw [← hcast]
  apply herror.trans
  apply one_div_le_one_div_of_le (mul_pos hb (by linarith : 0 < K))
  nlinarith [Nat.lt_floor_add_one K]

noncomputable def deltaApproximantFrequencyError (a : ℤ) (q : ℕ)
    (x : DeltaApproximant) : ℝ :=
  (a : ℝ) * x.index / q - (x.numerator : ℝ) / x.denominator

lemma delta_approximant_error_cast {a : ℤ} {q : ℕ} (hq : 0 < q)
    {x : DeltaApproximant} (hb : 0 < x.denominator) :
    (deltaApproximantError a q x : ℝ) =
      (q : ℝ) * x.denominator * deltaApproximantFrequencyError a q x := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hbR : (x.denominator : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [deltaApproximantError, deltaApproximantFrequencyError]
  push_cast
  field_simp

lemma delta_approximant_error_tolerance {a : ℤ} {q : ℕ} (hq : 0 < q)
    {x : DeltaApproximant} (hb : 0 < x.denominator) {δ : ℝ}
    (hδ : |deltaApproximantFrequencyError a q x| ≤ δ) :
    |(deltaApproximantError a q x : ℝ)| ≤ (q : ℝ) * x.denominator * δ := by
  rw [delta_approximant_error_cast hq hb, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) * x.denominator)]
  exact mul_le_mul_of_nonneg_left hδ (by positivity)

theorem exists_delta_centered_approximant {a q : ℕ} (hq : 0 < q)
    (hcop : q.Coprime a) (m : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (hden : K < (q / q.gcd m : ℕ)) :
    ∃ x : DeltaApproximant, x.index = m ∧ 0 < x.denominator ∧
      (x.denominator : ℝ) ≤ K ∧ IsUnit (x.numerator : ZMod x.denominator) ∧
      |deltaApproximantFrequencyError a q x| ≤ 1 / ((x.denominator : ℝ) * K) ∧
      deltaApproximantError a q x ≠ 0 := by
  obtain ⟨b, h, hb, hbK, hunit, herror⟩ :=
    exists_delta_dirichlet_approximant ((a : ℝ) * m / q) hK
  refine ⟨⟨m, b, h⟩, rfl, hb, hbK, hunit, herror, ?_⟩
  apply centered_delta_encoding_ne_zero hq hcop hb (le_refl b)
  exact_mod_cast hbK.trans_lt hden

end Erdos587

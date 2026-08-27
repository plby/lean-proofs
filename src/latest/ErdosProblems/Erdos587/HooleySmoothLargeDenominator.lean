import ErdosProblems.Erdos587.HooleyPowerMean
import ErdosProblems.Erdos587.HooleySmoothQuadratic

/-! # The smooth quadratic mean for indices with large exact denominator -/

open scoped BigOperators FourierTransform SchwartzMap

namespace Erdos587

theorem exists_delta_smooth_sum_majorant {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ W, ∀ (a : ℤ) (q : ℕ) (x : DeltaApproximant),
      0 < x.denominator → IsUnit (x.numerator : ZMod x.denominator) →
      ∀ K θ : ℝ, 0 < K → (x.denominator : ℝ) ≤ K →
      |deltaApproximantFrequencyError a q x| ≤ 2 / ((x.denominator : ℝ) * K) →
      ‖deltaSmoothQuadraticSum f K ((a : ℝ) * x.index / q) θ‖ ^ 2 ≤
        C * deltaQuadraticMajorant K a q x := by
  obtain ⟨C, hC, hbound⟩ := exists_delta_family_smooth_major_arc_sq_bound hW
  refine ⟨C, hC, ?_⟩
  intro f hf a q x hb hunit K θ hK hbK herror
  have h := hbound f hf x.denominator hb x.numerator hunit K
    (deltaApproximantFrequencyError a q x) θ hK hbK herror
  have hα : (x.numerator : ℝ) / x.denominator + deltaApproximantFrequencyError a q x =
      (a : ℝ) * x.index / q := by dsimp only [deltaApproximantFrequencyError]; ring
  rw [hα] at h
  exact h.trans_eq (by dsimp only [deltaQuadraticMajorant]; ring)

theorem exists_delta_centered_approximant_family {a q : ℕ} (hq : 0 < q)
    (hcop : q.Coprime a) (I : Finset ℕ) {K : ℝ} (hK : 1 ≤ K)
    (hden : ∀ m ∈ I, K < (q / q.gcd m : ℕ)) :
    ∃ x : ℕ → DeltaApproximant, (∀ m, (x m).index = m) ∧
      ∀ m ∈ I, 0 < (x m).denominator ∧ ((x m).denominator : ℝ) ≤ K ∧
        IsUnit ((x m).numerator : ZMod (x m).denominator) ∧
        |deltaApproximantFrequencyError a q (x m)| ≤ 2 / (((x m).denominator : ℝ) * K) ∧
        deltaApproximantError a q (x m) ≠ 0 := by
  classical
  have hex (m : ℕ) (hm : m ∈ I) := exists_delta_centered_approximant hq hcop m hK (hden m hm)
  let x (m : ℕ) : DeltaApproximant :=
    if hm : m ∈ I then Classical.choose (hex m hm) else ⟨m, 1, 0⟩
  have hx (m : ℕ) (hm : m ∈ I) := Classical.choose_spec (hex m hm)
  have hindex (m : ℕ) : (x m).index = m := by
    by_cases hm : m ∈ I
    · simpa only [x, dif_pos hm] using (hx m hm).1
    · simp only [x, dif_neg hm]
  refine ⟨x, hindex, ?_⟩
  intro m hm
  have h := hx m hm
  have hdenpos : (0 : ℝ) < (x m).denominator := by
    exact_mod_cast (show 0 < (x m).denominator from by simpa only [x, dif_pos hm] using h.2.1)
  have hwidth : 1 / (((x m).denominator : ℝ) * K) ≤
      2 / (((x m).denominator : ℝ) * K) := by
    apply div_le_div_of_nonneg_right (by norm_num)
    positivity
  have hxeq : x m = Classical.choose (hex m hm) := by simp only [x, dif_pos hm]
  rw [hxeq] at hwidth ⊢
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.trans hwidth, h.2.2.2.2.2⟩

theorem exists_delta_smooth_large_denominator_mean {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ a M q D : ℕ, 1 ≤ M → 0 < q → q.Coprime a →
      (q : ℝ) * (M * 2 ^ D : ℕ) ^ (3 / (r : ℝ)) ≤ (M * 2 ^ D : ℕ) →
      ∀ K : ℝ, 1 ≤ K → K ≤ 2 ^ D → ∀ I : Finset ℕ, I ⊆ Finset.Icc 1 M →
      (∀ m ∈ I, K < (q / q.gcd m : ℕ)) →
      ∀ (f : ℕ → 𝓢(ℝ, ℂ)) (θ : ℕ → ℝ), (∀ m ∈ I, f m ∈ W) →
      (∑ m ∈ I, ‖deltaSmoothQuadraticSum (f m) K ((a : ℝ) * m / q) (θ m)‖ ^ 2) ≤
        C * (M * 2 ^ D : ℕ) * (max 1 (Real.log (Real.log (M * 2 ^ D : ℕ)))) ^ 7 := by
  classical
  obtain ⟨C₀, hC₀, hpoint⟩ := exists_delta_smooth_sum_majorant hW
  obtain ⟨C₁, hC₁, hmean⟩ := exists_delta_majorant_power_mean r hr
  refine ⟨C₀ * C₁, by positivity, ?_⟩
  intro a M q D hM hq hcop hsep K hK hKD I hI hden f θ hf
  obtain ⟨x, hindex, hx⟩ := exists_delta_centered_approximant_family hq hcop I hK hden
  have hinj : Function.Injective x := by
    intro m n heq
    simpa only [hindex] using congrArg DeltaApproximant.index heq
  let S := I.image x
  have hcopZ : IsCoprime (a : ℤ) (q : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa only [Int.natAbs_natCast] using hcop.symm)
  have hidx (y : DeltaApproximant) (hy : y ∈ S) : 0 < y.index ∧ y.index ≤ M := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    rw [hindex]
    exact ⟨(Finset.mem_Icc.mp (hI hm)).1, (Finset.mem_Icc.mp (hI hm)).2⟩
  have hds (y : DeltaApproximant) (hy : y ∈ S) :
      0 < y.denominator ∧ (y.denominator : ℝ) ≤ K := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨(hx m hm).1, (hx m hm).2.1⟩
  have hz (y : DeltaApproximant) (hy : y ∈ S) : deltaApproximantError a q y ≠ 0 := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    exact (hx m hm).2.2.2.2
  have he (y : DeltaApproximant) (hy : y ∈ S) :
      |deltaApproximantFrequencyError a q y| ≤ 2 / ((y.denominator : ℝ) * K) := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    exact (hx m hm).2.2.2.1
  have h := hmean M q D hM hq hsep a hcopZ K (by linarith) hKD S hidx hds hz he
  calc
    _ ≤ ∑ m ∈ I, C₀ * deltaQuadraticMajorant K a q (x m) := by
      apply Finset.sum_le_sum
      intro m hm
      have hp := hpoint (f m) (hf m hm) a q (x m) (hx m hm).1
        (hx m hm).2.2.1 K (θ m) (by linarith) (hx m hm).2.1 (hx m hm).2.2.2.1
      simpa only [hindex, Int.cast_natCast] using hp
    _ = C₀ * ∑ y ∈ S, deltaQuadraticMajorant K a q y := by
      rw [Finset.mul_sum, Finset.sum_image hinj.injOn]
    _ ≤ C₀ * (C₁ * (M * 2 ^ D : ℕ) *
        (max 1 (Real.log (Real.log (M * 2 ^ D : ℕ)))) ^ 7) :=
      mul_le_mul_of_nonneg_left h hC₀.le
    _ = _ := by ring

end Erdos587

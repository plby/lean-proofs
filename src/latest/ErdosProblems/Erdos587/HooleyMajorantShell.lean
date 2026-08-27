import ErdosProblems.Erdos587.HooleyDirichlet
import ErdosProblems.Erdos587.HooleyDyadicShell
import ErdosProblems.Erdos587.HooleyApproximationSmallShell

/-! # Summing the major-arc kernel over one denominator block -/

open scoped BigOperators

namespace Erdos587

noncomputable def deltaQuadraticMajorant (K : ℝ) (a : ℤ) (q : ℕ)
    (x : DeltaApproximant) : ℝ :=
  K ^ 2 / ((x.denominator : ℝ) *
    (1 + K ^ 2 * |deltaApproximantFrequencyError a q x|))

theorem delta_sum_quadratic_majorant_of_error_count {q : ℕ} (hq : 0 < q)
    (a : ℤ) (S : Finset DeltaApproximant) {K B H : ℝ}
    (hK : 0 < K) (hB : 0 < B) (hH : 0 ≤ H) (J : ℕ)
    (hlow : ∀ x ∈ S, B < x.denominator)
    (hupp : ∀ x ∈ S, (x.denominator : ℝ) ≤ 2 * B)
    (hscale : ∀ x ∈ S, K ^ 2 * |deltaApproximantFrequencyError a q x| ≤ 2 ^ J)
    (hcount : ∀ T : ℝ, 0 ≤ T →
      ((S.filter (fun x => ((deltaApproximantError a q x).natAbs : ℝ) ≤ T)).card : ℝ) ≤
        H * T) :
    (∑ x ∈ S, deltaQuadraticMajorant K a q x) ≤ 4 * H * q * (J + 1) := by
  classical
  let u := fun x => K ^ 2 * |deltaApproximantFrequencyError a q x|
  let A := 2 * H * (q : ℝ) * B / K ^ 2
  let D := K ^ 2 / B
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hden (x : DeltaApproximant) (hx : x ∈ S) : 0 < x.denominator := by
    exact_mod_cast hB.trans (hlow x hx)
  have hlevels (j : ℕ) (_hj : j ≤ J) :
      ((S.filter (fun x => u x ≤ 2 ^ j)).card : ℝ) ≤ A * 2 ^ j := by
    let T := (q : ℝ) * (2 * B) * (2 ^ j / K ^ 2)
    have hsub : S.filter (fun x => u x ≤ 2 ^ j) ⊆
        S.filter (fun x => ((deltaApproximantError a q x).natAbs : ℝ) ≤ T) := by
      intro x hx
      obtain ⟨hxS, hxlevel⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hxS, ?_⟩
      have hδ : |deltaApproximantFrequencyError a q x| ≤ 2 ^ j / K ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hK)).mpr
        simpa only [u, mul_comm] using hxlevel
      have herr := delta_approximant_error_tolerance hq (hden x hxS) hδ
      rw [Nat.cast_natAbs, Int.cast_abs]
      apply herr.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hupp x hxS) (Nat.cast_nonneg q)) (by positivity)
    calc
      _ ≤ ((S.filter (fun x => ((deltaApproximantError a q x).natAbs : ℝ) ≤ T)).card : ℝ) :=
        by exact_mod_cast Finset.card_le_card hsub
      _ ≤ H * T := hcount T (by dsimp only [T]; positivity)
      _ = A * 2 ^ j := by dsimp only [T, A]; ring
  have hpoint (x : DeltaApproximant) (hx : x ∈ S) :
      deltaQuadraticMajorant K a q x ≤ D / (1 + u x) := by
    have hu : 0 < 1 + u x := by dsimp only [u]; positivity
    calc
      _ ≤ K ^ 2 / (B * (1 + u x)) := by
        apply div_le_div_of_nonneg_left (sq_nonneg K) (mul_pos hB hu)
        exact mul_le_mul_of_nonneg_right (hlow x hx).le hu.le
      _ = _ := by dsimp only [D]; rw [div_mul_eq_div_div]
  have hsum := delta_sum_majorant_of_dyadic_count S (deltaQuadraticMajorant K a q) u J
    hA hD (fun x hx => by dsimp only [deltaQuadraticMajorant]; positivity)
    (fun x hx => by dsimp only [u]; positivity) hscale hlevels hpoint
  apply hsum.trans_eq
  dsimp only [A, D]
  field_simp
  ring

theorem exists_delta_majorant_block_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ X q : ℕ, 0 < q → 16 ≤ X / q → X ≤ (X / q) ^ r →
      ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ K B : ℝ, 0 < K → 0 < B →
      ∀ (J : ℕ) (S : Finset DeltaApproximant),
      (∀ x ∈ S, 0 < x.index) → (∀ x ∈ S, B < x.denominator) →
      (∀ x ∈ S, (x.denominator : ℝ) ≤ 2 * B) →
      (∀ x ∈ S, x.index * x.denominator ≤ X) →
      (∀ x ∈ S, deltaApproximantError a q x ≠ 0) →
      (∀ x ∈ S, K ^ 2 * |deltaApproximantFrequencyError a q x| ≤ 2 ^ J) →
      (∑ x ∈ S, deltaQuadraticMajorant K a q x) ≤
        C * X * (J + 1) * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 := by
  classical
  obtain ⟨C, hC, hcount⟩ := exists_delta_approximant_shell_bound r hr
  refine ⟨4 * C, by positivity, ?_⟩
  intro X q hq hlength hsize a hcop K B hK hB J S hindex hlow hupp hproduct hzero hscale
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hcounts (T : ℝ) (hT : 0 ≤ T) :
      ((S.filter (fun x => ((deltaApproximantError a q x).natAbs : ℝ) ≤ T)).card : ℝ) ≤
        (C * ((X : ℝ) / q) * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7) * T := by
    have h := hcount X q hq hlength hsize a hcop B T hB hT
      (S.filter (fun x => ((deltaApproximantError a q x).natAbs : ℝ) ≤ T))
      (fun x hx => hindex x (Finset.mem_filter.mp hx).1)
      (fun x hx => hlow x (Finset.mem_filter.mp hx).1)
      (fun x hx => hupp x (Finset.mem_filter.mp hx).1)
      (fun x hx => hproduct x (Finset.mem_filter.mp hx).1)
      (fun x hx => hzero x (Finset.mem_filter.mp hx).1)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    exact h.trans_eq (by ring)
  have h := delta_sum_quadratic_majorant_of_error_count hq a S hK hB (by positivity)
    J hlow hupp hscale hcounts
  apply h.trans_eq
  field_simp

theorem exists_delta_majorant_small_block_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X q : ℕ, 0 < q → ∀ a : ℤ, IsCoprime a (q : ℤ) →
      ∀ K B : ℝ, 0 < K → 0 < B → ∀ (J : ℕ) (S : Finset DeltaApproximant),
      (∀ x ∈ S, 0 < x.index) → (∀ x ∈ S, B < x.denominator) →
      (∀ x ∈ S, (x.denominator : ℝ) ≤ 2 * B) →
      (∀ x ∈ S, x.index * x.denominator ≤ X) →
      (∀ x ∈ S, deltaApproximantError a q x ≠ 0) →
      (∀ x ∈ S, K ^ 2 * |deltaApproximantFrequencyError a q x| ≤ 2 ^ J) →
      (∑ x ∈ S, deltaQuadraticMajorant K a q x) ≤
        C * (X + q) * (J + 1) * (X : ℝ) ^ ε := by
  classical
  obtain ⟨C, hC, hcount⟩ := exists_delta_approximant_small_shell_bound hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro X q hq a hcop K B hK hB J S hindex hlow hupp hproduct hzero hscale
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hcounts (T : ℝ) (hT : 0 ≤ T) :
      ((S.filter (fun x => ((deltaApproximantError a q x).natAbs : ℝ) ≤ T)).card : ℝ) ≤
        (C * ((X : ℝ) / q + 1) * (X : ℝ) ^ ε) * T := by
    have h := hcount X q hq a hcop B T hB hT
      (S.filter (fun x => ((deltaApproximantError a q x).natAbs : ℝ) ≤ T))
      (fun x hx => hindex x (Finset.mem_filter.mp hx).1)
      (fun x hx => hlow x (Finset.mem_filter.mp hx).1)
      (fun x hx => hupp x (Finset.mem_filter.mp hx).1)
      (fun x hx => hproduct x (Finset.mem_filter.mp hx).1)
      (fun x hx => hzero x (Finset.mem_filter.mp hx).1)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    exact h.trans_eq (by ring)
  have h := delta_sum_quadratic_majorant_of_error_count hq a S hK hB (by positivity)
    J hlow hupp hscale hcounts
  apply h.trans_eq
  field_simp

end Erdos587

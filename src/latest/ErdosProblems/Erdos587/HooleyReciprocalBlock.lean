import ErdosProblems.Erdos587.HooleyReciprocalMajorant
import ErdosProblems.Erdos587.HooleyReciprocalShell

/-! # Reciprocal tolerance-shell summation for a fixed denominator -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_reciprocal_majorant_block_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ c q b X : ℕ, 0 < c → 0 < q → 0 < b → 2 ≤ X →
      ∀ (a v : ℤ) (A : ℕ → ℤ) (K R : ℝ), 0 < K → 0 < R →
      8 ≤ 2 * c * R * b / K ^ 2 → X ≤ ⌊2 * c * R * b / K ^ 2⌋₊ ^ r →
      ∀ (J : ℕ) (S : Finset DeltaApproximant),
      (∀ x ∈ S, R < x.index) → (∀ x ∈ S, (x.index : ℝ) ≤ 2 * R) →
      (∀ x ∈ S, x.denominator = b) →
      (∀ x ∈ S, ((c * x.index : ℕ) : ℤ) ∣ (q : ℤ) * A x.index - a * v) →
      (∀ t : ℤ, |(t : ℝ)| ≤ (2 * c * R * b / K ^ 2) * 2 ^ J →
        (b : ℤ) * a * v - q * t ≠ 0 ∧ ((b : ℤ) * a * v - q * t).natAbs ≤ X) →
      (∀ x ∈ S, K ^ 2 * |deltaReciprocalFrequencyError c A x| ≤ 2 ^ J) →
      (∑ x ∈ S, deltaReciprocalMajorant K c A x) ≤
        C * c * R * (Int.gcd ((b : ℤ) * a * v) q).divisors.card * (J + 1) *
          (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6 := by
  classical
  obtain ⟨C, hC, hcount⟩ := exists_delta_reciprocal_tolerance_bound r hr
  refine ⟨4 * C, by positivity, ?_⟩
  intro c q b X hc hq hb hX a v A K R hK hR hbase hsize J S hlow hupp hden hrel hvalues hscale
  let T₀ := 2 * (c : ℝ) * R * b / K ^ 2
  let H := C * (Int.gcd ((b : ℤ) * a * v) q).divisors.card *
    (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6
  have hT₀ : 0 ≤ T₀ := by dsimp only [T₀]; positivity
  have hcounts (j : ℕ) (hj : j ≤ J) :
      ((S.filter (fun x => |(deltaReciprocalApproximantError c A x : ℝ)| ≤ T₀ * 2 ^ j)).card : ℝ) ≤
        H * (T₀ * 2 ^ j) + 0 := by
    have hTlo : T₀ ≤ T₀ * 2 ^ j := le_mul_of_one_le_right hT₀ (one_le_pow₀ (by norm_num))
    have hThi : T₀ * 2 ^ j ≤ T₀ * 2 ^ J := by gcongr; norm_num
    have hsize' : X ≤ ⌊T₀ * 2 ^ j⌋₊ ^ r :=
      hsize.trans (Nat.pow_le_pow_left (Nat.floor_mono hTlo) r)
    have h := hcount c q b X hc hq hX a v A R (T₀ * 2 ^ j) hR
      (hbase.trans hTlo) hsize'
      (S.filter (fun x => |(deltaReciprocalApproximantError c A x : ℝ)| ≤ T₀ * 2 ^ j))
      (fun x hx => hlow x (Finset.mem_filter.mp hx).1)
      (fun x hx => hupp x (Finset.mem_filter.mp hx).1)
      (fun x hx => hden x (Finset.mem_filter.mp hx).1)
      (fun x hx => hrel x (Finset.mem_filter.mp hx).1)
      (fun t ht => hvalues t (ht.trans hThi)) (fun x hx => (Finset.mem_filter.mp hx).2)
    exact h.trans_eq (by dsimp only [H]; ring)
  have hindex (x : DeltaApproximant) (hx : x ∈ S) : 0 < x.index := by
    exact_mod_cast hR.trans (hlow x hx)
  have h := delta_sum_reciprocal_majorant_of_error_count hc hb A S hK hR
    (by dsimp only [H]; positivity) (by norm_num : (0 : ℝ) ≤ 0)
    J hindex hupp hden hscale hcounts
  exact h.trans_eq (by dsimp only [H]; ring)

theorem exists_delta_reciprocal_majorant_small_block_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c q b X : ℕ, 0 < c → 0 < b →
      ∀ (a v : ℤ) (A : ℕ → ℤ) (K R : ℝ), 0 < K → 0 < R →
      ∀ (J : ℕ) (S : Finset DeltaApproximant),
      (∀ x ∈ S, R < x.index) → (∀ x ∈ S, (x.index : ℝ) ≤ 2 * R) →
      (∀ x ∈ S, x.denominator = b) →
      (∀ x ∈ S, ((c * x.index : ℕ) : ℤ) ∣ (q : ℤ) * A x.index - a * v) →
      (∀ t : ℤ, |(t : ℝ)| ≤ (2 * c * R * b / K ^ 2) * 2 ^ J →
        (b : ℤ) * a * v - q * t ≠ 0 ∧ ((b : ℤ) * a * v - q * t).natAbs ≤ X) →
      (∀ x ∈ S, K ^ 2 * |deltaReciprocalFrequencyError c A x| ≤ 2 ^ J) →
      (∑ x ∈ S, deltaReciprocalMajorant K c A x) ≤
        C * (2 * c * R * (J + 1) + K ^ 2 / b) * (X : ℝ) ^ ε := by
  classical
  obtain ⟨C, hC, hcount⟩ := exists_delta_reciprocal_small_tolerance_bound hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro c q b X hc hb a v A K R hK hR J S hlow hupp hden hrel hvalues hscale
  let T₀ := 2 * (c : ℝ) * R * b / K ^ 2
  let H := 2 * C * (X : ℝ) ^ ε
  let G := C * (X : ℝ) ^ ε
  have hcounts (j : ℕ) (hj : j ≤ J) :
      ((S.filter (fun x => |(deltaReciprocalApproximantError c A x : ℝ)| ≤ T₀ * 2 ^ j)).card : ℝ) ≤
        H * (T₀ * 2 ^ j) + G := by
    have hThi : T₀ * 2 ^ j ≤ T₀ * 2 ^ J := by
      have hT₀ : 0 ≤ T₀ := by dsimp only [T₀]; positivity
      gcongr
      norm_num
    have h := hcount c q b X hc a v A R (T₀ * 2 ^ j) hR
      (by dsimp only [T₀]; positivity)
      (S.filter (fun x => |(deltaReciprocalApproximantError c A x : ℝ)| ≤ T₀ * 2 ^ j))
      (fun x hx => hlow x (Finset.mem_filter.mp hx).1)
      (fun x hx => hupp x (Finset.mem_filter.mp hx).1)
      (fun x hx => hden x (Finset.mem_filter.mp hx).1)
      (fun x hx => hrel x (Finset.mem_filter.mp hx).1)
      (fun t ht => hvalues t (ht.trans hThi)) (fun x hx => (Finset.mem_filter.mp hx).2)
    exact h.trans_eq (by dsimp only [H, G]; ring)
  have hindex (x : DeltaApproximant) (hx : x ∈ S) : 0 < x.index := by
    exact_mod_cast hR.trans (hlow x hx)
  have h := delta_sum_reciprocal_majorant_of_error_count hc hb A S hK hR
    (by dsimp only [H]; positivity) (by dsimp only [G]; positivity)
    J hindex hupp hden hscale hcounts
  exact h.trans_eq (by dsimp only [H, G]; ring)

end Erdos587

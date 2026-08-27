import ErdosProblems.Erdos587.HooleyMajorantShell
import ErdosProblems.Erdos587.HooleyDenominatorBlocks

/-! # Summation over the large-progression denominator blocks -/

open scoped BigOperators

namespace Erdos587

lemma delta_approximant_dyadic_scale {K : ℝ} (hK : 0 < K) {D j : ℕ}
    (hKD : K ≤ 2 ^ D) (hjD : j ≤ D) {a : ℤ} {q : ℕ}
    {x : DeltaApproximant} (hb : 0 < x.denominator)
    (hblock : Nat.clog 2 x.denominator = j)
    (herror : |deltaApproximantFrequencyError a q x| ≤
      2 / ((x.denominator : ℝ) * K)) :
    K ^ 2 * |deltaApproximantFrequencyError a q x| ≤ 2 ^ (D - j + 2) := by
  have hbR : (0 : ℝ) < x.denominator := by exact_mod_cast hb
  have hlo := (delta_dyadic_denominator_bounds hb).1
  rw [hblock] at hlo
  have hmul := (le_div_iff₀ (mul_pos hbR hK)).mp herror
  apply delta_dyadic_error_scale (by positivity) hKD hjD (by linarith :
    (2 : ℝ) ^ j ≤ 2 * x.denominator)
  nlinarith [mul_le_mul_of_nonneg_right hmul hK.le]

theorem exists_delta_majorant_good_blocks_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ M q D : ℕ, 0 < q →
      ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ K : ℝ, 0 < K → K ≤ 2 ^ D →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, 0 < x.index ∧ x.index ≤ M) →
      (∀ x ∈ S, 0 < x.denominator ∧ (x.denominator : ℝ) ≤ K) →
      (∀ x ∈ S, deltaApproximantError a q x ≠ 0) →
      (∀ x ∈ S, |deltaApproximantFrequencyError a q x| ≤
        2 / ((x.denominator : ℝ) * K)) →
      (∀ x ∈ S, let X := M * 2 ^ Nat.clog 2 x.denominator
        16 ≤ X / q ∧ X ≤ (X / q) ^ r) →
      (∑ x ∈ S, deltaQuadraticMajorant K a q x) ≤
        C * M * 2 ^ D * (max 1 (Real.log (Real.log (M * 2 ^ D : ℕ)))) ^ 7 := by
  classical
  obtain ⟨C, hC, hblockBound⟩ := exists_delta_majorant_block_bound r hr
  refine ⟨8 * C, by positivity, ?_⟩
  intro M q D hq a hcop K hK hKD S hindex hden hzero herror hgood
  let N := M * 2 ^ D
  let F := (max 1 (Real.log (Real.log (N : ℝ)))) ^ 7
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hmap (x : DeltaApproximant) (hx : x ∈ S) :
      Nat.clog 2 x.denominator ∈ Finset.range (D + 1) := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (delta_dyadic_denominator_index_le ((hden x hx).2.trans hKD))
  have hlevel (j : ℕ) (hj : j ∈ Finset.range (D + 1)) :
      (∑ x ∈ S with Nat.clog 2 x.denominator = j, deltaQuadraticMajorant K a q x) ≤
        C * M * 2 ^ j * ((D - j : ℕ) + 3) * F := by
    let T := S.filter (fun x => Nat.clog 2 x.denominator = j)
    have hjD : j ≤ D := by simpa using Finset.mem_range.mp hj
    by_cases hT : T.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hT
      have hsize := hgood x₀ (Finset.mem_filter.mp hx₀).1
      dsimp only at hsize
      rw [(Finset.mem_filter.mp hx₀).2] at hsize
      have hlo (x : DeltaApproximant) (hx : x ∈ T) :
          (2 : ℝ) ^ j / 2 < x.denominator := by
        have h := (delta_dyadic_denominator_bounds (hden x (Finset.mem_filter.mp hx).1).1).1
        simpa only [(Finset.mem_filter.mp hx).2] using h
      have hupp (x : DeltaApproximant) (hx : x ∈ T) :
          (x.denominator : ℝ) ≤ 2 * ((2 : ℝ) ^ j / 2) := by
        have h := (delta_dyadic_denominator_bounds (hden x (Finset.mem_filter.mp hx).1).1).2
        rw [(Finset.mem_filter.mp hx).2] at h
        linarith
      have hprod (x : DeltaApproximant) (hx : x ∈ T) :
          x.index * x.denominator ≤ M * 2 ^ j := by
        apply Nat.mul_le_mul (hindex x (Finset.mem_filter.mp hx).1).2
        have h := hupp x hx
        have hR : (x.denominator : ℝ) ≤ 2 ^ j := by linarith
        exact_mod_cast hR
      have hscale (x : DeltaApproximant) (hx : x ∈ T) :
          K ^ 2 * |deltaApproximantFrequencyError a q x| ≤ 2 ^ (D - j + 2) :=
        delta_approximant_dyadic_scale hK hKD hjD (hden x (Finset.mem_filter.mp hx).1).1
          (Finset.mem_filter.mp hx).2 (herror x (Finset.mem_filter.mp hx).1)
      have h := hblockBound (M * 2 ^ j) q hq hsize.1 hsize.2 a hcop K
        ((2 : ℝ) ^ j / 2) hK (by positivity) (D - j + 2) T
        (fun x hx => (hindex x (Finset.mem_filter.mp hx).1).1)
        hlo hupp hprod (fun x hx => hzero x (Finset.mem_filter.mp hx).1) hscale
      have hXN : M * 2 ^ j ≤ N := by dsimp only [N]; gcongr; norm_num
      have hlog : (max 1 (Real.log (Real.log (M * 2 ^ j : ℕ)))) ^ 7 ≤ F := by
        apply pow_le_pow_left₀ (by positivity) (delta_loglog_nat_mono hXN)
      calc
        _ ≤ C * (M * 2 ^ j) * ((D - j : ℕ) + 3) *
            (max 1 (Real.log (Real.log (M * 2 ^ j : ℕ)))) ^ 7 := by
          exact h.trans_eq (by push_cast; ring)
        _ ≤ C * (M * 2 ^ j) * ((D - j : ℕ) + 3) * F :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = _ := by ring
    · have hempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      change (∑ x ∈ T, deltaQuadraticMajorant K a q x) ≤ _
      rw [hempty, Finset.sum_empty]
      positivity
  calc
    _ = ∑ j ∈ Finset.range (D + 1),
        ∑ x ∈ S with Nat.clog 2 x.denominator = j, deltaQuadraticMajorant K a q x :=
      (Finset.sum_fiberwise_of_maps_to hmap (deltaQuadraticMajorant K a q)).symm
    _ ≤ ∑ j ∈ Finset.range (D + 1), C * M * 2 ^ j * ((D - j : ℕ) + 3) * F :=
      Finset.sum_le_sum hlevel
    _ = (C * M * F) * ∑ j ∈ Finset.range (D + 1), (2 : ℝ) ^ j * ((D - j : ℕ) + 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (C * M * F) * (8 * 2 ^ D) :=
      mul_le_mul_of_nonneg_left (delta_sum_dyadic_shell_cost D) (by positivity)
    _ = _ := by dsimp only [F, N]; ring

end Erdos587

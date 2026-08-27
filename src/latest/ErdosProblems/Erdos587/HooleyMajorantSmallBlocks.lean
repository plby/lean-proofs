import ErdosProblems.Erdos587.HooleyMajorantBlocks

/-! # The total cost of the short-progression denominator blocks -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_majorant_small_blocks_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M q D : ℕ, 0 < q →
      ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ K H : ℝ, 0 < K → K ≤ 2 ^ D → 0 ≤ H →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, 0 < x.index ∧ x.index ≤ M) →
      (∀ x ∈ S, 0 < x.denominator ∧ (x.denominator : ℝ) ≤ K) →
      (∀ x ∈ S, deltaApproximantError a q x ≠ 0) →
      (∀ x ∈ S, |deltaApproximantFrequencyError a q x| ≤
        2 / ((x.denominator : ℝ) * K)) →
      (∀ x ∈ S, (M : ℝ) * 2 ^ Nat.clog 2 x.denominator ≤ H) →
      (∑ x ∈ S, deltaQuadraticMajorant K a q x) ≤
        C * (M * 2 ^ D : ℕ) ^ ε * (2 * H + q * (D + 1)) * (D + 3) := by
  classical
  obtain ⟨C, hC, hblockBound⟩ := exists_delta_majorant_small_block_bound hε
  refine ⟨C, hC, ?_⟩
  intro M q D hq a hcop K H hK hKD hH S hindex hden hzero herror hsmall
  let N := M * 2 ^ D
  let I := (Finset.range (D + 1)).filter (fun j => (M : ℝ) * 2 ^ j ≤ H)
  have hmap (x : DeltaApproximant) (hx : x ∈ S) : Nat.clog 2 x.denominator ∈ I := by
    refine Finset.mem_filter.mpr ⟨?_, hsmall x hx⟩
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (delta_dyadic_denominator_index_le ((hden x hx).2.trans hKD))
  have hlevel (j : ℕ) (hj : j ∈ I) :
      (∑ x ∈ S with Nat.clog 2 x.denominator = j, deltaQuadraticMajorant K a q x) ≤
        C * (N : ℝ) ^ ε * ((M : ℝ) * 2 ^ j + q) * ((D - j : ℕ) + 3) := by
    let T := S.filter (fun x => Nat.clog 2 x.denominator = j)
    have hjD : j ≤ D := by simpa using Finset.mem_range.mp (Finset.mem_filter.mp hj).1
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
    have h := hblockBound (M * 2 ^ j) q hq a hcop K
      ((2 : ℝ) ^ j / 2) hK (by positivity) (D - j + 2) T
      (fun x hx => (hindex x (Finset.mem_filter.mp hx).1).1)
      hlo hupp hprod (fun x hx => hzero x (Finset.mem_filter.mp hx).1) hscale
    have hXN : M * 2 ^ j ≤ N := by dsimp only [N]; gcongr; norm_num
    have hpower : (M * 2 ^ j : ℕ) ^ ε ≤ (N : ℝ) ^ ε :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hXN) hε.le
    calc
      _ ≤ C * ((M : ℝ) * 2 ^ j + q) * ((D - j : ℕ) + 3) * (M * 2 ^ j : ℕ) ^ ε :=
        h.trans_eq (by push_cast; ring)
      _ ≤ C * ((M : ℝ) * 2 ^ j + q) * ((D - j : ℕ) + 3) * (N : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = _ := by ring
  calc
    _ = ∑ j ∈ I, ∑ x ∈ S with Nat.clog 2 x.denominator = j,
        deltaQuadraticMajorant K a q x :=
      (Finset.sum_fiberwise_of_maps_to hmap (deltaQuadraticMajorant K a q)).symm
    _ ≤ ∑ j ∈ I, C * (N : ℝ) ^ ε * ((M : ℝ) * 2 ^ j + q) * ((D - j : ℕ) + 3) :=
      Finset.sum_le_sum hlevel
    _ = (C * (N : ℝ) ^ ε) * ∑ j ∈ I,
        ((M : ℝ) * 2 ^ j + q) * ((D - j : ℕ) + 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (C * (N : ℝ) ^ ε) * ((2 * H + q * (D + 1)) * (D + 3)) :=
      mul_le_mul_of_nonneg_left
        (delta_sum_dyadic_small_cost D (Nat.cast_nonneg M) hH (Nat.cast_nonneg q)) (by positivity)
    _ = _ := by dsimp only [N]; ring

end Erdos587

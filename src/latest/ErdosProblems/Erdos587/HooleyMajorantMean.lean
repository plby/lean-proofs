import ErdosProblems.Erdos587.HooleyMajorantSmallBlocks

/-!
# The quadratic majorant mean with an explicit size margin

The split occurs at the product scale `q * Y`. Above it, every residue
progression has at least `Y` terms and the fixed-power mean applies.
Below it, the subpower divisor estimate has an explicit total cost.
-/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_majorant_mean_with_margin (r : ℕ) (hr : 0 < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M q D Y : ℕ, 0 < q → 16 ≤ Y → M * 2 ^ D ≤ Y ^ r →
      ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ K : ℝ, 0 < K → K ≤ 2 ^ D →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, 0 < x.index ∧ x.index ≤ M) →
      (∀ x ∈ S, 0 < x.denominator ∧ (x.denominator : ℝ) ≤ K) →
      (∀ x ∈ S, deltaApproximantError a q x ≠ 0) →
      (∀ x ∈ S, |deltaApproximantFrequencyError a q x| ≤
        2 / ((x.denominator : ℝ) * K)) →
      (∑ x ∈ S, deltaQuadraticMajorant K a q x) ≤
        C * ((M * 2 ^ D : ℕ) * (max 1 (Real.log (Real.log (M * 2 ^ D : ℕ)))) ^ 7 +
          q * (M * 2 ^ D : ℕ) ^ ε * (2 * Y + D + 1) * (D + 3)) := by
  classical
  obtain ⟨C₀, hC₀, hlarge⟩ := exists_delta_majorant_good_blocks_bound r hr
  obtain ⟨C₁, hC₁, hsmall⟩ := exists_delta_majorant_small_blocks_bound hε
  refine ⟨C₀ + C₁, by positivity, ?_⟩
  intro M q D Y hq hY hNY a hcop K hK hKD S hindex hden hzero herror
  let N := M * 2 ^ D
  let G := S.filter (fun x => q * Y ≤ M * 2 ^ Nat.clog 2 x.denominator)
  let T := S.filter (fun x => ¬q * Y ≤ M * 2 ^ Nat.clog 2 x.denominator)
  have hgood (x : DeltaApproximant) (hx : x ∈ G) :
      let X := M * 2 ^ Nat.clog 2 x.denominator
      16 ≤ X / q ∧ X ≤ (X / q) ^ r := by
    obtain ⟨hxS, hxlarge⟩ := Finset.mem_filter.mp hx
    have hjD := delta_dyadic_denominator_index_le ((hden x hxS).2.trans hKD)
    have hXN : M * 2 ^ Nat.clog 2 x.denominator ≤ M * 2 ^ D := by
      gcongr
      norm_num
    have hYX : Y ≤ M * 2 ^ Nat.clog 2 x.denominator / q :=
      (Nat.le_div_iff_mul_le hq).mpr (by simpa only [mul_comm] using hxlarge)
    exact ⟨hY.trans hYX, hXN.trans (hNY.trans (Nat.pow_le_pow_left hYX r))⟩
  have hcutoff (x : DeltaApproximant) (hx : x ∈ T) :
      (M : ℝ) * 2 ^ Nat.clog 2 x.denominator ≤ (q : ℝ) * Y := by
    have h := Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hx).2)
    exact_mod_cast h
  have hG := hlarge M q D hq a hcop K hK hKD G
    (fun x hx => hindex x (Finset.mem_filter.mp hx).1)
    (fun x hx => hden x (Finset.mem_filter.mp hx).1)
    (fun x hx => hzero x (Finset.mem_filter.mp hx).1)
    (fun x hx => herror x (Finset.mem_filter.mp hx).1) hgood
  have hT := hsmall M q D hq a hcop K ((q : ℝ) * Y) hK hKD (by positivity) T
    (fun x hx => hindex x (Finset.mem_filter.mp hx).1)
    (fun x hx => hden x (Finset.mem_filter.mp hx).1)
    (fun x hx => hzero x (Finset.mem_filter.mp hx).1)
    (fun x hx => herror x (Finset.mem_filter.mp hx).1) hcutoff
  let F := (N : ℝ) * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 7
  let E := (q : ℝ) * (N : ℝ) ^ ε * (2 * Y + D + 1) * (D + 3)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hGF : (∑ x ∈ G, deltaQuadraticMajorant K a q x) ≤ C₀ * F :=
    hG.trans_eq (by dsimp only [F, N]; push_cast; ring)
  have hTE : (∑ x ∈ T, deltaQuadraticMajorant K a q x) ≤ C₁ * E :=
    hT.trans_eq (by dsimp only [E, N]; ring)
  calc
    _ = (∑ x ∈ G, deltaQuadraticMajorant K a q x) +
        ∑ x ∈ T, deltaQuadraticMajorant K a q x := by
      dsimp only [G, T]
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ C₀ * F + C₁ * E := add_le_add hGF hTE
    _ ≤ (C₀ + C₁) * (F + E) := by nlinarith
    _ = _ := rfl

theorem exists_delta_majorant_loglog_mean (r : ℕ) (hr : 0 < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M q D Y : ℕ, 0 < q → 16 ≤ Y → M * 2 ^ D ≤ Y ^ r →
      (q : ℝ) * (M * 2 ^ D : ℕ) ^ ε * (2 * Y + D + 1) * (D + 3) ≤ M * 2 ^ D →
      ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ K : ℝ, 0 < K → K ≤ 2 ^ D →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, 0 < x.index ∧ x.index ≤ M) →
      (∀ x ∈ S, 0 < x.denominator ∧ (x.denominator : ℝ) ≤ K) →
      (∀ x ∈ S, deltaApproximantError a q x ≠ 0) →
      (∀ x ∈ S, |deltaApproximantFrequencyError a q x| ≤
        2 / ((x.denominator : ℝ) * K)) →
      (∑ x ∈ S, deltaQuadraticMajorant K a q x) ≤
        C * (M * 2 ^ D : ℕ) * (max 1 (Real.log (Real.log (M * 2 ^ D : ℕ)))) ^ 7 := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_majorant_mean_with_margin r hr hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro M q D Y hq hY hsize hmargin a hcop K hK hKD S hindex hden hzero herror
  have h := hmean M q D Y hq hY hsize a hcop K hK hKD S hindex hden hzero herror
  have hmargin' : (q : ℝ) * (M * 2 ^ D : ℕ) ^ ε * (2 * Y + D + 1) * (D + 3) ≤
      (M * 2 ^ D : ℕ) := by exact_mod_cast hmargin
  have hF : 1 ≤ (max 1 (Real.log (Real.log (M * 2 ^ D : ℕ)))) ^ 7 :=
    one_le_pow₀ (le_max_left _ _)
  have hNF := mul_le_mul_of_nonneg_left hF (by positivity : (0 : ℝ) ≤ (M * 2 ^ D : ℕ))
  nlinarith

end Erdos587

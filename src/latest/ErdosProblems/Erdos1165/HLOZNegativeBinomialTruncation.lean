/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.ModerateDeviation
import ErdosProblems.Erdos1165.TilingAwayNegativeBinomial

/-!
# A literal lower bound for the truncated HLOZ coordinate law

The stopped insertion fibres use a finite normalization of the geometric
total at each away domino.  This file proves that normalization is at least
one half once the truncation is at least twice the mean.  The proof is the
finite first-moment (Markov) argument applied to the exact negative-binomial
point masses; no path-space probability estimate is assumed.
-/

open scoped BigOperators

namespace Erdos1165.HLOZNegativeBinomialTruncation

open FiniteDominoProductLaw ModerateDeviation NegativeBinomial
open GeometricChernoff
open TilingAwayNegativeBinomial TilingCappedMarginalization
open TilingSpatialInsertionFiber

noncomputable section

/-- Markov's inequality for the explicitly reindexed HLOZ tail. -/
theorem tailMass_mul_le_mean {i k : ℕ} (hi : 0 < i) :
    (k : ℝ) * (∑' j : ℕ, hlozMass i (j + k)) ≤ (i : ℝ) / 15 := by
  let f : ℕ → ℝ := fun j ↦ (k : ℝ) * hlozMass i (j + k)
  let g : ℕ → ℝ := fun j ↦ ((j + k : ℕ) : ℝ) * hlozMass i (j + k)
  have hweighted : Summable (fun j : ℕ ↦ (j : ℝ) * hlozMass i j) :=
    (hasSum_weighted_hlozMass hi).summable
  have hf : Summable f := by
    have htail := (hasSum_hlozMass hi).summable.comp_injective
      (i := fun j : ℕ ↦ j + k) (add_left_injective k)
    simpa only [f, Function.comp_apply] using htail.mul_left (k : ℝ)
  have hg : Summable g :=
    hweighted.comp_injective (i := fun j : ℕ ↦ j + k)
      (add_left_injective k)
  have hfg : ∀ j, f j ≤ g j := by
    intro j
    dsimp only [f, g]
    exact mul_le_mul_of_nonneg_right (by norm_num)
      (hlozMass_nonneg i (j + k))
  have htail := Summable.tsum_le_tsum hfg hf hg
  have hsplit := hweighted.sum_add_tsum_nat_add k
  have hprefix : 0 ≤ ∑ j ∈ Finset.range k,
      (j : ℝ) * hlozMass i j :=
    Finset.sum_nonneg fun j _ ↦
      mul_nonneg (Nat.cast_nonneg _) (hlozMass_nonneg i j)
  calc
    (k : ℝ) * (∑' j : ℕ, hlozMass i (j + k)) = ∑' j, f j := by
      simp only [f, tsum_mul_left]
    _ ≤ ∑' j, g j := htail
    _ ≤ ∑' j : ℕ, (j : ℝ) * hlozMass i j := by
      rw [← hsplit]
      exact le_add_of_nonneg_left hprefix
    _ = (i : ℝ) / 15 := tsum_weighted_hlozMass hi

/-- At a truncation at least twice the mean, the retained finite mass is at
least one half. -/
theorem half_le_sum_range_hlozMass {i k : ℕ} (hi : 0 < i)
    (hk : 0 < k) (hmean : 2 * i ≤ 15 * k) :
    (1 / 2 : ℝ) ≤ ∑ j ∈ Finset.range k, hlozMass i j := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmarkov := tailMass_mul_le_mean (i := i) (k := k) hi
  have htail : (∑' j : ℕ, hlozMass i (j + k)) ≤ 1 / 2 := by
    have hmeanR : (2 : ℝ) * i ≤ 15 * k := by exact_mod_cast hmean
    apply (mul_le_mul_iff_of_pos_left hkR).mp
    nlinarith
  have hsplit := (hasSum_hlozMass hi).summable.sum_add_tsum_nat_add k
  rw [tsum_hlozMass hi] at hsplit
  nlinarith

/-- The literal capped away-coordinate denominator is at least one half.
All raw point masses in the retained prefix are identified with their exact
negative-binomial values before the first-moment estimate is applied. -/
theorem half_le_sum_tilingAwayPointMass
    {retainedCount cap : ℕ} (t : Tilings.Tiling) (x : Point)
    (r : TilingRetainedWord t x retainedCount) (D : Finset Point)
    (b : TilingAwayDomino t x r D) (upper : ℕ)
    (hupper : 0 < upper) (hupperCap : upper ≤ cap + 1)
    (hcoordinates : 0 < Fintype.card (TilingCoordinatesAt t x r b.1))
    (hmean : 2 * Fintype.card (TilingCoordinatesAt t x r b.1) ≤
      15 * upper) :
    (1 / 2 : ℝ) ≤
      ∑ v : Fin upper, tilingAwayPointMass (cap := cap) t x r D b v := by
  rw [Fin.sum_univ_eq_sum_range]
  have heq : ∀ v ∈ Finset.range upper,
      tilingAwayPointMass (cap := cap) t x r D b v =
        hlozMass (Fintype.card (TilingCoordinatesAt t x r b.1)) v := by
    intro v hv
    rw [Finset.mem_range] at hv
    apply tilingAwayPointMass_eq_negativeBinomial
    · omega
    · exact hcoordinates
  calc
    (1 / 2 : ℝ) ≤ ∑ v ∈ Finset.range upper,
        hlozMass (Fintype.card (TilingCoordinatesAt t x r b.1)) v :=
      half_le_sum_range_hlozMass hcoordinates hupper hmean
    _ = ∑ v ∈ Finset.range upper,
        tilingAwayPointMass (cap := cap) t x r D b v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (heq v hv).symm

/-! ## Ambient-scale negative-binomial Chernoff bounds -/

/-- The HLOZ upper tail with a real deviation, using an ambient scale `m`.
Unlike the optimized estimate, the deviation need only be at most `m`, not
at most the number `i` of retained coordinates.  This is the form needed for
the low-external half of Proposition 4.5. -/
theorem upperTailMass_le_exp_neg_ambient
    {m i k : ℕ} {a : ℝ} (hm : 0 < m) (hi : 0 < i) (him : i ≤ m)
    (ha0 : 0 ≤ a) (ham : a ≤ m)
    (hthreshold : (i : ℝ) / 15 + a ≤ k) :
    upperTailMass i k ≤ Real.exp (-(a ^ 2) / (4 * (m : ℝ))) := by
  let u : ℝ := a / (2 * (m : ℝ))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have huHalf : u ≤ 1 / 2 := by
    dsimp only [u]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))]
    nlinarith
  have hexp16 : Real.exp u < 16 := by
    exact lt_of_le_of_lt (exp_le_one_add_add_sq (by
      rw [abs_of_nonneg hu0]
      linarith)) (by nlinarith [sq_nonneg u])
  have hchern := upperTailMass_le_chernoff (i := i) (k := k)
    hi hu0 hexp16
  have hone := centered_geometric15_mgf_le_exp_sq hu0 huHalf
  rw [centered_geometric15_mgf u hexp16] at hone
  have hbase0 : 0 ≤ (15 : ℝ) / (16 - Real.exp u) := by
    exact div_nonneg (by norm_num) (by linarith)
  have hpow : ((Real.exp (-u / 15) *
      ((15 : ℝ) / (16 - Real.exp u))) ^ i) ≤
      Real.exp ((i : ℝ) * u ^ 2) := by
    calc
      _ ≤ (Real.exp (u ^ 2)) ^ i :=
        pow_le_pow_left₀ (mul_nonneg (Real.exp_nonneg _) hbase0) hone i
      _ = Real.exp ((i : ℝ) * u ^ 2) := by rw [← Real.exp_nat_mul]
  have himR : (i : ℝ) ≤ m := by exact_mod_cast him
  calc
    upperTailMass i k ≤
        Real.exp (-u * (k : ℝ)) *
          ((15 : ℝ) / (16 - Real.exp u)) ^ i := hchern
    _ ≤ Real.exp (-u * ((i : ℝ) / 15 + a)) *
          ((15 : ℝ) / (16 - Real.exp u)) ^ i := by
      apply mul_le_mul_of_nonneg_right
      · apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hthreshold (neg_nonpos.mpr hu0)
      · exact pow_nonneg hbase0 _
    _ = Real.exp (-u * a) *
          ((Real.exp (-u / 15) *
            ((15 : ℝ) / (16 - Real.exp u))) ^ i) := by
      rw [mul_add, mul_pow, ← Real.exp_nat_mul, ← mul_assoc,
        ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-u * a) * Real.exp ((i : ℝ) * u ^ 2) := by
      exact mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = Real.exp (-u * a + (i : ℝ) * u ^ 2) := by rw [← Real.exp_add]
    _ ≤ Real.exp (-(a ^ 2) / (4 * (m : ℝ))) := by
      apply Real.exp_le_exp.mpr
      dsimp only [u]
      have haSquare : 0 ≤ a ^ 2 := sq_nonneg a
      field_simp
      nlinarith [mul_nonneg haSquare (sub_nonneg.mpr himR)]

/-- Ambient-scale lower-tail companion to
`upperTailMass_le_exp_neg_ambient`. -/
theorem lowerTailMass_le_exp_neg_ambient
    {m i k : ℕ} {a : ℝ} (hm : 0 < m) (hi : 0 < i) (him : i ≤ m)
    (ha0 : 0 ≤ a) (ham : a ≤ m)
    (hthreshold : (k : ℝ) ≤ (i : ℝ) / 15 - a) :
    lowerTailMass i k ≤ Real.exp (-(a ^ 2) / (4 * (m : ℝ))) := by
  let u : ℝ := a / (2 * (m : ℝ))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have huHalf : u ≤ 1 / 2 := by
    dsimp only [u]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))]
    nlinarith
  have hexp16 : Real.exp (-u) < 16 := by
    calc
      Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu0)
      _ < 16 := by norm_num
  have hchern := lowerTailMass_le_chernoff (i := i) (k := k)
    hi (neg_nonpos.mpr hu0) hexp16
  have hone := centered_geometric15_mgf_neg_le_exp_sq hu0 huHalf
  rw [centered_geometric15_mgf (-u) hexp16] at hone
  have hbase0 : 0 ≤ (15 : ℝ) / (16 - Real.exp (-u)) := by
    exact div_nonneg (by norm_num) (by linarith)
  have hpow : ((Real.exp (u / 15) *
      ((15 : ℝ) / (16 - Real.exp (-u)))) ^ i) ≤
      Real.exp ((i : ℝ) * u ^ 2) := by
    have hone' : Real.exp (u / 15) *
        ((15 : ℝ) / (16 - Real.exp (-u))) ≤ Real.exp (u ^ 2) := by
      rw [show - -u / 15 = u / 15 by ring] at hone
      exact hone
    calc
      _ ≤ (Real.exp (u ^ 2)) ^ i :=
        pow_le_pow_left₀ (mul_nonneg (Real.exp_nonneg _) hbase0) hone' i
      _ = Real.exp ((i : ℝ) * u ^ 2) := by rw [← Real.exp_nat_mul]
  have himR : (i : ℝ) ≤ m := by exact_mod_cast him
  calc
    lowerTailMass i k ≤
        Real.exp (-(-u) * (k : ℝ)) *
          ((15 : ℝ) / (16 - Real.exp (-u))) ^ i := hchern
    _ ≤ Real.exp (u * ((i : ℝ) / 15 - a)) *
          ((15 : ℝ) / (16 - Real.exp (-u))) ^ i := by
      apply mul_le_mul_of_nonneg_right
      · apply Real.exp_le_exp.mpr
        calc
          - -u * (k : ℝ) = u * (k : ℝ) := by ring
          _ ≤ u * ((i : ℝ) / 15 - a) :=
            mul_le_mul_of_nonneg_left hthreshold hu0
      · exact pow_nonneg hbase0 _
    _ = Real.exp (-u * a) *
          ((Real.exp (u / 15) *
            ((15 : ℝ) / (16 - Real.exp (-u)))) ^ i) := by
      rw [mul_sub, mul_pow, ← Real.exp_nat_mul, ← mul_assoc,
        ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-u * a) * Real.exp ((i : ℝ) * u ^ 2) := by
      exact mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = Real.exp (-u * a + (i : ℝ) * u ^ 2) := by rw [← Real.exp_add]
    _ ≤ Real.exp (-(a ^ 2) / (4 * (m : ℝ))) := by
      apply Real.exp_le_exp.mpr
      dsimp only [u]
      have haSquare : 0 ≤ a ^ 2 := sq_nonneg a
      field_simp
      nlinarith [mul_nonneg haSquare (sub_nonneg.mpr himR)]

/-! ## Finite literal windows -/

theorem windowMass_le_upperTailMass {i k : ℕ} (hi : 0 < i)
    (window : Finset ℕ) (hwindow : ∀ v ∈ window, k ≤ v) :
    SmallWindow.windowMass i window ≤ upperTailMass i k := by
  rw [SmallWindow.windowMass, upperTailMass]
  calc
    (∑ v ∈ window, hlozMass i v) =
        ∑ v ∈ window, if k ≤ v then hlozMass i v else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [if_pos (hwindow v hv)]
    _ ≤ ∑' v : ℕ, if k ≤ v then hlozMass i v else 0 :=
      (summable_upperTailMass (i := i) (k := k) hi).sum_le_tsum
        window (fun v _ ↦ by
          split_ifs
          · exact hlozMass_nonneg i v
          · exact le_rfl)

theorem windowMass_le_lowerTailMass {i k : ℕ} (hi : 0 < i)
    (window : Finset ℕ) (hwindow : ∀ v ∈ window, v ≤ k) :
    SmallWindow.windowMass i window ≤ lowerTailMass i k := by
  rw [SmallWindow.windowMass, lowerTailMass]
  calc
    (∑ v ∈ window, hlozMass i v) =
        ∑ v ∈ window, if v ≤ k then hlozMass i v else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [if_pos (hwindow v hv)]
    _ ≤ ∑' v : ℕ, if v ≤ k then hlozMass i v else 0 :=
      (summable_lowerTailMass (i := i) (k := k) hi).sum_le_tsum
        window (fun v _ ↦ by
          split_ifs
          · exact hlozMass_nonneg i v
          · exact le_rfl)

theorem windowMass_le_exp_neg_upper_ambient
    {m i k : ℕ} {a : ℝ} (hm : 0 < m) (hi : 0 < i) (him : i ≤ m)
    (ha0 : 0 ≤ a) (ham : a ≤ m)
    (hthreshold : (i : ℝ) / 15 + a ≤ k)
    (window : Finset ℕ) (hwindow : ∀ v ∈ window, k ≤ v) :
    SmallWindow.windowMass i window ≤
      Real.exp (-(a ^ 2) / (4 * (m : ℝ))) :=
  (windowMass_le_upperTailMass hi window hwindow).trans
    (upperTailMass_le_exp_neg_ambient hm hi him ha0 ham hthreshold)

theorem windowMass_le_exp_neg_lower_ambient
    {m i k : ℕ} {a : ℝ} (hm : 0 < m) (hi : 0 < i) (him : i ≤ m)
    (ha0 : 0 ≤ a) (ham : a ≤ m)
    (hthreshold : (k : ℝ) ≤ (i : ℝ) / 15 - a)
    (window : Finset ℕ) (hwindow : ∀ v ∈ window, v ≤ k) :
    SmallWindow.windowMass i window ≤
      Real.exp (-(a ^ 2) / (4 * (m : ℝ))) :=
  (windowMass_le_lowerTailMass hi window hwindow).trans
    (lowerTailMass_le_exp_neg_ambient hm hi him ha0 ham hthreshold)

/-- Exact raw mass of a finite away-total window below the coordinate cap. -/
theorem sum_tilingAwayPointMass_window
    {retainedCount cap : ℕ} (t : Tilings.Tiling) (x : Point)
    (r : TilingRetainedWord t x retainedCount) (D : Finset Point)
    (b : TilingAwayDomino t x r D) (upper : ℕ) (window : Finset ℕ)
    (hwindowUpper : ∀ v ∈ window, v < upper)
    (hwindowCap : ∀ v ∈ window, v ≤ cap)
    (hcoordinates : 0 < Fintype.card (TilingCoordinatesAt t x r b.1)) :
    (∑ v : Fin upper, if (v : ℕ) ∈ window then
        tilingAwayPointMass (cap := cap) t x r D b v else 0) =
      SmallWindow.windowMass
        (Fintype.card (TilingCoordinatesAt t x r b.1)) window := by
  change (∑ v : Fin upper, (fun n : ℕ ↦ if n ∈ window then
      tilingAwayPointMass (cap := cap) t x r D b n else 0) v) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ if n ∈ window then
    tilingAwayPointMass (cap := cap) t x r D b n else 0) upper,
    SmallWindow.windowMass, ← Finset.sum_filter]
  have hfilter : (Finset.range upper).filter (fun v ↦ v ∈ window) = window := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun hv ↦ hv.2
    · intro hv
      exact ⟨hwindowUpper v hv, hv⟩
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro v hv
  exact tilingAwayPointMass_eq_negativeBinomial t x r D b v
    (hwindowCap v hv) hcoordinates

end

end Erdos1165.HLOZNegativeBinomialTruncation

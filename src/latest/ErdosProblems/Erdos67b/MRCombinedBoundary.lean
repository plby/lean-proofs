import ErdosProblems.Erdos67b.MRFiniteTypicalRamare

/-!
# A common endpoint budget for all narrow Ramaré rectangles

The union of endpoint supports is controlled before taking the mean
square. Grouped coefficients keep their `1/n` bound, so no subblock
count enters the boundary energy.
-/

open scoped BigOperators Interval
open Finset

namespace Erdos67b

noncomputable section

def mrCommonEndpointBands (X : ℕ) (epsilon : ℝ) : Finset ℕ :=
  Finset.Icc (Nat.ceil ((1 - epsilon) * X)) X ∪
    Finset.Ioc (2 * X) (Nat.floor ((1 + epsilon) * (2 * X)))

theorem rectangle_product_real_bounds
    {D S : Finset ℕ} {J : ℕ × ℕ} {X n : ℕ} {epsilon : ℝ}
    (heps0 : 0 ≤ epsilon) (heps1 : epsilon ≤ 1 / 2) (hJ : 0 < J.1)
    (hwidth : (J.2 : ℝ) ≤ (1 + epsilon) * J.1)
    (hD : ∀ p ∈ D, J.1 ≤ p ∧ p ≤ J.2)
    (hS : S ⊆ mrDyadicCofactorRectangle J X) (hn : n ∈ natProductImage D S) :
    (1 - epsilon) * X ≤ (n : ℝ) ∧ (n : ℝ) ≤ (1 + epsilon) * (2 * X) := by
  obtain ⟨⟨p, m⟩, hpm, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp, hm⟩ := Finset.mem_product.mp hpm
  have hpB := hD p hp
  have hU : 0 < J.2 := (hJ.trans_le hpB.1).trans_le hpB.2
  obtain ⟨hmlo, hmhi⟩ := Finset.mem_Ioc.mp (hS hm)
  have hlow : (X : ℝ) < (m : ℝ) * J.2 := by
    exact_mod_cast (Nat.div_lt_iff_lt_mul hU).mp hmlo
  have hhigh : (m : ℝ) * J.1 ≤ 2 * X := by
    exact_mod_cast (Nat.le_div_iff_mul_le hJ).mp hmhi
  have hpL : (J.1 : ℝ) ≤ p := by exact_mod_cast hpB.1
  have hpU : (p : ℝ) ≤ J.2 := by exact_mod_cast hpB.2
  have hXn : (X : ℝ) ≤ (1 + epsilon) * ((p : ℝ) * m) := by
    calc
      _ ≤ (m : ℝ) * J.2 := hlow.le
      _ ≤ (m : ℝ) * ((1 + epsilon) * J.1) :=
        mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg _)
      _ ≤ (m : ℝ) * ((1 + epsilon) * p) := by gcongr
      _ = _ := by ring
  constructor
  · push_cast
    have hh := mul_le_mul_of_nonneg_left hXn (show 0 ≤ 1 - epsilon by linarith)
    have hsq := mul_nonneg (sq_nonneg epsilon) (show 0 ≤ (p : ℝ) * m by positivity)
    nlinarith
  · push_cast
    calc
      _ ≤ (J.2 : ℝ) * m := mul_le_mul_of_nonneg_right hpU (Nat.cast_nonneg _)
      _ ≤ ((1 + epsilon) * J.1) * m := mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg _)
      _ = (1 + epsilon) * ((m : ℝ) * J.1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hhigh (by positivity)

theorem mem_mrCommonEndpointBands_of_bounds
    {X n : ℕ} {epsilon : ℝ}
    (hlo : (1 - epsilon) * X ≤ (n : ℝ))
    (hhi : (n : ℝ) ≤ (1 + epsilon) * (2 * X))
    (hout : n ∉ Finset.Ioc X (2 * X)) : n ∈ mrCommonEndpointBands X epsilon := by
  apply Finset.mem_union.mpr
  by_cases hnX : n ≤ X
  · exact Or.inl (Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, hnX⟩)
  · right
    have hnhi : 2 * X < n := by
      simp only [Finset.mem_Ioc] at hout
      omega
    exact Finset.mem_Ioc.mpr ⟨hnhi, Nat.le_floor hhi⟩

theorem mrCommonEndpointBands_outside
    {X n : ℕ} {epsilon : ℝ} (hn : n ∈ mrCommonEndpointBands X epsilon) :
    n ∉ Finset.Ioc X (2 * X) := by
  intro hin
  rcases Finset.mem_union.mp hn with hlo | hhi
  · exact (not_lt_of_ge (Finset.mem_Icc.mp hlo).2) (Finset.mem_Ioc.mp hin).1
  · exact (not_lt_of_ge (Finset.mem_Ioc.mp hin).2) (Finset.mem_Ioc.mp hhi).1

theorem mrCommonEndpointBands_real_bounds
    {X n : ℕ} {epsilon : ℝ} (heps0 : 0 ≤ epsilon) (heps1 : epsilon ≤ 1 / 2)
    (hn : n ∈ mrCommonEndpointBands X epsilon) :
    (X : ℝ) / 2 ≤ n ∧ n ≤ 3 * X := by
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hlow : (X : ℝ) / 2 ≤ (1 - epsilon) * X := by nlinarith
  have hhigh : (1 + epsilon) * (2 * X : ℕ) ≤ (3 * X : ℕ) := by
    push_cast
    nlinarith
  rcases Finset.mem_union.mp hn with hnlo | hnhi
  · obtain ⟨hL, hR⟩ := Finset.mem_Icc.mp hnlo
    have hnr : (Nat.ceil ((1 - epsilon) * X) : ℝ) ≤ n := by exact_mod_cast hL
    refine ⟨hlow.trans ((Nat.le_ceil _).trans hnr), ?_⟩
    omega
  · obtain ⟨hL, hR⟩ := Finset.mem_Ioc.mp hnhi
    have hnlo : (2 * X : ℕ) ≤ n := hL.le
    have hnr : (n : ℝ) ≤ Nat.floor ((1 + epsilon) * (2 * X)) := by exact_mod_cast hR
    have hfloor := Nat.floor_le (show 0 ≤ (1 + epsilon) * (2 * (X : ℝ)) by positivity)
    have hnupper : (n : ℝ) ≤ (3 * X : ℕ) := (hnr.trans hfloor).trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hhigh)
    refine ⟨?_, by exact_mod_cast hnupper⟩
    have hh : (2 * X : ℝ) ≤ n := by exact_mod_cast hnlo
    linarith

theorem card_mrCommonEndpointBands_le
    {X : ℕ} {epsilon : ℝ} (heps0 : 0 ≤ epsilon) :
    ((mrCommonEndpointBands X epsilon).card : ℝ) ≤ 3 * epsilon * X + 1 := by
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hceil : Nat.ceil ((1 - epsilon) * X) ≤ X := Nat.ceil_le.mpr (by nlinarith)
  have hfloor : 2 * X ≤ Nat.floor ((1 + epsilon) * (2 * X)) := by
    apply Nat.le_floor
    push_cast
    nlinarith
  have hleft : ((Finset.Icc (Nat.ceil ((1 - epsilon) * X)) X).card : ℝ) ≤ epsilon * X + 1 := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega)]
    push_cast
    have hh := Nat.le_ceil ((1 - epsilon) * X)
    nlinarith
  have hright : ((Finset.Ioc (2 * X) (Nat.floor ((1 + epsilon) * (2 * X)))).card : ℝ) ≤
      2 * epsilon * X := by
    rw [Nat.card_Ioc, Nat.cast_sub hfloor]
    push_cast
    have hh := Nat.floor_le (show 0 ≤ (1 + epsilon) * (2 * (X : ℝ)) by positivity)
    nlinarith
  have hcard := Finset.card_union_le
    (Finset.Icc (Nat.ceil ((1 - epsilon) * X)) X)
    (Finset.Ioc (2 * X) (Nat.floor ((1 + epsilon) * (2 * X))))
  have hcardr : ((mrCommonEndpointBands X epsilon).card : ℝ) ≤
      ((Finset.Icc (Nat.ceil ((1 - epsilon) * X)) X).card : ℝ) +
        ((Finset.Ioc (2 * X) (Nat.floor ((1 + epsilon) * (2 * X)))).card : ℝ) := by
    unfold mrCommonEndpointBands
    exact_mod_cast hcard
  linarith

/-- Mean square on the common thin endpoint bands, with no factor for
the number of narrow prime intervals. -/
theorem intervalIntegral_commonEndpointBands_le
    {A : Finset ℕ} {a : ℕ → ℂ} {X : ℕ} (hX : 0 < X)
    {epsilon : ℝ} (heps0 : 0 ≤ epsilon) (heps1 : epsilon ≤ 1 / 2)
    (hA : A ⊆ mrCommonEndpointBands X epsilon)
    (ha : ∀ n ∈ A, ‖a n‖ ≤ (n : ℝ)⁻¹)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖logarithmicDirichletPolynomial A a t‖ ^ 2) ≤
      32 * (1 + Real.pi) * (T / X + 1) * (3 * epsilon + 1 / X) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hApos (n : ℕ) (hn : n ∈ A) : 0 < n := by
    have hh := (mrCommonEndpointBands_real_bounds heps0 heps1 (hA hn)).1
    have hnreal : (0 : ℝ) < n := (show (0 : ℝ) < (X : ℝ) / 2 by positivity).trans_le hh
    exact_mod_cast hnreal
  have hAhi (n : ℕ) (hn : n ∈ A) : n ≤ 3 * X :=
    (mrCommonEndpointBands_real_bounds heps0 heps1 (hA hn)).2
  have hcard : (A.card : ℝ) ≤ 3 * epsilon * X + 1 := by
    have hh : (A.card : ℝ) ≤ (mrCommonEndpointBands X epsilon).card :=
      Nat.cast_le.mpr (Finset.card_le_card hA)
    exact hh.trans (card_mrCommonEndpointBands_le heps0)
  have hmass : (∑ n ∈ A, Complex.normSq (a n)) ≤ (3 * epsilon * X + 1) * ((2 : ℝ) / X) ^ 2 := by
    calc
      _ ≤ ∑ _n ∈ A, ((2 : ℝ) / X) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hinv := inv_anti₀ (show (0 : ℝ) < (X : ℝ) / 2 by positivity)
          (mrCommonEndpointBands_real_bounds heps0 heps1 (hA hn)).1
        have hinveq : ((X : ℝ) / 2)⁻¹ = 2 / X := by field_simp
        have hinv' : (n : ℝ)⁻¹ ≤ 2 / X := by simpa only [hinveq] using hinv
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) ((ha n hn).trans hinv') 2
      _ = (A.card : ℝ) * ((2 : ℝ) / X) ^ 2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  have htau : 0 ≤ T / X := by positivity
  have hscalar : 8 * (T / X + 3 * Real.pi) ≤ 32 * (1 + Real.pi) * (T / X + 1) := by
    nlinarith [Real.pi_pos, mul_nonneg htau Real.pi_pos.le]
  calc
    _ = ‖∫ t in -T..T,
        star (logarithmicDirichletPolynomial A a t) * logarithmicDirichletPolynomial A a t‖ :=
      intervalIntegral_norm_sq_eq_norm_conj_mul_self _ hT
    _ ≤ (2 * T + 2 * Real.pi * (3 * X : ℕ)) * ∑ n ∈ A, Complex.normSq (a n) :=
      norm_logarithmicDirichletPolynomial_intervalIntegral_le_support (by omega) hApos hAhi a hT
    _ ≤ (2 * T + 2 * Real.pi * (3 * X : ℕ)) * ((3 * epsilon * X + 1) * ((2 : ℝ) / X) ^ 2) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (8 * (T / X + 3 * Real.pi)) * (3 * epsilon + 1 / X) := by
      push_cast
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscalar (by positivity)

/-- Each typical subblock boundary lies in the same two endpoint bands
when its prime interval has a common relative width. -/
theorem mrTypicalRamareBoundarySupport_subset_common
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) {J : ℕ × ℕ} {D : Finset ℕ} {X : ℕ}
    {epsilon : ℝ} (heps0 : 0 ≤ epsilon) (heps1 : epsilon ≤ 1 / 2)
    (hJ : 0 < J.1) (hwidth : (J.2 : ℝ) ≤ (1 + epsilon) * J.1)
    (hD : ∀ p ∈ D, J.1 ≤ p ∧ p ≤ J.2) :
    mrTypicalRamareBoundarySupport blocks I J D X ⊆ mrCommonEndpointBands X epsilon := by
  intro n hn
  obtain ⟨hnprod, hnout⟩ := Finset.mem_sdiff.mp hn
  have hh := rectangle_product_real_bounds heps0 heps1 hJ hwidth hD
    (mrTypicalCofactorRectangle_subset blocks I J X) hnprod
  exact mem_mrCommonEndpointBands_of_bounds hh.1 hh.2 hnout

/-- All boundaries combine into one polynomial on the common endpoint
bands, with the grouped rectangle coefficient. -/
theorem sum_mrTypicalRamareBoundaryPolynomial_eq_common
    {ι : Type*} (V : Finset ι) (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ)
    (J : ι → ℕ × ℕ) (D : ι → Finset ℕ) (f : ℕ → ℂ) (X : ℕ)
    {epsilon : ℝ} (heps0 : 0 ≤ epsilon) (heps1 : epsilon ≤ 1 / 2)
    (hJ : ∀ v ∈ V, 0 < (J v).1)
    (hwidth : ∀ v ∈ V, ((J v).2 : ℝ) ≤ (1 + epsilon) * (J v).1)
    (hD : ∀ v ∈ V, ∀ p ∈ D v, (J v).1 ≤ p ∧ p ≤ (J v).2)
    (t : ℝ) :
    (∑ v ∈ V, mrTypicalRamareBoundaryPolynomial blocks I (J v) (D v) f X t) =
      logarithmicDirichletPolynomial (mrCommonEndpointBands X epsilon)
        (fun n ↦ ∑ v ∈ V, mrFiniteRamareSubblockRectangleCoefficient (primesInBlock I) (D v)
          (mrTypicalCofactorRectangle blocks I (J v) X) f n) t := by
  classical
  let c (v : ι) := mrFiniteRamareSubblockRectangleCoefficient (primesInBlock I) (D v)
    (mrTypicalCofactorRectangle blocks I (J v) X) f
  have hv (v : ι) (hv : v ∈ V) :
      mrTypicalRamareBoundaryPolynomial blocks I (J v) (D v) f X t =
        logarithmicDirichletPolynomial (mrCommonEndpointBands X epsilon) (c v) t := by
    unfold mrTypicalRamareBoundaryPolynomial logarithmicDirichletPolynomial
    apply Finset.sum_subset
      (mrTypicalRamareBoundarySupport_subset_common blocks I heps0 heps1 (hJ v hv) (hwidth v hv) (hD v hv))
    intro n hnK hnnot
    have hnprod : n ∉ natProductImage (D v) (mrTypicalCofactorRectangle blocks I (J v) X) := by
      intro hnprod
      exact hnnot (Finset.mem_sdiff.mpr ⟨hnprod, mrCommonEndpointBands_outside hnK⟩)
    change finiteProductCoefficient _ _ _ _ n * _ = 0
    rw [finiteProductCoefficient_eq_zero_of_not_mem hnprod, zero_mul]
  calc
    _ = ∑ v ∈ V, logarithmicDirichletPolynomial (mrCommonEndpointBands X epsilon) (c v) t :=
      Finset.sum_congr rfl hv
    _ = _ := by
      unfold logarithmicDirichletPolynomial
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul, c]

/-- The combined boundary energy has no subblock-count loss. -/
theorem intervalIntegral_sum_mrTypicalRamareBoundaryPolynomial_le
    {ι : Type*} (V : Finset ι) (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ)
    (J : ι → ℕ × ℕ) (D : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {X : ℕ} (hX : 0 < X)
    {epsilon : ℝ} (heps0 : 0 ≤ epsilon) (heps1 : epsilon ≤ 1 / 2)
    (hJ : ∀ v ∈ V, 0 < (J v).1)
    (hwidth : ∀ v ∈ V, ((J v).2 : ℝ) ≤ (1 + epsilon) * (J v).1)
    (hD : ∀ v ∈ V, ∀ p ∈ D v, (J v).1 ≤ p ∧ p ≤ (J v).2)
    (hDP : ∀ v ∈ V, D v ⊆ primesInBlock I) (hdisj : Set.PairwiseDisjoint (↑V) D)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖∑ v ∈ V, mrTypicalRamareBoundaryPolynomial blocks I (J v) (D v) f X t‖ ^ 2) ≤
      32 * (1 + Real.pi) * (T / X + 1) * (3 * epsilon + 1 / X) := by
  simp_rw [sum_mrTypicalRamareBoundaryPolynomial_eq_common V blocks I J D f X heps0 heps1 hJ hwidth hD]
  apply intervalIntegral_commonEndpointBands_le hX heps0 heps1 (Finset.Subset.refl _) ?_ hT
  intro n hn
  have hnlo := (mrCommonEndpointBands_real_bounds heps0 heps1 hn).1
  have hn0 : 0 < n := by
    have hnr : (0 : ℝ) < n := (show (0 : ℝ) < (X : ℝ) / 2 by positivity).trans_le hnlo
    exact_mod_cast hnr
  exact norm_sum_mrFiniteRamareSubblockRectangleCoefficient_le_inv
    (fun p hp ↦ (mem_primesInBlock.mp hp).1) hDP hdisj hbound hn0

end

end Erdos67b

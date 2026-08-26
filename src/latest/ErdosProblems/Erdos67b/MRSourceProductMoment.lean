import ErdosProblems.Erdos67b.MRPrimeCofactorMoment

/-!
# The source product moment with real block parameters

This discharges the ceiling and support bookkeeping in the MR moment
lemma. The finite cofactor remains arbitrary; its coefficients need not
be multiplicative or associated with the prime block.
-/

open scoped BigOperators Interval
open Finset

namespace Erdos67b

theorem primePowerSupport_real_bounds {P : Finset ℕ} {L U : ℝ} {k n : ℕ}
    (hL : 0 ≤ L) (hPlo : ∀ p ∈ P, L ≤ p) (hPhi : ∀ p ∈ P, (p : ℝ) ≤ U)
    (hn : n ∈ primePowerSupport P k) : L ^ k ≤ (n : ℝ) ∧ (n : ℝ) ≤ U ^ k := by
  classical
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hn
  have hprod : (tupleFromProduct v : ℝ) = ∏ i : Fin k, ((v i : ℕ) : ℝ) := by
    simp only [tupleFromProduct, tupleProduct, Nat.cast_prod]
  rw [hprod]
  constructor
  · calc
      L ^ k = ∏ _i : Fin k, L := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ hL) (fun i _ ↦ hPlo (v i) (v i).2)
  · calc
      _ ≤ ∏ _i : Fin k, U := Finset.prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _)
        (fun i _ ↦ hPhi (v i) (v i).2)
      _ = U ^ k := by simp

/-- The source ceiling power lies between the target scale and one
additional prime-band factor. -/
theorem ceil_log_ratio_power_bounds {Y Z : ℝ} (hY : 1 < Y) (hZ : 1 ≤ Z) :
    Z ≤ Y ^ (Nat.ceil (Real.log Z / Real.log Y)) ∧
      Y ^ (Nat.ceil (Real.log Z / Real.log Y)) ≤ Y * Z := by
  have hY0 : 0 < Y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hr : 0 ≤ Real.log Z / Real.log Y := div_nonneg (Real.log_nonneg hZ) hlog.le
  constructor
  · apply (Real.log_le_log_iff hZ0 (pow_pos hY0 _)).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ hlog).mp (Nat.le_ceil (Real.log Z / Real.log Y))
  · apply (Real.log_le_log_iff (pow_pos hY0 _) (mul_pos hY0 hZ0)).mp
    rw [Real.log_pow, Real.log_mul hY0.ne' hZ0.ne']
    have hc := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hr).le hlog.le
    rw [add_mul, div_mul_cancel₀ _ hlog.ne', one_mul] at hc
    linarith

/-- Rounding a real dyadic prime band upwards keeps it in an integer
dyadic band, without widening the uniform divisor constant. -/
theorem real_dyadic_prime_band_subset_ceil {P : Finset ℕ} {Y : ℝ}
    (hY : 2 ≤ Y) (hlo : ∀ p ∈ P, Y ≤ p) (hhi : ∀ p ∈ P, (p : ℝ) ≤ 2 * Y) :
    2 ≤ Nat.ceil Y ∧ P ⊆ Finset.Icc (Nat.ceil Y) (2 * Nat.ceil Y) := by
  have hceil : Y ≤ (Nat.ceil Y : ℝ) := Nat.le_ceil Y
  refine ⟨by exact_mod_cast hY.trans hceil, ?_⟩
  intro p hp
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.ceil_le.mpr (hlo p hp), ?_⟩
  have hbound : (p : ℝ) ≤ 2 * (Nat.ceil Y : ℝ) := (hhi p hp).trans (by linarith)
  exact_mod_cast hbound

/-- The product moment for any power-of-two cofactor width, with
explicit constants and all real endpoint rounding discharged. -/
theorem primeCofactorPolynomial_powerWidth_intervalIntegral_le
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {a b : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    {Y Z : ℝ} (hY : 2 ≤ Y) (hZ : 1 ≤ Z)
    (hPlo : ∀ p ∈ P, Y ≤ p) (hPhi : ∀ p ∈ P, (p : ℝ) ≤ 2 * Y)
    {X width : ℕ} (hX : 0 < X)
    (hSlo : ∀ m ∈ S, (X : ℝ) / Z ≤ m)
    (hShi : ∀ m ∈ S, (m : ℝ) ≤ (2 : ℝ) ^ width * X / Z)
    {k : ℕ} (hk : k = Nat.ceil (Real.log Z / Real.log Y))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
      ‖logarithmicDirichletPolynomial P a t ^ k * logarithmicDirichletPolynomial S b t‖ ^ 2) ≤
      8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 *
        (T / X + Real.pi * 2 ^ (k + width + 1) * Y) := by
  have hY0 : 0 < Y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpower : Z ≤ Y ^ k ∧ Y ^ k ≤ Y * Z := by
    rw [hk]
    exact ceil_log_ratio_power_bounds (by linarith) hZ
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    have hmpos : (0 : ℝ) < m := (div_pos hXr hZ0).trans_le (hSlo m hm)
    exact_mod_cast hmpos
  let B : ℝ := 2 ^ (k + width) * Y * X
  let N : ℕ := Nat.ceil B
  have hB1 : 1 ≤ B := by
    have hp : (1 : ℝ) ≤ 2 ^ (k + width) := one_le_pow₀ (by norm_num)
    dsimp only [B]
    have hY1 : (1 : ℝ) ≤ Y := by linarith
    calc
      1 = (1 : ℝ) * 1 * 1 := by norm_num
      _ ≤ 2 ^ (k + width) * Y * X := by gcongr
  have hN : 0 < N := by
    have hNreal : (0 : ℝ) < N := lt_of_lt_of_le (by linarith : (0 : ℝ) < B) (Nat.le_ceil B)
    exact_mod_cast hNreal
  have hD : natProductImage (primePowerSupport P k) S ⊆ Finset.Icc X N := by
    intro n hn
    obtain ⟨⟨d, m⟩, hdm, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hd, hm⟩ := Finset.mem_product.mp hdm
    have hdB := primePowerSupport_real_bounds hY0.le hPlo hPhi hd
    have hlo : (X : ℝ) ≤ (d : ℝ) * m := by
      calc
        (X : ℝ) = Z * ((X : ℝ) / Z) := by field_simp
        _ ≤ Y ^ k * ((X : ℝ) / Z) := mul_le_mul_of_nonneg_right hpower.1 (by positivity)
        _ ≤ (d : ℝ) * m := mul_le_mul hdB.1 (hSlo m hm) (by positivity) (by positivity)
    have hhi : (d : ℝ) * m ≤ B := by
      calc
        _ ≤ (2 * Y) ^ k * (2 ^ width * X / Z) :=
          mul_le_mul hdB.2 (hShi m hm) (by positivity) (by positivity)
        _ = 2 ^ k * Y ^ k * (2 ^ width * X / Z) := by rw [mul_pow]
        _ ≤ 2 ^ k * (Y * Z) * (2 ^ width * X / Z) := by gcongr; exact hpower.2
        _ = B := by dsimp only [B]; rw [pow_add]; field_simp
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo,
      by exact_mod_cast hhi.trans (Nat.le_ceil B)⟩
  obtain ⟨hceilY, hband⟩ := real_dyadic_prime_band_subset_ceil hY hPlo hPhi
  have hmoment := primeCofactorPolynomial_dyadic_intervalIntegral_le hP hSpos ha hb
    hceilY hband hX hN hD hT
  have hNupper : (N : ℝ) ≤ 2 * B := by
    have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ B)
    change (Nat.ceil B : ℝ) ≤ 2 * B
    linarith
  have hratio : Real.pi * (N : ℝ) / X ≤ Real.pi * 2 ^ (k + width + 1) * Y := by
    calc
      _ ≤ Real.pi * (2 * B) / X := by gcongr
      _ = _ := by
        dsimp only [B]
        rw [pow_succ]
        field_simp
  exact hmoment.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hratio) (by positivity))

/-- The original MR source-width moment, preserved as the width-one
specialization of the generalized cofactor estimate. -/
theorem primeCofactorPolynomial_source_intervalIntegral_le
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {a b : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    {Y Z : ℝ} (hY : 2 ≤ Y) (hZ : 1 ≤ Z)
    (hPlo : ∀ p ∈ P, Y ≤ p) (hPhi : ∀ p ∈ P, (p : ℝ) ≤ 2 * Y)
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ m ∈ S, (X : ℝ) / Z ≤ m)
    (hShi : ∀ m ∈ S, (m : ℝ) ≤ 2 * X / Z)
    {k : ℕ} (hk : k = Nat.ceil (Real.log Z / Real.log Y))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
      ‖logarithmicDirichletPolynomial P a t ^ k * logarithmicDirichletPolynomial S b t‖ ^ 2) ≤
      8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 * (T / X + Real.pi * 2 ^ (k + 2) * Y) := by
  simpa only [Nat.add_assoc] using
    primeCofactorPolynomial_powerWidth_intervalIntegral_le hP ha hb hY hZ hPlo hPhi hX hSlo
      (width := 1) (by simpa only [pow_one] using hShi) hk hT

end Erdos67b

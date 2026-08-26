import ErdosProblems.Erdos67b.MRPrimeCofactorCoefficient
import ErdosProblems.Erdos67b.MRLinearMeanTail

/-!
# The cross-block prime-cofactor moment

This is the finite product-moment input to the multiscale frequency
argument. It retains the inverse lower support scale and permits an
arbitrary cofactor polynomial, independent of the prime band.
-/

open scoped BigOperators ComplexConjugate Interval
open Finset

namespace Erdos67b

noncomputable section

theorem bandReciprocalEuler_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    0 ≤ bandReciprocalEuler P := by
  simpa [bandFactoredPrefix] using sum_bandFactoredPrefix_reciprocal_le P hP 0

/-- Weighted divisor tail, proved from the uniform Euler-product mean. -/
theorem sum_bandDivisorCount_sq_div_sq_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {X : ℕ} (hX : 0 < X) (N : ℕ) :
    (∑ n ∈ Finset.Icc X N, (bandDivisorCount P n : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤
      4 * bandReciprocalEuler P ^ 3 / X := by
  apply sum_Icc_div_sq_le_four_of_prefix (fun _ ↦ sq_nonneg _)
    (pow_nonneg (bandReciprocalEuler_nonneg hP) 3) ?_ hX N
  intro M
  simpa only [mul_comm] using sum_bandDivisorCount_sq_le_euler P hP M

/-- Coefficient square mass on any finite segment, with a factorial
constant and the required inverse lower endpoint. -/
theorem sum_normSq_primeCofactorCoefficient_le
    {P S D : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {a b : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    {X N : ℕ} (hX : 0 < X) (hD : D ⊆ Finset.Icc X N) (k : ℕ) :
    (∑ n ∈ D, Complex.normSq (primeCofactorCoefficient P S a b k n)) ≤
      4 * bandReciprocalEuler P ^ 3 * (k.factorial : ℝ) ^ 2 / X := by
  have hpoint (n : ℕ) (hn : n ∈ D) :
      Complex.normSq (primeCofactorCoefficient P S a b k n) ≤
        (k.factorial : ℝ) ^ 2 * ((bandDivisorCount P n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
    have hnpos : 0 < n := hX.trans_le (Finset.mem_Icc.mp (hD hn)).1
    have hnorm := norm_primeCofactorCoefficient_le hP ha hb k hnpos
    rw [Complex.normSq_eq_norm_sq]
    calc
      _ ≤ ((k.factorial : ℝ) * bandDivisorCount P n / n) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ D, (k.factorial : ℝ) ^ 2 *
        ((bandDivisorCount P n : ℝ) ^ 2 / (n : ℝ) ^ 2) := Finset.sum_le_sum hpoint
    _ ≤ ∑ n ∈ Finset.Icc X N, (k.factorial : ℝ) ^ 2 *
        ((bandDivisorCount P n : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hD (fun _ _ _ ↦ by positivity)
    _ = (k.factorial : ℝ) ^ 2 *
        ∑ n ∈ Finset.Icc X N, (bandDivisorCount P n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (k.factorial : ℝ) ^ 2 * (4 * bandReciprocalEuler P ^ 3 / X) :=
      mul_le_mul_of_nonneg_left (sum_bandDivisorCount_sq_div_sq_le hP hX N) (sq_nonneg _)
    _ = _ := by ring

/-- Exact multiplication identity on the actual product support. -/
theorem primeCofactorPolynomial_eq
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ m ∈ S, 0 < m) (a b : ℕ → ℂ) (k : ℕ) (t : ℝ) :
    logarithmicDirichletPolynomial P a t ^ k * logarithmicDirichletPolynomial S b t =
      logarithmicDirichletPolynomial (natProductImage (primePowerSupport P k) S)
        (primeCofactorCoefficient P S a b k) t := by
  rw [logarithmicDirichletPolynomial_pow_eq_primePowerSupport hP]
  exact logarithmicDirichletPolynomial_mul_eq_product
    (fun _ hn ↦ primePowerSupport_pos hP hn) hS _ _ t

/-- Complex integral form of the product moment, with explicit support
endpoints. No cofactor multiplicativity hypothesis occurs. -/
theorem norm_primeCofactorPolynomial_intervalIntegral_le
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ m ∈ S, 0 < m)
    {a b : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    {X N k : ℕ} (hX : 0 < X) (hN : 0 < N)
    (hD : natProductImage (primePowerSupport P k) S ⊆ Finset.Icc X N)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
      conj (logarithmicDirichletPolynomial P a t ^ k * logarithmicDirichletPolynomial S b t) *
        (logarithmicDirichletPolynomial P a t ^ k * logarithmicDirichletPolynomial S b t)‖ ≤
      8 * bandReciprocalEuler P ^ 3 * (k.factorial : ℝ) ^ 2 *
        (T / X + Real.pi * N / X) := by
  have hpos : ∀ n ∈ natProductImage (primePowerSupport P k) S, 0 < n :=
    fun n hn ↦ hX.trans_le (Finset.mem_Icc.mp (hD hn)).1
  have hupper : ∀ n ∈ natProductImage (primePowerSupport P k) S, n ≤ N :=
    fun n hn ↦ (Finset.mem_Icc.mp (hD hn)).2
  simp_rw [primeCofactorPolynomial_eq hP hS]
  calc
    _ ≤ (2 * T + 2 * Real.pi * (N : ℝ)) *
        ∑ n ∈ natProductImage (primePowerSupport P k) S,
          Complex.normSq (primeCofactorCoefficient P S a b k n) :=
      norm_logarithmicDirichletPolynomial_intervalIntegral_le hN hpos hupper _ hT
    _ ≤ (2 * T + 2 * Real.pi * (N : ℝ)) *
        (4 * bandReciprocalEuler P ^ 3 * (k.factorial : ℝ) ^ 2 / X) :=
      mul_le_mul_of_nonneg_left (sum_normSq_primeCofactorCoefficient_le hP ha hb hX hD k)
        (by positivity)
    _ = _ := by ring

/-- Real nonnegative form of the same moment estimate. -/
theorem primeCofactorPolynomial_intervalIntegral_le
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ m ∈ S, 0 < m)
    {a b : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    {X N k : ℕ} (hX : 0 < X) (hN : 0 < N)
    (hD : natProductImage (primePowerSupport P k) S ⊆ Finset.Icc X N)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
      ‖logarithmicDirichletPolynomial P a t ^ k * logarithmicDirichletPolynomial S b t‖ ^ 2) ≤
      8 * bandReciprocalEuler P ^ 3 * (k.factorial : ℝ) ^ 2 *
        (T / X + Real.pi * N / X) := by
  let F := fun t ↦ logarithmicDirichletPolynomial P a t ^ k *
    logarithmicDirichletPolynomial S b t
  have hnonneg : 0 ≤ ∫ t in -T..T, ‖F t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ ↦ sq_nonneg _)
  have hid : (∫ t in -T..T, conj (F t) * F t) =
      ((∫ t in -T..T, ‖F t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hbound := norm_primeCofactorPolynomial_intervalIntegral_le hP hS ha hb hX hN hD hT
  change ‖∫ t in -T..T, conj (F t) * F t‖ ≤ _ at hbound
  rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hbound
  exact hbound

/-- Multiplying finite support bounds preserves both endpoints. -/
theorem primeCofactorProductSupport_subset
    {P S : Finset ℕ} {L U M V k : ℕ}
    (hPlo : ∀ p ∈ P, L ≤ p) (hPhi : ∀ p ∈ P, p ≤ U)
    (hSlo : ∀ m ∈ S, M ≤ m) (hShi : ∀ m ∈ S, m ≤ V) :
    natProductImage (primePowerSupport P k) S ⊆ Finset.Icc (L ^ k * M) (U ^ k * V) := by
  intro n hn
  obtain ⟨⟨d, m⟩, hdm, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hd, hm⟩ := Finset.mem_product.mp hdm
  have hdBounds := primePowerSupport_bounds hPlo hPhi hd
  exact Finset.mem_Icc.mpr ⟨Nat.mul_le_mul hdBounds.1 (hSlo m hm),
    Nat.mul_le_mul hdBounds.2 (hShi m hm)⟩

/-- A uniform explicit constant for a dyadic prime band. -/
theorem primeCofactorPolynomial_dyadic_intervalIntegral_le
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ m ∈ S, 0 < m)
    {a b : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    {Y X N k : ℕ} (hY : 2 ≤ Y) (hPY : P ⊆ Finset.Icc Y (2 * Y))
    (hX : 0 < X) (hN : 0 < N)
    (hD : natProductImage (primePowerSupport P k) S ⊆ Finset.Icc X N)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
      ‖logarithmicDirichletPolynomial P a t ^ k * logarithmicDirichletPolynomial S b t‖ ^ 2) ≤
      8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 * (T / X + Real.pi * N / X) := by
  have hE : bandReciprocalEuler P ≤ Real.exp 4 :=
    (bandReciprocalEuler_le_exp P hP).trans (Real.exp_le_exp.mpr (by
      have hm := reciprocal_sum_le_two_of_dyadic_subset hY hPY
      linarith))
  have hcube : bandReciprocalEuler P ^ 3 ≤ Real.exp 12 := by
    have hc := pow_le_pow_left₀ (bandReciprocalEuler_nonneg hP) hE 3
    have heq : Real.exp 4 ^ 3 = Real.exp 12 := by rw [← Real.exp_nat_mul]; norm_num
    rwa [heq] at hc
  apply (primeCofactorPolynomial_intervalIntegral_le hP hS ha hb hX hN hD hT).trans
  gcongr

end

end Erdos67b

import ErdosProblems.Erdos4.DivisorCoefficients

/-!
# A weighted bound for the nonprincipal local Fourier matrix

The local matrix is a sum of differences of rank-one evaluation matrices.
Parseval bounds each occupied evaluation vector. After the divisor weights
are inserted, its weighted entry norm is at most `20 * k^3 / ell`.
-/

open scoped BigOperators

namespace Erdos4.LocalFourier

open LocalOrthogonality DivisorCoefficients

variable {k : ℕ}

theorem sqrt_mul_localWeight_le_two {ell : ℕ} (hell : 2 ≤ ell) (i : Fin k) :
    Real.sqrt (ell : ℝ) * localWeight ell (some i) ≤ 2 := by
  have hel : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hd : 0 < Real.sqrt ((ell : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hs := Real.sq_sqrt (show 0 ≤ (ell : ℝ) by positivity)
  have hds := Real.sq_sqrt (show 0 ≤ (ell : ℝ) - 1 by linarith)
  have hh : Real.sqrt (ell : ℝ) ≤ 2 * Real.sqrt ((ell : ℝ) - 1) := by
    nlinarith [Real.sqrt_nonneg (ell : ℝ)]
  simpa only [localWeight, div_eq_mul_inv] using (div_le_iff₀ hd).mpr hh

theorem abs_basis_le_sqrt {ell : ℕ} (hell : k + 2 ≤ ell) (i : Fin k)
    (s : Option (Fin k)) : |basis (ell : ℝ) i s| ≤ Real.sqrt (ell : ℝ) := by
  have hel : (k : ℝ) + 2 ≤ ell := by exact_mod_cast hell
  have hk : (k : ℝ) < ell := by linarith
  have hell0 : 0 ≤ (ell : ℝ) := by positivity
  cases s with
  | none =>
    have hcomp : 1 ≤ Real.sqrt ((ell : ℝ) - k) := Real.one_le_sqrt.mpr (by linarith)
    have hsqrt : 1 ≤ Real.sqrt (ell : ℝ) := Real.one_le_sqrt.mpr
      (by nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
    have hinv : (Real.sqrt ((ell : ℝ) - k))⁻¹ ≤ 1 := by
      apply (inv_le_one₀ (by linarith : 0 < Real.sqrt ((ell : ℝ) - k))).mpr hcomp
    simpa only [basis, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))] using hinv.trans hsqrt
  | some j =>
    have hsum := sum_evaluation_sq hk j
    have hsingle := Finset.single_le_sum (s := (Finset.univ : Finset (Option (Fin k))))
      (f := fun a => extendedBasis (ell : ℝ) a (some j) ^ 2)
      (fun a _ha => sq_nonneg _) (Finset.mem_univ (some i))
    rw [hsum] at hsingle
    simp only [extendedBasis] at hsingle
    have hs := Real.sq_sqrt hell0
    nlinarith [sq_abs (basis (ell : ℝ) i (some j)),
      Real.sqrt_nonneg (ell : ℝ), abs_nonneg (basis (ell : ℝ) i (some j))]

theorem weighted_evaluation_le {ell : ℕ} (hell : k + 2 ≤ ell)
    (a s : Option (Fin k)) :
    |extendedBasis (ell : ℝ) a s| * localWeight ell a ≤ if a = none then 1 else 2 := by
  cases a with
  | none => simp [extendedBasis, localWeight]
  | some i =>
    simp only [extendedBasis, reduceCtorEq, ↓reduceIte]
    exact (mul_le_mul_of_nonneg_right (abs_basis_le_sqrt hell i s)
      (localWeight_nonneg ell (some i))).trans (sqrt_mul_localWeight_le_two (by omega) i)

theorem sum_weighted_evaluation_le {ell : ℕ} (hell : k + 2 ≤ ell)
    (s : Option (Fin k)) :
    (∑ a, |extendedBasis (ell : ℝ) a s| * localWeight ell a) ≤ 1 + 2 * k := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Option (Fin k))))
    (fun a _ha => weighted_evaluation_le hell a s)
  simpa [Fintype.sum_option, Finset.sum_const, mul_comm] using hh

noncomputable def weightedMatrixNorm {A : Type*} [Fintype A]
    (c : A → ℝ) (M : A → A → ℂ) : ℝ :=
  ∑ a, ∑ b, ‖M a b‖ * c a * c b

theorem weightedMatrixNorm_nonneg {A : Type*} [Fintype A]
    (c : A → ℝ) (hc : ∀ a, 0 ≤ c a) (M : A → A → ℂ) :
    0 ≤ weightedMatrixNorm c M := by
  exact Finset.sum_nonneg (fun a _ha => Finset.sum_nonneg
    (fun b _hb => mul_nonneg (mul_nonneg (norm_nonneg _) (hc a)) (hc b)))

theorem weightedMatrixNorm_rankOne {A : Type*} [Fintype A]
    (c v : A → ℝ) :
    weightedMatrixNorm c (fun a b => ((v a * v b : ℝ) : ℂ)) =
      (∑ a, |v a| * c a) ^ 2 := by
  unfold weightedMatrixNorm
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  ring

theorem weightedMatrixNorm_sub_le {A : Type*} [Fintype A]
    (c : A → ℝ) (hc : ∀ a, 0 ≤ c a) (M N : A → A → ℂ) :
    weightedMatrixNorm c (fun a b => M a b - N a b) ≤
      weightedMatrixNorm c M + weightedMatrixNorm c N := by
  unfold weightedMatrixNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _hb
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (norm_sub_le (M a b) (N a b)) (hc a)) (hc b)
  simpa only [add_mul] using hh

theorem weightedMatrixNorm_sum_le {A I : Type*} [Fintype A]
    (c : A → ℝ) (hc : ∀ a, 0 ≤ c a) (S : Finset I) (M : I → A → A → ℂ) :
    weightedMatrixNorm c (fun a b => ∑ i ∈ S, M i a b) ≤
      ∑ i ∈ S, weightedMatrixNorm c (M i) := by
  unfold weightedMatrixNorm
  calc
    (∑ a, ∑ b, ‖∑ i ∈ S, M i a b‖ * c a * c b) ≤
        ∑ a, ∑ b, (∑ i ∈ S, ‖M i a b‖) * c a * c b := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro b _hb
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_sum_le S (fun i => M i a b)) (hc a)) (hc b)
    _ = _ := by
      simp only [Finset.sum_mul]
      have hinner : ∀ a : A, (∑ b : A, ∑ i ∈ S, ‖M i a b‖ * c a * c b) =
          ∑ i ∈ S, ∑ b : A, ‖M i a b‖ * c a * c b := fun a => Finset.sum_comm
      simp_rw [hinner]
      rw [Finset.sum_comm]

theorem weightedMatrixNorm_smul {A : Type*} [Fintype A]
    (c : A → ℝ) (z : ℂ) (M : A → A → ℂ) :
    weightedMatrixNorm c (fun a b => z * M a b) = ‖z‖ * weightedMatrixNorm c M := by
  unfold weightedMatrixNorm
  simp only [norm_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  ring

noncomputable def evaluationDifference (ell : ℝ) (i : Fin k)
    (a b : Option (Fin k)) : ℂ :=
  ((extendedBasis ell a (some i) * extendedBasis ell b (some i) : ℝ) : ℂ) -
    ((extendedBasis ell a none * extendedBasis ell b none : ℝ) : ℂ)

theorem weighted_evaluationDifference_le {ell : ℕ} (hell : k + 2 ≤ ell) (i : Fin k) :
    weightedMatrixNorm (localWeight ell) (evaluationDifference (ell : ℝ) i) ≤
      2 * (1 + 2 * k) ^ 2 := by
  have h0 (s : Option (Fin k)) :
      0 ≤ ∑ a, |extendedBasis (ell : ℝ) a s| * localWeight ell a :=
    Finset.sum_nonneg (fun a _ha => mul_nonneg (abs_nonneg _) (localWeight_nonneg ell a))
  have h1 (s : Option (Fin k)) := (sq_le_sq₀ (h0 s)
    (show (0 : ℝ) ≤ 1 + 2 * k by positivity)).mpr (sum_weighted_evaluation_le hell s)
  have hh := weightedMatrixNorm_sub_le (localWeight ell) (localWeight_nonneg ell)
    (fun a b => ((extendedBasis (ell : ℝ) a (some i) * extendedBasis (ell : ℝ) b (some i) : ℝ) : ℂ))
    (fun a b => ((extendedBasis (ell : ℝ) a none * extendedBasis (ell : ℝ) b none : ℝ) : ℂ))
  rw [weightedMatrixNorm_rankOne, weightedMatrixNorm_rankOne] at hh
  exact hh.trans (by nlinarith [h1 (some i), h1 none])

noncomputable def twistedMatrix (ell : ℝ) (j : Fin k) (phase : Fin k → ℂ)
    (a b : Option (Fin k)) : ℂ :=
  (ell : ℂ)⁻¹ * ∑ i ∈ Finset.univ.erase j, phase i * evaluationDifference ell i a b

/-- Uniform local Fourier decay after the exact divisor factors are inserted. -/
theorem weighted_twistedMatrix_le {ell : ℕ} (hell : k + 2 ≤ ell)
    (j : Fin k) (phase : Fin k → ℂ) (hphase : ∀ i, ‖phase i‖ ≤ 1) :
    weightedMatrixNorm (localWeight ell) (twistedMatrix (ell : ℝ) j phase) ≤
      20 * (k : ℝ) ^ 3 / ell := by
  have hk : 1 ≤ k := by have := j.isLt; omega
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hel : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  have hterms : ∀ i : Fin k, weightedMatrixNorm (localWeight ell)
      (fun a b => phase i * evaluationDifference (ell : ℝ) i a b) ≤ 2 * (1 + 2 * k) ^ 2 := by
    intro i
    rw [weightedMatrixNorm_smul]
    exact (mul_le_of_le_one_left
      (weightedMatrixNorm_nonneg (localWeight ell) (localWeight_nonneg ell) _) (hphase i)).trans
      (weighted_evaluationDifference_le hell i)
  have hsum := (weightedMatrixNorm_sum_le (localWeight ell) (localWeight_nonneg ell)
    (Finset.univ.erase j) (fun i a b => phase i * evaluationDifference (ell : ℝ) i a b)).trans
    (Finset.sum_le_sum (fun i _hi => hterms i))
  have hcard : ((Finset.univ.erase j).card : ℝ) ≤ k := by
    exact_mod_cast ((Finset.card_le_card (Finset.erase_subset j Finset.univ)).trans_eq
      (by simp : (Finset.univ : Finset (Fin k)).card = k))
  have hsum' : weightedMatrixNorm (localWeight ell)
      (fun a b => ∑ i ∈ Finset.univ.erase j, phase i * evaluationDifference (ell : ℝ) i a b) ≤
      20 * (k : ℝ) ^ 3 := by
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hsmall : 2 * (1 + 2 * (k : ℝ)) ^ 2 ≤ 20 * (k : ℝ) ^ 2 := by nlinarith
    have hh := mul_le_mul hcard hsmall (by positivity : (0 : ℝ) ≤ 2 * (1 + 2 * k) ^ 2)
      (by positivity : (0 : ℝ) ≤ k)
    nlinarith
  unfold twistedMatrix
  rw [weightedMatrixNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hel]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hsum' (inv_nonneg.mpr hel.le)

end Erdos4.LocalFourier

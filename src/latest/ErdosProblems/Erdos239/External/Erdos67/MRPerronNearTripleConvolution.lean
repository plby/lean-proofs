import ErdosProblems.Erdos239.External.Erdos67.MRPerronNearProgression
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SecondSecondaryChebyshevReduction

/-!
# A three-factor Perron near-mass bound

This is the finite hyperbola reindexing needed after the low--high A.10
coefficient has been grouped as one factor and the two generalized-Mangoldt
windows as the other two factors.
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRPerronNearTripleConvolution

noncomputable section

open BoundedGaps.Maynard
open MRHalaszBands
open MRPerronNearProgression

/-- Exact finite reindexing of a nested three-factor Dirichlet convolution.
The right side orders the two distinguished factors first and the residual
factor last. -/
theorem sum_Icc_nested_antidiagonal_eq_triple
    (N : ℕ) (A B C : ℕ → ℝ) (K : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N,
      ∑ uv ∈ n.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal,
          A uv.2 * B ab.1 * C ab.2 * K n) =
      ∑ a ∈ gsPositiveBelow (N + 1),
        ∑ b ∈ (gsPositiveBelow (N + 1)).filter
            (fun b ↦ a * b < N + 1),
          B a * C b *
            ∑ d ∈ (gsPositiveBelow (N + 1)).filter
                (fun d ↦ a * b * d < N + 1),
              A d * K (a * b * d) := by
  classical
  have hset : Finset.Icc 1 N = gsPositiveBelow (N + 1) := by
    ext n
    simp [gsPositiveBelow]
  rw [hset]
  have hfirst :
      (∑ n ∈ gsPositiveBelow (N + 1),
        ∑ uv ∈ n.divisorsAntidiagonal,
          ∑ ab ∈ uv.1.divisorsAntidiagonal,
            A uv.2 * B ab.1 * C ab.2 * K n) =
      ∑ n ∈ gsPositiveBelow (N + 1),
        ∑ q ∈ n.divisors,
          ∑ ab ∈ q.divisorsAntidiagonal,
            A (n / q) * B ab.1 * C ab.2 * K n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact Nat.sum_divisorsAntidiagonal
      (fun q d ↦ ∑ ab ∈ q.divisorsAntidiagonal,
        A d * B ab.1 * C ab.2 * K n)
  rw [hfirst]
  rw [sum_divisors_reindex_real (N + 1)
    (fun n q ↦ ∑ ab ∈ q.divisorsAntidiagonal,
      A (n / q) * B ab.1 * C ab.2 * K n)]
  have hcancel : ∀ q ∈ gsPositiveBelow (N + 1),
      ∀ d ∈ (gsPositiveBelow (N + 1)).filter
          (fun d ↦ q * d < N + 1),
        q * d / q = d := by
    intro q hq d hd
    exact Nat.mul_div_cancel_left d (Finset.mem_Ico.mp hq).1
  have hcancelSum :
      (∑ q ∈ gsPositiveBelow (N + 1),
        ∑ d ∈ (gsPositiveBelow (N + 1)).filter
            (fun d ↦ q * d < N + 1),
          ∑ ab ∈ q.divisorsAntidiagonal,
            A (q * d / q) * B ab.1 * C ab.2 * K (q * d)) =
      ∑ q ∈ gsPositiveBelow (N + 1),
        ∑ d ∈ (gsPositiveBelow (N + 1)).filter
            (fun d ↦ q * d < N + 1),
          ∑ ab ∈ q.divisorsAntidiagonal,
            A d * B ab.1 * C ab.2 * K (q * d) := by
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro d hd
    rw [hcancel q hq d hd]
  rw [hcancelSum]
  have hswap :
      (∑ q ∈ gsPositiveBelow (N + 1),
        ∑ d ∈ (gsPositiveBelow (N + 1)).filter
            (fun d ↦ q * d < N + 1),
          ∑ ab ∈ q.divisorsAntidiagonal,
            A d * B ab.1 * C ab.2 * K (q * d)) =
      ∑ q ∈ gsPositiveBelow (N + 1),
        ∑ ab ∈ q.divisorsAntidiagonal,
          B ab.1 * C ab.2 *
            ∑ d ∈ (gsPositiveBelow (N + 1)).filter
                (fun d ↦ q * d < N + 1),
              A d * K (q * d) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ab hab
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hswap]
  have hsecond :
      (∑ q ∈ gsPositiveBelow (N + 1),
        ∑ ab ∈ q.divisorsAntidiagonal,
          B ab.1 * C ab.2 *
            ∑ d ∈ (gsPositiveBelow (N + 1)).filter
                (fun d ↦ q * d < N + 1),
              A d * K (q * d)) =
      ∑ q ∈ gsPositiveBelow (N + 1),
        ∑ a ∈ q.divisors,
          B a * C (q / a) *
            ∑ d ∈ (gsPositiveBelow (N + 1)).filter
                (fun d ↦ q * d < N + 1),
              A d * K (q * d) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact Nat.sum_divisorsAntidiagonal
      (fun a b ↦ B a * C b *
        ∑ d ∈ (gsPositiveBelow (N + 1)).filter
            (fun d ↦ q * d < N + 1),
          A d * K (q * d))
  rw [hsecond]
  rw [sum_divisors_reindex_real (N + 1)
    (fun q a ↦ B a * C (q / a) *
      ∑ d ∈ (gsPositiveBelow (N + 1)).filter
          (fun d ↦ q * d < N + 1),
        A d * K (q * d))]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hab : a * b / a = b :=
    Nat.mul_div_cancel_left b (Finset.mem_Ico.mp ha).1
  rw [hab]

/-- Abstract near-kernel bound after the exact triple reindexing.  The
residual factor is merely one-bounded; the two distinguished nonnegative
weights retain both their hyperbolic term and reciprocal product. -/
theorem sum_Icc_nested_antidiagonal_near_le
    {x : ℕ} (hx : 0 < x) {T : ℝ} (hT : 0 < T)
    (A B C : ℕ → ℝ)
    (hA0 : ∀ d, 0 ≤ A d) (hA1 : ∀ d, A d ≤ 1)
    (hB0 : ∀ a, 0 ≤ B a) (hC0 : ∀ b, 0 ≤ C b) :
    (∑ n ∈ Finset.Icc 1 (2 * x),
      ∑ uv ∈ n.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal,
          A uv.2 * B ab.1 * C ab.2 *
            dirichletPerronNearError x T n) ≤
      ∑ a ∈ gsPositiveBelow (2 * x + 1),
        ∑ b ∈ (gsPositiveBelow (2 * x + 1)).filter
            (fun b ↦ a * b < 2 * x + 1),
          B a * C b *
            (2 + (4 * (x : ℝ) / T) * ((a * b : ℕ) : ℝ)⁻¹ *
              (harmonic (2 * x) : ℝ)) := by
  rw [sum_Icc_nested_antidiagonal_eq_triple]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  have haPos : 0 < a := (Finset.mem_Ico.mp ha).1
  have hbPos : 0 < b :=
    (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).1
  have habPos : 0 < a * b := Nat.mul_pos haPos hbPos
  apply mul_le_mul_of_nonneg_left
  · calc
      (∑ d ∈ (gsPositiveBelow (2 * x + 1)).filter
          (fun d ↦ a * b * d < 2 * x + 1),
          A d * dirichletPerronNearError x T (a * b * d)) ≤
        ∑ d ∈ (gsPositiveBelow (2 * x + 1)).filter
          (fun d ↦ a * b * d < 2 * x + 1),
          dirichletPerronNearError x T (d * (a * b)) := by
            apply Finset.sum_le_sum
            intro d hd
            rw [Nat.mul_comm (a * b) d]
            exact mul_le_of_le_one_left
              (dirichletPerronNearError_nonneg x hT _) (hA1 d)
      _ ≤ ∑ d ∈ Finset.Icc 1 (2 * x),
          dirichletPerronNearError x T (d * (a * b)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro d hd
              have hdData := Finset.mem_filter.mp hd
              have hdIco := Finset.mem_Ico.mp hdData.1
              have hdleprod : d ≤ a * b * d := by
                calc
                  d = 1 * d := by simp
                  _ ≤ (a * b) * d := Nat.mul_le_mul_right d habPos
              exact Finset.mem_Icc.mpr ⟨hdIco.1,
                hdleprod.trans (by omega : a * b * d ≤ 2 * x)⟩
            · intro d hd hnot
              exact dirichletPerronNearError_nonneg x hT _
      _ ≤ 2 + (4 * (x : ℝ) / T) * ((a * b : ℕ) : ℝ)⁻¹ *
          (harmonic (2 * x) : ℝ) :=
        sum_Icc_dirichletPerronNearError_mul_le habPos hT
  · exact mul_nonneg (hB0 a) (hC0 b)

/-- Coefficient-level majorization for a three-fold Dirichlet
convolution, ordered with the two distinguished factors first. -/
theorem norm_mul_mul_apply_le_nested
    (a b c : ArithmeticFunction ℂ) (A B C : ℕ → ℝ)
    (hA : ∀ n, ‖a n‖ ≤ A n) (hB : ∀ n, ‖b n‖ ≤ B n)
    (hC : ∀ n, ‖c n‖ ≤ C n)
    (hA0 : ∀ n, 0 ≤ A n) (hB0 : ∀ n, 0 ≤ B n)
    (hC0 : ∀ n, 0 ≤ C n) (n : ℕ) :
    ‖((b * c) * a) n‖ ≤
      ∑ uv ∈ n.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal,
          A uv.2 * B ab.1 * C ab.2 := by
  rw [ArithmeticFunction.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro uv huv
  rw [norm_mul, ArithmeticFunction.mul_apply]
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _)
    (norm_nonneg _)).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ab hab
  rw [norm_mul]
  calc
    ‖b ab.1‖ * ‖c ab.2‖ * ‖a uv.2‖ ≤
        (B ab.1 * C ab.2) * A uv.2 := by
      exact mul_le_mul
        (mul_le_mul (hB _) (hC _) (norm_nonneg _) (hB0 _))
        (hA _) (norm_nonneg _) (mul_nonneg (hB0 _) (hC0 _))
    _ = A uv.2 * B ab.1 * C ab.2 := by ring

/-- The abstract three-factor near mass.  This is the lossless bridge from
the exact coefficient convolution to the progression estimate: there is
no global coefficient-mass factor. -/
theorem dirichletPerronNearMass_mul_mul_le
    {x : ℕ} (hx : 0 < x) {T : ℝ} (hT : 0 < T)
    (a b c : ArithmeticFunction ℂ) (A B C : ℕ → ℝ)
    (hA : ∀ n, ‖a n‖ ≤ A n) (hB : ∀ n, ‖b n‖ ≤ B n)
    (hC : ∀ n, ‖c n‖ ≤ C n)
    (hA0 : ∀ n, 0 ≤ A n) (hA1 : ∀ n, A n ≤ 1)
    (hB0 : ∀ n, 0 ≤ B n) (hC0 : ∀ n, 0 ≤ C n) :
    dirichletPerronNearMass
        ((((b * c) * a : ArithmeticFunction ℂ) : ℕ → ℂ)) x T ≤
      ∑ aa ∈ gsPositiveBelow (2 * x + 1),
        ∑ bb ∈ (gsPositiveBelow (2 * x + 1)).filter
            (fun bb ↦ aa * bb < 2 * x + 1),
          B aa * C bb *
            (2 + (4 * (x : ℝ) / T) * ((aa * bb : ℕ) : ℝ)⁻¹ *
              (harmonic (2 * x) : ℝ)) := by
  unfold dirichletPerronNearMass
  rw [tsum_eq_sum (s := Finset.range (2 * x))]
  · calc
      (∑ n ∈ Finset.range (2 * x),
          ‖((b * c) * a) n‖ * dirichletPerronNearError x T n) ≤
        ∑ n ∈ Finset.Icc 1 (2 * x),
          ‖((b * c) * a) n‖ * dirichletPerronNearError x T n := by
            let E := Finset.Ico 1 (2 * x)
            have hrange : Finset.range (2 * x) = insert 0 E := by
              ext n
              simp only [Finset.mem_range, Finset.mem_insert,
                E, Finset.mem_Ico]
              omega
            rw [hrange, Finset.sum_insert (by simp [E])]
            simp only [dirichletPerronNearError_zero, mul_zero, zero_add]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn
              have hnData := Finset.mem_Ico.mp hn
              exact Finset.mem_Icc.mpr ⟨hnData.1, hnData.2.le⟩
            · intro n hn hnot
              exact mul_nonneg (norm_nonneg _)
                (dirichletPerronNearError_nonneg x hT n)
      _ ≤ ∑ n ∈ Finset.Icc 1 (2 * x),
          (∑ uv ∈ n.divisorsAntidiagonal,
            ∑ ab ∈ uv.1.divisorsAntidiagonal,
              A uv.2 * B ab.1 * C ab.2) *
                dirichletPerronNearError x T n := by
          apply Finset.sum_le_sum
          intro n hn
          exact mul_le_mul_of_nonneg_right
            (norm_mul_mul_apply_le_nested a b c A B C hA hB hC
              hA0 hB0 hC0 n)
            (dirichletPerronNearError_nonneg x hT n)
      _ = ∑ n ∈ Finset.Icc 1 (2 * x),
          ∑ uv ∈ n.divisorsAntidiagonal,
            ∑ ab ∈ uv.1.divisorsAntidiagonal,
              A uv.2 * B ab.1 * C ab.2 *
                dirichletPerronNearError x T n := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro uv huv
          rw [Finset.sum_mul]
      _ ≤ _ := sum_Icc_nested_antidiagonal_near_le hx hT
        A B C hA0 hA1 hB0 hC0
  · intro n hn
    have hnLower : 2 * x ≤ n := by simpa using hn
    rw [dirichletPerronNearError, if_neg]
    · simp
    · intro h
      have hnLowerR : (2 : ℝ) * x ≤ n := by exact_mod_cast hnLower
      exact (not_lt_of_ge hnLowerR) h.2.2.1

end

end Erdos67.MRPerronNearTripleConvolution

#print axioms
  Erdos67.MRPerronNearTripleConvolution.sum_Icc_nested_antidiagonal_near_le
#print axioms
  Erdos67.MRPerronNearTripleConvolution.dirichletPerronNearMass_mul_mul_le

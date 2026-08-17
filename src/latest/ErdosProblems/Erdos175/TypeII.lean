/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos175.Phase
import ErdosProblems.Erdos175.MobiusMeanSquareEndpoint
import ErdosProblems.Erdos175.ReciprocalExpSumBound
import ErdosProblems.Erdos175.VaughanFourSums
import ErdosProblems.Erdos175.VaughanTypeIIExpansion

/-!
# The Type II Cauchy--Schwarz block for Erdős Problem 175

Granville--Ramaré, Proposition 9.4, first applies Cauchy--Schwarz in the
outer variable of a bilinear exponential sum.  All of the analytic content
then sits in a mean-square estimate for the reciprocal inner sums.  This file
separates that analytic input from the finite Hilbert-space bookkeeping.

The formulation below deliberately allows an arbitrary complex kernel.  In
the application the kernel is the product of the indicator of `uv ∈ I` and
`exp (2 * pi * I * x / (u * v))`.  Thus `ReciprocalInnerBound` is precisely
the premise to be supplied by the reciprocal exponential-sum estimates.

The last section assembles finitely many dyadic blocks and records the exact
decimal constant `10.54 = 527 / 50` used in Corollary 9.7.
-/

open scoped BigOperators

namespace Erdos175.TypeII

section OneBlock

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- The unnormalised `L²` norm of coefficients on a finite support. -/
noncomputable def l2Norm (s : Finset U) (a : U → ℂ) : ℝ :=
  Real.sqrt (∑ u ∈ s, ‖a u‖ ^ 2)

lemma l2Norm_nonneg (s : Finset U) (a : U → ℂ) : 0 ≤ l2Norm s a :=
  Real.sqrt_nonneg _

lemma l2Norm_sq (s : Finset U) (a : U → ℂ) :
    l2Norm s a ^ 2 = ∑ u ∈ s, ‖a u‖ ^ 2 := by
  rw [l2Norm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The inner sum in the second variable of a bilinear block. -/
def innerSum (vSupport : Finset V) (beta : V → ℂ) (kernel : U → V → ℂ)
    (u : U) : ℂ :=
  ∑ v ∈ vSupport, beta v * kernel u v

/-- A finite bilinear block. -/
def bilinearSum (uSupport : Finset U) (vSupport : Finset V)
    (alpha : U → ℂ) (beta : V → ℂ) (kernel : U → V → ℂ) : ℂ :=
  ∑ u ∈ uSupport, alpha u * innerSum vSupport beta kernel u

/-- The only analytic input used by the Type II block: a mean-square bound
for the reciprocal inner sums. -/
def ReciprocalInnerBound (uSupport : Finset U) (vSupport : Finset V)
    (beta : V → ℂ) (kernel : U → V → ℂ) (R : ℝ) : Prop :=
  (∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2) ≤
    R * ∑ v ∈ vSupport, ‖beta v‖ ^ 2

/-- The Gram kernel obtained after expanding the square of the inner sum. -/
def kernelCorrelation (uSupport : Finset U) (kernel : U → V → ℂ)
    (v w : V) : ℂ :=
  ∑ u ∈ uSupport, (starRingEnd ℂ) (kernel u v) * kernel u w

/-- Exact finite Gram expansion of the mean square of the inner sums. -/
lemma innerSum_meanSquare_eq_gram
    (uSupport : Finset U) (vSupport : Finset V)
    (beta : V → ℂ) (kernel : U → V → ℂ) :
    ((∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2 : ℝ) : ℂ) =
      ∑ v ∈ vSupport, ∑ w ∈ vSupport,
        (starRingEnd ℂ) (beta v) * beta w *
          kernelCorrelation uSupport kernel v w := by
  classical
  simp only [innerSum, kernelCorrelation]
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro u hu
  ring

/-- The Gram expansion followed by the triangle inequality.  This is the
source-level Cauchy step used to split pairs `(v,w)` into near and far ranges. -/
lemma innerSum_meanSquare_le_sum_norm_correlation
    (uSupport : Finset U) (vSupport : Finset V)
    (beta : V → ℂ) (kernel : U → V → ℂ) :
    (∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2) ≤
      ∑ v ∈ vSupport, ∑ w ∈ vSupport,
        ‖beta v‖ * ‖beta w‖ * ‖kernelCorrelation uSupport kernel v w‖ := by
  have heq := innerSum_meanSquare_eq_gram uSupport vSupport beta kernel
  have hre :
      (∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2) =
        (∑ v ∈ vSupport, ∑ w ∈ vSupport,
          (starRingEnd ℂ) (beta v) * beta w *
            kernelCorrelation uSupport kernel v w).re := by
    exact_mod_cast congr_arg Complex.re heq
  rw [hre]
  calc
    (∑ v ∈ vSupport, ∑ w ∈ vSupport,
        (starRingEnd ℂ) (beta v) * beta w *
          kernelCorrelation uSupport kernel v w).re
        ≤ ‖∑ v ∈ vSupport, ∑ w ∈ vSupport,
            (starRingEnd ℂ) (beta v) * beta w *
              kernelCorrelation uSupport kernel v w‖ := Complex.re_le_norm _
    _ ≤ ∑ v ∈ vSupport, ‖∑ w ∈ vSupport,
          (starRingEnd ℂ) (beta v) * beta w *
            kernelCorrelation uSupport kernel v w‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ vSupport, ∑ w ∈ vSupport,
          ‖(starRingEnd ℂ) (beta v) * beta w *
            kernelCorrelation uSupport kernel v w‖ := by
          apply Finset.sum_le_sum
          intro v hv
          exact norm_sum_le _ _
    _ = ∑ v ∈ vSupport, ∑ w ∈ vSupport,
          ‖beta v‖ * ‖beta w‖ * ‖kernelCorrelation uSupport kernel v w‖ := by
          apply Finset.sum_congr rfl
          intro v hv
          apply Finset.sum_congr rfl
          intro w hw
          simp [norm_mul]

/-- Diagonal/off-diagonal correlation estimates imply a mean-square bound.
The diagonal contributes `D` once, while Cauchy--Schwarz bounds the full
off-diagonal coefficient mass by `card(vSupport) * ‖beta‖₂²`. -/
lemma reciprocalInnerBound_of_diagonal_offDiagonal
    (uSupport : Finset U) (vSupport : Finset V)
    (beta : V → ℂ) (kernel : U → V → ℂ) (D Q : ℝ)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hdiag : ∀ v ∈ vSupport,
      ‖kernelCorrelation uSupport kernel v v‖ ≤ D)
    (hoff : ∀ v ∈ vSupport, ∀ w ∈ vSupport, v ≠ w →
      ‖kernelCorrelation uSupport kernel v w‖ ≤ Q) :
    ReciprocalInnerBound uSupport vSupport beta kernel
      (D + Q * (vSupport.card : ℝ)) := by
  classical
  let a : V → ℝ := fun v ↦ ‖beta v‖
  have hpair (v : V) (hv : v ∈ vSupport) (w : V) (hw : w ∈ vSupport) :
      a v * a w * ‖kernelCorrelation uSupport kernel v w‖ ≤
        (if v = w then D * a v ^ 2 else 0) + Q * (a v * a w) := by
    by_cases hvw : v = w
    · subst w
      rw [if_pos rfl]
      have hav : 0 ≤ a v := norm_nonneg _
      have hmain : a v * a v * ‖kernelCorrelation uSupport kernel v v‖ ≤
          D * a v ^ 2 := by
        calc
          a v * a v * ‖kernelCorrelation uSupport kernel v v‖
              ≤ a v * a v * D :=
                mul_le_mul_of_nonneg_left (hdiag v hv) (mul_nonneg hav hav)
          _ = D * a v ^ 2 := by ring
      exact hmain.trans (le_add_of_nonneg_right (by positivity))
    · rw [if_neg hvw, zero_add]
      calc
        a v * a w * ‖kernelCorrelation uSupport kernel v w‖
            ≤ a v * a w * Q :=
              mul_le_mul_of_nonneg_left (hoff v hv w hw hvw)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = Q * (a v * a w) := by ring
  have hmass :
      (∑ v ∈ vSupport, a v) ^ 2 ≤
        (vSupport.card : ℝ) * ∑ v ∈ vSupport, a v ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq vSupport
      (fun _v ↦ (1 : ℝ)) a
    simpa using hcs
  have hdiagSum :
      (∑ v ∈ vSupport, ∑ w ∈ vSupport,
          if v = w then D * a v ^ 2 else 0) =
        D * ∑ v ∈ vSupport, a v ^ 2 := by
    calc
      (∑ v ∈ vSupport, ∑ w ∈ vSupport,
          if v = w then D * a v ^ 2 else 0) =
          ∑ v ∈ vSupport, D * a v ^ 2 := by
            apply Finset.sum_congr rfl
            intro v hv
            simp [hv]
      _ = D * ∑ v ∈ vSupport, a v ^ 2 := by rw [Finset.mul_sum]
  have hoffSum :
      (∑ v ∈ vSupport, ∑ w ∈ vSupport, Q * (a v * a w)) =
        Q * (∑ v ∈ vSupport, a v) ^ 2 := by
    rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    calc
      (∑ w ∈ vSupport, Q * (a v * a w)) =
          Q * ∑ w ∈ vSupport, a v * a w :=
        (Finset.mul_sum (s := vSupport) (f := fun w ↦ a v * a w) Q).symm
      _ = Q * (a v * ∑ w ∈ vSupport, a w) := by
        congr 1
        exact (Finset.mul_sum (s := vSupport) (f := a) (a v)).symm
  unfold ReciprocalInnerBound
  calc
    (∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2)
        ≤ ∑ v ∈ vSupport, ∑ w ∈ vSupport,
          a v * a w * ‖kernelCorrelation uSupport kernel v w‖ :=
      innerSum_meanSquare_le_sum_norm_correlation
        uSupport vSupport beta kernel
    _ ≤ ∑ v ∈ vSupport, ∑ w ∈ vSupport,
          ((if v = w then D * a v ^ 2 else 0) + Q * (a v * a w)) := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw
      exact hpair v hv w hw
    _ = D * (∑ v ∈ vSupport, a v ^ 2) +
          Q * (∑ v ∈ vSupport, a v) ^ 2 := by
      simp only [Finset.sum_add_distrib]
      rw [hdiagSum, hoffSum]
    _ ≤ D * (∑ v ∈ vSupport, a v ^ 2) +
          Q * ((vSupport.card : ℝ) * ∑ v ∈ vSupport, a v ^ 2) := by
      gcongr
    _ = (D + Q * (vSupport.card : ℝ)) *
          ∑ v ∈ vSupport, ‖beta v‖ ^ 2 := by
      simp only [a]
      ring

/-- Cauchy--Schwarz in the outer variable, before any estimate for the
reciprocal inner sums is used. -/
lemma bilinear_cauchy_sq (uSupport : Finset U) (vSupport : Finset V)
    (alpha : U → ℂ) (beta : V → ℂ) (kernel : U → V → ℂ) :
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ^ 2 ≤
      (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
        ∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2 := by
  classical
  calc
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ^ 2
        ≤ (∑ u ∈ uSupport,
            ‖alpha u * innerSum vSupport beta kernel u‖) ^ 2 := by
          gcongr
          exact norm_sum_le _ _
    _ = (∑ u ∈ uSupport,
          ‖alpha u‖ * ‖innerSum vSupport beta kernel u‖) ^ 2 := by
          simp_rw [norm_mul]
    _ ≤ (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
          ∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2 := by
          exact Finset.sum_mul_sq_le_sq_mul_sq uSupport _ _

/-- Squared Type II estimate, conditional only on the reciprocal inner-sum
bound.  This division-free form is useful when the analytic estimate has
already been squared. -/
lemma bilinear_sq_le_of_reciprocalInnerBound
    (uSupport : Finset U) (vSupport : Finset V)
    (alpha : U → ℂ) (beta : V → ℂ) (kernel : U → V → ℂ) (R : ℝ)
    (hinner : ReciprocalInnerBound uSupport vSupport beta kernel R) :
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ^ 2 ≤
      (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
        (R * ∑ v ∈ vSupport, ‖beta v‖ ^ 2) := by
  calc
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ^ 2
        ≤ (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
            ∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2 :=
          bilinear_cauchy_sq uSupport vSupport alpha beta kernel
    _ ≤ (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
          (R * ∑ v ∈ vSupport, ‖beta v‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hinner
            (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- Unsquared Type II estimate in `L² × L²` form. -/
lemma norm_bilinearSum_le_of_reciprocalInnerBound
    (uSupport : Finset U) (vSupport : Finset V)
    (alpha : U → ℂ) (beta : V → ℂ) (kernel : U → V → ℂ) (R : ℝ)
    (hR : 0 ≤ R)
    (hinner : ReciprocalInnerBound uSupport vSupport beta kernel R) :
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ≤
      l2Norm uSupport alpha * Real.sqrt R * l2Norm vSupport beta := by
  have hsquare := bilinear_sq_le_of_reciprocalInnerBound
    uSupport vSupport alpha beta kernel R hinner
  have hrhs_sq :
      (l2Norm uSupport alpha * Real.sqrt R * l2Norm vSupport beta) ^ 2 =
        (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
          (R * ∑ v ∈ vSupport, ‖beta v‖ ^ 2) := by
    rw [mul_pow, mul_pow, l2Norm_sq, Real.sq_sqrt hR, l2Norm_sq]
    ring
  rw [← hrhs_sq] at hsquare
  have hleft : 0 ≤ ‖bilinearSum uSupport vSupport alpha beta kernel‖ := norm_nonneg _
  have hright :
      0 ≤ l2Norm uSupport alpha * Real.sqrt R * l2Norm vSupport beta := by
    exact mul_nonneg
      (mul_nonneg (l2Norm_nonneg _ _) (Real.sqrt_nonneg _))
      (l2Norm_nonneg _ _)
  nlinarith

/-- Bilinear consequence of the diagonal/off-diagonal Gram estimate. -/
lemma norm_bilinearSum_le_of_diagonal_offDiagonal
    (uSupport : Finset U) (vSupport : Finset V)
    (alpha : U → ℂ) (beta : V → ℂ) (kernel : U → V → ℂ) (D Q : ℝ)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hdiag : ∀ v ∈ vSupport,
      ‖kernelCorrelation uSupport kernel v v‖ ≤ D)
    (hoff : ∀ v ∈ vSupport, ∀ w ∈ vSupport, v ≠ w →
      ‖kernelCorrelation uSupport kernel v w‖ ≤ Q) :
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ≤
      l2Norm uSupport alpha *
        Real.sqrt (D + Q * (vSupport.card : ℝ)) *
          l2Norm vSupport beta := by
  apply norm_bilinearSum_le_of_reciprocalInnerBound
  · positivity
  · exact reciprocalInnerBound_of_diagonal_offDiagonal
      uSupport vSupport beta kernel D Q hD hQ hdiag hoff

/-- A norm-one kernel always satisfies the trivial reciprocal inner-sum
bound.  This is the unconditional baseline in the remark following
Granville--Ramaré, Proposition 9.4; the derivative estimates improve the
factor supplied here for far pairs. -/
lemma reciprocalInnerBound_of_norm_kernel_le_one
    (uSupport : Finset U) (vSupport : Finset V)
    (beta : V → ℂ) (kernel : U → V → ℂ)
    (hkernel : ∀ u ∈ uSupport, ∀ v ∈ vSupport, ‖kernel u v‖ ≤ 1) :
    ReciprocalInnerBound uSupport vSupport beta kernel
      ((uSupport.card : ℝ) * (vSupport.card : ℝ)) := by
  classical
  have hone_v : (∑ _v ∈ vSupport, (1 : ℝ) ^ 2) = vSupport.card := by simp
  have hinner_point (u : U) (hu : u ∈ uSupport) :
      ‖innerSum vSupport beta kernel u‖ ^ 2 ≤
        (vSupport.card : ℝ) * ∑ v ∈ vSupport, ‖beta v‖ ^ 2 := by
    calc
      ‖innerSum vSupport beta kernel u‖ ^ 2
          ≤ (∑ v ∈ vSupport, ‖beta v * kernel u v‖) ^ 2 := by
            gcongr
            exact norm_sum_le _ _
      _ = (∑ v ∈ vSupport, ‖beta v‖ * ‖kernel u v‖) ^ 2 := by
            simp_rw [norm_mul]
      _ ≤ (∑ v ∈ vSupport, ‖beta v‖) ^ 2 := by
            gcongr with v hv
            simpa using mul_le_mul_of_nonneg_left (hkernel u hu v hv) (norm_nonneg _)
      _ ≤ (∑ _v ∈ vSupport, (1 : ℝ) ^ 2) *
            ∑ v ∈ vSupport, ‖beta v‖ ^ 2 := by
            simpa using Finset.sum_mul_sq_le_sq_mul_sq vSupport
              (fun _v ↦ (1 : ℝ)) (fun v ↦ ‖beta v‖)
      _ = (vSupport.card : ℝ) * ∑ v ∈ vSupport, ‖beta v‖ ^ 2 := by
            rw [hone_v]
  unfold ReciprocalInnerBound
  calc
    (∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2)
        ≤ ∑ _u ∈ uSupport,
            (vSupport.card : ℝ) * ∑ v ∈ vSupport, ‖beta v‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro u hu
          exact hinner_point u hu
    _ = ((uSupport.card : ℝ) * (vSupport.card : ℝ)) *
          ∑ v ∈ vSupport, ‖beta v‖ ^ 2 := by
          simp
          ring

/-- The unconditional `L² × L²` bound for a norm-one bilinear kernel. -/
lemma norm_bilinearSum_le_of_norm_kernel_le_one
    (uSupport : Finset U) (vSupport : Finset V)
    (alpha : U → ℂ) (beta : V → ℂ) (kernel : U → V → ℂ)
    (hkernel : ∀ u ∈ uSupport, ∀ v ∈ vSupport, ‖kernel u v‖ ≤ 1) :
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ≤
      l2Norm uSupport alpha *
        Real.sqrt ((uSupport.card : ℝ) * (vSupport.card : ℝ)) *
          l2Norm vSupport beta := by
  exact norm_bilinearSum_le_of_reciprocalInnerBound
    uSupport vSupport alpha beta kernel
    ((uSupport.card : ℝ) * (vSupport.card : ℝ)) (by positivity)
    (reciprocalInnerBound_of_norm_kernel_le_one
      uSupport vSupport beta kernel hkernel)

end OneBlock

section ReciprocalKernel

/-- The unrestricted reciprocal phase kernel on a rectangle. -/
noncomputable def reciprocalKernel (x : ℝ) (u v : ℕ) : ℂ :=
  e (x / ((u * v : ℕ) : ℝ))

@[simp] lemma norm_reciprocalKernel (x : ℝ) (u v : ℕ) :
    ‖reciprocalKernel x u v‖ = 1 := by
  simp [reciprocalKernel]

/-- The kernel of a reciprocal bilinear sum, restricted to those products
which lie in an arbitrary finite interval `I`. -/
noncomputable def restrictedReciprocalKernel
    (I : Finset ℕ) (x : ℝ) (u v : ℕ) : ℂ :=
  if u * v ∈ I then e (x / ((u * v : ℕ) : ℝ)) else 0

lemma norm_restrictedReciprocalKernel_le_one
    (I : Finset ℕ) (x : ℝ) (u v : ℕ) :
    ‖restrictedReciprocalKernel I x u v‖ ≤ 1 := by
  simp only [restrictedReciprocalKernel]
  split_ifs
  · rw [norm_e]
  · simp

/-- Common outer-variable support of two product-restricted reciprocal
kernels. -/
def productCorrelationSupport (y y' U v w : ℕ) : Finset ℕ :=
  (Finset.Ioc U (2 * U)).filter fun u =>
    u * v ∈ Finset.Ioc y y' ∧ u * w ∈ Finset.Ioc y y'

/-- The common support is again one integer interval.  This is the exact
endpoint calculation required before applying the real-endpoint version of
Proposition 8.1. -/
lemma productCorrelationSupport_eq_Ioc
    (y y' U v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    productCorrelationSupport y y' U v w =
      Finset.Ioc (max U (max (y / v) (y / w)))
        (min (2 * U) (min (y' / v) (y' / w))) := by
  ext u
  simp only [productCorrelationSupport, Finset.mem_filter,
    Finset.mem_Ioc]
  simp only [max_lt_iff, le_min_iff]
  rw [Nat.div_lt_iff_lt_mul hv, Nat.div_lt_iff_lt_mul hw,
    Nat.le_div_iff_mul_le hv, Nat.le_div_iff_mul_le hw]
  omega

/-- Exact correlation identity for the product-restricted kernel on
`y < uv ≤ y'`.  In particular, the analytic sum has no holes: it is the
single `Ioc` interval displayed by `productCorrelationSupport_eq_Ioc`. -/
lemma kernelCorrelation_restrictedReciprocalKernel_eq
    (x : ℝ) (y y' U v w : ℕ) (hU : 1 ≤ U) (hv : 0 < v) (hw : 0 < w) :
    kernelCorrelation (Finset.Ioc U (2 * U))
        (restrictedReciprocalKernel (Finset.Ioc y y') x) v w =
      ∑ u ∈ Finset.Ioc (max U (max (y / v) (y / w)))
          (min (2 * U) (min (y' / v) (y' / w))),
        e ((x * (1 / (w : ℝ) - 1 / (v : ℝ))) / (u : ℝ)) := by
  rw [← productCorrelationSupport_eq_Ioc y y' U v w hv hw]
  unfold kernelCorrelation productCorrelationSupport restrictedReciprocalKernel
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases huv : u * v ∈ Finset.Ioc y y'
  · by_cases huw : u * w ∈ Finset.Ioc y y'
    · simp only [huv, huw, if_pos, and_self]
      have huI := Finset.mem_Ioc.mp hu
      have hu0 : (u : ℝ) ≠ 0 := by
        exact_mod_cast (by omega : u ≠ 0)
      have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
      have hw0 : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
      rw [conj_e, ← e_add]
      congr 1
      push_cast
      field_simp
      ring
    · simp [huv, huw]
  · simp [huv]

/-- Common support on an arbitrary outer interval `(A,B]`.  This variant is
used for the exact power-of-two partition, whose natural blocks are
`(2^j-1,2^(j+1)-1]`. -/
def productCorrelationSupportOn
    (y y' A B v w : ℕ) : Finset ℕ :=
  (Finset.Ioc A B).filter fun u ↦
    u * v ∈ Finset.Ioc y y' ∧ u * w ∈ Finset.Ioc y y'

lemma productCorrelationSupportOn_eq_Ioc
    (y y' A B v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    productCorrelationSupportOn y y' A B v w =
      Finset.Ioc (max A (max (y / v) (y / w)))
        (min B (min (y' / v) (y' / w))) := by
  ext u
  simp only [productCorrelationSupportOn, Finset.mem_filter, Finset.mem_Ioc]
  simp only [max_lt_iff, le_min_iff]
  rw [Nat.div_lt_iff_lt_mul hv, Nat.div_lt_iff_lt_mul hw,
    Nat.le_div_iff_mul_le hv, Nat.le_div_iff_mul_le hw]
  omega

/-- Exact product-restricted Gram correlation on an arbitrary outer
interval. -/
lemma kernelCorrelation_restrictedReciprocalKernel_Ioc_eq
    (x : ℝ) (y y' A B v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    kernelCorrelation (Finset.Ioc A B)
        (restrictedReciprocalKernel (Finset.Ioc y y') x) v w =
      ∑ u ∈ Finset.Ioc (max A (max (y / v) (y / w)))
          (min B (min (y' / v) (y' / w))),
        e ((x * (1 / (w : ℝ) - 1 / (v : ℝ))) / (u : ℝ)) := by
  rw [← productCorrelationSupportOn_eq_Ioc y y' A B v w hv hw]
  unfold kernelCorrelation productCorrelationSupportOn restrictedReciprocalKernel
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases huv : u * v ∈ Finset.Ioc y y'
  · by_cases huw : u * w ∈ Finset.Ioc y y'
    · simp only [huv, huw, if_pos, and_self]
      have huI := Finset.mem_Ioc.mp hu
      have hu0 : (u : ℝ) ≠ 0 := by
        exact_mod_cast (by omega : u ≠ 0)
      have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
      have hw0 : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
      rw [conj_e, ← e_add]
      congr 1
      push_cast
      field_simp
      ring
    · simp [huv, huw]
  · simp [huv]

/-- Norm form of the preceding identity with a positive phase.  This is the
exact interface expected by the q-free reciprocal exponential-sum bounds. -/
lemma norm_kernelCorrelation_restrictedReciprocalKernel_Ioc_eq_abs
    (x : ℝ) (y y' A B v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    ‖kernelCorrelation (Finset.Ioc A B)
        (restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ =
      ‖reciprocalExpSum
        |x * (1 / (w : ℝ) - 1 / (v : ℝ))|
        (max A (max (y / v) (y / w)))
        (min B (min (y' / v) (y' / w)))‖ := by
  rw [kernelCorrelation_restrictedReciprocalKernel_Ioc_eq x y y' A B v w hv hw]
  change ‖reciprocalExpSum
      (x * (1 / (w : ℝ) - 1 / (v : ℝ)))
      (max A (max (y / v) (y / w)))
      (min B (min (y' / v) (y' / w)))‖ = _
  by_cases hphase : 0 ≤ x * (1 / (w : ℝ) - 1 / (v : ℝ))
  · rw [abs_of_nonneg hphase]
  · rw [abs_of_neg (lt_of_not_ge hphase)]
    exact (norm_reciprocalExpSum_neg
      (x * (1 / (w : ℝ) - 1 / (v : ℝ)))
      (max A (max (y / v) (y / w)))
      (min B (min (y' / v) (y' / w)))).symm

/-- The exact finite bilinear reciprocal sum to which Proposition 9.4 is
applied.  The product restriction encodes the paper's arbitrary interval
`uv ∈ I`. -/
noncomputable def reciprocalBilinearSum
    (I uSupport vSupport : Finset ℕ) (x : ℝ)
    (alpha beta : ℕ → ℂ) : ℂ :=
  bilinearSum uSupport vSupport alpha beta
    (restrictedReciprocalKernel I x)

lemma reciprocalBilinearSum_eq
    (I uSupport vSupport : Finset ℕ) (x : ℝ)
    (alpha beta : ℕ → ℂ) :
    reciprocalBilinearSum I uSupport vSupport x alpha beta =
      ∑ u ∈ uSupport, ∑ v ∈ vSupport,
        if u * v ∈ I then alpha u * beta v * e (x / ((u * v : ℕ) : ℝ))
        else 0 := by
  unfold reciprocalBilinearSum bilinearSum innerSum restrictedReciprocalKernel
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> ring

/-- The product-restricted reciprocal bilinear sum is symmetric after
swapping the two supports and their coefficient sequences.  This permits
each dyadic rectangle to be oriented with its larger side as the
Cauchy--Schwarz variable. -/
lemma reciprocalBilinearSum_comm
    (I uSupport vSupport : Finset ℕ) (x : ℝ)
    (alpha beta : ℕ → ℂ) :
    reciprocalBilinearSum I uSupport vSupport x alpha beta =
      reciprocalBilinearSum I vSupport uSupport x beta alpha := by
  rw [reciprocalBilinearSum_eq, reciprocalBilinearSum_eq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  by_cases huv : u * v ∈ I
  · rw [if_pos huv]
    have hvu : v * u ∈ I := by simpa [Nat.mul_comm] using huv
    rw [if_pos hvu]
    simp only [Nat.mul_comm]
    ring
  · rw [if_neg huv]
    have hvu : v * u ∉ I := by simpa [Nat.mul_comm] using huv
    rw [if_neg hvu]

/-- In the residual branch of the reciprocal exponential-sum estimate the
one-step upper-frequency condition has failed, while the two-step
lower-frequency condition has also failed.  These two failures force the
remaining summation interval to be short.  This polynomial form avoids any
rounding issues involving fractional powers: if `N` is the interval length,
then `N⁴ ≤ 256 C³`.

Downstream we use this as the elementary source of the harmless
`4 * C^(3/4)` residual term. -/
lemma residual_interval_length_fourth_le
    (C N : ℕ) (t : ℝ) (hC : 0 < C) (hN : 0 < N)
    (hmiddle : (C : ℝ) ^ 3 < 4 * t)
    (hhighFails : 12 * t * (Nat.sqrt N : ℝ) ^ 3 ≤ (C : ℝ) ^ 4) :
    N ^ 4 ≤ 256 * C ^ 3 := by
  let s := Nat.sqrt N
  have hs : 0 < s := by
    dsimp only [s]
    exact Nat.sqrt_pos.mpr hN
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hscaled :
      3 * (C : ℝ) ^ 3 * (s : ℝ) ^ 3 <
        12 * t * (s : ℝ) ^ 3 := by
    have hmul := mul_lt_mul_of_pos_right hmiddle
      (mul_pos (by norm_num : (0 : ℝ) < 3) (pow_pos hsR 3))
    nlinarith
  have hcancel : (s : ℝ) ^ 3 < (C : ℝ) := by
    have hCpos : 0 < (C : ℝ) := by exact_mod_cast hC
    have hcombined :
        3 * (C : ℝ) ^ 3 * (s : ℝ) ^ 3 < (C : ℝ) ^ 4 :=
      hscaled.trans_le hhighFails
    have hC3pos : 0 < (C : ℝ) ^ 3 := pow_pos hCpos 3
    by_contra hnot
    have hle : (C : ℝ) ≤ (s : ℝ) ^ 3 := le_of_not_gt hnot
    have hmulNonneg :
        0 ≤ (C : ℝ) ^ 3 * ((s : ℝ) ^ 3 - (C : ℝ)) :=
      mul_nonneg hC3pos.le (sub_nonneg.mpr hle)
    nlinarith [pow_pos hCpos 4]
  have hscube : s ^ 3 ≤ C := by
    have hscubeLt : s ^ 3 < C := by exact_mod_cast hcancel
    exact hscubeLt.le
  have hNsq : N ≤ 4 * s ^ 2 := by
    have hsOne : 1 ≤ s := hs
    have hroot := Nat.lt_succ_sqrt N
    dsimp only [s] at hroot ⊢
    nlinarith
  have hpow := Nat.pow_le_pow_left hNsq 4
  have hsEightNine : s ^ 8 ≤ s ^ 9 := by
    rw [show s ^ 9 = s ^ 8 * s by ring]
    exact Nat.le_mul_of_pos_right _ hs
  calc
    N ^ 4 ≤ (4 * s ^ 2) ^ 4 := hpow
    _ = 256 * s ^ 8 := by ring
    _ ≤ 256 * s ^ 9 := Nat.mul_le_mul_left 256 hsEightNine
    _ = 256 * (s ^ 3) ^ 3 := by ring
    _ ≤ 256 * C ^ 3 :=
      Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left hscube 3)

/-- Fourth-root form of `residual_interval_length_fourth_le`. -/
lemma residual_interval_length_le_three_quarters
    (C N : ℕ) (hfourth : N ^ 4 ≤ 256 * C ^ 3) :
    (N : ℝ) ≤ 4 * (C : ℝ) ^ (3 / 4 : ℝ) := by
  have hC0 : 0 ≤ (C : ℝ) := by positivity
  have hCp : ((C : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = (C : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast hC0]
    norm_num [Real.rpow_natCast]
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
  rw [mul_pow, hCp]
  norm_num
  exact_mod_cast hfourth

/-- Interpolation for the difficult middle-frequency residual.  If `q` is
simultaneously bounded by the correlation length and by the one-step
reciprocal estimate, while the two-step high-frequency inequality fails,
then its seventh power has the uniform `C⁶` scale.  This is the
power-saving substitute for taking either of the two bounds separately. -/
lemma effective_k1_highFailure_seventh_le
    (C N : ℕ) (t L q : ℝ) (hC : 0 < C) (hN : 0 < N)
    (ht : 0 ≤ t) (hL : 0 ≤ L) (hq : 0 ≤ q)
    (hqN : q ≤ (N : ℝ))
    (hqK : q ≤ 24 * (C : ℝ) * Real.sqrt (t / (C : ℝ) ^ 3) *
      Real.sqrt L)
    (hhighFails : 12 * t * (Nat.sqrt N : ℝ) ^ 3 ≤ (C : ℝ) ^ 4) :
    q ^ 7 ≤ 147456 * (C : ℝ) ^ 6 * L ^ 2 := by
  let s := Nat.sqrt N
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast hC
  have hs : 0 < s := by
    dsimp only [s]
    exact Nat.sqrt_pos.mpr hN
  have hsR : 0 ≤ (s : ℝ) := by positivity
  have hNsqNat : N ≤ 4 * s ^ 2 := by
    have hroot := Nat.lt_succ_sqrt N
    dsimp only [s] at hroot ⊢
    nlinarith
  have hNsq : (N : ℝ) ≤ 4 * (s : ℝ) ^ 2 := by
    exact_mod_cast hNsqNat
  have hq3 : q ^ 3 ≤ 64 * (s : ℝ) ^ 6 := by
    calc
      q ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hq hqN 3
      _ ≤ (4 * (s : ℝ) ^ 2) ^ 3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg N) hNsq 3
      _ = 64 * (s : ℝ) ^ 6 := by ring
  have hratio : 0 ≤ t / (C : ℝ) ^ 3 :=
    div_nonneg ht (pow_nonneg hCpos.le 3)
  have hsratio : Real.sqrt (t / (C : ℝ) ^ 3) ^ 2 =
      t / (C : ℝ) ^ 3 := Real.sq_sqrt hratio
  have hsL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL
  let K := 24 * (C : ℝ) * Real.sqrt (t / (C : ℝ) ^ 3) * Real.sqrt L
  have hq4 : q ^ 4 ≤ K ^ 4 :=
    pow_le_pow_left₀ hq (by simpa only [K] using hqK) 4
  have hKscaled : (C : ℝ) ^ 2 * K ^ 4 = 24 ^ 4 * t ^ 2 * L ^ 2 := by
    dsimp only [K]
    rw [show (24 * (C : ℝ) * Real.sqrt (t / (C : ℝ) ^ 3) *
        Real.sqrt L) ^ 4 =
        24 ^ 4 * (C : ℝ) ^ 4 *
          (Real.sqrt (t / (C : ℝ) ^ 3) ^ 2) ^ 2 *
          (Real.sqrt L ^ 2) ^ 2 by ring, hsratio, hsL]
    field_simp
  have hq4scaled : (C : ℝ) ^ 2 * q ^ 4 ≤ 24 ^ 4 * t ^ 2 * L ^ 2 := by
    calc
      (C : ℝ) ^ 2 * q ^ 4 ≤ (C : ℝ) ^ 2 * K ^ 4 :=
        mul_le_mul_of_nonneg_left hq4 (sq_nonneg _)
      _ = 24 ^ 4 * t ^ 2 * L ^ 2 := hKscaled
  have hhighSq : 144 * t ^ 2 * (s : ℝ) ^ 6 ≤ (C : ℝ) ^ 8 := by
    have hleft : 0 ≤ 12 * t * (s : ℝ) ^ 3 := by positivity
    have hsquare := pow_le_pow_left₀ hleft
      (by simpa only [s] using hhighFails) 2
    nlinarith
  have hscaled : (C : ℝ) ^ 2 * q ^ 7 ≤
      (C : ℝ) ^ 2 * (147456 * (C : ℝ) ^ 6 * L ^ 2) := by
    have hmul := mul_le_mul hq3 hq4scaled
      (mul_nonneg (sq_nonneg _) (pow_nonneg hq 4))
      (mul_nonneg (by positivity) (pow_nonneg hsR 6))
    nlinarith [mul_nonneg (sq_nonneg L)
      (sub_nonneg.mpr hhighSq)]
  by_contra hnot
  have hlt : 147456 * (C : ℝ) ^ 6 * L ^ 2 < q ^ 7 :=
    lt_of_not_ge hnot
  have hscaledLt := mul_lt_mul_of_pos_left hlt (sq_pos_of_pos hCpos)
  exact (not_lt_of_ge hscaled) hscaledLt

/-- A convenient seventh-root form of the preceding polynomial bound.
The round coefficient `128` is deliberately generous; its seventh power
dominates `147456`. -/
lemma effective_k1_highFailure_le
    (C : ℕ) (L q : ℝ) (hC : 0 < C) (hL : 0 ≤ L)
    (hseven : q ^ 7 ≤ 147456 * (C : ℝ) ^ 6 * L ^ 2) :
    q ≤ 128 * (C : ℝ) ^ (6 / 7 : ℝ) * L ^ (2 / 7 : ℝ) := by
  have hC0 : 0 ≤ (C : ℝ) := by positivity
  have hCp : ((C : ℝ) ^ (6 / 7 : ℝ)) ^ 7 = (C : ℝ) ^ 6 := by
    rw [← Real.rpow_mul_natCast hC0]
    norm_num [Real.rpow_natCast]
  have hLp : (L ^ (2 / 7 : ℝ)) ^ 7 = L ^ 2 := by
    rw [← Real.rpow_mul_natCast hL]
    norm_num [Real.rpow_natCast]
  have hrhs :
      (128 * (C : ℝ) ^ (6 / 7 : ℝ) * L ^ (2 / 7 : ℝ)) ^ 7 =
        128 ^ 7 * (C : ℝ) ^ 6 * L ^ 2 := by
    rw [mul_pow, mul_pow, hCp, hLp]
  apply le_of_pow_le_pow_left₀ (by norm_num : (7 : ℕ) ≠ 0) (by positivity)
  rw [hrhs]
  calc
    q ^ 7 ≤ 147456 * (C : ℝ) ^ 6 * L ^ 2 := hseven
    _ ≤ 128 ^ 7 * (C : ℝ) ^ 6 * L ^ 2 := by gcongr <;> norm_num

/-- The integer near-pair threshold used on the power block of length
`2^j`.  Taking the exponent floor at the integer level makes the threshold
exactly computable while retaining the scale `(2^j)^(3/4)`. -/
def powerBlockThreshold (j : ℕ) : ℕ := 2 ^ (3 * j / 4)

@[simp] lemma powerBlockThreshold_pos (j : ℕ) :
    0 < powerBlockThreshold j := by
  simp [powerBlockThreshold]

/-- The near threshold never exceeds the length of its power block. -/
lemma powerBlockThreshold_le_two_pow (j : ℕ) :
    powerBlockThreshold j ≤ 2 ^ j := by
  unfold powerBlockThreshold
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Removing the floor in `3j/4` costs at most the factor `2³`.  This is
the polynomial inequality used when a fourth power of the near threshold
is compared with a cube of the outer block length. -/
lemma two_pow_cube_le_eight_powerBlockThreshold_fourth (j : ℕ) :
    (2 ^ j) ^ 3 ≤ 8 * powerBlockThreshold j ^ 4 := by
  have hexp : 3 * j ≤ 4 * (3 * j / 4) + 3 := by omega
  have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
  unfold powerBlockThreshold
  calc
    (2 ^ j) ^ 3 = 2 ^ (3 * j) := by rw [← pow_mul]; congr 1; omega
    _ ≤ 2 ^ (4 * (3 * j / 4) + 3) := hp
    _ = 8 * (2 ^ (3 * j / 4)) ^ 4 := by
      rw [pow_add, ← pow_mul]
      simp [Nat.mul_comm]

/-- Fully unconditional Type II estimate for the actual reciprocal kernel.
It is the trivial part of Proposition 9.4 and is also used for the near-pair
range before the sharper reciprocal exponential-sum theorem is invoked. -/
lemma norm_reciprocalBilinearSum_le_trivial
    (I uSupport vSupport : Finset ℕ) (x : ℝ)
    (alpha beta : ℕ → ℂ) :
    ‖reciprocalBilinearSum I uSupport vSupport x alpha beta‖ ≤
      l2Norm uSupport alpha *
        Real.sqrt ((uSupport.card : ℝ) * (vSupport.card : ℝ)) *
          l2Norm vSupport beta := by
  apply norm_bilinearSum_le_of_norm_kernel_le_one
  intro u hu v hv
  exact norm_restrictedReciprocalKernel_le_one I x u v

/-- The standard dyadic support `(U,2U]`. -/
def dyadicNatBlock (U : ℕ) : Finset ℕ := Finset.Ioc U (2 * U)

@[simp] lemma card_dyadicNatBlock (U : ℕ) : (dyadicNatBlock U).card = U := by
  simp [dyadicNatBlock]
  omega

/-- On a rectangular block, the Gram kernel is exactly the unweighted
reciprocal exponential sum to which Proposition 8.1 applies. -/
lemma kernelCorrelation_reciprocalKernel_eq
    (x : ℝ) (U v w : ℕ) (hU : 1 ≤ U) (hv : v ≠ 0) (hw : w ≠ 0) :
    kernelCorrelation (dyadicNatBlock U) (reciprocalKernel x) v w =
      ∑ u ∈ Finset.Ioc U (2 * U),
        e ((x * (1 / (w : ℝ) - 1 / (v : ℝ))) / (u : ℝ)) := by
  unfold kernelCorrelation reciprocalKernel dyadicNatBlock
  apply Finset.sum_congr rfl
  intro u hu
  have huI := Finset.mem_Ioc.mp hu
  have hu0 : (u : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : u ≠ 0)
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hw0 : (w : ℝ) ≠ 0 := by exact_mod_cast hw
  rw [conj_e, ← e_add]
  congr 1
  push_cast
  field_simp
  ring

/-- The source-shaped trivial estimate `‖alpha‖₂ ‖beta‖₂ sqrt(UV)` on one dyadic
block.  This declaration has no abstract analytic premise. -/
lemma norm_reciprocalBilinearSum_dyadic_le_trivial
    (I : Finset ℕ) (x : ℝ) (U V : ℕ) (alpha beta : ℕ → ℂ) :
    ‖reciprocalBilinearSum I (dyadicNatBlock U) (dyadicNatBlock V)
        x alpha beta‖ ≤
      l2Norm (dyadicNatBlock U) alpha *
        Real.sqrt ((U : ℝ) * (V : ℝ)) *
          l2Norm (dyadicNatBlock V) beta := by
  simpa using norm_reciprocalBilinearSum_le_trivial I
    (dyadicNatBlock U) (dyadicNatBlock V) x alpha beta

/-! ## Concrete Vaughan coefficient input -/

open VaughanFourSums

/-- On a positive input, the coefficient `a_z = μ_{≤z} * ζ` is exactly
the truncated Möbius divisor sum estimated in Proposition 10.1. -/
lemma aCoeff_eq_truncatedMobiusDivisorSum
    (z n : ℕ) (hn : 0 < n) :
    aCoeff z n = truncatedMobiusDivisorSum z n := by
  rw [aCoeff, ArithmeticFunction.coe_mul_zeta_apply]
  simp only [Vaughan.muLow, ArithmeticFunction.coe_mk]
  rw [← Finset.sum_filter]
  unfold truncatedMobiusDivisorSum
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd, _⟩, hdz⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, hdz⟩, hd⟩
  · rintro ⟨⟨_hdpos, hdz⟩, hd⟩
    exact ⟨⟨hd, hn.ne'⟩, hdz⟩

/-- At a power of two, the truncated Möbius divisor sum is either `1`
or `0`: only the divisors `1` and `2` can contribute.  This controls the
single endpoint by which a closed-open power block differs from `(N,2N]`. -/
lemma abs_aCoeff_two_pow_le_one (M j : ℕ) (hM : 1 ≤ M) :
    |aCoeff M (2 ^ j)| ≤ 1 := by
  rw [aCoeff, ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow Nat.prime_two]
  simp only [Vaughan.muLow, ArithmeticFunction.coe_mk]
  let t : ℕ → ℝ := fun i ↦
    if 2 ^ i ≤ M then (ArithmeticFunction.moebius (2 ^ i) : ℝ) else 0
  change |∑ i ∈ Finset.range (j + 1), t i| ≤ 1
  have ht0 : t 0 = 1 := by simp [t, hM]
  have ht_ge_two (i : ℕ) (hi : 2 ≤ i) : t i = 0 := by
    simp only [t]
    split_ifs
    · rw [ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by omega)]
      simp [show i ≠ 1 by omega]
    · rfl
  rcases eq_or_lt_of_le hM with rfl | htwo
  · have ht_pos (i : ℕ) (hi : 1 ≤ i) : t i = 0 := by
      simp [t, show ¬ 2 ^ i ≤ 1 by
        exact not_le.mpr (Nat.one_lt_pow (by omega) (by norm_num))]
    have hsum : ∀ j : ℕ, ∑ i ∈ Finset.range (j + 1), t i = 1 := by
      intro k
      induction k with
      | zero => simpa using ht0
      | succ k ih =>
          rw [show k + 1 + 1 = (k + 1) + 1 by omega,
            Finset.sum_range_succ, ih, ht_pos (k + 1) (by omega), add_zero]
    rw [hsum j]
    norm_num
  · have ht1 : t 1 = -1 := by
      have h2M : 2 ≤ M := by omega
      simp [t, h2M, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    have hsum : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 2), t i = 0 := by
      intro k
      induction k with
      | zero =>
          rw [show 0 + 2 = (1 : ℕ) + 1 by omega, Finset.sum_range_succ]
          simp [ht0, ht1]
      | succ k ih =>
          rw [show k + 1 + 2 = (k + 2) + 1 by omega,
            Finset.sum_range_succ, ih, ht_ge_two (k + 2) (by omega), add_zero]
    by_cases hj : j = 0
    · subst j
      simp [ht0]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := by
        exact ⟨j - 1, by omega⟩
      rw [show k + 1 + 1 = k + 2 by omega, hsum k]
      norm_num

/-- Proposition 10.1, transported to the actual complex `a` coefficients
on a dyadic block. -/
lemma sum_norm_aCoeff_sq_le (N z : ℕ) (hz : 1 ≤ z) :
    (∑ n ∈ dyadicNatBlock N, ‖((aCoeff z n : ℝ) : ℂ)‖ ^ 2) ≤
      (8 / 9 : ℝ) * (N : ℝ) * (Real.log z + 3) ^ 3 := by
  rw [show dyadicNatBlock N = Finset.Ioc N (2 * N) from rfl]
  have h := granville_ramare_prop_10_1 N z hz
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [aCoeff_eq_truncatedMobiusDivisorSum z n (by
    have := (Finset.mem_Ioc.mp hn).1
    omega)]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The preceding estimate stated through the local `L²` norm API. -/
lemma l2Norm_aCoeff_sq_le (N z : ℕ) (hz : 1 ≤ z) :
    l2Norm (dyadicNatBlock N) (fun n ↦ ((aCoeff z n : ℝ) : ℂ)) ^ 2 ≤
      (8 / 9 : ℝ) * (N : ℝ) * (Real.log z + 3) ^ 3 := by
  rw [l2Norm_sq]
  exact sum_norm_aCoeff_sq_le N z hz

/-- Square-root form of Proposition 10.1 for the `a` coefficients. -/
lemma l2Norm_aCoeff_le (N z : ℕ) (hz : 1 ≤ z) :
    l2Norm (dyadicNatBlock N) (fun n ↦ ((aCoeff z n : ℝ) : ℂ)) ≤
      Real.sqrt ((8 / 9 : ℝ) * (N : ℝ) * (Real.log z + 3) ^ 3) := by
  unfold l2Norm
  exact Real.sqrt_le_sqrt (sum_norm_aCoeff_sq_le N z hz)

/-- The actual `b_r = μ_{≤M} * Λ_{≤K}` coefficients satisfy the same
elementary dyadic second-moment estimate as any sequence bounded by `log r`. -/
lemma sum_norm_bCoeff_sq_le (R M K : ℕ) (hR : 1 ≤ R) :
    (∑ r ∈ dyadicNatBlock R, ‖((bCoeff M K r : ℝ) : ℂ)‖ ^ 2) ≤
      (R : ℝ) * Real.log (2 * R : ℕ) ^ 2 := by
  have hterm (r : ℕ) (hr : r ∈ dyadicNatBlock R) :
      ‖((bCoeff M K r : ℝ) : ℂ)‖ ^ 2 ≤ Real.log (2 * R : ℕ) ^ 2 := by
    have hrI : R < r ∧ r ≤ 2 * R := by
      simpa [dyadicNatBlock] using Finset.mem_Ioc.mp hr
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hlogle : Real.log (r : ℝ) ≤ Real.log (2 * R : ℕ) :=
      Real.log_le_log hrpos (by exact_mod_cast hrI.2)
    have habs := abs_bCoeff_le_log M K r
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (habs.trans hlogle) 2
  calc
    (∑ r ∈ dyadicNatBlock R, ‖((bCoeff M K r : ℝ) : ℂ)‖ ^ 2)
        ≤ ∑ _r ∈ dyadicNatBlock R, Real.log (2 * R : ℕ) ^ 2 := by
          apply Finset.sum_le_sum
          intro r hr
          exact hterm r hr
    _ = (R : ℝ) * Real.log (2 * R : ℕ) ^ 2 := by simp

/-- The `b`-coefficient estimate through the local `L²` norm API. -/
lemma l2Norm_bCoeff_sq_le (R M K : ℕ) (hR : 1 ≤ R) :
    l2Norm (dyadicNatBlock R) (fun r ↦ ((bCoeff M K r : ℝ) : ℂ)) ^ 2 ≤
      (R : ℝ) * Real.log (2 * R : ℕ) ^ 2 := by
  rw [l2Norm_sq]
  exact sum_norm_bCoeff_sq_le R M K hR

/-- Square-root form of the `b`-coefficient second moment. -/
lemma l2Norm_bCoeff_le (R M K : ℕ) (hR : 1 ≤ R) :
    l2Norm (dyadicNatBlock R) (fun r ↦ ((bCoeff M K r : ℝ) : ℂ)) ≤
      Real.sqrt ((R : ℝ) * Real.log (2 * R : ℕ) ^ 2) := by
  unfold l2Norm
  exact Real.sqrt_le_sqrt (sum_norm_bCoeff_sq_le R M K hR)

/-- A coarse but completely explicit second-moment estimate for the von
Mangoldt coefficients on `(K,2K]`.  Granville--Ramaré use the sharper
`1.285 K log(2K)` estimate; this elementary `K log(2K)^2` bound costs only
one additional logarithm and preserves the decisive power saving. -/
lemma sum_norm_vonMangoldt_sq_le (K : ℕ) (hK : 1 ≤ K) :
    (∑ k ∈ dyadicNatBlock K,
        ‖((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)‖ ^ 2) ≤
      (K : ℝ) * Real.log (2 * K : ℕ) ^ 2 := by
  have hterm (k : ℕ) (hk : k ∈ dyadicNatBlock K) :
      ‖((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)‖ ^ 2 ≤
        Real.log (2 * K : ℕ) ^ 2 := by
    have hkI : K < k ∧ k ≤ 2 * K := by
      simpa [dyadicNatBlock] using Finset.mem_Ioc.mp hk
    have hkposNat : 0 < k := by omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkposNat
    have hlogle : Real.log (k : ℝ) ≤ Real.log (2 * K : ℕ) := by
      exact Real.log_le_log hkpos (by exact_mod_cast hkI.2)
    have hlam_nonneg : 0 ≤ ArithmeticFunction.vonMangoldt k :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hlam_le : ArithmeticFunction.vonMangoldt k ≤ Real.log (2 * K : ℕ) :=
      ArithmeticFunction.vonMangoldt_le_log.trans hlogle
    rw [Complex.norm_of_nonneg hlam_nonneg]
    exact pow_le_pow_left₀ hlam_nonneg hlam_le 2
  calc
    (∑ k ∈ dyadicNatBlock K,
        ‖((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)‖ ^ 2)
        ≤ ∑ _k ∈ dyadicNatBlock K, Real.log (2 * K : ℕ) ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm k hk
    _ = (K : ℝ) * Real.log (2 * K : ℕ) ^ 2 := by simp

/-- The preceding estimate stated through the local `L²` norm API. -/
lemma l2Norm_vonMangoldt_sq_le (K : ℕ) (hK : 1 ≤ K) :
    l2Norm (dyadicNatBlock K)
        (fun k ↦ ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ^ 2 ≤
      (K : ℝ) * Real.log (2 * K : ℕ) ^ 2 := by
  rw [l2Norm_sq]
  exact sum_norm_vonMangoldt_sq_le K hK

/-- Square-root form of the elementary von Mangoldt second moment. -/
lemma l2Norm_vonMangoldt_le (K : ℕ) (hK : 1 ≤ K) :
    l2Norm (dyadicNatBlock K)
        (fun k ↦ ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ≤
      Real.sqrt ((K : ℝ) * Real.log (2 * K : ℕ) ^ 2) := by
  unfold l2Norm
  exact Real.sqrt_le_sqrt (sum_norm_vonMangoldt_sq_le K hK)

end ReciprocalKernel

section DyadicAssembly

variable {J : Type*} [DecidableEq J]

/-- Triangle inequality followed by Cauchy--Schwarz across a finite family
of dyadic blocks. -/
lemma norm_sum_blocks_le (blocks : Finset J) (blockSum : J → ℂ)
    (A B : J → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ j ∈ blocks, 0 ≤ A j) (hB : ∀ j ∈ blocks, 0 ≤ B j)
    (hblock : ∀ j ∈ blocks, ‖blockSum j‖ ≤ C * A j * B j) :
    ‖∑ j ∈ blocks, blockSum j‖ ≤
      C * Real.sqrt (∑ j ∈ blocks, A j ^ 2) *
        Real.sqrt (∑ j ∈ blocks, B j ^ 2) := by
  classical
  have hsum_nonneg : 0 ≤ ∑ j ∈ blocks, A j * B j := by
    exact Finset.sum_nonneg fun j hj ↦ mul_nonneg (hA j hj) (hB j hj)
  have hcs :
      (∑ j ∈ blocks, A j * B j) ≤
        Real.sqrt (∑ j ∈ blocks, A j ^ 2) *
          Real.sqrt (∑ j ∈ blocks, B j ^ 2) := by
    calc
      (∑ j ∈ blocks, A j * B j)
          ≤ Real.sqrt ((∑ j ∈ blocks, A j ^ 2) *
              ∑ j ∈ blocks, B j ^ 2) := by
            apply Real.le_sqrt_of_sq_le
            exact Finset.sum_mul_sq_le_sq_mul_sq blocks A B
      _ = Real.sqrt (∑ j ∈ blocks, A j ^ 2) *
            Real.sqrt (∑ j ∈ blocks, B j ^ 2) := by
            rw [Real.sqrt_mul]
            exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  calc
    ‖∑ j ∈ blocks, blockSum j‖
        ≤ ∑ j ∈ blocks, ‖blockSum j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ blocks, C * A j * B j :=
      Finset.sum_le_sum fun j hj ↦ hblock j hj
    _ = C * ∑ j ∈ blocks, A j * B j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ C * (Real.sqrt (∑ j ∈ blocks, A j ^ 2) *
          Real.sqrt (∑ j ∈ blocks, B j ^ 2)) :=
      mul_le_mul_of_nonneg_left hcs hC
    _ = C * Real.sqrt (∑ j ∈ blocks, A j ^ 2) *
          Real.sqrt (∑ j ∈ blocks, B j ^ 2) := by ring

/-- A dyadic family of Type II blocks.  The same reciprocal mean-square
constant `R` may be used on every block; disjointness or bounded-overlap
information is subsequently supplied through the two sums of squared local
`L²` norms. -/
lemma norm_sum_bilinearBlocks_le
    {U V : Type*} [DecidableEq U] [DecidableEq V]
    (blocks : Finset J) (uSupport : J → Finset U) (vSupport : J → Finset V)
    (alpha : J → U → ℂ) (beta : J → V → ℂ)
    (kernel : J → U → V → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hinner : ∀ j ∈ blocks,
      ReciprocalInnerBound (uSupport j) (vSupport j) (beta j) (kernel j) R) :
    ‖∑ j ∈ blocks,
        bilinearSum (uSupport j) (vSupport j) (alpha j) (beta j) (kernel j)‖ ≤
      Real.sqrt R *
        Real.sqrt (∑ j ∈ blocks, l2Norm (uSupport j) (alpha j) ^ 2) *
          Real.sqrt (∑ j ∈ blocks, l2Norm (vSupport j) (beta j) ^ 2) := by
  apply norm_sum_blocks_le blocks
    (fun j ↦ bilinearSum (uSupport j) (vSupport j)
      (alpha j) (beta j) (kernel j))
    (fun j ↦ l2Norm (uSupport j) (alpha j))
    (fun j ↦ l2Norm (vSupport j) (beta j))
    (Real.sqrt R) (Real.sqrt_nonneg _)
  · intro j hj
    exact l2Norm_nonneg _ _
  · intro j hj
    exact l2Norm_nonneg _ _
  · intro j hj
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      norm_bilinearSum_le_of_reciprocalInnerBound
        (uSupport j) (vSupport j) (alpha j) (beta j) (kernel j) R hR
        (hinner j hj)

end DyadicAssembly

section ExplicitConstant

/-- The purely numerical rounding at the end of Granville--Ramaré,
Corollary 9.7(b).  The unrounded coefficient is at most
`sqrt 68 * (2/3)^(1/4) * sqrt 2`; this is below `10.54 = 527/50`.

Writing the fourth root as `sqrt (sqrt (2/3))` keeps the certificate within
elementary ordered-field arithmetic and `Real.sqrt`. -/
lemma gr_typeII_coefficient_le :
    Real.sqrt 68 * Real.sqrt (Real.sqrt ((2 : ℝ) / 3)) * Real.sqrt 2 ≤
      (527 : ℝ) / 50 := by
  have h68 : 0 ≤ (68 : ℝ) := by norm_num
  have h23 : 0 ≤ (2 : ℝ) / 3 := by norm_num
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hs68 : Real.sqrt (68 : ℝ) ^ 2 = 68 := Real.sq_sqrt h68
  have hs23 : Real.sqrt ((2 : ℝ) / 3) ^ 2 = (2 : ℝ) / 3 :=
    Real.sq_sqrt h23
  have hss23 : Real.sqrt (Real.sqrt ((2 : ℝ) / 3)) ^ 2 =
      Real.sqrt ((2 : ℝ) / 3) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt h2
  have hprod_nonneg :
      0 ≤ Real.sqrt 68 * Real.sqrt (Real.sqrt ((2 : ℝ) / 3)) * Real.sqrt 2 := by
    positivity
  have hc_nonneg : 0 ≤ (527 : ℝ) / 50 := by norm_num
  have hfourth :
      (Real.sqrt 68 * Real.sqrt (Real.sqrt ((2 : ℝ) / 3)) * Real.sqrt 2) ^ 4 ≤
        ((527 : ℝ) / 50) ^ 4 := by
    calc
      (Real.sqrt 68 * Real.sqrt (Real.sqrt ((2 : ℝ) / 3)) * Real.sqrt 2) ^ 4
          = (Real.sqrt 68 ^ 2) ^ 2 *
              (Real.sqrt (Real.sqrt ((2 : ℝ) / 3)) ^ 2) ^ 2 *
                (Real.sqrt 2 ^ 2) ^ 2 := by ring
      _ = 68 ^ 2 * Real.sqrt ((2 : ℝ) / 3) ^ 2 * 2 ^ 2 := by
        rw [hs68, hss23, hs2]
      _ = 68 ^ 2 * ((2 : ℝ) / 3) * 2 ^ 2 := by rw [hs23]
      _ ≤ ((527 : ℝ) / 50) ^ 4 := by norm_num
  by_contra hnot
  have hlt : (527 : ℝ) / 50 <
      Real.sqrt 68 * Real.sqrt (Real.sqrt ((2 : ℝ) / 3)) * Real.sqrt 2 :=
    lt_of_not_ge hnot
  have hpow_lt := pow_lt_pow_left₀ hlt hc_nonneg (by norm_num : 4 ≠ 0)
  exact (not_lt_of_ge hfourth) hpow_lt

/-- A source-shaped constant propagation lemma.  Once a block estimate has
the unrounded coefficient and a nonnegative scale `T`, the published `10.54`
constant follows without any further analytic assumption. -/
lemma norm_le_gr_constant {z : ℂ} {A B T : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hz : ‖z‖ ≤
      (Real.sqrt 68 * Real.sqrt (Real.sqrt ((2 : ℝ) / 3)) * Real.sqrt 2) *
        A * B * T) :
    ‖z‖ ≤ (527 / 50 : ℝ) * A * B * T := by
  calc
    ‖z‖ ≤ (Real.sqrt 68 * Real.sqrt (Real.sqrt ((2 : ℝ) / 3)) * Real.sqrt 2) *
        A * B * T := hz
    _ ≤ (527 / 50 : ℝ) * A * B * T := by
      gcongr
      exact gr_typeII_coefficient_le

end ExplicitConstant

#print axioms bilinear_cauchy_sq
#print axioms norm_bilinearSum_le_of_reciprocalInnerBound
#print axioms norm_bilinearSum_le_of_diagonal_offDiagonal
#print axioms kernelCorrelation_restrictedReciprocalKernel_eq
#print axioms residual_interval_length_fourth_le
#print axioms effective_k1_highFailure_seventh_le
#print axioms effective_k1_highFailure_le
#print axioms abs_aCoeff_two_pow_le_one
#print axioms l2Norm_aCoeff_sq_le
#print axioms l2Norm_bCoeff_sq_le
#print axioms l2Norm_vonMangoldt_sq_le
#print axioms norm_sum_bilinearBlocks_le
#print axioms gr_typeII_coefficient_le

end Erdos175.TypeII

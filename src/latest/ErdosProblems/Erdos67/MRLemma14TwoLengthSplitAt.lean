import ErdosProblems.Erdos67.MRLemma14SingleLengthSplit
import ErdosProblems.Erdos67.MRLemma14UncenteredJoin
import ErdosProblems.Erdos67.MRDyadicCover

/-!
# Spatially decoupled two-length Lemma 14 join

The exact two-dyadic cover has spatial starting points in `(X,2X]`, but
its second coefficient polynomial is restricted at scale `Y = 2X`.
This file supplies the missing `Y`/`X`-decoupled versions of the corrected
Perron limit, low-frequency estimate, and uncentered recovery.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

def dyadicTwoLengthShortMeanSquareAt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H₁ H₂ : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq
      (dyadicRestrictedShortAverage S f Y x H₁ -
        dyadicRestrictedShortAverage S f Y x H₂)

def dyadicTwoLengthCorrectedPerronMeanSquareAt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H₁ H₂ : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq
      (dyadicRestrictedCorrectedPerronAverage S f Y x H₁ T -
        dyadicRestrictedCorrectedPerronAverage S f Y x H₂ T)

def dyadicTwoLengthPerronTruncationErrorMeanSquareAt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H₁ H₂ : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    (lemma14PerronTruncationError
        (dyadicRestrictedCoefficient S f Y) x H₁ T +
      lemma14PerronTruncationError
        (dyadicRestrictedCoefficient S f Y) x H₂ T) ^ 2

theorem tendsto_dyadicTwoLengthPerronTruncationErrorMeanSquareAt_atTop
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H₁ H₂ : ℕ) :
    Filter.Tendsto (fun T : ℝ ↦
        dyadicTwoLengthPerronTruncationErrorMeanSquareAt
          S f Y X H₁ H₂ T)
      Filter.atTop (nhds 0) := by
  unfold dyadicTwoLengthPerronTruncationErrorMeanSquareAt
  simpa using tendsto_finsetSum (Finset.Ioc X (2 * X)) (fun x hx ↦
    (((tendsto_lemma14PerronTruncationError_atTop
        (dyadicRestrictedCoefficient S f Y) x H₁).add
      (tendsto_lemma14PerronTruncationError_atTop
        (dyadicRestrictedCoefficient S f Y) x H₂)).pow 2))

theorem exists_dyadicTwoLengthPerronTruncationErrorMeanSquareAt_lt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H₁ H₂ : ℕ)
    {e : ℝ} (he : 0 < e) :
    ∃ U₀ : ℝ, ∀ U ≥ U₀,
      dyadicTwoLengthPerronTruncationErrorMeanSquareAt
        S f Y X H₁ H₂ U < e := by
  obtain ⟨U₀, hU₀⟩ := Metric.tendsto_atTop.mp
    (tendsto_dyadicTwoLengthPerronTruncationErrorMeanSquareAt_atTop
      S f Y X H₁ H₂) e he
  refine ⟨U₀, fun U hU ↦ ?_⟩
  have hnonneg : 0 ≤
      dyadicTwoLengthPerronTruncationErrorMeanSquareAt
        S f Y X H₁ H₂ U := by
    unfold dyadicTwoLengthPerronTruncationErrorMeanSquareAt
    exact Finset.sum_nonneg (fun x hx ↦ sq_nonneg _)
  have h := hU₀ U hU
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at h

theorem dyadicTwoLengthShortMeanSquareAt_le_correctedPerron
    (S : Finset ℕ) (f : ℕ → ℂ) {Y X H₁ H₂ : ℕ}
    (_hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 < T) :
    dyadicTwoLengthShortMeanSquareAt S f Y X H₁ H₂ ≤
      2 * dyadicTwoLengthCorrectedPerronMeanSquareAt S f Y X H₁ H₂ T +
        2 * dyadicTwoLengthPerronTruncationErrorMeanSquareAt
          S f Y X H₁ H₂ T := by
  classical
  unfold dyadicTwoLengthShortMeanSquareAt
    dyadicTwoLengthCorrectedPerronMeanSquareAt
    dyadicTwoLengthPerronTruncationErrorMeanSquareAt
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hxmem
  have hx : 0 < x := by
    have := Finset.mem_Ioc.mp hxmem
    omega
  let A : ℂ := dyadicRestrictedShortAverage S f Y x H₁ -
    dyadicRestrictedShortAverage S f Y x H₂
  let M : ℂ := dyadicRestrictedCorrectedPerronAverage S f Y x H₁ T -
    dyadicRestrictedCorrectedPerronAverage S f Y x H₂ T
  let E : ℝ :=
    lemma14PerronTruncationError
        (dyadicRestrictedCoefficient S f Y) x H₁ T +
      lemma14PerronTruncationError
        (dyadicRestrictedCoefficient S f Y) x H₂ T
  have h₁ := norm_dyadicShortAverage_sub_correctedPerron_le_truncationError
    S f Y hx hH₁ hT
  have h₂ := norm_dyadicShortAverage_sub_correctedPerron_le_truncationError
    S f Y hx hH₂ hT
  have happrox : ‖A - M‖ ≤ E := by
    calc
      ‖A - M‖ =
          ‖(dyadicRestrictedShortAverage S f Y x H₁ -
              dyadicRestrictedCorrectedPerronAverage S f Y x H₁ T) -
            (dyadicRestrictedShortAverage S f Y x H₂ -
              dyadicRestrictedCorrectedPerronAverage S f Y x H₂ T)‖ := by
            dsimp [A, M]
            congr 1
            ring
      _ ≤ ‖dyadicRestrictedShortAverage S f Y x H₁ -
              dyadicRestrictedCorrectedPerronAverage S f Y x H₁ T‖ +
            ‖dyadicRestrictedShortAverage S f Y x H₂ -
              dyadicRestrictedCorrectedPerronAverage S f Y x H₂ T‖ :=
          norm_sub_le _ _
      _ ≤ E := by dsimp [E]; exact add_le_add h₁ h₂
  have hsq : Complex.normSq (A - M) ≤ E ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (E - ‖A - M‖), norm_nonneg (A - M)]
  have hbasic : Complex.normSq A ≤
      2 * Complex.normSq M + 2 * Complex.normSq (A - M) := by
    have hnormA : ‖A‖ ≤ ‖M‖ + ‖A - M‖ := by
      calc
        ‖A‖ = ‖M + (A - M)‖ := by congr 1; abel
        _ ≤ ‖M‖ + ‖A - M‖ := norm_add_le _ _
    simp only [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖M‖ - ‖A - M‖), norm_nonneg A,
      norm_nonneg M, norm_nonneg (A - M)]
  exact hbasic.trans (by nlinarith)

/-- Decoupled low-frequency estimate for the corrected two-length model. -/
theorem dyadicTwoLengthCorrectedPerronMeanSquareAt_low_le
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y X H₁ H₂ : ℕ}
    (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 ≤ T) :
    dyadicTwoLengthCorrectedPerronMeanSquareAt S f Y X H₁ H₂ T ≤
      2 * ((X : ℝ) *
        (‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X)) ^ 2) +
      2 * (X : ℝ) * (((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹) ^ 2 := by
  classical
  unfold dyadicTwoLengthCorrectedPerronMeanSquareAt
    dyadicRestrictedCorrectedPerronAverage
  let A : ℕ → ℂ := fun x ↦
    dyadicRestrictedPerronAverage S f Y x H₁ T -
      dyadicRestrictedPerronAverage S f Y x H₂ T
  let E : ℕ → ℂ := fun x ↦
    dyadicRestrictedPerronEndpointCorrection S f Y x H₁ -
      dyadicRestrictedPerronEndpointCorrection S f Y x H₂
  have hraw := dyadicTwoLengthPerronMeanSquare_low_le
    S hf (Y := Y) hX hH₁ hH₂ hT
  have hrawA :
      (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (A x)) ≤
        (X : ℝ) *
          (‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
            (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X)) ^ 2 := by
    simpa only [A] using hraw
  have hE (x : ℕ) : ‖E x‖ ≤
      ((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹ := by
    dsimp [E]
    exact (norm_sub_le _ _).trans (add_le_add
      (norm_dyadicRestrictedPerronEndpointCorrection_le S hf Y x hH₁)
      (norm_dyadicRestrictedPerronEndpointCorrection_le S hf Y x hH₂))
  have hEsq :
      (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (E x)) ≤
        (X : ℝ) * (((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹) ^ 2 := by
    calc
      _ ≤ ∑ _x ∈ Finset.Ioc X (2 * X),
          (((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Complex.normSq_eq_norm_sq]
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hE x)
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        simp
        omega
  have hpoint (x : ℕ) :
      Complex.normSq (A x + E x) ≤
        2 * Complex.normSq (A x) + 2 * Complex.normSq (E x) := by
    have h := normSq_sub_le_two_mul_add (A x) (-E x)
    simp only [sub_neg_eq_add, Complex.normSq_neg] at h
    linarith
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          ((dyadicRestrictedPerronAverage S f Y x H₁ T +
              dyadicRestrictedPerronEndpointCorrection S f Y x H₁) -
            (dyadicRestrictedPerronAverage S f Y x H₂ T +
              dyadicRestrictedPerronEndpointCorrection S f Y x H₂))) =
        ∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (A x + E x) := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 2
      dsimp [A, E]
      ring
    _ ≤ ∑ x ∈ Finset.Ioc X (2 * X),
        (2 * Complex.normSq (A x) + 2 * Complex.normSq (E x)) := by
      exact Finset.sum_le_sum (fun x hx ↦ hpoint x)
    _ = 2 * (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (A x)) +
        2 * (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (E x)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by nlinarith [hrawA, hEsq]

theorem dyadicTwoLengthCorrectedPerronMeanSquareAt_low_le_scale
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y X H₁ H₂ K : ℕ}
    (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hK : 0 < K) (hH₁H₂ : H₁ ≤ H₂) (hscale : K * H₂ ≤ X)
    {T : ℝ} (hT : 0 ≤ T) :
    dyadicTwoLengthCorrectedPerronMeanSquareAt S f Y X H₁ H₂ T ≤
      (X : ℝ) *
        (32 * T ^ 4 / (K : ℝ) ^ 2 + 8 / (H₁ : ℝ) ^ 2) := by
  have hbase := dyadicTwoLengthCorrectedPerronMeanSquareAt_low_le
    S hf hX hH₁ hH₂ hT (Y := Y)
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hH₁r : (0 : ℝ) < H₁ := by exact_mod_cast hH₁
  have hH₂r : (0 : ℝ) < H₂ := by exact_mod_cast hH₂
  have hH₁H₂r : (H₁ : ℝ) ≤ H₂ := by exact_mod_cast hH₁H₂
  have hscaleR : (K : ℝ) * H₂ ≤ X := by exact_mod_cast hscale
  have hc : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    apply (inv_le_one₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hsum : (H₁ : ℝ) + H₂ ≤ 2 * (H₂ : ℝ) := by linarith
  have hratio : ((H₁ : ℝ) + H₂) / X ≤ 2 / (K : ℝ) := by
    rw [div_le_div_iff₀ hXr hKr]
    nlinarith
  have hrawFactor :
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X) ≤
        4 * T ^ 2 / (K : ℝ) := by
    have hnonneg : 0 ≤ 2 * T ^ 2 * (((H₁ : ℝ) + H₂) / X) := by
      positivity
    calc
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X) ≤
          1 * (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X) := by
            gcongr
      _ ≤ 1 * (2 * T ^ 2 * (2 / (K : ℝ))) := by
            simpa only [one_mul, mul_div_assoc] using
              mul_le_mul_of_nonneg_left hratio
                (by positivity : 0 ≤ 2 * T ^ 2)
      _ = 4 * T ^ 2 / (K : ℝ) := by ring
  have hrawSq :
      (‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X)) ^ 2 ≤
        16 * T ^ 4 / (K : ℝ) ^ 2 := by
    calc
      _ ≤ (4 * T ^ 2 / (K : ℝ)) ^ 2 := by gcongr
      _ = _ := by field_simp; ring
  have hinv : ((H₂ : ℝ))⁻¹ ≤ ((H₁ : ℝ))⁻¹ :=
    inv_anti₀ hH₁r hH₁H₂r
  have hendSq :
      (((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹) ^ 2 ≤
        4 / (H₁ : ℝ) ^ 2 := by
    have hsumInv : ((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹ ≤
        2 * ((H₁ : ℝ))⁻¹ := by linarith
    calc
      _ ≤ (2 * ((H₁ : ℝ))⁻¹) ^ 2 := by gcongr
      _ = 4 / (H₁ : ℝ) ^ 2 := by
        rw [div_eq_mul_inv, ← inv_pow]
        ring
  have hXnonneg : (0 : ℝ) ≤ X := by positivity
  calc
    dyadicTwoLengthCorrectedPerronMeanSquareAt S f Y X H₁ H₂ T ≤
        2 * ((X : ℝ) *
          (‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
            (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X)) ^ 2) +
          2 * (X : ℝ) *
            (((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹) ^ 2 := hbase
    _ ≤ 2 * ((X : ℝ) * (16 * T ^ 4 / (K : ℝ) ^ 2)) +
          2 * (X : ℝ) * (4 / (H₁ : ℝ) ^ 2) := by
        gcongr
    _ = (X : ℝ) *
        (32 * T ^ 4 / (K : ℝ) ^ 2 + 8 / (H₁ : ℝ) ^ 2) := by ring

/-- A corrected two-length model at outer height `U` is controlled by its
central model and the decoupled high-frequency mass. -/
theorem dyadicTwoLengthCorrectedPerronMeanSquareAt_le_low_add_high
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H₁ H₂ : ℕ} (_hX : 0 < X)
    (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T U : ℝ} (hTU : T ≤ U) :
    dyadicTwoLengthCorrectedPerronMeanSquareAt S f Y X H₁ H₂ U ≤
      2 * dyadicTwoLengthCorrectedPerronMeanSquareAt S f Y X H₁ H₂ T +
        4 * dyadicTwoLengthPerronHighMeanSquare S f Y X H₁ H₂ T U := by
  classical
  let L : ℕ → ℂ := fun x ↦
    dyadicRestrictedCorrectedPerronAverage S f Y x H₁ T -
      dyadicRestrictedCorrectedPerronAverage S f Y x H₂ T
  let N : ℕ → ℂ := fun x ↦
    dyadicTwoLengthPerronSegment S f Y x H₁ H₂ (-U) (-T)
  let P : ℕ → ℂ := fun x ↦
    dyadicTwoLengthPerronSegment S f Y x H₁ H₂ T U
  have hdecomp (x : ℕ) (hxmem : x ∈ Finset.Ioc X (2 * X)) :
      dyadicRestrictedCorrectedPerronAverage S f Y x H₁ U -
          dyadicRestrictedCorrectedPerronAverage S f Y x H₂ U =
        L x + N x + P x := by
    have hx : 0 < x := by have := Finset.mem_Ioc.mp hxmem; omega
    have hrawU := dyadicRestrictedPerronAverage_sub_eq_segment
      S f Y hx hH₁ hH₂ U
    have hrawT := dyadicRestrictedPerronAverage_sub_eq_segment
      S f Y hx hH₁ hH₂ T
    have hseg := dyadicTwoLengthPerronSegment_eq_low_add_high
      S f (Y := Y) hx hH₁ hH₂ hTU
    unfold dyadicRestrictedCorrectedPerronAverage
    dsimp [L, N, P]
    rw [show
      dyadicRestrictedPerronAverage S f Y x H₁ U +
            dyadicRestrictedPerronEndpointCorrection S f Y x H₁ -
          (dyadicRestrictedPerronAverage S f Y x H₂ U +
            dyadicRestrictedPerronEndpointCorrection S f Y x H₂) =
        (dyadicRestrictedPerronAverage S f Y x H₁ U -
            dyadicRestrictedPerronAverage S f Y x H₂ U) +
          (dyadicRestrictedPerronEndpointCorrection S f Y x H₁ -
            dyadicRestrictedPerronEndpointCorrection S f Y x H₂) by ring]
    rw [hrawU, hseg, ← hrawT]
    unfold dyadicRestrictedCorrectedPerronAverage
    ring
  have hpoint (x : ℕ) (hxmem : x ∈ Finset.Ioc X (2 * X)) :
      Complex.normSq
        (dyadicRestrictedCorrectedPerronAverage S f Y x H₁ U -
          dyadicRestrictedCorrectedPerronAverage S f Y x H₂ U) ≤
        2 * Complex.normSq (L x) +
          4 * (Complex.normSq (N x) + Complex.normSq (P x)) := by
    rw [hdecomp x hxmem]
    have houter := normSq_sub_le_two_mul_add (L x) (-(N x + P x))
    have hinner := normSq_sub_le_two_mul_add (N x) (-P x)
    simp only [sub_neg_eq_add, Complex.normSq_neg] at houter hinner
    calc
      Complex.normSq (L x + N x + P x) =
          Complex.normSq (L x + (N x + P x)) := by congr 1; abel
      _ ≤ 2 * (Complex.normSq (L x) + Complex.normSq (N x + P x)) := houter
      _ ≤ 2 * Complex.normSq (L x) +
          4 * (Complex.normSq (N x) + Complex.normSq (P x)) := by linarith
  unfold dyadicTwoLengthCorrectedPerronMeanSquareAt
    dyadicTwoLengthPerronHighMeanSquare
  calc
    _ ≤ ∑ x ∈ Finset.Ioc X (2 * X),
        (2 * Complex.normSq (L x) +
          4 * (Complex.normSq (N x) + Complex.normSq (P x))) :=
      Finset.sum_le_sum hpoint
    _ = 2 * (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (L x)) +
        4 * ∑ x ∈ Finset.Ioc X (2 * X),
          (Complex.normSq (N x) + Complex.normSq (P x)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rfl

theorem dyadicTwoLengthShortMeanSquareAt_le_of_uniform_high
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H₁ H₂ : ℕ} (hX : 0 < X)
    (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T E : ℝ} (_hT : 0 < T)
    (hhigh : ∀ U : ℝ, T ≤ U →
      dyadicTwoLengthPerronHighMeanSquare S f Y X H₁ H₂ T U ≤ E) :
    dyadicTwoLengthShortMeanSquareAt S f Y X H₁ H₂ ≤
      4 * dyadicTwoLengthCorrectedPerronMeanSquareAt S f Y X H₁ H₂ T +
        8 * E := by
  apply le_of_forall_pos_le_add
  intro e he
  obtain ⟨U₀, hU₀⟩ :=
    exists_dyadicTwoLengthPerronTruncationErrorMeanSquareAt_lt
      S f Y X H₁ H₂ (half_pos he)
  let U : ℝ := max U₀ (max T 1)
  have hU₀U : U₀ ≤ U := le_max_left _ _
  have hTU : T ≤ U := le_trans (le_max_left _ _) (le_max_right _ _)
  have hUpos : 0 < U := by
    exact lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right T 1) (le_max_right U₀ (max T 1)))
  have herr := hU₀ U hU₀U
  have hshort := dyadicTwoLengthShortMeanSquareAt_le_correctedPerron
    S f hX hH₁ hH₂ hUpos (Y := Y)
  have hsplit := dyadicTwoLengthCorrectedPerronMeanSquareAt_le_low_add_high
    S f hX hH₁ hH₂ hTU (Y := Y)
  have henergy := hhigh U hTU
  linarith

/-- Spatially decoupled recovery of the shorter uncentered sum from the
two-length difference and the longer normalized average. -/
theorem uncenteredShortIntervalMeanSquare_dyadicRestrictedAt_le_twoLength_add_long
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (_hH₂ : 0 < H₂) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H₁ ≤
      2 * (H₁ : ℝ) ^ 2 *
        (dyadicTwoLengthShortMeanSquareAt S f Y X H₁ H₂ +
          dyadicRestrictedShortAverageMeanSquareAt S f Y X H₂) := by
  classical
  unfold uncenteredShortIntervalMeanSquare
    dyadicTwoLengthShortMeanSquareAt
    dyadicRestrictedShortAverageMeanSquareAt
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  have hshort (H : ℕ) (hH : 0 < H) :
      (∑ j ∈ Finset.Icc 1 H,
          dyadicRestrictedCoefficient S f Y (x + j)) =
        (H : ℂ) * dyadicRestrictedShortAverage S f Y x H := by
    unfold dyadicRestrictedShortAverage
    rw [sum_Icc_add_eq_sum_Ioc]
    rw [mul_div_cancel₀]
    exact_mod_cast hH.ne'
  rw [hshort H₁ hH₁]
  let A : ℂ := dyadicRestrictedShortAverage S f Y x H₁ -
    dyadicRestrictedShortAverage S f Y x H₂
  let B : ℂ := dyadicRestrictedShortAverage S f Y x H₂
  have hdecomp : dyadicRestrictedShortAverage S f Y x H₁ = A + B := by
    dsimp [A, B]
    ring
  conv_lhs => rw [hdecomp]
  rw [Complex.normSq_mul, Complex.normSq_natCast]
  have hsum := normSq_sub_le_two_mul_add A (-B)
  simp only [sub_neg_eq_add, Complex.normSq_neg] at hsum
  calc
    (H₁ : ℝ) * H₁ * Complex.normSq (A + B) =
        (H₁ : ℝ) ^ 2 * Complex.normSq (A + B) := by ring
    _ ≤ (H₁ : ℝ) ^ 2 *
        (2 * (Complex.normSq A + Complex.normSq B)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = 2 * (H₁ : ℝ) ^ 2 * Complex.normSq
            (dyadicRestrictedShortAverage S f Y x H₁ -
              dyadicRestrictedShortAverage S f Y x H₂) +
          2 * (H₁ : ℝ) ^ 2 *
            Complex.normSq (dyadicRestrictedShortAverage S f Y x H₂) := by
      dsimp [A, B]
      ring

/-- Fully quantitative, support-scale-decoupled Lemma 14 endpoint.  The
two high-frequency terms, the central long-average term, and all elementary
low/endpoint costs remain separate. -/
theorem uncenteredShortIntervalMeanSquare_dyadicRestrictedAt_le_source_parameters
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y X H₁ H₂ K : ℕ}
    (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hK : 0 < K) (hH₁H₂ : H₁ ≤ H₂) (hscale : K * H₂ ≤ X)
    {T Ehigh ElongHigh ElongCentral : ℝ} (hT : 0 < T)
    (hhigh : ∀ U : ℝ, T ≤ U →
      dyadicTwoLengthPerronHighMeanSquare S f Y X H₁ H₂ T U ≤
        X * Ehigh)
    (hlongHigh : ∀ U : ℝ, T ≤ U →
      dyadicSinglePerronHighMeanSquare S f Y X H₂ T U ≤
        X * ElongHigh)
    (hlongCentral :
      dyadicRestrictedPerronAverageMeanSquareAt S f Y X H₂ T ≤
        X * ElongCentral) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H₁ ≤
      (256 * T ^ 4 / (K : ℝ) ^ 2 + 64 / (H₁ : ℝ) ^ 2 +
          16 * Ehigh + 16 * ElongHigh + 16 * ElongCentral +
          16 / (H₂ : ℝ) ^ 2) * (H₁ : ℝ) ^ 2 * X := by
  have htwo := dyadicTwoLengthShortMeanSquareAt_le_of_uniform_high
    S f hX hH₁ hH₂ hT hhigh (Y := Y)
  have hlow := dyadicTwoLengthCorrectedPerronMeanSquareAt_low_le_scale
    S hf hX hH₁ hH₂ hK hH₁H₂ hscale hT.le (Y := Y)
  have hcorr := dyadicSingleCorrectedPerronMeanSquareAt_le_raw_add_endpoint
    S hf hH₂ T (Y := Y) (X := X)
  have hlong := dyadicRestrictedShortAverageMeanSquareAt_le_of_uniform_high
    S f hX hH₂ hT hlongHigh (Y := Y)
  have hbase :=
    uncenteredShortIntervalMeanSquare_dyadicRestrictedAt_le_twoLength_add_long
      S f hH₁ hH₂ (Y := Y) (X := X)
  have hXnonneg : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hH₁sq : (0 : ℝ) ≤ (H₁ : ℝ) ^ 2 := sq_nonneg _
  have htwo' :
      dyadicTwoLengthShortMeanSquareAt S f Y X H₁ H₂ ≤
        X * (128 * T ^ 4 / (K : ℝ) ^ 2 +
          32 / (H₁ : ℝ) ^ 2 + 8 * Ehigh) := by
    calc
      _ ≤ 4 * dyadicTwoLengthCorrectedPerronMeanSquareAt
            S f Y X H₁ H₂ T + 8 * (X * Ehigh) := htwo
      _ ≤ 4 * (X * (32 * T ^ 4 / (K : ℝ) ^ 2 +
            8 / (H₁ : ℝ) ^ 2)) + 8 * (X * Ehigh) := by gcongr
      _ = _ := by ring
  have hlongCorr :
      dyadicSingleCorrectedPerronMeanSquareAt S f Y X H₂ T ≤
        X * (2 * ElongCentral + 2 / (H₂ : ℝ) ^ 2) := by
    calc
      _ ≤ 2 * dyadicRestrictedPerronAverageMeanSquareAt
            S f Y X H₂ T + 2 * (X : ℝ) / (H₂ : ℝ) ^ 2 := hcorr
      _ ≤ 2 * (X * ElongCentral) +
            2 * (X : ℝ) / (H₂ : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have hlong' :
      dyadicRestrictedShortAverageMeanSquareAt S f Y X H₂ ≤
        X * (8 * ElongCentral + 8 / (H₂ : ℝ) ^ 2 +
          8 * ElongHigh) := by
    calc
      _ ≤ 4 * dyadicSingleCorrectedPerronMeanSquareAt S f Y X H₂ T +
            8 * (X * ElongHigh) := hlong
      _ ≤ 4 * (X * (2 * ElongCentral + 2 / (H₂ : ℝ) ^ 2)) +
            8 * (X * ElongHigh) := by gcongr
      _ = _ := by ring
  calc
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H₁ ≤
      2 * (H₁ : ℝ) ^ 2 *
        (dyadicTwoLengthShortMeanSquareAt S f Y X H₁ H₂ +
          dyadicRestrictedShortAverageMeanSquareAt S f Y X H₂) := hbase
    _ ≤ 2 * (H₁ : ℝ) ^ 2 *
        (X * (128 * T ^ 4 / (K : ℝ) ^ 2 +
            32 / (H₁ : ℝ) ^ 2 + 8 * Ehigh) +
          X * (8 * ElongCentral + 8 / (H₂ : ℝ) ^ 2 +
            8 * ElongHigh)) := by gcongr
    _ = _ := by ring

/-- Final exact cover consumer for two independently estimated dyadic
coefficient scales.  It is intentionally stated with separate coefficients
so the `Y=X` and `Y=2X` analytic errors need not be artificially maximized. -/
theorem uncenteredShortIntervalMeanSquare_le_of_two_dyadic_bounds
    (f : ℕ → ℂ) {X H : ℕ} (hHX : H ≤ X)
    {E₁ E₂ : ℝ}
    (h₁ : uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient (Finset.Ioc X (2 * X)) f X) X H ≤
      E₁ * (H : ℝ) ^ 2 * X)
    (h₂ : uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient
          (Finset.Ioc (2 * X) (4 * X)) f (2 * X)) X H ≤
      E₂ * (H : ℝ) ^ 2 * X) :
    uncenteredShortIntervalMeanSquare f X H ≤
      2 * (E₁ + E₂) * (H : ℝ) ^ 2 * X := by
  have hcover := uncenteredShortIntervalMeanSquare_le_two_dyadic f hHX
  calc
    uncenteredShortIntervalMeanSquare f X H ≤
        2 * uncenteredShortIntervalMeanSquare
          (dyadicRestrictedCoefficient (Finset.Ioc X (2 * X)) f X) X H +
        2 * uncenteredShortIntervalMeanSquare
          (dyadicRestrictedCoefficient
            (Finset.Ioc (2 * X) (4 * X)) f (2 * X)) X H := hcover
    _ ≤ 2 * (E₁ * (H : ℝ) ^ 2 * X) +
        2 * (E₂ * (H : ℝ) ^ 2 * X) := by gcongr
    _ = 2 * (E₁ + E₂) * (H : ℝ) ^ 2 * X := by ring

end

end Erdos67

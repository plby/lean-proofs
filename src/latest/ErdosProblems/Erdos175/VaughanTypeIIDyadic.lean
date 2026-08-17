/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.TypeI
import ErdosProblems.Erdos175.TypeIINearFar
import ErdosProblems.Erdos175.VaughanTypeIIBridge

/-!
# Dyadic support decomposition for the Type-II Vaughan sums

This file decomposes an arbitrary finite positive support into the exact
power blocks used by the reciprocal exponential-sum estimate.  Coefficients
are extended by zero outside their original support, so the rectangular
dyadic blocks introduce no extra terms.
-/

noncomputable section

namespace Erdos175.VaughanTypeIIDyadic

open scoped BigOperators

/-- Extend a coefficient sequence by zero outside a finite support. -/
def restrictCoeff (s : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ s then a n else 0

@[simp] lemma restrictCoeff_of_mem
    (s : Finset ℕ) (a : ℕ → ℂ) {n : ℕ} (hn : n ∈ s) :
    restrictCoeff s a n = a n := by
  simp [restrictCoeff, hn]

@[simp] lemma restrictCoeff_of_not_mem
    (s : Finset ℕ) (a : ℕ → ℂ) {n : ℕ} (hn : n ∉ s) :
    restrictCoeff s a n = 0 := by
  simp [restrictCoeff, hn]

/-- Restricting a coefficient sequence cannot increase its squared mass on
any finite block. -/
theorem sum_norm_sq_restrictCoeff_le
    (block support : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ block, ‖restrictCoeff support a n‖ ^ 2) ≤
      ∑ n ∈ block, ‖a n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  by_cases hns : n ∈ support
  · simp [restrictCoeff, hns]
  · simp [restrictCoeff, hns]

/-- `L²`-norm form of `sum_norm_sq_restrictCoeff_le`. -/
theorem l2Norm_restrictCoeff_le
    (block support : Finset ℕ) (a : ℕ → ℂ) :
    TypeII.l2Norm block (restrictCoeff support a) ≤
      TypeII.l2Norm block a := by
  unfold TypeII.l2Norm
  exact Real.sqrt_le_sqrt (sum_norm_sq_restrictCoeff_le block support a)

/-- The half-open power block used in `TypeI` is the natural-number `Ioc`
interval whose endpoints are one less than consecutive powers of two. -/
theorem dyadicBlock_eq_Ioc_pred (j : ℕ) :
    TypeI.dyadicBlock j = Finset.Ioc (2 ^ j - 1) (2 ^ (j + 1) - 1) := by
  ext n
  have hjpos : 0 < 2 ^ j := pow_pos (by norm_num) j
  simp only [TypeI.dyadicBlock, Finset.mem_Ico, Finset.mem_Ioc]
  omega

/-! ## Coefficient estimates on the shifted power blocks -/

/-- Proposition 10.1 on `[2^j,2^(j+1))`.  Compared with its native
interval `(2^j,2^(j+1)]`, this costs only the left endpoint, whose
`aCoeff` has norm at most one.  An arbitrary support mask can only decrease
the squared mass. -/
theorem l2Norm_restrict_aCoeff_dyadicBlock_sq_le
    (support : Finset ℕ) (M j : ℕ) (hM : 1 ≤ M) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support
          (fun n => ((VaughanFourSums.aCoeff M n : ℝ) : ℂ))) ^ 2 ≤
      (8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1 := by
  let p : ℕ := 2 ^ j
  have hp : 0 < p := pow_pos (by norm_num) j
  have hsubset : TypeI.dyadicBlock j ⊆
      insert p (TypeII.dyadicNatBlock p) := by
    intro n hn
    have hn' : p ≤ n ∧ n < 2 * p := by
      simpa [TypeI.dyadicBlock, p, pow_succ, Nat.mul_comm] using
        (Finset.mem_Ico.mp hn)
    simp only [Finset.mem_insert, TypeII.dyadicNatBlock, Finset.mem_Ioc]
    omega
  have hpnot : p ∉ TypeII.dyadicNatBlock p := by
    simp [TypeII.dyadicNatBlock]
  have hpoint :
      ‖((VaughanFourSums.aCoeff M p : ℝ) : ℂ)‖ ^ 2 ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h : |VaughanFourSums.aCoeff M p| ≤ (1 : ℝ) := by
      simpa [p] using TypeII.abs_aCoeff_two_pow_le_one M j hM
    change |VaughanFourSums.aCoeff M p| ^ 2 ≤ 1
    simpa using pow_le_pow_left₀ (abs_nonneg _ ) h 2
  rw [TypeII.l2Norm_sq]
  calc
    (∑ n ∈ TypeI.dyadicBlock j,
        ‖restrictCoeff support
          (fun n => ((VaughanFourSums.aCoeff M n : ℝ) : ℂ)) n‖ ^ 2) ≤
        ∑ n ∈ TypeI.dyadicBlock j,
          ‖((VaughanFourSums.aCoeff M n : ℝ) : ℂ)‖ ^ 2 :=
      sum_norm_sq_restrictCoeff_le _ _ _
    _ ≤ ∑ n ∈ insert p (TypeII.dyadicNatBlock p),
          ‖((VaughanFourSums.aCoeff M n : ℝ) : ℂ)‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n hn _hnblock
      positivity
    _ = ‖((VaughanFourSums.aCoeff M p : ℝ) : ℂ)‖ ^ 2 +
          ∑ n ∈ TypeII.dyadicNatBlock p,
            ‖((VaughanFourSums.aCoeff M n : ℝ) : ℂ)‖ ^ 2 := by
      rw [Finset.sum_insert hpnot]
    _ ≤ 1 + (8 / 9 : ℝ) * (p : ℝ) * (Real.log M + 3) ^ 3 :=
      add_le_add hpoint (TypeII.sum_norm_aCoeff_sq_le p M hM)
    _ = (8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1 := by
      simp only [p]
      ring

/-- The elementary `|b_r| ≤ log r` estimate on the shifted power block,
again allowing an arbitrary support mask. -/
theorem l2Norm_restrict_bCoeff_dyadicBlock_sq_le
    (support : Finset ℕ) (M K j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support
          (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ))) ^ 2 ≤
      (2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2 := by
  let p : ℕ := 2 ^ j
  have hp : 0 < p := pow_pos (by norm_num) j
  have hterm (r : ℕ) (hr : r ∈ TypeI.dyadicBlock j) :
      ‖restrictCoeff support
          (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ)) r‖ ^ 2 ≤
        Real.log (2 * p : ℕ) ^ 2 := by
    by_cases hrs : r ∈ support
    · rw [restrictCoeff_of_mem support _ hrs, Complex.norm_real,
          Real.norm_eq_abs]
      have hrI := TypeI.mem_dyadicBlock.mp hr
      have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le hp hrI.1)
      have hrle : r ≤ 2 * p := by
        simpa [p, pow_succ, Nat.mul_comm] using (Nat.le_of_lt hrI.2)
      have hlog : Real.log (r : ℝ) ≤ Real.log (2 * p : ℕ) :=
        Real.log_le_log hrpos (by exact_mod_cast hrle)
      exact pow_le_pow_left₀ (abs_nonneg _)
        ((VaughanFourSums.abs_bCoeff_le_log M K r).trans hlog) 2
    · rw [restrictCoeff_of_not_mem support _ hrs, norm_zero]
      simpa using sq_nonneg (Real.log (2 * p : ℕ))
  rw [TypeII.l2Norm_sq]
  calc
    (∑ r ∈ TypeI.dyadicBlock j,
        ‖restrictCoeff support
          (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ)) r‖ ^ 2) ≤
        ∑ _r ∈ TypeI.dyadicBlock j, Real.log (2 * p : ℕ) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact hterm r hr
    _ = (2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2 := by
      simp [TypeI.card_dyadicBlock, p]

/-- The pointwise von Mangoldt estimate on the shifted power block. -/
theorem l2Norm_restrict_vonMangoldt_dyadicBlock_sq_le
    (support : Finset ℕ) (j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))) ^ 2 ≤
      (2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2 := by
  let p : ℕ := 2 ^ j
  have hp : 0 < p := pow_pos (by norm_num) j
  have hterm (k : ℕ) (hk : k ∈ TypeI.dyadicBlock j) :
      ‖restrictCoeff support
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) k‖ ^ 2 ≤
        Real.log (2 * p : ℕ) ^ 2 := by
    by_cases hks : k ∈ support
    · rw [restrictCoeff_of_mem support _ hks]
      have hkI := TypeI.mem_dyadicBlock.mp hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hp hkI.1)
      have hkle : k ≤ 2 * p := by
        simpa [p, pow_succ, Nat.mul_comm] using (Nat.le_of_lt hkI.2)
      have hlog : Real.log (k : ℝ) ≤ Real.log (2 * p : ℕ) :=
        Real.log_le_log hkpos (by exact_mod_cast hkle)
      have hlam0 := ArithmeticFunction.vonMangoldt_nonneg (n := k)
      rw [Complex.norm_of_nonneg hlam0]
      exact pow_le_pow_left₀ hlam0
        (ArithmeticFunction.vonMangoldt_le_log.trans hlog) 2
    · rw [restrictCoeff_of_not_mem support _ hks, norm_zero]
      simpa using sq_nonneg (Real.log (2 * p : ℕ))
  rw [TypeII.l2Norm_sq]
  calc
    (∑ k ∈ TypeI.dyadicBlock j,
        ‖restrictCoeff support
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) k‖ ^ 2) ≤
        ∑ _k ∈ TypeI.dyadicBlock j, Real.log (2 * p : ℕ) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact hterm k hk
    _ = (2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2 := by
      simp [TypeI.card_dyadicBlock, p]

/-- A finite sum on positive indices bounded by `N` is the sum of its power
blocks after extending the summand by zero outside the original support. -/
theorem sum_eq_sum_dyadic_restrict
    {A : Type*} [AddCommMonoid A]
    (s : Finset ℕ) (f : ℕ → A) (N : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) :
    (∑ n ∈ s, f n) =
      ∑ j ∈ Finset.range (TypeI.dyadicCount N),
        ∑ n ∈ TypeI.dyadicBlock j, if n ∈ s then f n else 0 := by
  rw [← TypeI.sum_dyadicBlocks]
  have hsub : s ⊆ Finset.Ico 1 (2 ^ TypeI.dyadicCount N) := by
    intro n hn
    have hnrange := hs n hn
    exact Finset.mem_Ico.mpr
      ⟨hnrange.1,
        lt_of_le_of_lt hnrange.2 (TypeI.lt_two_pow_dyadicCount N)⟩
  calc
    (∑ n ∈ s, f n) = ∑ n ∈ s, if n ∈ s then f n else 0 := by simp
    _ = ∑ n ∈ Finset.Ico 1 (2 ^ TypeI.dyadicCount N),
          if n ∈ s then f n else 0 := by
      apply Finset.sum_subset hsub
      intro n _hnIco hnnot
      simp [hnnot]

/-- Two bounded positive supports decompose into rectangular power blocks.
The two membership tests are retained explicitly for later identification
with restricted coefficient sequences. -/
theorem doubleSum_eq_sum_dyadic_restrict
    {A : Type*} [AddCommMonoid A]
    (s t : Finset ℕ) (F : ℕ → ℕ → A) (S T : ℕ)
    (hs : ∀ u ∈ s, 1 ≤ u ∧ u ≤ S)
    (ht : ∀ v ∈ t, 1 ≤ v ∧ v ≤ T) :
    (∑ u ∈ s, ∑ v ∈ t, F u v) =
      ∑ j ∈ Finset.range (TypeI.dyadicCount S),
        ∑ k ∈ Finset.range (TypeI.dyadicCount T),
          ∑ u ∈ TypeI.dyadicBlock j,
            ∑ v ∈ TypeI.dyadicBlock k,
              if u ∈ s then (if v ∈ t then F u v else 0) else 0 := by
  rw [sum_eq_sum_dyadic_restrict s (fun u => ∑ v ∈ t, F u v) S hs]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ u ∈ TypeI.dyadicBlock j,
        if u ∈ s then (∑ v ∈ t, F u v) else 0) =
        ∑ u ∈ TypeI.dyadicBlock j,
          ∑ k ∈ Finset.range (TypeI.dyadicCount T),
            ∑ v ∈ TypeI.dyadicBlock k,
              if u ∈ s then (if v ∈ t then F u v else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hus : u ∈ s
      · simp only [hus, if_pos]
        exact sum_eq_sum_dyadic_restrict t (F u) T ht
      · simp [hus]
    _ = ∑ k ∈ Finset.range (TypeI.dyadicCount T),
          ∑ u ∈ TypeI.dyadicBlock j,
            ∑ v ∈ TypeI.dyadicBlock k,
              if u ∈ s then (if v ∈ t then F u v else 0) else 0 := by
      rw [Finset.sum_comm]

/-- Exact dyadic decomposition of the concrete product-restricted reciprocal
bilinear sum. -/
theorem reciprocalBilinearSum_eq_sum_dyadic
    (I uSupport vSupport : Finset ℕ) (x : ℝ)
    (alpha beta : ℕ → ℂ) (HU HV : ℕ)
    (hu : ∀ u ∈ uSupport, 1 ≤ u ∧ u ≤ HU)
    (hv : ∀ v ∈ vSupport, 1 ≤ v ∧ v ≤ HV) :
    TypeII.reciprocalBilinearSum I uSupport vSupport x alpha beta =
      ∑ j ∈ Finset.range (TypeI.dyadicCount HU),
        ∑ k ∈ Finset.range (TypeI.dyadicCount HV),
          TypeII.reciprocalBilinearSum I
            (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x
            (restrictCoeff uSupport alpha) (restrictCoeff vSupport beta) := by
  unfold TypeII.reciprocalBilinearSum TypeII.bilinearSum TypeII.innerSum
  simp_rw [Finset.mul_sum]
  rw [doubleSum_eq_sum_dyadic_restrict uSupport vSupport
    (fun u v => alpha u *
      (beta v * TypeII.restrictedReciprocalKernel I x u v)) HU HV hu hv]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro u huj
  apply Finset.sum_congr rfl
  intro v hvk
  by_cases hus : u ∈ uSupport
  · by_cases hvs : v ∈ vSupport
    · simp [restrictCoeff, hus, hvs]
    · simp [restrictCoeff, hus, hvs]
  · simp [restrictCoeff, hus]

/-- Dyadic decomposition of the actual `Σ₂,₂` Vaughan term. -/
theorem sigma22_eq_sum_dyadic
    (y y' M K : ℕ) (x : ℝ) :
    VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K =
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          TypeII.reciprocalBilinearSum (Finset.Ioc y y')
            (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x
            (restrictCoeff (Finset.Ioc M (M * K))
              (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
            (restrictCoeff (Finset.Icc 1 y') (fun _ => 1)) := by
  rw [VaughanTypeIIBridge.sigma22_eq_reciprocalBilinearSum]
  apply reciprocalBilinearSum_eq_sum_dyadic
  · intro r hr
    have hr' := Finset.mem_Ioc.mp hr
    exact ⟨by omega, hr'.2⟩
  · intro l hl
    exact Finset.mem_Icc.mp hl

/-- Dyadic decomposition of the actual `Σ₃` Vaughan term. -/
theorem sigma3_eq_sum_dyadic
    (y y' M K : ℕ) (x : ℝ) :
    VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K =
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          TypeII.reciprocalBilinearSum (Finset.Ioc y y')
            (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x
            (restrictCoeff (Finset.Ioc M y')
              (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
            (restrictCoeff (Finset.Ioc K y')
              (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))) := by
  rw [VaughanTypeIIBridge.sigma3_eq_reciprocalBilinearSum]
  apply reciprocalBilinearSum_eq_sum_dyadic
  · intro l hl
    have hl' := Finset.mem_Ioc.mp hl
    exact ⟨by omega, hl'.2⟩
  · intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    exact ⟨by omega, hk'.2⟩

/-! ## Norm endpoints for the dyadic bilinear sums -/

/-- Triangle inequality for a finite rectangular family of complex sums. -/
theorem norm_doubleSum_le_of_norm_le
    (J K : Finset ℕ) (z : ℕ → ℕ → ℂ) (F : ℕ → ℕ → ℝ)
    (h : ∀ j ∈ J, ∀ k ∈ K, ‖z j k‖ ≤ F j k) :
    ‖∑ j ∈ J, ∑ k ∈ K, z j k‖ ≤
      ∑ j ∈ J, ∑ k ∈ K, F j k := by
  calc
    ‖∑ j ∈ J, ∑ k ∈ K, z j k‖ ≤
        ∑ j ∈ J, ‖∑ k ∈ K, z j k‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ∑ k ∈ K, ‖z j k‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ∑ k ∈ K, F j k := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact h j hj k hk

/-- Raw norm endpoint for the dyadic `Σ₂,₂` expansion. -/
theorem norm_sigma22_le_sum_dyadic_of_block
    (y y' M K : ℕ) (x : ℝ) (F : ℕ → ℕ → ℝ)
    (hblock : ∀ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
      ∀ k ∈ Finset.range (TypeI.dyadicCount y'),
        ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
          (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x
          (restrictCoeff (Finset.Ioc M (M * K))
            (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
          (restrictCoeff (Finset.Icc 1 y') (fun _ => 1))‖ ≤ F j k) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'), F j k := by
  rw [sigma22_eq_sum_dyadic]
  exact norm_doubleSum_le_of_norm_le _ _ _ F hblock

/-- Raw norm endpoint for the dyadic `Σ₃` expansion. -/
theorem norm_sigma3_le_sum_dyadic_of_block
    (y y' M K : ℕ) (x : ℝ) (F : ℕ → ℕ → ℝ)
    (hblock : ∀ j ∈ Finset.range (TypeI.dyadicCount y'),
      ∀ k ∈ Finset.range (TypeI.dyadicCount y'),
        ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
          (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x
          (restrictCoeff (Finset.Ioc M y')
            (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
          (restrictCoeff (Finset.Ioc K y')
            (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)))‖ ≤ F j k) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'), F j k := by
  rw [sigma3_eq_sum_dyadic]
  exact norm_doubleSum_le_of_norm_le _ _ _ F hblock

/-- The fully explicit near--far factor for a pair of power blocks. -/
noncomputable def dyadicNearFarFactor
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) : ℝ :=
  TypeII.l2Norm (TypeI.dyadicBlock j) alpha *
    Real.sqrt
      (2 * (2 ^ j : ℕ) * (2 * T + 1) +
        TypeII.threeBranchFarQ x y y'
          (2 ^ j - 1) (2 ^ (j + 1) - 1)
          (2 ^ k - 1) (2 ^ (k + 1) - 1) T * (2 ^ k : ℕ)) *
    TypeII.l2Norm (TypeI.dyadicBlock k) beta

/-- The premise-free near--far estimate on two power blocks. -/
theorem norm_reciprocalBilinearSum_dyadic_le_near_far
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) (hx : 0 < x) :
    ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta‖ ≤
      dyadicNearFarFactor x y y' j k T alpha beta := by
  have hjpos : 0 < 2 ^ j := pow_pos (by norm_num) j
  have hkpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hjdiff :
      (2 ^ (j + 1) - 1) - (2 ^ j - 1) = 2 ^ j := by
    rw [pow_succ]
    omega
  have hkdiff :
      (2 ^ (k + 1) - 1) - (2 ^ k - 1) = 2 ^ k := by
    rw [pow_succ]
    omega
  have hdyadic :
      (2 ^ (j + 1) - 1) - (2 ^ j - 1) ≤ (2 ^ j - 1) + 1 := by
    rw [hjdiff]
    omega
  rw [dyadicBlock_eq_Ioc_pred j, dyadicBlock_eq_Ioc_pred k]
  have h := TypeII.norm_reciprocalBilinearSum_Ioc_le_near_far
    x y y' (2 ^ j - 1) (2 ^ (j + 1) - 1)
      (2 ^ k - 1) (2 ^ (k + 1) - 1) T alpha beta hx hdyadic
  simpa only [dyadicNearFarFactor, dyadicBlock_eq_Ioc_pred, hjdiff, hkdiff]
    using h

/-- A power-block rectangle can meet the product interval `(y,y']` only if
its exclusive upper product is above `y` and its inclusive lower product is
at most `y'`. -/
def blockActive (y y' j k : ℕ) : Prop :=
  y < 2 ^ (j + 1) * 2 ^ (k + 1) ∧ 2 ^ j * 2 ^ k ≤ y'

instance blockActiveDecidable (y y' j k : ℕ) : Decidable (blockActive y y' j k) :=
  by
    unfold blockActive
    infer_instance

/-- An active block has lower product at most `y'`. -/
theorem blockActive_lower_product_le
    {y y' j k : ℕ} (h : blockActive y y' j k) :
    2 ^ j * 2 ^ k ≤ y' := h.2

/-- An active block also has lower product greater than `y/4`; the factor
four is the ratio between the exclusive upper and inclusive lower products
of two power blocks. -/
theorem blockActive_y_lt_four_mul_lower_product
    {y y' j k : ℕ} (h : blockActive y y' j k) :
    y < 4 * (2 ^ j * 2 ^ k) := by
  calc
    y < 2 ^ (j + 1) * 2 ^ (k + 1) := h.1
    _ = 4 * (2 ^ j * 2 ^ k) := by
      rw [pow_succ, pow_succ]
      ring

/-- An inactive power rectangle contributes exactly zero to the
product-restricted reciprocal bilinear sum. -/
theorem reciprocalBilinearSum_dyadic_eq_zero_of_not_blockActive
    (y y' j k : ℕ) (x : ℝ) (alpha beta : ℕ → ℂ)
    (hinactive : ¬ blockActive y y' j k) :
    TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta = 0 := by
  rw [TypeII.reciprocalBilinearSum_eq]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have huI := TypeI.mem_dyadicBlock.mp hu
  have hvI := TypeI.mem_dyadicBlock.mp hv
  have hvpos : 0 < v :=
    lt_of_lt_of_le (pow_pos (by norm_num) k) hvI.1
  have huppos : 0 < 2 ^ (j + 1) := pow_pos (by norm_num) (j + 1)
  have huvUpper : u * v < 2 ^ (j + 1) * 2 ^ (k + 1) := by
    calc
      u * v < 2 ^ (j + 1) * v :=
        (Nat.mul_lt_mul_right hvpos).2 huI.2
      _ < 2 ^ (j + 1) * 2 ^ (k + 1) :=
        (Nat.mul_lt_mul_left huppos).2 hvI.2
  have huvLower : 2 ^ j * 2 ^ k ≤ u * v :=
    Nat.mul_le_mul huI.1 hvI.1
  have hnotmem : u * v ∉ Finset.Ioc y y' := by
    intro hmem
    have hmem' := Finset.mem_Ioc.mp hmem
    rcases not_and_or.mp hinactive with hlow | hupp
    · have : 2 ^ (j + 1) * 2 ^ (k + 1) ≤ y := Nat.le_of_not_gt hlow
      omega
    · have : y' < 2 ^ j * 2 ^ k := Nat.lt_of_not_ge hupp
      omega
  rw [if_neg hnotmem]

/-- The explicit near--far factor, with inactive rectangles erased. -/
theorem norm_reciprocalBilinearSum_dyadic_le_near_far_active
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) (hx : 0 < x) :
    ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta‖ ≤
      if blockActive y y' j k then
        dyadicNearFarFactor x y y' j k T alpha beta
      else 0 := by
  by_cases hactive : blockActive y y' j k
  · rw [if_pos hactive]
    exact norm_reciprocalBilinearSum_dyadic_le_near_far
      x y y' j k T alpha beta hx
  · rw [if_neg hactive,
      reciprocalBilinearSum_dyadic_eq_zero_of_not_blockActive
        y y' j k x alpha beta hactive, norm_zero]

/-- Orient a dyadic rectangle so the larger power block is the first
variable (the reciprocal-summation variable), using the supplied diagonal
threshold. -/
noncomputable def orientedDyadicNearFarFactorAt
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) : ℝ :=
  if j < k then
    dyadicNearFarFactor x y y' k j T beta alpha
  else
    dyadicNearFarFactor x y y' j k T alpha beta

/-- Zero-threshold specialization retained for convenience. -/
noncomputable def orientedDyadicNearFarFactor
    (x : ℝ) (y y' j k : ℕ) (alpha beta : ℕ → ℂ) : ℝ :=
  orientedDyadicNearFarFactorAt x y y' j k 0 alpha beta

/-- Premise-free near--far estimate with the larger of the two blocks
chosen as the reciprocal-summation variable and arbitrary threshold. -/
theorem norm_reciprocalBilinearSum_dyadic_le_oriented_at
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) (hx : 0 < x) :
    ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta‖ ≤
      orientedDyadicNearFarFactorAt x y y' j k T alpha beta := by
  by_cases hjk : j < k
  · rw [TypeII.reciprocalBilinearSum_comm]
    rw [orientedDyadicNearFarFactorAt, if_pos hjk]
    exact norm_reciprocalBilinearSum_dyadic_le_near_far
      x y y' k j T beta alpha hx
  · rw [orientedDyadicNearFarFactorAt, if_neg hjk]
    exact norm_reciprocalBilinearSum_dyadic_le_near_far
      x y y' j k T alpha beta hx

/-- Zero-threshold specialization of the oriented estimate. -/
theorem norm_reciprocalBilinearSum_dyadic_le_oriented
    (x : ℝ) (y y' j k : ℕ) (alpha beta : ℕ → ℂ) (hx : 0 < x) :
    ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta‖ ≤
      orientedDyadicNearFarFactor x y y' j k alpha beta := by
  simpa only [orientedDyadicNearFarFactor] using
    norm_reciprocalBilinearSum_dyadic_le_oriented_at
      x y y' j k 0 alpha beta hx

/-- Active-block version of the oriented bound with arbitrary threshold. -/
theorem norm_reciprocalBilinearSum_dyadic_le_oriented_active_at
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) (hx : 0 < x) :
    ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta‖ ≤
      if blockActive y y' j k then
        orientedDyadicNearFarFactorAt x y y' j k T alpha beta
      else 0 := by
  by_cases hactive : blockActive y y' j k
  · rw [if_pos hactive]
    exact norm_reciprocalBilinearSum_dyadic_le_oriented_at
      x y y' j k T alpha beta hx
  · rw [if_neg hactive,
      reciprocalBilinearSum_dyadic_eq_zero_of_not_blockActive
        y y' j k x alpha beta hactive, norm_zero]

/-- Zero-threshold specialization of the active oriented bound. -/
theorem norm_reciprocalBilinearSum_dyadic_le_oriented_active
    (x : ℝ) (y y' j k : ℕ) (alpha beta : ℕ → ℂ) (hx : 0 < x) :
    ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta‖ ≤
      if blockActive y y' j k then
        orientedDyadicNearFarFactor x y y' j k alpha beta
      else 0 := by
  simpa only [orientedDyadicNearFarFactor] using
    norm_reciprocalBilinearSum_dyadic_le_oriented_active_at
      x y y' j k 0 alpha beta hx

/-- A no-analytic-premise finite-double-sum bound for the actual `Σ₂,₂`.
The threshold may be optimized independently on each pair of blocks. -/
theorem norm_sigma22_le_sum_dyadic_near_far
    (y y' M K : ℕ) (x : ℝ) (threshold : ℕ → ℕ → ℕ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          dyadicNearFarFactor x y y' j k (threshold j k)
            (restrictCoeff (Finset.Ioc M (M * K))
              (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
            (restrictCoeff (Finset.Icc 1 y') (fun _ => 1)) := by
  apply norm_sigma22_le_sum_dyadic_of_block
  intro j hj k hk
  exact norm_reciprocalBilinearSum_dyadic_le_near_far
    x y y' j k (threshold j k) _ _ hx

/-- A no-analytic-premise finite-double-sum bound for the actual `Σ₃`. -/
theorem norm_sigma3_le_sum_dyadic_near_far
    (y y' M K : ℕ) (x : ℝ) (threshold : ℕ → ℕ → ℕ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          dyadicNearFarFactor x y y' j k (threshold j k)
            (restrictCoeff (Finset.Ioc M y')
              (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
            (restrictCoeff (Finset.Ioc K y')
              (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))) := by
  apply norm_sigma3_le_sum_dyadic_of_block
  intro j hj k hk
  exact norm_reciprocalBilinearSum_dyadic_le_near_far
    x y y' j k (threshold j k) _ _ hx

/-- Active-block strengthening of the no-premise `Σ₂,₂` endpoint. -/
theorem norm_sigma22_le_sum_dyadic_near_far_active
    (y y' M K : ℕ) (x : ℝ) (threshold : ℕ → ℕ → ℕ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            dyadicNearFarFactor x y y' j k (threshold j k)
              (restrictCoeff (Finset.Ioc M (M * K))
                (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
              (restrictCoeff (Finset.Icc 1 y') (fun _ => 1))
          else 0 := by
  apply norm_sigma22_le_sum_dyadic_of_block
  intro j hj k hk
  exact norm_reciprocalBilinearSum_dyadic_le_near_far_active
    x y y' j k (threshold j k) _ _ hx

/-- Active-block strengthening of the no-premise `Σ₃` endpoint. -/
theorem norm_sigma3_le_sum_dyadic_near_far_active
    (y y' M K : ℕ) (x : ℝ) (threshold : ℕ → ℕ → ℕ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            dyadicNearFarFactor x y y' j k (threshold j k)
              (restrictCoeff (Finset.Ioc M y')
                (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
              (restrictCoeff (Finset.Ioc K y')
                (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)))
          else 0 := by
  apply norm_sigma3_le_sum_dyadic_of_block
  intro j hj k hk
  exact norm_reciprocalBilinearSum_dyadic_le_near_far_active
    x y y' j k (threshold j k) _ _ hx

/-- Oriented active-block endpoint for the actual `Σ₂,₂`, with an
independently supplied diagonal threshold for every rectangle. -/
theorem norm_sigma22_le_sum_dyadic_oriented_active_at
    (y y' M K : ℕ) (x : ℝ) (threshold : ℕ → ℕ → ℕ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            orientedDyadicNearFarFactorAt x y y' j k (threshold j k)
              (restrictCoeff (Finset.Ioc M (M * K))
                (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
              (restrictCoeff (Finset.Icc 1 y') (fun _ => 1))
          else 0 := by
  apply norm_sigma22_le_sum_dyadic_of_block
  intro j hj k hk
  exact norm_reciprocalBilinearSum_dyadic_le_oriented_active_at
    x y y' j k (threshold j k) _ _ hx

/-- Oriented active-block endpoint for the actual `Σ₃`, with an
independently supplied diagonal threshold for every rectangle. -/
theorem norm_sigma3_le_sum_dyadic_oriented_active_at
    (y y' M K : ℕ) (x : ℝ) (threshold : ℕ → ℕ → ℕ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            orientedDyadicNearFarFactorAt x y y' j k (threshold j k)
              (restrictCoeff (Finset.Ioc M y')
                (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
              (restrictCoeff (Finset.Ioc K y')
                (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)))
          else 0 := by
  apply norm_sigma3_le_sum_dyadic_of_block
  intro j hj k hk
  exact norm_reciprocalBilinearSum_dyadic_le_oriented_active_at
    x y y' j k (threshold j k) _ _ hx

/-- Canonical three-quarter-power diagonal threshold on the selected
larger block. -/
def threeQuarterThreshold (j k : ℕ) : ℕ :=
  2 ^ (3 * max j k / 4)

/-- Canonically thresholded oriented endpoint for `Σ₂,₂`. -/
theorem norm_sigma22_le_sum_dyadic_oriented_active_threeQuarter
    (y y' M K : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            orientedDyadicNearFarFactorAt x y y' j k
              (threeQuarterThreshold j k)
              (restrictCoeff (Finset.Ioc M (M * K))
                (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
              (restrictCoeff (Finset.Icc 1 y') (fun _ => 1))
          else 0 := by
  exact norm_sigma22_le_sum_dyadic_oriented_active_at
    y y' M K x threeQuarterThreshold hx

/-- Canonically thresholded oriented endpoint for `Σ₃`. -/
theorem norm_sigma3_le_sum_dyadic_oriented_active_threeQuarter
    (y y' M K : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            orientedDyadicNearFarFactorAt x y y' j k
              (threeQuarterThreshold j k)
              (restrictCoeff (Finset.Ioc M y')
                (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
              (restrictCoeff (Finset.Ioc K y')
                (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)))
          else 0 := by
  exact norm_sigma3_le_sum_dyadic_oriented_active_at
    y y' M K x threeQuarterThreshold hx

/-- Zero-threshold oriented active-block endpoint for the actual `Σ₂,₂`. -/
theorem norm_sigma22_le_sum_dyadic_oriented_active
    (y y' M K : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            orientedDyadicNearFarFactor x y y' j k
              (restrictCoeff (Finset.Ioc M (M * K))
                (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
              (restrictCoeff (Finset.Icc 1 y') (fun _ => 1))
          else 0 := by
  simpa only [orientedDyadicNearFarFactor] using
    norm_sigma22_le_sum_dyadic_oriented_active_at
      y y' M K x (fun _ _ => 0) hx

/-- Zero-threshold oriented active-block endpoint for the actual `Σ₃`. -/
theorem norm_sigma3_le_sum_dyadic_oriented_active
    (y y' M K : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            orientedDyadicNearFarFactor x y y' j k
              (restrictCoeff (Finset.Ioc M y')
                (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
              (restrictCoeff (Finset.Ioc K y')
                (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)))
          else 0 := by
  simpa only [orientedDyadicNearFarFactor] using
    norm_sigma3_le_sum_dyadic_oriented_active_at
      y y' M K x (fun _ _ => 0) hx

#print axioms reciprocalBilinearSum_eq_sum_dyadic
#print axioms sigma22_eq_sum_dyadic
#print axioms sigma3_eq_sum_dyadic
#print axioms norm_sigma22_le_sum_dyadic_near_far
#print axioms norm_sigma3_le_sum_dyadic_near_far
#print axioms norm_sigma22_le_sum_dyadic_near_far_active
#print axioms norm_sigma3_le_sum_dyadic_near_far_active
#print axioms norm_sigma22_le_sum_dyadic_oriented_active_at
#print axioms norm_sigma3_le_sum_dyadic_oriented_active_at
#print axioms norm_sigma22_le_sum_dyadic_oriented_active_threeQuarter
#print axioms norm_sigma3_le_sum_dyadic_oriented_active_threeQuarter
#print axioms norm_sigma22_le_sum_dyadic_oriented_active
#print axioms norm_sigma3_le_sum_dyadic_oriented_active

end Erdos175.VaughanTypeIIDyadic

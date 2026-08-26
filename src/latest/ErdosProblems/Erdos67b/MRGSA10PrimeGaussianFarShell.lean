import ErdosProblems.Erdos67b.MRGSA10PrimeLogHarmonicShell

/-!
# A uniform Gaussian row bound from logarithmic prime shells

The fixed-gap estimate in `MRGSA10PrimeGaussianNearRow` pays the entire
prime-log harmonic mass after extracting just one Gaussian factor.  Here we
retain all of the Gaussian decay.  We put each prime `m` in its unique dyadic
shell `(2^k,2^(k+1)]`; the two-sided prime Mertens estimate gives a uniform
bound for the weighted mass of every shell, while the existing Gaussian
dyadic-shell theorem has a uniformly bounded row sum.

Although motivated by the far part, the resulting argument bounds the entire
prime row.  In particular the far row is bounded by the same universal
constant, independently of `X`.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b
open Erdos67b.MRIntervalBetaSieve

/-- The dyadic shell index adapted to intervals `(2^k,2^(k+1)]`. -/
def gsA10PrimeDyadicShellIndex (m : ℕ) : ℕ :=
  Nat.log 2 (m - 1)

/-- Every prime belongs to the dyadic shell selected by
`gsA10PrimeDyadicShellIndex`. -/
theorem prime_mem_Ioc_pow_two_shell (m : ℕ) (hm : m.Prime) :
    m ∈ Finset.Ioc (2 ^ gsA10PrimeDyadicShellIndex m)
      (2 ^ (gsA10PrimeDyadicShellIndex m + 1)) := by
  have hm2 : 2 ≤ m := hm.two_le
  have hmSub : m - 1 ≠ 0 := by omega
  have hlower : 2 ^ Nat.log 2 (m - 1) ≤ m - 1 :=
    Nat.pow_log_le_self 2 hmSub
  have hupper : m - 1 < 2 ^ (Nat.log 2 (m - 1)).succ :=
    Nat.lt_pow_succ_log_self (by omega) (m - 1)
  rw [Finset.mem_Ioc]
  constructor <;> simp only [gsA10PrimeDyadicShellIndex]
  · omega
  · simpa only [Nat.succ_eq_add_one] using (show m ≤
      2 ^ (Nat.log 2 (m - 1) + 1) by omega)

/-- Shell indices of primes in the A.10 window lie in `range X`. -/
theorem gsA10PrimeDyadicShellIndex_lt_ambient
    {y X m : ℕ} (hm : m ∈ gsA10PrimeWindow y X) :
    gsA10PrimeDyadicShellIndex m < X := by
  have hmData := mem_gsA10PrimeWindow.mp hm
  have hmX : m < X := hmData.2.1.trans_le (Nat.div_le_self X y)
  have hidx : gsA10PrimeDyadicShellIndex m ≤ m - 1 := by
    unfold gsA10PrimeDyadicShellIndex
    exact Nat.log_le_self 2 (m - 1)
  omega

/-- Grouping four consecutive dyadic shells only loses the three endpoint
steps displayed here. -/
theorem four_mul_dist_div_four_sub_one_le_dist_sub_one (a b : ℕ) :
    4 * (Nat.dist (a / 4) (b / 4) - 1) ≤ Nat.dist a b - 1 := by
  wlog hab : a ≤ b generalizing a b
  · rw [Nat.dist_comm a b, Nat.dist_comm (a / 4) (b / 4)]
    exact this b a (Nat.le_of_not_ge hab)
  have hdiv : a / 4 ≤ b / 4 := Nat.div_le_div_right hab
  rw [Nat.dist_eq_sub_of_le hab, Nat.dist_eq_sub_of_le hdiv]
  by_cases hnear : b / 4 - a / 4 ≤ 1
  · omega
  · have haLower := Nat.div_mul_le_self a 4
    have hbLower := Nat.div_mul_le_self b 4
    have haUpper := Nat.lt_mul_div_succ a (by omega : 0 < 4)
    have hbUpper := Nat.lt_mul_div_succ b (by omega : 0 < 4)
    omega

/-- Four times the coarse (four-dyadic-shell) logarithmic gap is no larger
than the fine dyadic gap. -/
theorem four_mul_coarseDyadicShellGap_le_fine
    (a b : ℕ) :
    4 * finiteHalaszDyadicShellGap (a / 4) (b / 4) ≤
      finiteHalaszDyadicShellGap a b := by
  have hnat := four_mul_dist_div_four_sub_one_le_dist_sub_one a b
  have hcast :
      (4 * (Nat.dist (a / 4) (b / 4) - 1) : ℕ) ≤
        Nat.dist a b - 1 := hnat
  unfold finiteHalaszDyadicShellGap
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hreal :
      ((4 * (Nat.dist (a / 4) (b / 4) - 1) : ℕ) : ℝ) ≤
        ((Nat.dist a b - 1 : ℕ) : ℝ) := by exact_mod_cast hcast
  push_cast at hreal ⊢
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hreal hlog

/-- If the actual logarithmic gap is four times a shell gap, then every
Gaussian with `T ≥ 1` is bounded by the dyadic shell kernel at parameter
four. -/
theorem finiteHalaszGaussianPairKernel_le_shellKernel_four_of_four_gap
    {T x g : ℝ} (hT : 1 ≤ T) (hg : 0 ≤ g)
    (hgap : 4 * g ≤ |x|) :
    finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) x ≤
      finiteHalaszGaussianPairKernel ((4 : ℝ)⁻¹ ^ 2) g := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hxSq : (4 * g) ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (mul_nonneg (by norm_num) hg) hgap 2
  have hT2 : 1 ≤ T ^ 2 := by nlinarith
  have hprod : x ^ 2 ≤ T ^ 2 * x ^ 2 := by
    nlinarith [sq_nonneg x, mul_nonneg (sub_nonneg.mpr hT2) (sq_nonneg x)]
  unfold finiteHalaszGaussianPairKernel
  apply Real.exp_le_exp.mpr
  have hTne : T ≠ 0 := ne_of_gt hTpos
  have hmain : 16 * g ^ 2 ≤ T ^ 2 * x ^ 2 := by
    nlinarith [hxSq, hprod]
  norm_num [hTne]
  field_simp [hTne]
  nlinarith

/-- Beyond unit logarithmic distance, increasing the Gaussian radius from
one to `T` extracts an explicit inverse-radius factor.  The harmless constant
five avoids optimizing the transition range `1 ≤ T ≤ 5`. -/
theorem finiteHalaszGaussianPairKernel_le_five_div_mul_one_of_one_le_gap
    {T x : ℝ} (hT : 1 ≤ T) (hgap : 1 ≤ |x|) :
    finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) x ≤
      (5 / T) * finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2) x := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hxSq : 1 ≤ x ^ 2 := by
    rw [← sq_abs x]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hgap 2]
  let u : ℝ := (T ^ 2 - 1) * x ^ 2 / 4
  have hu : 0 ≤ u := by
    dsimp only [u]
    exact div_nonneg
      (mul_nonneg (by nlinarith) (sq_nonneg x)) (by norm_num)
  have hdecay : T * Real.exp (-u) ≤ 5 := by
    by_cases hsmall : T ≤ 5
    · have hexp : Real.exp (-u) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (neg_nonpos.mpr hu)
      nlinarith [Real.exp_pos (-u)]
    · have hlarge : 5 < T := lt_of_not_ge hsmall
      have hprod : T ^ 2 - 1 ≤ (T ^ 2 - 1) * x ^ 2 := by
        have hcoef : 0 ≤ T ^ 2 - 1 := by nlinarith
        nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hxSq)]
      have hTu : T ≤ u := by
        dsimp only [u]
        nlinarith
      have hexp : Real.exp (-u) ≤ Real.exp (-T) :=
        Real.exp_le_exp.mpr (neg_le_neg hTu)
      have hbasic := Real.mul_exp_neg_le_exp_neg_one T
      have hnonnegT : 0 ≤ T := hTpos.le
      have hmul : T * Real.exp (-u) ≤ T * Real.exp (-T) :=
        mul_le_mul_of_nonneg_left hexp hnonnegT
      have hone : Real.exp (-1) ≤ 1 :=
        (Real.exp_neg_one_lt_half.trans (by norm_num)).le
      linarith
  have hfactor :
      finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) x =
        finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2) x *
          Real.exp (-u) := by
    unfold finiteHalaszGaussianPairKernel
    have hTne : T ≠ 0 := ne_of_gt hTpos
    rw [← Real.exp_add]
    congr 1
    dsimp only [u]
    field_simp [hTne]
    ring
  rw [hfactor]
  have hK0 : 0 ≤
      finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2) x :=
    finiteHalaszGaussianPairKernel_nonneg _ _
  rw [show (5 / T) *
      finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2) x =
        (5 * finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2) x) / T by
      field_simp]
  apply (le_div_iff₀ hTpos).2
  calc
    finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2) x *
          Real.exp (-u) * T =
        finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2) x *
          (T * Real.exp (-u)) := by ring
    _ ≤ finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2) x * 5 :=
      mul_le_mul_of_nonneg_left hdecay hK0
    _ = 5 * finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2) x := by
      ring

/-- Four adjacent dyadic shells are grouped into one coarse shell. -/
def gsA10PrimeCoarseDyadicShellIndex (m : ℕ) : ℕ :=
  gsA10PrimeDyadicShellIndex m / 4

/-- A prime lies between the endpoints of its coarse four-dyadic-shell
block. -/
theorem prime_mem_Ioc_coarse_pow_two_shell (m : ℕ) (hm : m.Prime) :
    m ∈ Finset.Ioc
      (2 ^ (4 * gsA10PrimeCoarseDyadicShellIndex m))
      (2 ^ (4 * (gsA10PrimeCoarseDyadicShellIndex m + 1))) := by
  let a := gsA10PrimeDyadicShellIndex m
  have hfine := Finset.mem_Ioc.mp (prime_mem_Ioc_pow_two_shell m hm)
  have haLower := Nat.div_mul_le_self a 4
  have haUpper := Nat.lt_mul_div_succ a (by omega : 0 < 4)
  have hleftExp : 4 * (a / 4) ≤ a := by omega
  have hrightExp : a + 1 ≤ 4 * (a / 4 + 1) := by omega
  have hleftPow : 2 ^ (4 * (a / 4)) ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by omega) hleftExp
  have hrightPow : 2 ^ (a + 1) ≤ 2 ^ (4 * (a / 4 + 1)) :=
    Nat.pow_le_pow_right (by omega) hrightExp
  rw [Finset.mem_Ioc]
  simpa only [gsA10PrimeCoarseDyadicShellIndex, a] using
    And.intro (hleftPow.trans_lt hfine.1) (hfine.2.trans hrightPow)

theorem gsA10PrimeCoarseDyadicShellIndex_lt_ambient
    {y X m : ℕ} (hm : m ∈ gsA10PrimeWindow y X) :
    gsA10PrimeCoarseDyadicShellIndex m < X := by
  have hfine := gsA10PrimeDyadicShellIndex_lt_ambient hm
  unfold gsA10PrimeCoarseDyadicShellIndex
  exact (Nat.div_le_self _ _).trans_lt hfine

/-- At Gaussian frequency radius at least four, the complete logarithmically
weighted A.10 prime row is bounded by a universal constant. -/
theorem sum_gsA10PrimeWindow_log_div_gaussian_le_shell_constant
    {y X n : ℕ} {T : ℝ} (hT : 4 ≤ T)
    (hnWindow : n ∈ gsA10PrimeWindow y X) :
    (∑ m ∈ gsA10PrimeWindow y X,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      8 * gsA10PrimeLogHarmonicFactorFourConstant := by
  let E := gsA10PrimeWindow y X
  let idx := gsA10PrimeDyadicShellIndex
  let term : ℕ → ℝ := fun m ↦
    (Real.log (m : ℝ) / m) *
      finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
        (Real.log m - Real.log n)
  let M := gsA10PrimeLogHarmonicFactorFourConstant
  let j := idx n
  have hTpos : 0 < T := by linarith
  have hb : 0 < T⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hTpos)
  have hnData := mem_gsA10PrimeWindow.mp hnWindow
  have hnShell : n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)) := by
    simpa only [j, idx] using
      prime_mem_Ioc_pow_two_shell n hnData.2.2
  have hj : j < X := by
    simpa only [j, idx, E] using
      gsA10PrimeDyadicShellIndex_lt_ambient hnWindow
  have hmaps : ∀ m ∈ E, idx m ∈ Finset.range X := by
    intro m hm
    rw [Finset.mem_range]
    simpa only [idx, E] using
      gsA10PrimeDyadicShellIndex_lt_ambient hm
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps term
  rw [← hfiber]
  calc
    (∑ k ∈ Finset.range X, ∑ m ∈ E with idx m = k, term m) ≤
        ∑ k ∈ Finset.range X,
          finiteHalaszDyadicShellKernel T j k * M := by
      apply Finset.sum_le_sum
      intro k hk
      let F := E.filter fun m ↦ idx m = k
      let K := finiteHalaszDyadicShellKernel T j k
      have hpoint : ∀ m ∈ F, term m ≤
          (Real.log (m : ℝ) / m) * K := by
        intro m hm
        have hmFilter := Finset.mem_filter.mp hm
        have hmWindow : m ∈ gsA10PrimeWindow y X := by
          simpa only [E] using hmFilter.1
        have hmData := mem_gsA10PrimeWindow.mp hmWindow
        have hmShell0 := prime_mem_Ioc_pow_two_shell m hmData.2.2
        have hmShell : m ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)) := by
          simpa only [idx, hmFilter.2] using hmShell0
        have hgap : finiteHalaszDyadicShellGap j k ≤
            |Real.log m - Real.log n| := by
          have := finiteHalaszDyadicShellGap_le_abs_log_sub
            (L := 1) (j := j) (k := k) (n := n) (m := m)
            (by norm_num) (by simpa using hnShell) (by simpa using hmShell)
          simpa using this
        have hkernel :
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n) ≤ K := by
          simpa only [K, finiteHalaszDyadicShellKernel] using
            finiteHalaszGaussianPairKernel_le_of_gap hb
              (by unfold finiteHalaszDyadicShellGap; positivity) hgap
        have hweight : 0 ≤ Real.log (m : ℝ) / m :=
          div_nonneg
            (Real.log_nonneg (by exact_mod_cast hmData.2.2.one_le))
            (by positivity)
        exact mul_le_mul_of_nonneg_left hkernel hweight
      have hmass : (∑ m ∈ F, Real.log (m : ℝ) / m) ≤ M := by
        have hsubset : F ⊆ gsA10PrimeWindow y X := by
          intro m hm
          have := (Finset.mem_filter.mp hm).1
          simpa only [E] using this
        have hshell : ∀ m ∈ F, 2 ^ k < m ∧ m ≤ 2 ^ (k + 1) := by
          intro m hm
          have hmFilter := Finset.mem_filter.mp hm
          have hmWindow : m ∈ gsA10PrimeWindow y X := by
            simpa only [E] using hmFilter.1
          have hmPrime := (mem_gsA10PrimeWindow.mp hmWindow).2.2
          have hmShell0 := prime_mem_Ioc_pow_two_shell m hmPrime
          have hmShell : m ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)) := by
            simpa only [idx, hmFilter.2] using hmShell0
          exact Finset.mem_Ioc.mp hmShell
        have hA : 0 < 2 ^ k := pow_pos (by omega) _
        have hAB : 2 ^ k ≤ 2 ^ (k + 1) := by
          rw [pow_succ]
          omega
        have hB4A : 2 ^ (k + 1) ≤ 4 * 2 ^ k := by
          rw [pow_succ]
          omega
        simpa only [M] using
          sum_primeLog_div_subset_interval_le_factorFourConstant
            hA hAB hB4A (by
              intro m hm
              exact PrimeEstimates.mem_primesInInterval.mpr
                ⟨(hshell m hm).1, (hshell m hm).2,
                  (mem_gsA10PrimeWindow.mp (hsubset hm)).2.2⟩)
      calc
        (∑ m ∈ E with idx m = k, term m) = ∑ m ∈ F, term m := rfl
        _ ≤ ∑ m ∈ F, (Real.log (m : ℝ) / m) * K :=
          Finset.sum_le_sum hpoint
        _ = K * ∑ m ∈ F, Real.log (m : ℝ) / m := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          ring
        _ ≤ K * M := mul_le_mul_of_nonneg_left hmass
          (finiteHalaszDyadicShellKernel_nonneg T j k)
        _ = finiteHalaszDyadicShellKernel T j k * M := rfl
    _ = M * ∑ k ∈ Finset.range X,
          finiteHalaszDyadicShellKernel T j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ M * 8 := mul_le_mul_of_nonneg_left
      (sum_dyadicShellKernel_le_eight hT hj)
      gsA10PrimeLogHarmonicFactorFourConstant_nonneg
    _ = 8 * gsA10PrimeLogHarmonicFactorFourConstant := by
      simp only [M]
      ring

/-- The requested `T ≥ 1` form.  Grouping four consecutive dyadic shells
turns their actual logarithmic separation into four times the ordinary
dyadic-shell gap, so the already proved parameter-four Gaussian row theorem
applies. -/
theorem sum_gsA10PrimeWindow_log_div_gaussian_le_shell_constant_of_one_le
    {y X n : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hnWindow : n ∈ gsA10PrimeWindow y X) :
    (∑ m ∈ gsA10PrimeWindow y X,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      16 * gsA10PrimeLogHarmonicFactorFourConstant := by
  let E := gsA10PrimeWindow y X
  let fine := gsA10PrimeDyadicShellIndex
  let idx := gsA10PrimeCoarseDyadicShellIndex
  let term : ℕ → ℝ := fun m ↦
    (Real.log (m : ℝ) / m) *
      finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
        (Real.log m - Real.log n)
  let M := gsA10PrimeLogHarmonicFactorFourConstant
  let j := idx n
  have hnData := mem_gsA10PrimeWindow.mp hnWindow
  have hnFineShell : n ∈ Finset.Ioc
      (2 ^ fine n) (2 ^ (fine n + 1)) := by
    simpa only [fine] using prime_mem_Ioc_pow_two_shell n hnData.2.2
  have hj : j < X := by
    simpa only [j, idx] using
      gsA10PrimeCoarseDyadicShellIndex_lt_ambient hnWindow
  have hmaps : ∀ m ∈ E, idx m ∈ Finset.range X := by
    intro m hm
    rw [Finset.mem_range]
    simpa only [idx, E] using
      gsA10PrimeCoarseDyadicShellIndex_lt_ambient hm
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps term
  rw [← hfiber]
  calc
    (∑ k ∈ Finset.range X, ∑ m ∈ E with idx m = k, term m) ≤
        ∑ k ∈ Finset.range X,
          finiteHalaszDyadicShellKernel 4 j k * (2 * M) := by
      apply Finset.sum_le_sum
      intro k hk
      let F := E.filter fun m ↦ idx m = k
      let K := finiteHalaszDyadicShellKernel 4 j k
      have hpoint : ∀ m ∈ F, term m ≤
          (Real.log (m : ℝ) / m) * K := by
        intro m hm
        have hmFilter := Finset.mem_filter.mp hm
        have hmWindow : m ∈ gsA10PrimeWindow y X := by
          simpa only [E] using hmFilter.1
        have hmData := mem_gsA10PrimeWindow.mp hmWindow
        have hmFineShell : m ∈ Finset.Ioc
            (2 ^ fine m) (2 ^ (fine m + 1)) := by
          simpa only [fine] using prime_mem_Ioc_pow_two_shell m hmData.2.2
        have hfineGap : finiteHalaszDyadicShellGap (fine n) (fine m) ≤
            |Real.log m - Real.log n| := by
          simpa using finiteHalaszDyadicShellGap_le_abs_log_sub
            (L := 1) (j := fine n) (k := fine m) (n := n) (m := m)
            (by norm_num) (by simpa using hnFineShell)
            (by simpa using hmFineShell)
        have hcoarseGap :
            4 * finiteHalaszDyadicShellGap j k ≤
              |Real.log m - Real.log n| := by
          have hgroup := four_mul_coarseDyadicShellGap_le_fine
            (fine n) (fine m)
          have hidxN : fine n / 4 = j := by
            simp only [j, idx, fine, gsA10PrimeCoarseDyadicShellIndex]
          have hidxM : fine m / 4 = k := by
            have := hmFilter.2
            simpa only [idx, fine, gsA10PrimeCoarseDyadicShellIndex] using this
          rw [hidxN, hidxM] at hgroup
          exact hgroup.trans hfineGap
        have hkernel :
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n) ≤ K := by
          simpa only [K, finiteHalaszDyadicShellKernel] using
            finiteHalaszGaussianPairKernel_le_shellKernel_four_of_four_gap
              hT (by unfold finiteHalaszDyadicShellGap; positivity) hcoarseGap
        have hweight : 0 ≤ Real.log (m : ℝ) / m :=
          div_nonneg
            (Real.log_nonneg (by exact_mod_cast hmData.2.2.one_le))
            (by positivity)
        exact mul_le_mul_of_nonneg_left hkernel hweight
      have hmass : (∑ m ∈ F, Real.log (m : ℝ) / m) ≤ 2 * M := by
        let A : ℕ := 2 ^ (4 * k)
        let B : ℕ := 2 ^ (4 * (k + 1))
        have hA : 0 < A := by dsimp only [A]; positivity
        have hAB : A ≤ B := by
          dsimp only [A, B]
          apply Nat.pow_le_pow_right (by omega)
          omega
        have hsubset : F ⊆ gsA10PrimeWindow y X := by
          intro m hm
          have := (Finset.mem_filter.mp hm).1
          simpa only [E] using this
        have hshell : ∀ m ∈ F, A < m ∧ m ≤ B := by
          intro m hm
          have hmFilter := Finset.mem_filter.mp hm
          have hmWindow : m ∈ gsA10PrimeWindow y X := by
            simpa only [E] using hmFilter.1
          have hmPrime := (mem_gsA10PrimeWindow.mp hmWindow).2.2
          have hmShell0 := prime_mem_Ioc_coarse_pow_two_shell m hmPrime
          have hidxm : gsA10PrimeCoarseDyadicShellIndex m = k := by
            simpa only [idx] using hmFilter.2
          rw [hidxm] at hmShell0
          have hmShell : m ∈ Finset.Ioc A B := by
            simpa only [A, B] using hmShell0
          exact Finset.mem_Ioc.mp hmShell
        have hraw :=
          sum_primeLog_div_subset_gsA10PrimeWindow_le_log_div_add_two_mertens
            (S := F) (y := y) (X := X) hA hAB hsubset hshell
        have hB : B = 16 * A := by
          dsimp only [A, B]
          rw [show 4 * (k + 1) = 4 * k + 4 by omega, pow_add]
          norm_num [Nat.mul_comm]
        have hratio : ((B : ℝ) / (A : ℝ)) = 16 := by
          rw [hB]
          push_cast
          field_simp
        have hlog16 : Real.log (16 : ℝ) = 2 * Real.log 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
          norm_num
        rw [hratio, hlog16] at hraw
        dsimp only [M, gsA10PrimeLogHarmonicFactorFourConstant]
        nlinarith [Erdos67b.primeLogMertensConstant_nonneg]
      calc
        (∑ m ∈ E with idx m = k, term m) = ∑ m ∈ F, term m := rfl
        _ ≤ ∑ m ∈ F, (Real.log (m : ℝ) / m) * K :=
          Finset.sum_le_sum hpoint
        _ = K * ∑ m ∈ F, Real.log (m : ℝ) / m := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          ring
        _ ≤ K * (2 * M) := mul_le_mul_of_nonneg_left hmass
          (finiteHalaszDyadicShellKernel_nonneg 4 j k)
        _ = finiteHalaszDyadicShellKernel 4 j k * (2 * M) := rfl
    _ = (2 * M) * ∑ k ∈ Finset.range X,
          finiteHalaszDyadicShellKernel 4 j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (2 * M) * 8 := mul_le_mul_of_nonneg_left
      (sum_dyadicShellKernel_le_eight (T := (4 : ℝ)) (by norm_num) hj)
      (mul_nonneg (by norm_num)
        gsA10PrimeLogHarmonicFactorFourConstant_nonneg)
    _ = 16 * gsA10PrimeLogHarmonicFactorFourConstant := by
      simp only [M]
      ring

/-- The far portion alone inherits the same universal shell bound. -/
theorem sum_gsA10PrimeFarWindow_log_div_gaussian_le_shell_constant
    {y X n : ℕ} {T : ℝ} (hT : 4 ≤ T)
    (hnWindow : n ∈ gsA10PrimeWindow y X) :
    (∑ m ∈ gsA10PrimeFarWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      8 * gsA10PrimeLogHarmonicFactorFourConstant := by
  let term : ℕ → ℝ := fun m ↦
    (Real.log (m : ℝ) / m) *
      finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
        (Real.log m - Real.log n)
  have hsubset : gsA10PrimeFarWindow y X n ⊆ gsA10PrimeWindow y X :=
    Finset.filter_subset _ _
  have hnonneg : ∀ m ∈ gsA10PrimeWindow y X,
      m ∉ gsA10PrimeFarWindow y X n → 0 ≤ term m := by
    intro m hm _
    have hmData := mem_gsA10PrimeWindow.mp hm
    exact mul_nonneg
      (div_nonneg
        (Real.log_nonneg (by exact_mod_cast hmData.2.2.one_le))
        (by positivity))
      (finiteHalaszGaussianPairKernel_nonneg _ _)
  calc
    (∑ m ∈ gsA10PrimeFarWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) =
        ∑ m ∈ gsA10PrimeFarWindow y X n, term m := rfl
    _ ≤ ∑ m ∈ gsA10PrimeWindow y X, term m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    _ ≤ 8 * gsA10PrimeLogHarmonicFactorFourConstant :=
      sum_gsA10PrimeWindow_log_div_gaussian_le_shell_constant hT hnWindow

/-- Universal far-row bound in the full requested range `T ≥ 1`. -/
theorem sum_gsA10PrimeFarWindow_log_div_gaussian_le_shell_constant_of_one_le
    {y X n : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hnWindow : n ∈ gsA10PrimeWindow y X) :
    (∑ m ∈ gsA10PrimeFarWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      16 * gsA10PrimeLogHarmonicFactorFourConstant := by
  let term : ℕ → ℝ := fun m ↦
    (Real.log (m : ℝ) / m) *
      finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
        (Real.log m - Real.log n)
  have hsubset : gsA10PrimeFarWindow y X n ⊆ gsA10PrimeWindow y X :=
    Finset.filter_subset _ _
  have hnonneg : ∀ m ∈ gsA10PrimeWindow y X,
      m ∉ gsA10PrimeFarWindow y X n → 0 ≤ term m := by
    intro m hm _
    have hmData := mem_gsA10PrimeWindow.mp hm
    exact mul_nonneg
      (div_nonneg
        (Real.log_nonneg (by exact_mod_cast hmData.2.2.one_le))
        (by positivity))
      (finiteHalaszGaussianPairKernel_nonneg _ _)
  calc
    (∑ m ∈ gsA10PrimeFarWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) =
        ∑ m ∈ gsA10PrimeFarWindow y X n, term m := rfl
    _ ≤ ∑ m ∈ gsA10PrimeWindow y X, term m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    _ ≤ 16 * gsA10PrimeLogHarmonicFactorFourConstant :=
      sum_gsA10PrimeWindow_log_div_gaussian_le_shell_constant_of_one_le
        hT hnWindow

/-- Radius-decaying far-row estimate.  The fixed multiplicative gap extracts
`5/T` pointwise, and the remaining radius-one row has the universal shell
bound above. -/
theorem sum_gsA10PrimeFarWindow_log_div_gaussian_le_shell_constant_div
    {y X n : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hnWindow : n ∈ gsA10PrimeWindow y X) :
    (∑ m ∈ gsA10PrimeFarWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      (80 * gsA10PrimeLogHarmonicFactorFourConstant) / T := by
  let E := gsA10PrimeFarWindow y X n
  let w : ℕ → ℝ := fun m ↦ Real.log (m : ℝ) / m
  let oneTerm : ℕ → ℝ := fun m ↦
    w m * finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2)
      (Real.log m - Real.log n)
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hnData := mem_gsA10PrimeWindow.mp hnWindow
  have hnpos : 0 < n := (Nat.zero_le y).trans_lt hnData.1
  have hlogFour : (1 : ℝ) ≤ Real.log 4 := by
    have hstrict : (1 : ℝ) < Real.log 4 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2
        (Real.exp_one_lt_three.trans (by norm_num))
    exact hstrict.le
  have hpoint : ∀ m ∈ E,
      w m * finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
          (Real.log m - Real.log n) ≤
        (5 / T) * oneTerm m := by
    intro m hm
    have hmData := mem_gsA10PrimeFarWindow.mp (by simpa only [E] using hm)
    have hmWindow := mem_gsA10PrimeWindow.mp hmData.1
    have hmpos : 0 < m := (Nat.zero_le y).trans_lt hmWindow.1
    have hfarGap : (1 : ℝ) ≤ |Real.log m - Real.log n| :=
      hlogFour.trans
        (log_four_le_abs_log_sub_log_of_far hmpos hnpos hmData.2)
    have hkernel :=
      finiteHalaszGaussianPairKernel_le_five_div_mul_one_of_one_le_gap
        hT hfarGap
    have hw : 0 ≤ w m := by
      dsimp only [w]
      exact div_nonneg
        (Real.log_nonneg (by exact_mod_cast hmWindow.2.2.one_le))
        (by positivity)
    dsimp only [oneTerm]
    calc
      w m * finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
          (Real.log m - Real.log n) ≤
        w m * ((5 / T) *
          finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2)
            (Real.log m - Real.log n)) :=
          mul_le_mul_of_nonneg_left hkernel hw
      _ = (5 / T) *
          (w m * finiteHalaszGaussianPairKernel ((1 : ℝ)⁻¹ ^ 2)
            (Real.log m - Real.log n)) := by ring
  have hsubset : E ⊆ gsA10PrimeWindow y X := by
    intro m hm
    exact (mem_gsA10PrimeFarWindow.mp (by simpa only [E] using hm)).1
  have honeNonneg : ∀ m ∈ gsA10PrimeWindow y X,
      m ∉ E → 0 ≤ oneTerm m := by
    intro m hm _
    have hmData := mem_gsA10PrimeWindow.mp hm
    exact mul_nonneg
      (by
        dsimp only [w]
        exact div_nonneg
          (Real.log_nonneg (by exact_mod_cast hmData.2.2.one_le))
          (by positivity))
      (finiteHalaszGaussianPairKernel_nonneg _ _)
  have hbaseFar : (∑ m ∈ E, oneTerm m) ≤
      ∑ m ∈ gsA10PrimeWindow y X, oneTerm m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset honeNonneg
  have hbaseFull : (∑ m ∈ gsA10PrimeWindow y X, oneTerm m) ≤
      16 * gsA10PrimeLogHarmonicFactorFourConstant := by
    simpa only [oneTerm, w] using
      (sum_gsA10PrimeWindow_log_div_gaussian_le_shell_constant_of_one_le
        (T := (1 : ℝ)) (y := y) (X := X) (n := n) (by norm_num) hnWindow)
  calc
    (∑ m ∈ gsA10PrimeFarWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) =
        ∑ m ∈ E, w m *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := rfl
    _ ≤ ∑ m ∈ E, (5 / T) * oneTerm m :=
      Finset.sum_le_sum hpoint
    _ = (5 / T) * ∑ m ∈ E, oneTerm m := by
      rw [Finset.mul_sum]
    _ ≤ (5 / T) *
        (∑ m ∈ gsA10PrimeWindow y X, oneTerm m) :=
      mul_le_mul_of_nonneg_left hbaseFar (div_nonneg (by norm_num) hTpos.le)
    _ ≤ (5 / T) *
        (16 * gsA10PrimeLogHarmonicFactorFourConstant) :=
      mul_le_mul_of_nonneg_left hbaseFull (div_nonneg (by norm_num) hTpos.le)
    _ = (80 * gsA10PrimeLogHarmonicFactorFourConstant) / T := by ring

/-- The source-useful full row: retain the beta-sieved local estimate and
replace only the former global fixed-gap tail by the radius-decaying shell
bound. -/
theorem sum_gsA10PrimeWindow_log_div_gaussian_le_of_intervalBeta_farShell
    {I : ℕ × ℕ} {y X n : ℕ} {T density remainder : ℝ}
    (hT : 1 ≤ T) (hnWindow : n ∈ gsA10PrimeWindow y X)
    (hIz : ∀ q ∈ primesInBlock I, q ≤ y)
    (hdensity : 0 ≤ density) (hrem : 0 ≤ remainder)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    (∑ m ∈ gsA10PrimeWindow y X,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      (4 * Real.log (X : ℝ) / n) *
          (32 * ((4 * n : ℕ) : ℝ) / T * density +
            6 * density + 2 * remainder) +
        (80 * gsA10PrimeLogHarmonicFactorFourConstant) / T := by
  let term : ℕ → ℝ := fun m ↦
    (Real.log (m : ℝ) / m) *
      finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
        (Real.log m - Real.log n)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (gsA10PrimeWindow y X)
    (fun m ↦ m ∈ Finset.Ioc (n / 4) (4 * n)) term
  have hnear :=
    sum_gsA10PrimeNearWindow_log_div_gaussian_le_of_intervalBeta
      (show 0 < T by linarith) hnWindow hIz hdensity hrem hbeta
  have hfar :=
    sum_gsA10PrimeFarWindow_log_div_gaussian_le_shell_constant_div
      hT hnWindow
  have hEq :
      (∑ m ∈ gsA10PrimeWindow y X, term m) =
        (∑ m ∈ gsA10PrimeNearWindow y X n, term m) +
          ∑ m ∈ gsA10PrimeFarWindow y X n, term m := by
    simpa only [gsA10PrimeNearWindow, gsA10PrimeFarWindow] using hsplit.symm
  rw [show (∑ m ∈ gsA10PrimeWindow y X,
      (Real.log (m : ℝ) / m) *
        finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
          (Real.log m - Real.log n)) =
      ∑ m ∈ gsA10PrimeWindow y X, term m by rfl,
    hEq]
  exact add_le_add hnear hfar

/-- Concrete finite-beta wrapper matching the former A.10 row API, with the
radius-decaying far-shell term. -/
theorem exists_sum_gsA10PrimeWindow_log_div_gaussian_beta_bound_farShell :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ y X n Q S : ℕ, ∀ T : ℝ,
        n ∈ gsA10PrimeWindow y X → 3 ≤ Q → Q ≤ y → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 → 1 ≤ T →
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤
          (4 * Real.log (X : ℝ) / n) *
              (32 * ((4 * n : ℕ) : ℝ) / T *
                    gsA10PrimeRowBetaDensity Cβ Q S +
                6 * gsA10PrimeRowBetaDensity Cβ Q S +
                2 * gsA10PrimeRowBetaRemainder Q S) +
            (80 * gsA10PrimeLogHarmonicFactorFourConstant) / T := by
  obtain ⟨Cβ, hCβ, hbeta⟩ :=
    Erdos67b.MRIntervalBetaSieve.exists_card_intervalMissingPrimeBlockSet_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro y X n Q S T hnWindow hQ hQy hS hlog hT
  have hdensity : 0 ≤ gsA10PrimeRowBetaDensity Cβ Q S := by
    unfold gsA10PrimeRowBetaDensity
    exact mul_nonneg (by positivity) (primeBlockDensity_nonneg _)
  have hrem : 0 ≤ gsA10PrimeRowBetaRemainder Q S := by
    unfold gsA10PrimeRowBetaRemainder
    positivity
  have hIz : ∀ q ∈ primesInBlock (3, Q), q ≤ y := by
    intro q hq
    exact (mem_primesInBlock.mp hq).2.2.trans hQy
  have hinterval : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet (3, Q) A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * gsA10PrimeRowBetaDensity Cβ Q S +
          gsA10PrimeRowBetaRemainder Q S) := by
    intro A B hAB
    have h := hbeta A B 3 Q S hAB (by norm_num) hQ hS hlog
    simpa only [gsA10PrimeRowBetaDensity,
      gsA10PrimeRowBetaRemainder] using h
  exact sum_gsA10PrimeWindow_log_div_gaussian_le_of_intervalBeta_farShell
    hT hnWindow hIz hdensity hrem hinterval

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.prime_mem_Ioc_pow_two_shell
#print axioms Erdos67b.MRHalaszBands.sum_gsA10PrimeWindow_log_div_gaussian_le_shell_constant
#print axioms Erdos67b.MRHalaszBands.sum_gsA10PrimeFarWindow_log_div_gaussian_le_shell_constant
#print axioms Erdos67b.MRHalaszBands.sum_gsA10PrimeWindow_log_div_gaussian_le_shell_constant_of_one_le
#print axioms Erdos67b.MRHalaszBands.sum_gsA10PrimeFarWindow_log_div_gaussian_le_shell_constant_of_one_le
#print axioms Erdos67b.MRHalaszBands.sum_gsA10PrimeFarWindow_log_div_gaussian_le_shell_constant_div
#print axioms Erdos67b.MRHalaszBands.sum_gsA10PrimeWindow_log_div_gaussian_le_of_intervalBeta_farShell
#print axioms Erdos67b.MRHalaszBands.exists_sum_gsA10PrimeWindow_log_div_gaussian_beta_bound_farShell

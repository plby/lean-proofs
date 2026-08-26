import ErdosProblems.Erdos4b.SingularSeriesAverage

namespace Erdos4b

open scoped BigOperators

lemma one_sub_pow_linear_remainder_bounds
    (x : ℝ) (n : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (1 - x) ^ n - (1 - (n : ℝ) * x) ∧
      (1 - x) ^ n - (1 - (n : ℝ) * x) ≤ (n : ℝ) ^ 2 * x ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have ha0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
      have ha1 : 1 - x ≤ 1 := by linarith
      let R : ℝ := (1 - x) ^ n - (1 - (n : ℝ) * x)
      have hrec :
          (1 - x) ^ (n + 1) - (1 - ((n + 1 : ℕ) : ℝ) * x) =
            (1 - x) * R + (n : ℝ) * x ^ 2 := by
        dsimp [R]
        rw [pow_succ]
        push_cast
        ring
      rw [hrec]
      constructor
      · exact add_nonneg (mul_nonneg ha0 ih.1)
          (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x))
      · have hmul : (1 - x) * R ≤ R := by
          exact mul_le_of_le_one_left ih.1 ha1
        calc
          (1 - x) * R + (n : ℝ) * x ^ 2 ≤
              R + (n : ℝ) * x ^ 2 :=
            by simpa [add_comm] using
              add_le_add_right hmul ((n : ℝ) * x ^ 2)
          _ ≤ (n : ℝ) ^ 2 * x ^ 2 + (n : ℝ) * x ^ 2 := by
            gcongr
            exact ih.2
          _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * x ^ 2 := by
            push_cast
            have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            nlinarith [sq_nonneg x, mul_nonneg hn0 (sq_nonneg x)]

lemma genericLargeGapLocalFactor_lower
    {K p : ℕ} (hpPrime : p.Prime) (hKp : 4 * K < p) :
    1 - (8 * (K : ℝ) ^ 2) / (p : ℝ) ^ 2 ≤
      genericLargeGapLocalFactor K p := by
  have hp : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  let x : ℝ := 1 / (p : ℝ)
  let n : ℕ := 2 * K
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hpR).2 (by exact_mod_cast hp)
  have hnHalf : (n : ℝ) * x < 1 / 2 := by
    dsimp [n, x]
    rw [show (((2 * K : ℕ) : ℝ) * (1 / (p : ℝ))) =
        (((2 * K : ℕ) : ℝ) / (p : ℝ)) by ring]
    rw [div_lt_iff₀ hpR]
    have hcast : (((4 * K : ℕ) : ℝ)) < p := by exact_mod_cast hKp
    push_cast at hcast ⊢
    linarith
  have hb : 0 < (1 - x) ^ n := by
    have : 0 < 1 - x := by
      rw [sub_pos, div_lt_one hpR]
      exact_mod_cast hpPrime.one_lt
    positivity
  have hrem := one_sub_pow_linear_remainder_bounds x n hx0 hx1
  have hdenHalf : 1 / 2 < (1 - x) ^ n := by
    have hlinear : 1 / 2 < 1 - (n : ℝ) * x := by linarith
    linarith [hrem.1]
  have hform : genericLargeGapLocalFactor K p =
      (1 - (n : ℝ) * x) / ((1 - x) ^ n) := by
    unfold genericLargeGapLocalFactor
    dsimp [n, x]
    rw [inv_pow]
    field_simp
  rw [hform]
  rw [le_div_iff₀ hb]
  have hbound :
      (1 - x) ^ n - (1 - (n : ℝ) * x) ≤
        (8 * (K : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - x) ^ n := by
    have hconst : (n : ℝ) ^ 2 * x ^ 2 =
        4 * (K : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
      dsimp [n, x]
      push_cast
      field_simp
      ring
    have hcoef : 0 ≤ 8 * (K : ℝ) ^ 2 / (p : ℝ) ^ 2 := by positivity
    have hfactor :=
      mul_le_mul_of_nonneg_left hdenHalf.le hcoef
    have hfactor' :
        4 * (K : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤
          (8 * (K : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - x) ^ n := by
      calc
        4 * (K : ℝ) ^ 2 / (p : ℝ) ^ 2 =
            (8 * (K : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 / 2) := by ring
        _ ≤ _ := hfactor
    exact hrem.2.trans (hconst ▸ hfactor')
  linarith

lemma genericLargeGapLocalFactor_pos
    {K p : ℕ} (hpPrime : p.Prime) (hKp : 2 * K < p) :
    0 < genericLargeGapLocalFactor K p := by
  unfold genericLargeGapLocalFactor
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hnum : (0 : ℝ) < 1 - (2 * K : ℕ) / (p : ℝ) := by
    rw [sub_pos, div_lt_one hpR]
    exact_mod_cast hKp
  have hbase : (0 : ℝ) < 1 - (1 : ℝ) / p := by
    rw [sub_pos, div_lt_one hpR]
    exact_mod_cast hpPrime.one_lt
  positivity

lemma genericLargeGapLocalFactor_le_one
    {K p : ℕ} (hpPrime : p.Prime) (_hKp : 2 * K < p) :
    genericLargeGapLocalFactor K p ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  let x : ℝ := 1 / (p : ℝ)
  let n : ℕ := 2 * K
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hpR).2 (by exact_mod_cast hpPrime.pos)
  have hb : 0 < (1 - x) ^ n := by
    have : 0 < 1 - x := by
      rw [sub_pos, div_lt_one hpR]
      exact_mod_cast hpPrime.one_lt
    positivity
  have hrem := one_sub_pow_linear_remainder_bounds x n hx0 hx1
  have hform : genericLargeGapLocalFactor K p =
      (1 - (n : ℝ) * x) / ((1 - x) ^ n) := by
    unfold genericLargeGapLocalFactor
    dsimp [n, x]
    rw [inv_pow]
    field_simp
  rw [hform, div_le_one hb]
  linarith [hrem.1]

lemma sum_roughPrimeSupport_one_div_sq_le
    {w y : ℕ} (hw : 0 < w) :
    (∑ p ∈ BoundedGaps.Maynard.roughPrimeSupport w y,
        (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 / (w : ℝ) := by
  classical
  by_cases hwy : w < y
  · have hsub :
        BoundedGaps.Maynard.roughPrimeSupport w y ⊆
          Finset.Ico (w + 1) (y + 1) := by
      intro p hp
      have hpIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_Ico.mpr ⟨hpIcc.1, by omega⟩
    calc
      (∑ p ∈ BoundedGaps.Maynard.roughPrimeSupport w y,
          (1 : ℝ) / (p : ℝ) ^ 2) ≤
          ∑ p ∈ Finset.Ico (w + 1) (y + 1),
            (1 : ℝ) / (p : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp hpNot
        positivity
      _ ≤ 2 / ((w : ℝ) + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (BoundedGaps.Maynard.sum_Ico_one_div_nat_sq_le
            (D := w + 1) (Q := y + 1) (by omega) (by omega))
      _ ≤ 2 / (w : ℝ) := by
        have hwR : (0 : ℝ) < w := by exact_mod_cast hw
        exact div_le_div_of_nonneg_left (by norm_num) hwR (by norm_num)
  · have hempty :
        BoundedGaps.Maynard.roughPrimeSupport w y = ∅ := by
      rw [BoundedGaps.Maynard.roughPrimeSupport]
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp
      have hpIcc := Finset.mem_Icc.mp hp
      omega
    simp [hempty]
    positivity

lemma genericRoughSingularProduct_lower
    {K w y : ℕ} (hfour : 4 * K ≤ w) (hw : 0 < w) :
    1 - 16 * (K : ℝ) ^ 2 / (w : ℝ) ≤
      genericRoughSingularProduct K w y := by
  let S := BoundedGaps.Maynard.roughPrimeSupport w y
  let loss : ℕ → ℝ := fun p =>
    8 * (K : ℝ) ^ 2 / (p : ℝ) ^ 2
  have hloss0 : ∀ p ∈ S, 0 ≤ loss p := by
    intro p hp
    dsimp [loss]
    positivity
  have hloss1 : ∀ p ∈ S, loss p ≤ 1 := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpIcc := Finset.mem_Icc.mp hpData.1
    have hKp : 4 * K < p := hfour.trans_lt hpIcc.1
    by_cases hK0 : K = 0
    · simp [loss, hK0]
    · have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpData.2.pos
      have hcast : (4 : ℝ) * K < p := by exact_mod_cast hKp
      dsimp [loss]
      rw [div_le_one (sq_pos_of_pos hpR)]
      nlinarith [sq_nonneg ((p : ℝ) - 4 * K)]
  have hlocal : ∀ p ∈ S,
      1 - loss p ≤ genericLargeGapLocalFactor K p := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpIcc := Finset.mem_Icc.mp hpData.1
    exact genericLargeGapLocalFactor_lower hpData.2
      (hfour.trans_lt hpIcc.1)
  have hprod :
      ∏ p ∈ S, (1 - loss p) ≤
        ∏ p ∈ S, genericLargeGapLocalFactor K p := by
    apply Finset.prod_le_prod
    · intro p hp
      exact sub_nonneg.mpr (hloss1 p hp)
    · intro p hp
      exact hlocal p hp
  have hbon :
      1 - ∑ p ∈ S, loss p ≤ ∏ p ∈ S, (1 - loss p) :=
    one_sub_sum_le_prod_one_sub S loss hloss0 hloss1
  have hsum :
      (∑ p ∈ S, loss p) ≤ 16 * (K : ℝ) ^ 2 / (w : ℝ) := by
    calc
      (∑ p ∈ S, loss p) =
          8 * (K : ℝ) ^ 2 *
            (∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2) := by
        unfold loss
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ 8 * (K : ℝ) ^ 2 * (2 / (w : ℝ)) := by
        gcongr
        exact sum_roughPrimeSupport_one_div_sq_le hw
      _ = 16 * (K : ℝ) ^ 2 / (w : ℝ) := by ring
  calc
    1 - 16 * (K : ℝ) ^ 2 / (w : ℝ) ≤
        1 - ∑ p ∈ S, loss p := sub_le_sub_left hsum _
    _ ≤ ∏ p ∈ S, (1 - loss p) := hbon
    _ ≤ ∏ p ∈ S, genericLargeGapLocalFactor K p := hprod
    _ = genericRoughSingularProduct K w y := by
      rfl

lemma genericRoughSingularProduct_pos
    {K w y : ℕ} (hfour : 4 * K ≤ w) :
    0 < genericRoughSingularProduct K w y := by
  unfold genericRoughSingularProduct
  apply Finset.prod_pos
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpIcc := Finset.mem_Icc.mp hpData.1
  exact genericLargeGapLocalFactor_pos hpData.2 (by omega)

lemma genericRoughSingularProduct_le_one
    {K w y : ℕ} (hfour : 4 * K ≤ w) :
    genericRoughSingularProduct K w y ≤ 1 := by
  unfold genericRoughSingularProduct
  calc
    (∏ p ∈ BoundedGaps.Maynard.roughPrimeSupport w y,
        genericLargeGapLocalFactor K p) ≤
        ∏ _p ∈ BoundedGaps.Maynard.roughPrimeSupport w y, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact (genericLargeGapLocalFactor_pos
          (Finset.mem_filter.mp hp).2 (by
            have hpIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
            omega)).le
      · intro p hp
        exact genericLargeGapLocalFactor_le_one
          (Finset.mem_filter.mp hp).2 (by
            have hpIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
            omega)
    _ = 1 := by simp

/-- The reciprocal large-gap singular series has, on average over the
auxiliary prime, the exact lower bound needed in the fibre-covering
argument.  The denominator on the left is independent of `q`: it is the
small-prime pre-sieve factor times the universal rough-prime factor. -/
theorem sum_inv_largeGapSingularSeries_primeInterval_lower
    {theta exponent C : ℝ} {X₀ K w A B m y : ℕ}
    (hlevel : BoundedGaps.Maynard.PrimeLevelWitness
      theta exponent C X₀)
    (hK : 0 < K) (hfour : 4 * K ≤ w) (hw : 0 < w) (hwy : w ≤ y)
    (hyA : y < A) (hA : 0 < A) (hAB : A ≤ B) (hm : Even m)
    (hBthreshold : X₀ ≤ B - 1) (hAthreshold : X₀ ≤ A - 1)
    (hyBcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (B - 1))
    (hyAcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (A - 1)) :
    fixedSingularInverseFactor K w y m *
          (((auxiliaryPrimeInterval A B).card : ℝ) -
            singularAverageLossBound K w A B C exponent) /
        (largeGapSingularSeries (preSievedShifts K w) m 1 w *
          genericRoughSingularProduct K w y) ≤
      ∑ q ∈ auxiliaryPrimeInterval A B,
        (1 : ℝ) /
          largeGapSingularSeries (preSievedShifts K w) m q y := by
  let U : ℝ :=
    largeGapSingularSeries (preSievedShifts K w) m 1 w *
      genericRoughSingularProduct K w y
  have hsmallIndependent : ∀ q : ℕ,
      largeGapSingularSeries (preSievedShifts K w) m q w =
        largeGapSingularSeries (preSievedShifts K w) m 1 w := by
    intro q
    rw [largeGapSingularSeries_preSieveCutoff hK,
      largeGapSingularSeries_preSieveCutoff hK]
  have hU : 0 < U := mul_pos
    (largeGapSingularSeries_preSievedShifts_pos
      (m := m) (q := 1) (y := w) (by omega) hm)
    (genericRoughSingularProduct_pos hfour)
  have havg :=
    sum_universal_div_largeGapSingularSeries_primeInterval_lower
      hlevel hfour hw hwy hyA hA hAB hm hBthreshold hAthreshold
        hyBcut hyAcut
  apply (div_le_iff₀ hU).2
  calc
    fixedSingularInverseFactor K w y m *
          (((auxiliaryPrimeInterval A B).card : ℝ) -
            singularAverageLossBound K w A B C exponent) ≤
        ∑ q ∈ auxiliaryPrimeInterval A B,
          (largeGapSingularSeries (preSievedShifts K w) m q w *
              genericRoughSingularProduct K w y) /
            largeGapSingularSeries (preSievedShifts K w) m q y := havg
    _ = U * ∑ q ∈ auxiliaryPrimeInterval A B,
          (1 : ℝ) /
            largeGapSingularSeries (preSievedShifts K w) m q y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [hsmallIndependent q]
      dsimp [U]
      ring
    _ = (∑ q ∈ auxiliaryPrimeInterval A B,
          (1 : ℝ) /
            largeGapSingularSeries (preSievedShifts K w) m q y) * U := by
      ring

/-- A convenient absolute lower bound for the universal rough Euler factor.
The deliberately generous cutoff `32 * K^2` leaves a factor `1/2`. -/
lemma one_half_le_genericRoughSingularProduct
    {K w y : ℕ} (hK : 0 < K) (hstrong : 32 * K ^ 2 ≤ w) :
    (1 / 2 : ℝ) ≤ genericRoughSingularProduct K w y := by
  have hfour : 4 * K ≤ w := by
    have hKle : K ≤ K ^ 2 := by
      nlinarith
    omega
  have hw : 0 < w := by omega
  have hlower := genericRoughSingularProduct_lower
    (K := K) (y := y) hfour hw
  calc
    (1 / 2 : ℝ) ≤ 1 - 16 * (K : ℝ) ^ 2 / (w : ℝ) := by
      have hwR : (0 : ℝ) < w := by exact_mod_cast hw
      have hstrongR : (32 : ℝ) * (K : ℝ) ^ 2 ≤ w := by
        exact_mod_cast hstrong
      have hdiv : 16 * (K : ℝ) ^ 2 / (w : ℝ) ≤ 1 / 2 := by
        apply (div_le_iff₀ hwR).2
        nlinarith
      linarith
    _ ≤ genericRoughSingularProduct K w y := hlower

/-- If the explicit average loss is smaller than the number of auxiliary
primes, the universal rough factor can be discarded from the denominator.
What remains is the small pre-sieve singular series and the fixed factor
from primes dividing `m`. -/
theorem sum_inv_largeGapSingularSeries_primeInterval_lower_small
    {theta exponent C : ℝ} {X₀ K w A B m y : ℕ}
    (hlevel : BoundedGaps.Maynard.PrimeLevelWitness
      theta exponent C X₀)
    (hK : 0 < K) (hfour : 4 * K ≤ w) (hw : 0 < w) (hwy : w ≤ y)
    (hyA : y < A) (hA : 0 < A) (hAB : A ≤ B) (hm : Even m)
    (hBthreshold : X₀ ≤ B - 1) (hAthreshold : X₀ ≤ A - 1)
    (hyBcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (B - 1))
    (hyAcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (A - 1))
    (hloss : singularAverageLossBound K w A B C exponent ≤
      ((auxiliaryPrimeInterval A B).card : ℝ)) :
    fixedSingularInverseFactor K w y m *
          (((auxiliaryPrimeInterval A B).card : ℝ) -
            singularAverageLossBound K w A B C exponent) /
        largeGapSingularSeries (preSievedShifts K w) m 1 w ≤
      ∑ q ∈ auxiliaryPrimeInterval A B,
        (1 : ℝ) /
          largeGapSingularSeries (preSievedShifts K w) m q y := by
  have hsmall : 0 < largeGapSingularSeries
      (preSievedShifts K w) m 1 w :=
    largeGapSingularSeries_preSievedShifts_pos
      (m := m) (q := 1) (y := w) (by omega) hm
  have hgenericPos : 0 < genericRoughSingularProduct K w y :=
    genericRoughSingularProduct_pos hfour
  have hgenericLe : genericRoughSingularProduct K w y ≤ 1 :=
    genericRoughSingularProduct_le_one hfour
  have hnum : 0 ≤ fixedSingularInverseFactor K w y m *
      (((auxiliaryPrimeInterval A B).card : ℝ) -
        singularAverageLossBound K w A B C exponent) := by
    exact mul_nonneg (fixedSingularInverseFactor_pos hfour hw).le
      (sub_nonneg.mpr hloss)
  apply le_trans ?_ (sum_inv_largeGapSingularSeries_primeInterval_lower
    hlevel hK hfour hw hwy hyA hA hAB hm hBthreshold hAthreshold
      hyBcut hyAcut)
  apply div_le_div_of_nonneg_left hnum
  · exact mul_pos hsmall hgenericPos
  · nlinarith [mul_le_mul_of_nonneg_left hgenericLe hsmall.le]

end Erdos4b

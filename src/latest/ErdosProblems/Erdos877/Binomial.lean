import ErdosProblems.Erdos877.Core

open scoped BigOperators

namespace Erdos877

variable {α : Type*}

/-- The number of `k`-element subsets of a finite set is the corresponding
binomial coefficient. -/
theorem powersetCard_card (L : Finset α) (k : ℕ) :
    (L.powersetCard k).card = L.card.choose k := by
  exact Finset.card_powersetCard _ _

/-- The family of subsets of `L` having cardinality at most `r`. -/
def subsetsUpTo [DecidableEq α] (L : Finset α) (r : ℕ) : Finset (Finset α) :=
  L.powerset.filter fun A => A.card ≤ r

@[simp]
theorem mem_subsetsUpTo [DecidableEq α] {L A : Finset α} {r : ℕ} :
    A ∈ subsetsUpTo L r ↔ A ⊆ L ∧ A.card ≤ r := by
  simp [subsetsUpTo]

/-- Exact cardinality of a lower layer of the Boolean lattice. -/
theorem card_subsetsUpTo_eq_sum_choose [DecidableEq α] (L : Finset α) (r : ℕ) :
    (subsetsUpTo L r).card = ∑ i ∈ Finset.range (r + 1), L.card.choose i := by
  classical
  rw [show subsetsUpTo L r =
      Finset.biUnion (Finset.range (r + 1)) (fun i ↦ L.powersetCard i) by
        ext A
        simp only [mem_subsetsUpTo, Finset.mem_biUnion, Finset.mem_range,
          Finset.mem_powersetCard]
        constructor
        · rintro ⟨hAL, hAr⟩
          exact ⟨A.card, Nat.lt_succ_of_le hAr, hAL, rfl⟩
        · rintro ⟨i, hi, hAL, hAi⟩
          exact ⟨hAL, hAi.symm ▸ Nat.le_of_lt_succ hi⟩,
    Finset.card_biUnion]
  · simp [Finset.card_powersetCard]
  · intro i hi j hj hij
    exact Finset.disjoint_left.mpr fun A hAi hAj ↦ hij <| by
      have hiA := (Finset.mem_powersetCard.mp hAi).2
      have hjA := (Finset.mem_powersetCard.mp hAj).2
      omega

/-- A weighted lower-layer estimate. Multiplying by `x^r` lets every set in
the lower layer be compared with its natural binomial weight. -/
theorem card_subsetsUpTo_mul_pow_le [DecidableEq α] (L : Finset α) (r : ℕ)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((subsetsUpTo L r).card : ℝ) * x ^ r ≤ (1 + x) ^ L.card := by
  calc
    ((subsetsUpTo L r).card : ℝ) * x ^ r =
        ∑ A ∈ subsetsUpTo L r, x ^ r := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ A ∈ subsetsUpTo L r, x ^ A.card := by
      apply Finset.sum_le_sum
      intro A hA
      exact pow_le_pow_of_le_one hx0 hx1 (mem_subsetsUpTo.mp hA).2
    _ ≤ ∑ A ∈ L.powerset, x ^ A.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro A hA
        exact Finset.mem_powerset.mpr (mem_subsetsUpTo.mp hA).1
      · intro A hA hnot
        positivity
    _ = (1 + x) ^ L.card := by
      simpa [add_comm] using Finset.sum_pow_mul_eq_add_pow x 1 L

/-- The sum of the first `n/10` binomial coefficients, after multiplication
by `(1/8)^(n/10)`, is at most `(9/8)^n`. -/
theorem partialChooseSum_div_ten_mul_eighth_pow_le (n : ℕ) :
    ((∑ i ∈ Finset.range (n / 10 + 1), n.choose i : ℕ) : ℝ) *
        (1 / 8 : ℝ) ^ (n / 10) ≤ (9 / 8 : ℝ) ^ n := by
  let L : Finset (Fin n) := Finset.univ
  have h := card_subsetsUpTo_mul_pow_le L (n / 10)
    (x := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
  have hbase : (1 : ℝ) + 1 / 8 = 9 / 8 := by norm_num
  rw [hbase] at h
  simpa [L, card_subsetsUpTo_eq_sum_choose] using h

/-- A concrete entropy-free estimate for the small binomial tail. The base
`7/5` is strictly smaller than `sqrt 2`. -/
theorem partialChooseSum_div_ten_le_seven_fifths_pow (n : ℕ) :
    ((∑ i ∈ Finset.range (n / 10 + 1), n.choose i : ℕ) : ℝ) ≤
        (7 / 5 : ℝ) ^ n := by
  let S : ℝ := ((∑ i ∈ Finset.range (n / 10 + 1), n.choose i : ℕ) : ℝ)
  have hweighted : S * (1 / 8 : ℝ) ^ (n / 10) ≤ (9 / 8 : ℝ) ^ n := by
    simpa [S] using partialChooseSum_div_ten_mul_eighth_pow_le n
  have hspos : 0 < (1 / 8 : ℝ) ^ (n / 10) := by positivity
  have hcancel : S ≤ (8 : ℝ) ^ (n / 10) * (9 / 8 : ℝ) ^ n := by
    calc
      S ≤ (9 / 8 : ℝ) ^ n / (1 / 8 : ℝ) ^ (n / 10) :=
        (le_div_iff₀ hspos).2 hweighted
      _ = (8 : ℝ) ^ (n / 10) * (9 / 8 : ℝ) ^ n := by
        have hinv : ((1 / 8 : ℝ) ^ (n / 10))⁻¹ = 8 ^ (n / 10) := by
          rw [← inv_pow]
          norm_num
        rw [div_eq_mul_inv, hinv, mul_comm]
  have hbase : (8 : ℝ) ≤ (56 / 45 : ℝ) ^ 10 := by norm_num
  have hpow : (8 : ℝ) ^ (n / 10) ≤ (56 / 45 : ℝ) ^ n := by
    calc
      (8 : ℝ) ^ (n / 10) ≤ ((56 / 45 : ℝ) ^ 10) ^ (n / 10) :=
        pow_le_pow_left₀ (by positivity) hbase _
      _ = (56 / 45 : ℝ) ^ (10 * (n / 10)) := by rw [pow_mul]
      _ ≤ (56 / 45 : ℝ) ^ n := by
        apply pow_le_pow_right₀ (by norm_num)
        simpa [mul_comm] using Nat.div_mul_le_self n 10
  calc
    S ≤ (8 : ℝ) ^ (n / 10) * (9 / 8 : ℝ) ^ n := hcancel
    _ ≤ (56 / 45 : ℝ) ^ n * (9 / 8 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (7 / 5 : ℝ) ^ n := by rw [← mul_pow]; norm_num

/-- Boolean-lattice form of the concrete small-tail estimate. -/
theorem card_subsetsUpTo_div_ten_le_seven_fifths_pow [DecidableEq α]
    (L : Finset α) :
    ((subsetsUpTo L (L.card / 10)).card : ℝ) ≤ (7 / 5 : ℝ) ^ L.card := by
  rw [card_subsetsUpTo_eq_sum_choose]
  exact partialChooseSum_div_ten_le_seven_fifths_pow L.card

/-- The explicit base in the preceding estimate is below the benchmark base. -/
theorem seven_fifths_lt_sqrt_two : (7 / 5 : ℝ) < Real.sqrt 2 := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  nlinarith

/-- A convenient fixed-denominator lower bound for a binomial slice.  This is
the direct consequence of Mathlib's factorial lower bound for `choose`; it is
within one unit of the sharper base `D` bound. -/
theorem pred_pow_div_le_choose (m D : ℕ) (hD : 1 ≤ D) :
    (D - 1) ^ (m / D) ≤ m.choose (m / D) := by
  let k := m / D
  have hkD : k * D ≤ m := by
    simpa [k] using Nat.div_mul_le_self m D
  have hDk : D * k ≤ m := by simpa [mul_comm] using hkD
  have hsum : (D - 1) * k + k ≤ m := by
    calc
      (D - 1) * k + k = ((D - 1) + 1) * k := by rw [add_mul, one_mul]
      _ = D * k := by rw [Nat.sub_add_cancel hD]
      _ ≤ m := hDk
  have hnum : (D - 1) * k ≤ m + 1 - k := by
    apply Nat.le_sub_of_add_le
    exact hsum.trans (Nat.le_succ m)
  have hpowNat : ((D - 1) * k) ^ k ≤ (m + 1 - k) ^ k :=
    Nat.pow_le_pow_left hnum k
  have hfac : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
  have hmulfac : (D - 1) ^ k * k.factorial ≤ (m + 1 - k) ^ k := by
    calc
      (D - 1) ^ k * k.factorial ≤ (D - 1) ^ k * k ^ k :=
        Nat.mul_le_mul_left _ hfac
      _ = ((D - 1) * k) ^ k := by rw [mul_pow]
      _ ≤ (m + 1 - k) ^ k := hpowNat
  have hraw : (((m + 1 - k : ℕ) ^ k : ℚ) / k.factorial) ≤ m.choose k :=
    Nat.pow_le_choose k m
  have hleft : ((D - 1 : ℕ) ^ k : ℚ) ≤
      (((m + 1 - k : ℕ) ^ k : ℚ) / k.factorial) := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < k.factorial)).2
    exact_mod_cast hmulfac
  have hq : ((D - 1 : ℕ) ^ k : ℚ) ≤ m.choose k := hleft.trans hraw
  exact_mod_cast hq

/-- Finset-cardinality form of `pred_pow_div_le_choose`. -/
theorem pred_pow_div_le_powersetCard_card (L : Finset α) (D : ℕ)
    (hD : 1 ≤ D) :
    (D - 1) ^ (L.card / D) ≤ (L.powersetCard (L.card / D)).card := by
  rw [powersetCard_card]
  exact pred_pow_div_le_choose L.card D hD

/-- A fully numerical fixed-proportion slice bound used by the deletion
double count.  Its base is `2^21`; the harmless `+1` in the denominator is
the price of deriving the estimate directly from Mathlib's factorial bound. -/
theorem two_pow_twenty_one_pow_div_succ_le_choose (m : ℕ) :
    (2 ^ 21) ^ (m / (2 ^ 21 + 1)) ≤ m.choose (m / (2 ^ 21 + 1)) := by
  simpa only [Nat.succ_sub_one, Nat.succ_eq_add_one] using
    pred_pow_div_le_choose m (Nat.succ (2 ^ 21))
      (Nat.succ_le_succ (Nat.zero_le _))

end Erdos877

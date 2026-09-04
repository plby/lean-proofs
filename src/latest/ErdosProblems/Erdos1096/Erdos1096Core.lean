import Mathlib

/-!
# Erdős Problem 1096: combinatorial and analytic core

The increasing enumeration of the finite binary spectrum in every sufficiently
small base greater than one has successive gaps tending to zero.

The mathematical proof and a detailed Leanization guide are in `tex/1096.tex`.
-/

open Filter Set
open scoped BigOperators Pointwise Topology

namespace Erdos1096

noncomputable section

/-- Finite sums of distinct nonnegative powers of `q`. -/
def Spectrum (q : ℝ) : Set ℝ :=
  {a | ∃ S : Finset ℕ, a = ∑ i ∈ S, q ^ i}

/-- Every sufficiently large interval immediately to the right of its left
endpoint contains a member of `A`, with arbitrary prescribed length. -/
def EventuallyRightDense (A : Set ℝ) : Prop :=
  ∀ η > 0, ∃ B : ℝ, ∀ t, B ≤ t → ∃ a ∈ A, t < a ∧ a < t + η

/-- `U` contains finite increasing chains of arbitrarily small mesh and
arbitrarily large span. -/
def HasFineChains (U : Set ℝ) : Prop :=
  ∀ η > 0, ∀ D > 0, ∃ n : ℕ, ∃ u : ℕ → ℝ,
    (∀ k ≤ n, u k ∈ U) ∧
    (∀ k < n, u k < u (k + 1) ∧ u (k + 1) - u k < η) ∧
    D < u n - u 0

/-- Far enough out, every point has a member of `V` at most `D` to its
left.  This is the form of bounded coarse gaps used in the sumset argument. -/
def EventuallyLeftDense (V : Set ℝ) (D : ℝ) : Prop :=
  ∃ B : ℝ, ∀ t, B ≤ t → ∃ v ∈ V, t - D < v ∧ v ≤ t

/-- Pointwise multiplication of a real set by a positive scale. -/
def scaleSet (c : ℝ) (A : Set ℝ) : Set ℝ := (fun a ↦ c * a) '' A

/-- Arbitrarily small positive signed binary sums, with their positive and
negative supports already cancelled. -/
def SmallDisjointDifferences (r : ℝ) : Prop :=
  ∀ ε > 0, ∃ A B : Finset ℕ, Disjoint A B ∧
    0 < (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i ∧
    (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i < ε

/-- Zero is approached by nonzero differences of finite binary sums. -/
def SmallSpectrumDifferences (r : ℝ) : Prop :=
  ∀ ε > 0, ∃ A B : Finset ℕ,
    0 < |(∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i| ∧
    |(∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i| < ε

/-! ### The finite collision dichotomy -/

private def supportPolynomial (S : Finset ℕ) : Polynomial ℤ :=
  ∑ i ∈ S, Polynomial.X ^ i

private lemma eval₂_supportPolynomial (q : ℝ) (S : Finset ℕ) :
    (supportPolynomial S).eval₂ (algebraMap ℤ ℝ) q = ∑ i ∈ S, q ^ i := by
  rw [supportPolynomial, Polynomial.eval₂_finsetSum]
  simp

private lemma supportPolynomial_natDegree_le {S : Finset ℕ} {d : ℕ}
    (hS : ∀ i ∈ S, i ≤ d) : (supportPolynomial S).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [supportPolynomial, ← Polynomial.lcoeff_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hiD := hS i hi
  have hNi : N ≠ i := by omega
  simp [Polynomial.coeff_X_pow, hNi]

/-- Orienting the largest exponent of two disjoint supports makes their signed
support polynomial monic. -/
private lemma supportPolynomial_sub_monic {P N : Finset ℕ} {d : ℕ}
    (hPN : Disjoint P N) (hdP : d ∈ P)
    (hmax : ∀ i ∈ P ∪ N, i ≤ d) :
    (supportPolynomial P - supportPolynomial N).Monic := by
  have hdN : d ∉ N := Finset.disjoint_left.mp hPN hdP
  have hP : ∀ i ∈ P, i ≤ d :=
    fun i hi ↦ hmax i (Finset.mem_union_left N hi)
  have hN : ∀ i ∈ N, i ≤ d :=
    fun i hi ↦ hmax i (Finset.mem_union_right P hi)
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one d
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (supportPolynomial_natDegree_le hP) (supportPolynomial_natDegree_le hN))
  · simp [supportPolynomial, hdP, hdN]

/-- An exact collision between two distinct binary power sums gives an
explicit monic integer polynomial having the base as a root. -/
lemma isIntegral_of_powerSum_eq {q : ℝ} {A B : Finset ℕ} (hAB : A ≠ B)
    (hsum : (∑ i ∈ A, q ^ i) = ∑ i ∈ B, q ^ i) : IsIntegral ℤ q := by
  let P := A \ B
  let N := B \ A
  let U := P ∪ N
  have hPN : Disjoint P N := by
    dsimp [P, N]
    exact disjoint_sdiff_sdiff
  have hU : U.Nonempty := by
    by_contra hne
    have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    apply hAB
    apply Finset.Subset.antisymm
    · intro i hiA
      by_contra hiB
      have hiP : i ∈ P := by simpa [P] using And.intro hiA hiB
      have hiU : i ∈ U := Finset.mem_union_left N hiP
      rw [hUempty] at hiU
      simp at hiU
    · intro i hiB
      by_contra hiA
      have hiN : i ∈ N := by simpa [N] using And.intro hiB hiA
      have hiU : i ∈ U := Finset.mem_union_right P hiN
      rw [hUempty] at hiU
      simp at hiU
  let d := U.max' hU
  have hdU : d ∈ U := Finset.max'_mem U hU
  have hmax : ∀ i ∈ P ∪ N, i ≤ d := by
    intro i hi
    exact Finset.le_max' U i hi
  have hdiff : (∑ i ∈ P, q ^ i) - ∑ i ∈ N, q ^ i = 0 := by
    dsimp [P, N]
    rw [Finset.sum_sdiff_sub_sum_sdiff]
    linarith
  rcases Finset.mem_union.mp hdU with hdP | hdN
  · refine ⟨supportPolynomial P - supportPolynomial N,
      supportPolynomial_sub_monic hPN hdP hmax, ?_⟩
    rw [Polynomial.eval₂_sub, eval₂_supportPolynomial, eval₂_supportPolynomial]
    exact hdiff
  · refine ⟨supportPolynomial N - supportPolynomial P,
      supportPolynomial_sub_monic hPN.symm hdN (by simpa [Finset.union_comm] using hmax), ?_⟩
    have : (∑ i ∈ N, q ^ i) - ∑ i ∈ P, q ^ i = 0 := by linarith
    rw [Polynomial.eval₂_sub, eval₂_supportPolynomial, eval₂_supportPolynomial]
    exact this

private lemma exists_geometric_packing_scale {q ε : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (hε : 0 < ε) :
    ∃ n : ℕ, q ^ n / (q - 1) < ε * ((2 : ℝ) ^ n - 1) := by
  have hc0 : 0 ≤ q / 2 := by positivity
  have hc1 : q / 2 < 1 := by linarith
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
  have htarget : 0 < ε * (q - 1) / 2 := by positivity
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht (ε * (q - 1) / 2) htarget
  let n := N + 1
  have hnN : N ≤ n := by dsimp [n]; omega
  have hsmall : (q / 2) ^ n < ε * (q - 1) / 2 := by
    have := hN n hnN
    simpa [Real.dist_eq, abs_of_pos (by linarith : 0 < q)] using this
  have htwo_pos : 0 < (2 : ℝ) ^ n := by positivity
  have htwo : 2 ≤ (2 : ℝ) ^ n := by
    dsimp [n]
    rw [pow_succ]
    have hone : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    nlinarith
  have hratio : q ^ n / (2 : ℝ) ^ n < ε * (q - 1) / 2 := by
    simpa [div_pow] using hsmall
  have hqpow : q ^ n < (ε * (q - 1) / 2) * (2 : ℝ) ^ n :=
    (div_lt_iff₀ htwo_pos).mp hratio
  have hqden : 0 < q - 1 := by linarith
  apply Exists.intro n
  apply (div_lt_iff₀ hqden).mpr
  nlinarith

/-- For a nonintegral base below two, the elementary powerset pigeonhole
argument already gives arbitrarily small nonzero signed binary sums. -/
lemma smallSpectrumDifferences_of_not_isIntegral {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (hq_nonintegral : ¬ IsIntegral ℤ q) : SmallSpectrumDifferences q := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_geometric_packing_scale hq1 hq2 hε
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    norm_num at hn
    have hden : 0 < q - 1 := by linarith
    have hone : 0 < 1 / (q - 1) := one_div_pos.mpr hden
    linarith
  let K : ℕ := 2 ^ n - 1
  let F : Finset (Finset ℕ) := (Finset.range n).powerset
  let bin : Finset ℕ → ℕ := fun S ↦ ⌊(∑ i ∈ S, q ^ i) / ε⌋₊
  have hpow_one : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  have hcastK : (K : ℝ) = (2 : ℝ) ^ n - 1 := by
    dsimp [K]
    rw [Nat.cast_sub hpow_one]
    norm_num
  have hq0 : 0 ≤ q := by linarith
  have hqden : 0 < q - 1 := by linarith
  have hmaps : Set.MapsTo bin (F : Set (Finset ℕ)) (Finset.range K : Set ℕ) := by
    intro S hSF
    have hS : S ⊆ Finset.range n := Finset.mem_powerset.mp hSF
    have hsum0 : 0 ≤ ∑ i ∈ S, q ^ i := by positivity
    have hsum_le : (∑ i ∈ S, q ^ i) ≤ ∑ i ∈ Finset.range n, q ^ i :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (by
        intro i hi hiS
        positivity)
    have hfull_lt : (∑ i ∈ Finset.range n, q ^ i) < q ^ n / (q - 1) := by
      rw [geom_sum_eq (by linarith)]
      calc
        (q ^ n - 1) / (q - 1) = q ^ n / (q - 1) - 1 / (q - 1) := by ring
        _ < q ^ n / (q - 1) := by
          have hinv : 0 < 1 / (q - 1) := one_div_pos.mpr hqden
          linarith
    have hsum_lt : (∑ i ∈ S, q ^ i) < ε * ((2 : ℝ) ^ n - 1) :=
      lt_of_le_of_lt hsum_le (hfull_lt.trans hn)
    change bin S ∈ Finset.range K
    rw [Finset.mem_range]
    apply (Nat.floor_lt (div_nonneg hsum0 hε.le)).mpr
    rw [hcastK]
    exact (div_lt_iff₀ hε).mpr (by nlinarith)
  have hcard : (Finset.range K).card < F.card := by
    have hpowpos : 0 < 2 ^ n := pow_pos (by omega) n
    simp only [Finset.card_range, F, Finset.card_powerset, Finset.card_range]
    dsimp [K]
    omega
  obtain ⟨A, hAF, B, hBF, hAB, hbin⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  let a : ℝ := ∑ i ∈ A, q ^ i
  let b : ℝ := ∑ i ∈ B, q ^ i
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hfloor : ⌊a / ε⌋₊ = ⌊b / ε⌋₊ := by simpa [bin, a, b] using hbin
  let k : ℕ := ⌊a / ε⌋₊
  have halo : (k : ℝ) ≤ a / ε := by
    dsimp [k]
    exact Nat.floor_le (div_nonneg ha0 hε.le)
  have hahi : a / ε < (k : ℝ) + 1 := by
    dsimp [k]
    exact Nat.lt_floor_add_one (a / ε)
  have hblo : (k : ℝ) ≤ b / ε := by
    rw [show k = ⌊b / ε⌋₊ by exact hfloor]
    exact Nat.floor_le (div_nonneg hb0 hε.le)
  have hbhi : b / ε < (k : ℝ) + 1 := by
    rw [show k = ⌊b / ε⌋₊ by exact hfloor]
    exact Nat.lt_floor_add_one (b / ε)
  have hab_ne : b - a ≠ 0 := by
    intro hz
    have hab : a = b := by linarith
    apply hq_nonintegral
    apply isIntegral_of_powerSum_eq hAB
    simpa [a, b] using hab
  have hba_div : (b - a) / ε < 1 := by
    rw [sub_div]
    linarith
  have hab_div : (a - b) / ε < 1 := by
    rw [sub_div]
    linarith
  have hba_lt : b - a < ε := by
    have := (div_lt_iff₀ hε).mp hba_div
    nlinarith
  have hab_lt : a - b < ε := by
    have := (div_lt_iff₀ hε).mp hab_div
    nlinarith
  refine ⟨A, B, ?_, ?_⟩
  · dsimp [a, b] at hab_ne ⊢
    exact abs_pos.mpr hab_ne
  · dsimp [a, b] at hba_lt hab_lt ⊢
    rw [abs_lt]
    constructor <;> linarith

/-! ### The lazy binary-expansion engine -/

private def binaryRemainder (q x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if binaryRemainder q x n ≤ (q⁻¹) ^ (n + 1) / (q - 1) then
        binaryRemainder q x n
      else
        binaryRemainder q x n - (q⁻¹) ^ (n + 1)

private def binaryDigit (q x : ℝ) (n : ℕ) : ℕ :=
  if binaryRemainder q x n ≤ (q⁻¹) ^ (n + 1) / (q - 1) then 0 else 1

private lemma binaryDigit_eq_zero_or_one (q x : ℝ) (n : ℕ) :
    binaryDigit q x n = 0 ∨ binaryDigit q x n = 1 := by
  unfold binaryDigit
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma binaryRemainder_succ (q x : ℝ) (n : ℕ) :
    binaryRemainder q x (n + 1) = binaryRemainder q x n -
      (binaryDigit q x n : ℝ) * (q⁻¹) ^ (n + 1) := by
  simp only [binaryRemainder, binaryDigit]
  split_ifs <;> simp

private lemma inverse_geometric_step {q : ℝ} (hq : 1 < q) (n : ℕ) :
    (q⁻¹) ^ n / (q - 1) - (q⁻¹) ^ (n + 1) =
      (q⁻¹) ^ (n + 1) / (q - 1) := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hqm1 : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  rw [pow_succ]
  field_simp
  ring

private lemma binaryRemainder_bounds {q x : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (q - 1)) (n : ℕ) :
    0 ≤ binaryRemainder q x n ∧
      binaryRemainder q x n ≤ (q⁻¹) ^ n / (q - 1) := by
  induction n with
  | zero => simpa [binaryRemainder] using And.intro hx0 hx1
  | succ n ih =>
      have hden : 0 < q - 1 := sub_pos.mpr hq1
      have hpow : 0 ≤ (q⁻¹) ^ (n + 1) := pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one hq1.le)) _
      have hweight_le : (q⁻¹) ^ (n + 1) ≤ (q⁻¹) ^ (n + 1) / (q - 1) := by
        rw [le_div_iff₀ hden]
        nlinarith
      rw [binaryRemainder]
      split_ifs with hsmall
      · exact ⟨ih.1, hsmall⟩
      · have hlarge : (q⁻¹) ^ (n + 1) < binaryRemainder q x n :=
          lt_of_le_of_lt hweight_le (lt_of_not_ge hsmall)
        constructor
        · linarith
        · rw [← inverse_geometric_step hq1 n]
          linarith [ih.2]

private lemma binaryRemainder_eq_sub_sum (q x : ℝ) (n : ℕ) :
    binaryRemainder q x n = x -
      ∑ i ∈ Finset.range n, (binaryDigit q x i : ℝ) * (q⁻¹) ^ (i + 1) := by
  induction n with
  | zero => simp [binaryRemainder]
  | succ n ih =>
      rw [binaryRemainder_succ, ih, Finset.sum_range_succ]
      ring

private lemma binaryRemainder_tendsto_zero {q x : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (q - 1)) :
    Tendsto (binaryRemainder q x) atTop (𝓝 0) := by
  have hq0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hq1.le)
  have hqinv : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  have hpow : Tendsto (fun n : ℕ ↦ (q⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hqinv
  have hcap : Tendsto (fun n : ℕ ↦ (q⁻¹) ^ n / (q - 1)) atTop (𝓝 0) := by
    simpa using hpow.div_const (q - 1)
  exact squeeze_zero
    (fun n ↦ (binaryRemainder_bounds hq1 hq2 hx0 hx1 n).1)
    (fun n ↦ (binaryRemainder_bounds hq1 hq2 hx0 hx1 n).2) hcap

lemma exists_binary_expansion {q x : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (q - 1)) :
    ∃ d : ℕ → ℕ, (∀ n, d n = 0 ∨ d n = 1) ∧
      Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
        (d i : ℝ) * (q⁻¹) ^ (i + 1)) atTop (𝓝 x) := by
  refine ⟨binaryDigit q x, binaryDigit_eq_zero_or_one q x, ?_⟩
  have hrem := binaryRemainder_tendsto_zero hq1 hq2 hx0 hx1
  convert tendsto_const_nhds.sub hrem using 1
  · funext n
    rw [binaryRemainder_eq_sub_sum]
    ring
  · ring_nf

/-- The greedy/lazy binary expansion above, retaining the geometric bound on
its finite remainders. -/
lemma exists_binary_expansion_with_remainder_bounds {q x : ℝ}
    (hq1 : 1 < q) (hq2 : q ≤ 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (q - 1)) :
    ∃ d : ℕ → ℕ, (∀ n, d n = 0 ∨ d n = 1) ∧
      ∀ n, 0 ≤ x - ∑ i ∈ Finset.range n,
        (d i : ℝ) * (q⁻¹) ^ (i + 1) ∧
      x - ∑ i ∈ Finset.range n,
        (d i : ℝ) * (q⁻¹) ^ (i + 1) ≤ (q⁻¹) ^ n / (q - 1) := by
  refine ⟨binaryDigit q x, binaryDigit_eq_zero_or_one q x, fun n ↦ ?_⟩
  rw [← binaryRemainder_eq_sub_sum]
  exact binaryRemainder_bounds hq1 hq2 hx0 hx1 n

lemma smallDisjointDifferences_of_smallSpectrumDifferences {r : ℝ}
    (h : SmallSpectrumDifferences r) : SmallDisjointDifferences r := by
  intro ε hε
  obtain ⟨A, B, hne, hlt⟩ := h ε hε
  have hdifference :
      (∑ i ∈ B \ A, r ^ i) - ∑ i ∈ A \ B, r ^ i =
        (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i := by
    rw [Finset.sum_sdiff_sub_sum_sdiff]
  by_cases hpos : 0 < (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i
  · refine ⟨A \ B, B \ A, disjoint_sdiff_sdiff, ?_, ?_⟩
    · rwa [hdifference]
    · calc
        (∑ i ∈ B \ A, r ^ i) - ∑ i ∈ A \ B, r ^ i =
            (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i := hdifference
        _ < ε := by simpa [abs_of_pos hpos] using hlt
  · have hneg : (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i < 0 := by
      have hnonzero : (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i ≠ 0 := by
        intro hz
        rw [hz, abs_zero] at hne
        exact lt_irrefl 0 hne
      exact lt_of_le_of_ne (le_of_not_gt hpos) hnonzero
    refine ⟨B \ A, A \ B, disjoint_sdiff_sdiff, ?_, ?_⟩
    · have := hdifference
      linarith
    · have := hdifference
      rw [abs_of_neg hneg] at hlt
      linarith

private def shiftSupport (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image (fun i ↦ N + i)

private lemma sum_shiftSupport (r : ℝ) (N : ℕ) (S : Finset ℕ) :
    (∑ k ∈ shiftSupport N S, r ^ k) = r ^ N * ∑ i ∈ S, r ^ i := by
  rw [shiftSupport, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
  · intro i hi j hj hij
    change N + i = N + j at hij
    omega

private lemma shiftSupport_disjoint {N : ℕ} {A B : Finset ℕ} (h : Disjoint A B) :
    Disjoint (shiftSupport N A) (shiftSupport N B) := by
  rw [Finset.disjoint_left] at h ⊢
  intro k hkA hkB
  rcases Finset.mem_image.mp hkA with ⟨i, hiA, hik⟩
  rcases Finset.mem_image.mp hkB with ⟨j, hjB, hjk⟩
  have : i = j := by omega
  subst j
  exact h hiA hjB

private lemma le_of_mem_shiftSupport {N : ℕ} {S : Finset ℕ} {i : ℕ}
    (hi : i ∈ shiftSupport N S) : N ≤ i := by
  rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
  omega

/-- A tiny signed value may be shifted and rescaled to a prescribed support
tail while keeping its size between `δ` and `2δ`. -/
lemma exists_close_pair_above {r : ℝ} (hr1 : 1 < r) (hr2 : r < 2)
    (hsmall : SmallDisjointDifferences r) {δ : ℝ} (hδ : 0 < δ) (H : ℕ) :
    ∃ A B : Finset ℕ, Disjoint A B ∧
      (∀ i ∈ A, H ≤ i) ∧ (∀ i ∈ B, H ≤ i) ∧
      δ < (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i ∧
      (∑ i ∈ B, r ^ i) - ∑ i ∈ A, r ^ i < 2 * δ := by
  have hr0 : 0 < r := by linarith
  have hrH : 0 < r ^ H := by positivity
  obtain ⟨A₀, B₀, hAB₀, hdpos, hdlt⟩ := hsmall (δ / r ^ H) (div_pos hδ hrH)
  let d := (∑ i ∈ B₀, r ^ i) - ∑ i ∈ A₀, r ^ i
  have hd : 0 < d := hdpos
  have hdHlt : r ^ H * d < δ := by
    dsimp [d]
    have h := (lt_div_iff₀ hrH).mp hdlt
    nlinarith
  have hdHpos : 0 < r ^ H * d := mul_pos hrH hd
  have hpow := tendsto_pow_atTop_atTop_of_one_lt hr1
  obtain ⟨N₀, hN₀⟩ :=
    tendsto_atTop_atTop.mp hpow (δ / (r ^ H * d) + 1)
  have hex : ∃ N : ℕ, δ < r ^ N * (r ^ H * d) := by
    refine ⟨N₀, ?_⟩
    have hp := hN₀ N₀ le_rfl
    have hden : 0 < r ^ H * d := hdHpos
    exact (div_lt_iff₀ hden).mp
      (lt_of_lt_of_le (lt_add_one (δ / (r ^ H * d))) hp)
  let N := Nat.find hex
  have hNspec : δ < r ^ N * (r ^ H * d) := Nat.find_spec hex
  have hNpos : 0 < N := by
    by_contra hnot
    have hNzero : N = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hNzero, pow_zero, one_mul] at hNspec
    linarith
  have hNmin : r ^ (N - 1) * (r ^ H * d) ≤ δ := by
    have hnot := Nat.find_min hex (Nat.pred_lt hNpos.ne')
    simpa only [Nat.pred_eq_sub_one, not_lt] using hnot
  let K := H + N
  refine ⟨shiftSupport K A₀, shiftSupport K B₀, shiftSupport_disjoint hAB₀,
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact le_trans (Nat.le_add_right H N) (le_of_mem_shiftSupport hi)
  · intro i hi
    exact le_trans (Nat.le_add_right H N) (le_of_mem_shiftSupport hi)
  · rw [sum_shiftSupport, sum_shiftSupport]
    dsimp [K]
    rw [pow_add]
    dsimp [d] at hNspec ⊢
    nlinarith
  · rw [sum_shiftSupport, sum_shiftSupport]
    dsimp [K]
    rw [pow_add]
    have hpowN : r ^ N = r * r ^ (N - 1) := by
      obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
      rw [hM]
      simp [pow_succ, mul_comm]
    dsimp [d] at hNmin ⊢
    rw [hpowN]
    nlinarith

/-- Iterating high disjoint close pairs gives a chain of binary supports.
The quantitative lower bound on its span is retained for the later crossing
argument. -/
private lemma exists_support_chain {r : ℝ} (hr1 : 1 < r) (hr2 : r < 2)
    (hsmall : SmallDisjointDifferences r) {δ : ℝ} (hδ : 0 < δ) :
    ∀ M H : ℕ, ∃ W : ℕ → Finset ℕ,
      (∀ k ≤ M, ∀ i ∈ W k, H ≤ i) ∧
      (∀ k < M, δ < (∑ i ∈ W (k + 1), r ^ i) - ∑ i ∈ W k, r ^ i ∧
        (∑ i ∈ W (k + 1), r ^ i) - ∑ i ∈ W k, r ^ i < 2 * δ) ∧
      (M : ℝ) * δ ≤ (∑ i ∈ W M, r ^ i) - ∑ i ∈ W 0, r ^ i := by
  intro M
  induction M with
  | zero =>
      intro H
      refine ⟨fun _ ↦ ∅, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp
  | succ M ih =>
      intro H
      obtain ⟨A, B, hAB, hAabove, hBabove, hdlo, hdhi⟩ :=
        exists_close_pair_above hr1 hr2 hsmall hδ H
      let H₁ := H + (A ∪ B).sup id + 1
      obtain ⟨W, hWabove, hWstep, hWspan⟩ := ih H₁
      let W' : ℕ → Finset ℕ
        | 0 => A ∪ W 0
        | k + 1 => B ∪ W k
      have hHH₁ : H ≤ H₁ := by dsimp [H₁]; omega
      have hpair_lt {i : ℕ} (hi : i ∈ A ∪ B) : i < H₁ := by
        have hisup : i ≤ (A ∪ B).sup id := Finset.le_sup (f := id) hi
        dsimp [H₁]
        omega
      have hAdisj (k : ℕ) (hk : k ≤ M) : Disjoint A (W k) := by
        rw [Finset.disjoint_left]
        intro i hiA hiW
        have hilt : i < H₁ := hpair_lt (Finset.mem_union_left B hiA)
        have hige : H₁ ≤ i := hWabove k hk i hiW
        omega
      have hBdisj (k : ℕ) (hk : k ≤ M) : Disjoint B (W k) := by
        rw [Finset.disjoint_left]
        intro i hiB hiW
        have hilt : i < H₁ := hpair_lt (Finset.mem_union_right A hiB)
        have hige : H₁ ≤ i := hWabove k hk i hiW
        omega
      refine ⟨W', ?_, ?_, ?_⟩
      · intro k hk i hi
        cases k with
        | zero =>
            simp only [W'] at hi
            rcases Finset.mem_union.mp hi with hiA | hiW
            · exact hAabove i hiA
            · exact hHH₁.trans (hWabove 0 (Nat.zero_le M) i hiW)
        | succ k =>
            simp only [W'] at hi
            have hkM : k ≤ M := by omega
            rcases Finset.mem_union.mp hi with hiB | hiW
            · exact hBabove i hiB
            · exact hHH₁.trans (hWabove k hkM i hiW)
      · intro k hk
        cases k with
        | zero =>
            simp only [W', zero_add]
            rw [Finset.sum_union (hBdisj 0 (Nat.zero_le M))]
            rw [Finset.sum_union (hAdisj 0 (Nat.zero_le M))]
            constructor <;> linarith
        | succ k =>
            have hkM : k < M := by omega
            simp only [W']
            rw [Finset.sum_union (hBdisj (k + 1) (by omega))]
            rw [Finset.sum_union (hBdisj k hkM.le)]
            have hs := hWstep k hkM
            constructor <;> linarith
      · simp only [W']
        rw [Finset.sum_union (hBdisj M le_rfl)]
        rw [Finset.sum_union (hAdisj 0 (Nat.zero_le M))]
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith

/-- The elementary Erdős--Joó--Komornik replacement-chain lemma. -/
lemma spectrum_hasFineChains_of_smallDifferences {r : ℝ} (hr1 : 1 < r) (hr2 : r < 2)
    (hsmall : SmallDisjointDifferences r) : HasFineChains (Spectrum r) := by
  intro η hη D hD
  have hhalf : 0 < η / 2 := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, D < (M : ℝ) * (η / 2) := by
    obtain ⟨M, hM⟩ := exists_nat_gt (D / (η / 2))
    refine ⟨M, ?_⟩
    have := (div_lt_iff₀ hhalf).mp hM
    nlinarith
  obtain ⟨W, hWabove, hWstep, hWspan⟩ :=
    exists_support_chain hr1 hr2 hsmall hhalf M 0
  let u : ℕ → ℝ := fun k ↦ ∑ i ∈ W k, r ^ i
  refine ⟨M, u, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨W k, rfl⟩
  · intro k hk
    have hs := hWstep k hk
    dsimp [u]
    constructor <;> linarith
  · dsimp [u]
    linarith

@[simp] lemma mem_spectrum_iff {q a : ℝ} :
    a ∈ Spectrum q ↔ ∃ S : Finset ℕ, a = ∑ i ∈ S, q ^ i := Iff.rfl

lemma pow_mem_spectrum (q : ℝ) (n : ℕ) : q ^ n ∈ Spectrum q := by
  refine ⟨{n}, ?_⟩
  simp

lemma spectrum_nonneg {q : ℝ} (hq : 0 ≤ q) {a : ℝ} (ha : a ∈ Spectrum q) : 0 ≤ a := by
  rcases ha with ⟨S, rfl⟩
  positivity

/-- Binary sums using only exponents below `n` approximate every point of
`[0,q^n)` from below with error less than one when `q ≤ 2`. -/
lemma exists_powerSum_below_of_lt_pow {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2) :
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < q ^ n →
      ∃ S : Finset ℕ, S ⊆ Finset.range n ∧
        t - 1 < ∑ i ∈ S, q ^ i ∧ (∑ i ∈ S, q ^ i) ≤ t := by
  intro n
  induction n with
  | zero =>
      intro t ht0 ht1
      refine ⟨∅, by simp, ?_, by simp [ht0]⟩
      simpa using ht1
  | succ n ih =>
      intro t ht0 htpow
      by_cases hlow : t < q ^ n
      · obtain ⟨S, hS, hlo, hhi⟩ := ih t ht0 hlow
        exact ⟨S, hS.trans (Finset.range_mono (Nat.le_succ n)), hlo, hhi⟩
      · have hqn : 0 ≤ q ^ n := by positivity
        have hrem0 : 0 ≤ t - q ^ n := sub_nonneg.mpr (le_of_not_gt hlow)
        have hrem_lt : t - q ^ n < q ^ n := by
          rw [pow_succ] at htpow
          nlinarith
        obtain ⟨S, hS, hlo, hhi⟩ := ih (t - q ^ n) hrem0 hrem_lt
        have hnS : n ∉ S := by
          intro hn
          have := hS hn
          simp only [Finset.mem_range] at this
          omega
        refine ⟨insert n S, ?_, ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_insert] at hi
          simp only [Finset.mem_range]
          rcases hi with hi | hi
          · subst i
            exact Nat.lt_succ_self n
          · exact (Finset.mem_range.mp (hS hi)).trans_le (Nat.le_succ n)
        · rw [Finset.sum_insert hnS]
          linarith
        · rw [Finset.sum_insert hnS]
          linarith

/-- For bases at most two the binary spectrum meets every interval `(t-1,t]`
with `t ≥ 0`. -/
lemma spectrum_one_left_dense {q : ℝ} (hq : 1 < q) (hq2 : q ≤ 2) :
    ∀ t : ℝ, 0 ≤ t → ∃ a ∈ Spectrum q, t - 1 < a ∧ a ≤ t := by
  intro t ht
  have hpow := tendsto_pow_atTop_atTop_of_one_lt hq
  obtain ⟨n, hn⟩ := tendsto_atTop_atTop.mp hpow (t + 1)
  have htlt : t < q ^ n := lt_of_lt_of_le (lt_add_one t) (hn n le_rfl)
  obtain ⟨S, hS, hlo, hhi⟩ :=
    exists_powerSum_below_of_lt_pow (q := q) (by linarith) hq2 n t ht htlt
  exact ⟨∑ i ∈ S, q ^ i, ⟨S, rfl⟩, hlo, hhi⟩

lemma spectrum_eventuallyLeftDense_one {q : ℝ} (hq : 1 < q) (hq2 : q ≤ 2) :
    EventuallyLeftDense (Spectrum q) 1 := by
  refine ⟨0, fun t ht ↦ ?_⟩
  exact spectrum_one_left_dense hq hq2 t ht

lemma scaleSet_spectrum_eventuallyLeftDense {c r : ℝ} (hc : 0 < c)
    (hr : 1 < r) (hr2 : r ≤ 2) :
    EventuallyLeftDense (scaleSet c (Spectrum r)) c := by
  refine ⟨0, fun t ht ↦ ?_⟩
  have htc : 0 ≤ t / c := div_nonneg ht hc.le
  obtain ⟨a, ha, hlo, hhi⟩ := spectrum_one_left_dense hr hr2 (t / c) htc
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcancel : c * (t / c) = t := by field_simp
  refine ⟨c * a, ⟨a, ha, rfl⟩, ?_, ?_⟩ <;> nlinarith

private def evenSupport (S : Finset ℕ) : Finset ℕ := S.image (fun i ↦ 2 * i)

private def oddSupport (S : Finset ℕ) : Finset ℕ := S.image (fun i ↦ 2 * i + 1)

private lemma evenSupport_disjoint_oddSupport (S T : Finset ℕ) :
    Disjoint (evenSupport S) (oddSupport T) := by
  rw [Finset.disjoint_left]
  intro k hkS hkT
  rcases Finset.mem_image.mp hkS with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hkT with ⟨j, hj, h⟩
  omega

private lemma sum_evenSupport (q : ℝ) (S : Finset ℕ) :
    (∑ k ∈ evenSupport S, q ^ k) = ∑ i ∈ S, (q ^ 2) ^ i := by
  rw [evenSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [pow_mul]
  · intro i hi j hj hij
    change 2 * i = 2 * j at hij
    omega

private lemma sum_oddSupport (q : ℝ) (S : Finset ℕ) :
    (∑ k ∈ oddSupport S, q ^ k) = q * ∑ i ∈ S, (q ^ 2) ^ i := by
  rw [oddSupport, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ, pow_mul]
    ring
  · intro i hi j hj hij
    change 2 * i + 1 = 2 * j + 1 at hij
    omega

/-- The even powers represented by `Spectrum (q^2)` and a scaled copy using
the odd powers add without digit collisions to a binary `q`-spectrum value. -/
lemma add_scaleSet_square_subset_spectrum (q : ℝ) :
    ∀ u ∈ Spectrum (q ^ 2), ∀ v ∈ scaleSet q (Spectrum (q ^ 2)), u + v ∈ Spectrum q := by
  intro u hu v hv
  rcases hu with ⟨S, rfl⟩
  rcases hv with ⟨a, ⟨T, rfl⟩, rfl⟩
  refine ⟨evenSupport S ∪ oddSupport T, ?_⟩
  rw [Finset.sum_union (evenSupport_disjoint_oddSupport S T)]
  rw [sum_evenSupport, sum_oddSupport]

/-- The supplied increasing enumeration tends to infinity.  Strict
monotonicity alone would not suffice; the range equality supplies the
unbounded singleton powers. -/
lemma strictMono_spectrum_tendsto_atTop {q : ℝ} (hq : 1 < q)
    {x : ℕ → ℝ} (hx : StrictMono x) (hrange : Set.range x = Spectrum q) :
    Tendsto x atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b ≤ q ^ n := by
    have hpow := tendsto_pow_atTop_atTop_of_one_lt hq
    obtain ⟨n, hn⟩ := tendsto_atTop_atTop.mp hpow b
    exact ⟨n, hn n le_rfl⟩
  have hmem : q ^ n ∈ Set.range x := by
    rw [hrange]
    exact pow_mem_spectrum q n
  rcases hmem with ⟨k, hk⟩
  refine ⟨k, fun m hkm ↦ ?_⟩
  calc
    b ≤ q ^ n := hn
    _ = x k := hk.symm
    _ ≤ x m := hx.monotone hkm

/-- Eventual right-density forces the gaps in any increasing, unbounded exact
enumeration to tend to zero. -/
lemma gaps_tendsto_zero_of_eventuallyRightDense {A : Set ℝ} {x : ℕ → ℝ}
    (hx : StrictMono x) (hrange : Set.range x = A)
    (hxtop : Tendsto x atTop atTop) (hA : EventuallyRightDense A) :
    Tendsto (fun k ↦ x (k + 1) - x k) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  rcases hA η hη with ⟨B, hB⟩
  have hxB : ∀ᶠ k in atTop, B ≤ x k := hxtop.eventually (eventually_ge_atTop B)
  rw [eventually_atTop] at hxB
  rcases hxB with ⟨K, hK⟩
  refine ⟨K, fun k hk ↦ ?_⟩
  have hkB := hK k hk
  rcases hB (x k) hkB with ⟨a, haA, hka, hakη⟩
  rw [← hrange] at haA
  rcases haA with ⟨j, rfl⟩
  have hkj : k < j := hx.lt_iff_lt.mp hka
  have hsucc : k + 1 ≤ j := hkj
  have hgap_nonneg : 0 ≤ x (k + 1) - x k := sub_nonneg.mpr (hx.monotone (Nat.le_succ k))
  have hgap_lt : x (k + 1) - x k < η := by
    have := hx.monotone hsucc
    linarith
  simpa [Real.dist_eq, abs_of_nonneg hgap_nonneg] using hgap_lt

/-- A long fine chain translated by a coarsely left-dense set crosses every
sufficiently late target in a step shorter than the fine mesh. -/
lemma eventuallyRightDense_of_fineChains_add_leftDense
    {U V Z : Set ℝ} {D : ℝ} (hD : 0 < D)
    (hU : HasFineChains U) (hV : EventuallyLeftDense V D)
    (hadd : ∀ u ∈ U, ∀ v ∈ V, u + v ∈ Z) :
    EventuallyRightDense Z := by
  intro η hη
  obtain ⟨n, u, huU, hstep, hspan⟩ := hU η hη D hD
  obtain ⟨C, hC⟩ := hV
  refine ⟨C + u 0, fun t ht ↦ ?_⟩
  have htC : C ≤ t - u 0 := by linarith
  obtain ⟨v, hvV, hvlo, hvhi⟩ := hC (t - u 0) htC
  have hcross : t < u n + v := by linarith
  let P : ℕ → Prop := fun k ↦ k ≤ n ∧ t < u k + v
  have hex : ∃ k, P k := ⟨n, le_rfl, hcross⟩
  let k := Nat.find hex
  have hk : k ≤ n ∧ t < u k + v := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hkzero] at hk
    linarith
  let j := k - 1
  have hjk : j < k := by
    dsimp [j]
    omega
  have hjle : j ≤ n := hjk.le.trans hk.1
  have hprev : u j + v ≤ t := by
    by_contra hnotle
    have hjcross : t < u j + v := lt_of_not_ge hnotle
    exact Nat.find_min hex hjk ⟨hjle, hjcross⟩
  have hjn : j < n := hjk.trans_le hk.1
  have hjstep := (hstep j hjn).2
  have hjsk : j + 1 = k := by
    dsimp [j]
    omega
  rw [hjsk] at hjstep
  refine ⟨u k + v, hadd (u k) (huU k hk.1) v hvV, hk.2, ?_⟩
  linarith

/-- Complete elementary even/odd bridge: small signed values in base `q²`
force arbitrary eventual mesh in the binary spectrum of base `q`. -/
lemma spectrum_eventuallyRightDense_of_square_smallDifferences {q : ℝ}
    (hq : 1 < q) (hq_sq : q ^ 2 < 2)
    (hsmall : SmallDisjointDifferences (q ^ 2)) :
    EventuallyRightDense (Spectrum q) := by
  have hq0 : 0 < q := by linarith
  have hsq1 : 1 < q ^ 2 := by nlinarith
  have hfine : HasFineChains (Spectrum (q ^ 2)) :=
    spectrum_hasFineChains_of_smallDifferences hsq1 hq_sq hsmall
  have hleft : EventuallyLeftDense (scaleSet q (Spectrum (q ^ 2))) q :=
    scaleSet_spectrum_eventuallyLeftDense hq0 hsq1 hq_sq.le
  exact eventuallyRightDense_of_fineChains_add_leftDense hq0 hfine hleft
    (add_scaleSet_square_subset_spectrum q)

/-- Once the small-base signed-spectrum input is available, this is the exact
statement of Problem 1096.  Keeping the front end as an explicit argument
makes the analytic/combinatorial transfer independently checkable. -/
lemma erdos_1096_of_small_base_spectral
    (hspectral : ∀ r : ℝ, 1 < r → r < 121 / 100 → SmallSpectrumDifferences r) :
    ∃ ε > 0, ∀ q, 1 < q → q < 1 + ε →
      ∀ x : ℕ → ℝ, StrictMono x →
        Set.range x = { ∑ i ∈ S, q ^ i | S : Finset ℕ } →
        Tendsto (fun k ↦ x (k + 1) - x k) atTop (𝓝 0) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro htrue
    refine ⟨1 / 10, by norm_num, fun q hq hqε x hx hrange ↦ ?_⟩
    have hqbound : q < 11 / 10 := by norm_num at hqε ⊢; exact hqε
    have hsq1 : 1 < q ^ 2 := by nlinarith
    have hsqbound : q ^ 2 < 121 / 100 := by nlinarith
    have hsq2 : q ^ 2 < 2 := by nlinarith
    have hsmall : SmallDisjointDifferences (q ^ 2) :=
      smallDisjointDifferences_of_smallSpectrumDifferences
        (hspectral (q ^ 2) hsq1 hsqbound)
    have hdense : EventuallyRightDense (Spectrum q) :=
      spectrum_eventuallyRightDense_of_square_smallDifferences hq hsq2 hsmall
    have hrange' : Set.range x = Spectrum q := by
      rw [hrange]
      ext a
      simp only [Spectrum, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨S, rfl⟩
        exact ⟨S, rfl⟩
      · rintro ⟨S, rfl⟩
        exact ⟨S, rfl⟩
    exact gaps_tendsto_zero_of_eventuallyRightDense hx hrange'
      (strictMono_spectrum_tendsto_atTop hq hx hrange') hdense
  · intro h
    trivial

end

end Erdos1096

import ErdosProblems.Erdos360.Core

namespace Erdos360

open scoped BigOperators

def hybridA (K w : ℕ) : ℕ := 3 * w - 2 * K
def hybridT (K w : ℕ) : ℕ := pairWeight K w - 2 * K
def hybridG (K w : ℕ) : ℕ := 4 * w - 2 * K

def hybridX (K M : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ) (i : ℕ) : ℤ :=
  2 * (K : ℤ) - 3 * (w i : ℤ) +
    (if i ∈ Good then (hybridG K (w i) : ℤ) else 0) +
    (if M < w i then 2 * (hybridA K (w i) : ℤ) else 0)

def hybridY (K : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ) (i : ℕ) : ℤ :=
  2 * (K : ℤ) - 3 * (w i : ℤ) +
    (if i ∈ Good then (hybridG K (w i) : ℤ) else 0) +
    (hybridT K (w i) : ℤ)

lemma three_mul_le_two_mul_add_hybridT {K v : ℕ} (hv : v ≤ K) :
    3 * v ≤ 2 * K + hybridT K v := by
  simp only [hybridT]
  have hp := larger_add_two_smaller_le_pairWeight (a := v) (b := K) hv
  rw [pairWeight_comm v K] at hp
  omega

lemma hybridY_nonneg {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hi : w i ≤ K) : 0 ≤ hybridY K Good w i := by
  have ht := three_mul_le_two_mul_add_hybridT hi
  simp only [hybridY]
  split_ifs <;> omega

lemma hybrid_regular_weighted {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hi : w i ≤ K) (hreg : i ∈ Good ∨ M < w i) :
    2 * (K : ℤ) ≤
      2 * hybridX K M Good w i + 3 * hybridY K Good w i := by
  simp only [hybridX, hybridY, hybridA, hybridT, hybridG, pairWeight,
    max_eq_left hi, min_eq_right hi, largestPairWeight, max_def]
  rcases hreg with hgood | hhigh
  · simp only [if_pos hgood]
    split_ifs <;> omega
  · simp only [if_pos hhigh]
    split_ifs <;> omega

lemma hybrid_low_weighted_case_one
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hMK : M ≤ K) (hhalf : 2 * M ≤ K)
    (hibad : i ∉ Good) (hiw : w i ≤ M) :
    10 * (K : ℤ) - 15 * (M : ℤ) ≤
      2 * hybridX K M Good w i + 3 * hybridY K Good w i := by
  have hiK : w i ≤ K := hiw.trans hMK
  have hnotHigh : ¬M < w i := by omega
  simp only [hybridX, hybridY, hybridA, hybridT, hybridG,
    if_neg hibad, if_neg hnotHigh, add_zero, pairWeight,
    max_eq_left hiK, min_eq_right hiK, largestPairWeight, max_def]
  split_ifs <;> omega

lemma hybrid_low_weighted_case_two
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hMK : M ≤ K) (hhalf : K < 2 * M) (hthree : 4 * M < 3 * K)
    (hibad : i ∉ Good) (hiw : w i ≤ M) :
    4 * (K : ℤ) - 3 * (M : ℤ) ≤
      2 * hybridX K M Good w i + 3 * hybridY K Good w i := by
  have hiK : w i ≤ K := hiw.trans hMK
  have hnotHigh : ¬M < w i := by omega
  simp only [hybridX, hybridY, hybridA, hybridT, hybridG,
    if_neg hibad, if_neg hnotHigh, add_zero, pairWeight,
    max_eq_left hiK, min_eq_right hiK, largestPairWeight, max_def]
  split_ifs <;> omega

lemma hybrid_low_weighted_case_three
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hMK : M ≤ K) (hthree : 3 * K ≤ 4 * M)
    (hibad : i ∉ Good) (hiw : w i ≤ M) :
    13 * (K : ℤ) - 15 * (M : ℤ) ≤
      2 * hybridX K M Good w i + 3 * hybridY K Good w i := by
  have hiK : w i ≤ K := hiw.trans hMK
  have hnotHigh : ¬M < w i := by omega
  simp only [hybridX, hybridY, hybridA, hybridT, hybridG,
    if_neg hibad, if_neg hnotHigh, add_zero, pairWeight,
    max_eq_left hiK, min_eq_right hiK, largestPairWeight, max_def]
  split_ifs <;> omega

lemma hybrid_base_weighted_case_one
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base : ℕ}
    (hMK : M ≤ K) (hhalf : 2 * M ≤ K)
    (hbase : base ∈ Good) (hbasew : w base = M) :
    10 * (K : ℤ) - 15 * (M : ℤ) ≤
      2 * hybridX K M Good w base + 3 * hybridY K Good w base := by
  simp only [hybridX, hybridY, hybridA, hybridT, hybridG, hbasew,
    if_pos hbase, pairWeight, max_eq_left hMK, min_eq_right hMK,
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma hybrid_base_weighted_case_two
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base : ℕ}
    (hMK : M ≤ K) (hhalf : K < 2 * M) (hthree : 4 * M < 3 * K)
    (hbase : base ∈ Good) (hbasew : w base = M) :
    17 * (M : ℤ) - 6 * (K : ℤ) ≤
      2 * hybridX K M Good w base + 3 * hybridY K Good w base := by
  simp only [hybridX, hybridY, hybridA, hybridT, hybridG, hbasew,
    if_pos hbase, pairWeight, max_eq_left hMK, min_eq_right hMK,
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma hybrid_base_weighted_case_three
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base : ℕ}
    (hMK : M ≤ K) (hthree : 3 * K ≤ 4 * M)
    (hbase : base ∈ Good) (hbasew : w base = M) :
    3 * (K : ℤ) + 5 * (M : ℤ) ≤
      2 * hybridX K M Good w base + 3 * hybridY K Good w base := by
  simp only [hybridX, hybridY, hybridA, hybridT, hybridG, hbasew,
    if_pos hbase, pairWeight, max_eq_left hMK, min_eq_right hMK,
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma hybrid_base_low_one
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base i : ℕ}
    (hMK : M ≤ K) (hMrange : 6 * M ≤ 5 * K)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hibad : i ∉ Good) (hiw : w i ≤ M) :
    4 * (K : ℤ) ≤
      (2 * hybridX K M Good w base + 3 * hybridY K Good w base) +
        (2 * hybridX K M Good w i + 3 * hybridY K Good w i) := by
  rcases le_or_gt (2 * M) K with hhalf | hhalf
  · have hb := hybrid_base_weighted_case_one hMK hhalf hbase hbasew
    have hi := hybrid_low_weighted_case_one hMK hhalf hibad hiw
    omega
  · rcases lt_or_ge (4 * M) (3 * K) with hthree | hthree
    · have hb := hybrid_base_weighted_case_two hMK hhalf hthree hbase hbasew
      have hi := hybrid_low_weighted_case_two hMK hhalf hthree hibad hiw
      omega
    · have hb := hybrid_base_weighted_case_three hMK hthree hbase hbasew
      have hi := hybrid_low_weighted_case_three hMK hthree hibad hiw
      omega

lemma hybrid_base_low_two
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base i j : ℕ}
    (hMK : M ≤ K) (hMrange : 6 * M ≤ 5 * K)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hibad : i ∉ Good) (hiw : w i ≤ M)
    (hjbad : j ∉ Good) (hjw : w j ≤ M) :
    6 * (K : ℤ) ≤
      (2 * hybridX K M Good w base + 3 * hybridY K Good w base) +
        (2 * hybridX K M Good w i + 3 * hybridY K Good w i) +
        (2 * hybridX K M Good w j + 3 * hybridY K Good w j) := by
  rcases le_or_gt (2 * M) K with hhalf | hhalf
  · have hb := hybrid_base_weighted_case_one hMK hhalf hbase hbasew
    have hi := hybrid_low_weighted_case_one hMK hhalf hibad hiw
    have hj := hybrid_low_weighted_case_one hMK hhalf hjbad hjw
    omega
  · rcases lt_or_ge (4 * M) (3 * K) with hthree | hthree
    · have hb := hybrid_base_weighted_case_two hMK hhalf hthree hbase hbasew
      have hi := hybrid_low_weighted_case_two hMK hhalf hthree hibad hiw
      have hj := hybrid_low_weighted_case_two hMK hhalf hthree hjbad hjw
      omega
    · have hb := hybrid_base_weighted_case_three hMK hthree hbase hbasew
      have hi := hybrid_low_weighted_case_three hMK hthree hibad hiw
      have hj := hybrid_low_weighted_case_three hMK hthree hjbad hjw
      omega

lemma hybrid_base_low_three
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base i j k : ℕ}
    (hMK : M ≤ K) (hMrange : 6 * M ≤ 5 * K)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hibad : i ∉ Good) (hiw : w i ≤ M)
    (hjbad : j ∉ Good) (hjw : w j ≤ M)
    (hkbad : k ∉ Good) (hkw : w k ≤ M) :
    8 * (K : ℤ) ≤
      (2 * hybridX K M Good w base + 3 * hybridY K Good w base) +
        (2 * hybridX K M Good w i + 3 * hybridY K Good w i) +
        (2 * hybridX K M Good w j + 3 * hybridY K Good w j) +
        (2 * hybridX K M Good w k + 3 * hybridY K Good w k) := by
  rcases le_or_gt (2 * M) K with hhalf | hhalf
  · have hb := hybrid_base_weighted_case_one hMK hhalf hbase hbasew
    have hi := hybrid_low_weighted_case_one hMK hhalf hibad hiw
    have hj := hybrid_low_weighted_case_one hMK hhalf hjbad hjw
    have hk := hybrid_low_weighted_case_one hMK hhalf hkbad hkw
    omega
  · rcases lt_or_ge (4 * M) (3 * K) with hthree | hthree
    · have hb := hybrid_base_weighted_case_two hMK hhalf hthree hbase hbasew
      have hi := hybrid_low_weighted_case_two hMK hhalf hthree hibad hiw
      have hj := hybrid_low_weighted_case_two hMK hhalf hthree hjbad hjw
      have hk := hybrid_low_weighted_case_two hMK hhalf hthree hkbad hkw
      omega
    · have hb := hybrid_base_weighted_case_three hMK hthree hbase hbasew
      have hi := hybrid_low_weighted_case_three hMK hthree hibad hiw
      have hj := hybrid_low_weighted_case_three hMK hthree hjbad hjw
      have hk := hybrid_low_weighted_case_three hMK hthree hkbad hkw
      omega

lemma hybrid_low_y_half
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hMK : M ≤ K) (hMrange : 6 * M ≤ 5 * K)
    (hibad : i ∉ Good) (hiw : w i ≤ M) :
    (K : ℤ) ≤ 2 * hybridY K Good w i := by
  have hiK : w i ≤ K := hiw.trans hMK
  have hnotHigh : ¬M < w i := by omega
  simp only [hybridY, hybridT, hybridG, if_neg hibad, add_zero,
    pairWeight, max_eq_left hiK, min_eq_right hiK,
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma hybrid_base_low_y_high
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base i : ℕ}
    (hMK : M < K) (hMhigh : 5 * K < 6 * M)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hibad : i ∉ Good) (hiw : w i ≤ M) :
    2 * (K : ℤ) ≤ hybridY K Good w base + hybridY K Good w i := by
  have hMle : M ≤ K := hMK.le
  have hiK : w i ≤ K := hiw.trans hMle
  simp only [hybridY, hybridT, hybridG, hbasew, if_pos hbase,
    if_neg hibad, pairWeight, max_eq_left hMle, min_eq_right hMle,
    max_eq_left hiK, min_eq_right hiK, largestPairWeight, max_def]
  split_ifs <;> omega

lemma hybrid_rest_max_bound
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top M K : ℕ}
    (hcard : 6 ≤ A.card) (hbaseA : base ∈ A) (htopA : top ∈ A)
    (hbase : base ∈ Good) (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hmax : ∀ i ∈ A, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M) :
    2 * (K : ℤ) ≤ max
      (∑ i ∈ A.erase top, hybridX K M Good w i)
      (∑ i ∈ A.erase top, hybridY K Good w i) := by
  classical
  let Rest := A.erase top
  let Low := Rest.filter fun i => i ∉ Good ∧ w i ≤ M
  let Reg := Rest \ Low
  let W : ℕ → ℤ := fun i =>
    2 * hybridX K M Good w i + 3 * hybridY K Good w i
  have htopne : top ≠ base := by
    intro h
    subst top
    omega
  have hbaseRest : base ∈ Rest := Finset.mem_erase.mpr ⟨htopne.symm, hbaseA⟩
  have hLowSub : Low ⊆ Rest := Finset.filter_subset _ _
  have hRegSub : Reg ⊆ Rest := Finset.sdiff_subset
  have hbaseNotLow : base ∉ Low := by
    intro hb
    exact (Finset.mem_filter.mp hb).2.1 hbase
  have hbaseReg : base ∈ Reg := Finset.mem_sdiff.mpr ⟨hbaseRest, hbaseNotLow⟩
  have hpart : Low ∪ Reg = Rest := by
    dsimp only [Reg]
    exact Finset.union_sdiff_of_subset hLowSub
  have hdisj : Disjoint Low Reg := Finset.disjoint_sdiff
  have hRestCard : Rest.card = A.card - 1 := by
    dsimp only [Rest]
    rw [Finset.card_erase_of_mem htopA]
  have hRegCard : Reg.card = Rest.card - Low.card := by
    dsimp only [Reg]
    exact Finset.card_sdiff_of_subset hLowSub
  have hYnonneg : ∀ i ∈ Rest, 0 ≤ hybridY K Good w i := by
    intro i hi
    exact hybridY_nonneg (M := M) (hmax i (Finset.mem_of_mem_erase hi))
  have hregular : ∀ i ∈ Reg, i ∈ Good ∨ M < w i := by
    intro i hi
    by_cases hiG : i ∈ Good
    · exact Or.inl hiG
    · right
      have hiRest := hRegSub hi
      have hiNotLow := (Finset.mem_sdiff.mp hi).2
      by_contra hnot
      exact hiNotLow (Finset.mem_filter.mpr ⟨hiRest, hiG, by omega⟩)
  have regular_sum_bound : ∀ S : Finset ℕ, S ⊆ Reg →
      2 * (S.card : ℤ) * (K : ℤ) ≤ ∑ i ∈ S, W i := by
    intro S hS
    have hs : (∑ _i ∈ S, 2 * (K : ℤ)) ≤ ∑ i ∈ S, W i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hybrid_regular_weighted
        (hmax i (Finset.mem_of_mem_erase (hRegSub (hS hi))))
        (hregular i (hS hi))
    calc
      2 * (S.card : ℤ) * (K : ℤ) = (S.card : ℤ) * (2 * (K : ℤ)) := by ring
      _ ≤ ∑ i ∈ S, W i := by simpa [W] using hs
  have hRegEraseSub : Reg.erase base ⊆ Reg := Finset.erase_subset _ _
  have hRegSplit : (∑ i ∈ Reg, W i) =
      W base + ∑ i ∈ Reg.erase base, W i := by
    rw [add_comm]
    exact (Finset.sum_erase_add Reg W hbaseReg).symm
  have hsumW : (∑ i ∈ Rest, W i) =
      (∑ i ∈ Low, W i) + W base + ∑ i ∈ Reg.erase base, W i := by
    calc
      (∑ i ∈ Rest, W i) = ∑ i ∈ Low ∪ Reg, W i := by rw [hpart]
      _ = (∑ i ∈ Low, W i) + ∑ i ∈ Reg, W i :=
        Finset.sum_union hdisj
      _ = (∑ i ∈ Low, W i) +
          (W base + ∑ i ∈ Reg.erase base, W i) := by
        rw [hRegSplit]
      _ = _ := by ring
  have hweighted : (∑ i ∈ Rest, W i) =
      2 * (∑ i ∈ Rest, hybridX K M Good w i) +
        3 * (∑ i ∈ Rest, hybridY K Good w i) := by
    dsimp only [W]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have max_of_weighted (h : 10 * (K : ℤ) ≤ ∑ i ∈ Rest, W i) :
      2 * (K : ℤ) ≤ max
        (∑ i ∈ Rest, hybridX K M Good w i)
        (∑ i ∈ Rest, hybridY K Good w i) := by
    rw [hweighted] at h
    have hx := le_max_left
      (∑ i ∈ Rest, hybridX K M Good w i)
      (∑ i ∈ Rest, hybridY K Good w i)
    have hy := le_max_right
      (∑ i ∈ Rest, hybridX K M Good w i)
      (∑ i ∈ Rest, hybridY K Good w i)
    omega
  by_cases hMhigh : 5 * K < 6 * M
  · by_cases hLowNe : Low.Nonempty
    · obtain ⟨i, hiLow⟩ := hLowNe
      have hi := (Finset.mem_filter.mp hiLow).2
      have hpair := hybrid_base_low_y_high hMK hMhigh hbase hbasew hi.1 hi.2
      have hbasei : ({base, i} : Finset ℕ) ⊆ Rest := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hbaseRest
        · exact hLowSub hiLow
      have hpairSum : hybridY K Good w base + hybridY K Good w i =
          ∑ z ∈ ({base, i} : Finset ℕ), hybridY K Good w z := by
        have hne : i ≠ base := by
          intro h
          subst i
          exact hi.1 hbase
        rw [Finset.sum_insert (by simpa using hne.symm), Finset.sum_singleton]
      have hsubsum : (∑ z ∈ ({base, i} : Finset ℕ), hybridY K Good w z) ≤
          ∑ z ∈ Rest, hybridY K Good w z :=
        Finset.sum_le_sum_of_subset_of_nonneg hbasei (by
          intro z hz hznot
          exact hYnonneg z hz)
      rw [← hpairSum] at hsubsum
      have hYfull : 2 * (K : ℤ) ≤
          ∑ z ∈ A.erase top, hybridY K Good w z := by
        simpa only [Rest] using hpair.trans hsubsum
      exact hYfull.trans (le_max_right _ _)
    · have hLowEmpty : Low = ∅ := Finset.not_nonempty_iff_eq_empty.mp hLowNe
      have hRegEq : Reg = Rest := by simp [Reg, hLowEmpty]
      have hregsum := regular_sum_bound Rest (by rw [hRegEq])
      have hcard5 : 5 ≤ Rest.card := by omega
      have hten : 10 * (K : ℤ) ≤ ∑ i ∈ Rest, W i := by
        have hc : (5 : ℤ) ≤ Rest.card := by exact_mod_cast hcard5
        nlinarith
      simpa only [Rest] using max_of_weighted hten
  · have hMrange : 6 * M ≤ 5 * K := by omega
    by_cases hLow4 : 4 ≤ Low.card
    · obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hLow4
      have hlocal : (∑ _i ∈ S, (K : ℤ)) ≤
          ∑ i ∈ S, 2 * hybridY K Good w i := by
        apply Finset.sum_le_sum
        intro i hi
        have hiLow := hS hi
        have hib := (Finset.mem_filter.mp hiLow).2
        exact hybrid_low_y_half hMK.le hMrange hib.1 hib.2
      have htwo : 2 * (K : ℤ) ≤ ∑ i ∈ S, hybridY K Good w i := by
        simp only [Finset.sum_const, nsmul_eq_mul, hScard, ← Finset.mul_sum] at hlocal
        norm_num at hlocal ⊢
        omega
      have hSRest : S ⊆ Rest := hS.trans hLowSub
      have hsubsum : (∑ i ∈ S, hybridY K Good w i) ≤
          ∑ i ∈ Rest, hybridY K Good w i :=
        Finset.sum_le_sum_of_subset_of_nonneg hSRest (by
          intro i hi hin
          exact hYnonneg i hi)
      have hYfull : 2 * (K : ℤ) ≤
          ∑ i ∈ A.erase top, hybridY K Good w i := by
        simpa only [Rest] using htwo.trans hsubsum
      exact hYfull.trans (le_max_right _ _)
    · have hLowLe : Low.card ≤ 3 := by omega
      interval_cases hLcard : Low.card
      · have hLowEmpty : Low = ∅ := Finset.card_eq_zero.mp hLcard
        have hRegEq : Reg = Rest := by simp [Reg, hLowEmpty]
        have hregsum := regular_sum_bound Rest (by rw [hRegEq])
        have hcard5 : 5 ≤ Rest.card := by omega
        apply max_of_weighted
        have hc : (5 : ℤ) ≤ Rest.card := by exact_mod_cast hcard5
        nlinarith
      · obtain ⟨i, hLowEq⟩ := Finset.card_eq_one.mp hLcard
        have hiLow : i ∈ Low := by simp [hLowEq]
        have hi := (Finset.mem_filter.mp hiLow).2
        have htuple := hybrid_base_low_one hMK.le hMrange hbase hbasew hi.1 hi.2
        have hregsum := regular_sum_bound (Reg.erase base) hRegEraseSub
        have hregcard : 3 ≤ (Reg.erase base).card := by
          rw [Finset.card_erase_of_mem hbaseReg, hRegCard, hRestCard]
          omega
        apply max_of_weighted
        rw [hsumW, hLowEq]
        simp only [Finset.sum_singleton]
        have hc : (3 : ℤ) ≤ (Reg.erase base).card := by exact_mod_cast hregcard
        nlinarith
      · obtain ⟨i, j, hij, hLowEq⟩ := Finset.card_eq_two.mp hLcard
        have hiLow : i ∈ Low := by simp [hLowEq]
        have hjLow : j ∈ Low := by simp [hLowEq]
        have hi := (Finset.mem_filter.mp hiLow).2
        have hj := (Finset.mem_filter.mp hjLow).2
        have htuple := hybrid_base_low_two hMK.le hMrange hbase hbasew
          hi.1 hi.2 hj.1 hj.2
        have hregsum := regular_sum_bound (Reg.erase base) hRegEraseSub
        have hregcard : 2 ≤ (Reg.erase base).card := by
          rw [Finset.card_erase_of_mem hbaseReg, hRegCard, hRestCard]
          omega
        apply max_of_weighted
        rw [hsumW, hLowEq]
        simp [hij]
        have hc : (2 : ℤ) ≤ (Reg.erase base).card := by exact_mod_cast hregcard
        nlinarith
      · obtain ⟨i, j, k, hij, hik, hjk, hLowEq⟩ := Finset.card_eq_three.mp hLcard
        have hiLow : i ∈ Low := by simp [hLowEq]
        have hjLow : j ∈ Low := by simp [hLowEq]
        have hkLow : k ∈ Low := by simp [hLowEq]
        have hi := (Finset.mem_filter.mp hiLow).2
        have hj := (Finset.mem_filter.mp hjLow).2
        have hk := (Finset.mem_filter.mp hkLow).2
        have htuple := hybrid_base_low_three hMK.le hMrange hbase hbasew
          hi.1 hi.2 hj.1 hj.2 hk.1 hk.2
        have hregsum := regular_sum_bound (Reg.erase base) hRegEraseSub
        have hregcard : 1 ≤ (Reg.erase base).card := by
          rw [Finset.card_erase_of_mem hbaseReg, hRegCard, hRestCard]
          omega
        apply max_of_weighted
        rw [hsumW, hLowEq]
        simp [hij, hik, hjk]
        have hc : (1 : ℤ) ≤ (Reg.erase base).card := by exact_mod_cast hregcard
        nlinarith

lemma hybrid_arithmetic_of_maximal_dense
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top M K : ℕ}
    (hcard : 6 ≤ A.card) (hGoodSub : Good ⊆ A)
    (hbaseA : base ∈ A) (htopA : top ∈ A)
    (hbase : base ∈ Good) (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hmax : ∀ i ∈ A, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M) :
    5 * (∑ i ∈ A, w i) ≤
      2 * ((∑ i ∈ A, w i) + (A.card - 1) * K) +
        (∑ i ∈ Good, hybridG K (w i)) +
          max (2 * (∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i)) - K)
            (∑ i ∈ A, hybridT K (w i)) := by
  classical
  let S := ∑ i ∈ A, w i
  let G := ∑ i ∈ Good, hybridG K (w i)
  let AH := ∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i)
  let T := ∑ i ∈ A, hybridT K (w i)
  have htopNotGood : top ∉ Good := by
    intro ht
    have := hGoodMax top ht
    omega
  have htopHigh : top ∈ A.filter (fun i => M < w i) :=
    Finset.mem_filter.mpr ⟨htopA, by omega⟩
  have hKleAH : K ≤ AH := by
    have hself : hybridA K (w top) = K := by
      simp only [hybridA, htopw]
      omega
    calc
      K = hybridA K (w top) := hself.symm
      _ ≤ ∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i) :=
        Finset.single_le_sum (f := fun i => hybridA K (w i))
          (fun _ _ => Nat.zero_le _) htopHigh
  have hGoodFilter : A.filter (fun i => i ∈ Good) = Good := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi => hi.2
    · exact fun hi => ⟨hGoodSub hi, hi⟩
  have hsumGood : (∑ i ∈ A,
      if i ∈ Good then (hybridG K (w i) : ℤ) else 0) = (G : ℤ) := by
    rw [← Finset.sum_filter]
    rw [hGoodFilter]
    exact_mod_cast rfl
  have hsumHigh : (∑ i ∈ A,
      if M < w i then 2 * (hybridA K (w i) : ℤ) else 0) = 2 * (AH : ℤ) := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    exact_mod_cast rfl
  have hsumT : (∑ i ∈ A, (hybridT K (w i) : ℤ)) = (T : ℤ) := by
    exact_mod_cast rfl
  have hsumS : (∑ i ∈ A, (w i : ℤ)) = (S : ℤ) := by
    exact_mod_cast rfl
  have hsumX : (∑ i ∈ A, hybridX K M Good w i) =
      2 * (A.card : ℤ) * (K : ℤ) - 3 * (S : ℤ) +
        (G : ℤ) + 2 * (AH : ℤ) := by
    simp only [hybridX, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hsumGood, hsumHigh]
    rw [hsumS]
    push_cast
    ring
  have hsumY : (∑ i ∈ A, hybridY K Good w i) =
      2 * (A.card : ℤ) * (K : ℤ) - 3 * (S : ℤ) +
        (G : ℤ) + (T : ℤ) := by
    simp only [hybridY, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hsumGood, hsumT]
    rw [hsumS]
    push_cast
    ring
  have htopX : hybridX K M Good w top = (K : ℤ) := by
    simp only [hybridX, hybridA, hybridG, htopw, if_neg htopNotGood,
      if_pos hMK, add_zero]
    norm_num
    omega
  have htopY : hybridY K Good w top = 0 := by
    simp only [hybridY, hybridG, hybridT, hybridA, htopw, if_neg htopNotGood,
      pairWeight_self, add_zero]
    norm_num
    omega
  have hrestX : (∑ i ∈ A.erase top, hybridX K M Good w i) =
      2 * (A.card : ℤ) * (K : ℤ) - 3 * (S : ℤ) +
        (G : ℤ) + 2 * (AH : ℤ) - K := by
    have hsplit := Finset.sum_erase_add A (fun i => hybridX K M Good w i) htopA
    rw [htopX, hsumX] at hsplit
    omega
  have hrestY : (∑ i ∈ A.erase top, hybridY K Good w i) =
      2 * (A.card : ℤ) * (K : ℤ) - 3 * (S : ℤ) +
        (G : ℤ) + T := by
    have hsplit := Finset.sum_erase_add A (fun i => hybridY K Good w i) htopA
    rw [htopY, hsumY] at hsplit
    omega
  have hrest := hybrid_rest_max_bound A Good w hcard hbaseA htopA
    hbase hbasew htopw hMK hmax hGoodMax
  rw [hrestX, hrestY] at hrest
  have hcardPos : 1 ≤ A.card := by omega
  have hKtwoAH : K ≤ 2 * AH := by omega
  have hthree : 3 * S ≤
      2 * (A.card - 1) * K + G + max (2 * AH - K) T := by
    rw [le_max_iff] at hrest
    rcases hrest with hx | hy
    · have hx' : 3 * (S : ℤ) ≤
          2 * ((A.card - 1 : ℕ) : ℤ) * K + G + (2 * AH - K : ℕ) := by
        rw [Nat.cast_sub hcardPos, Nat.cast_sub hKtwoAH]
        push_cast
        nlinarith
      have hxNat : 3 * S ≤ 2 * (A.card - 1) * K + G + (2 * AH - K) := by
        exact_mod_cast hx'
      exact hxNat.trans (Nat.add_le_add_left (le_max_left _ _) _)
    · have hy' : 3 * (S : ℤ) ≤
          2 * ((A.card - 1 : ℕ) : ℤ) * K + G + T := by
        rw [Nat.cast_sub hcardPos]
        push_cast
        nlinarith
      have hyNat : 3 * S ≤ 2 * (A.card - 1) * K + G + T := by
        exact_mod_cast hy'
      exact hyNat.trans (Nat.add_le_add_left (le_max_right _ _) _)
  dsimp only [S, G, AH, T] at hthree ⊢
  calc
    5 * (∑ i ∈ A, w i) =
        2 * (∑ i ∈ A, w i) + 3 * (∑ i ∈ A, w i) := by ring
    _ ≤ 2 * (∑ i ∈ A, w i) +
        (2 * (A.card - 1) * K +
          (∑ i ∈ Good, hybridG K (w i)) +
          max (2 * (∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i)) - K)
            (∑ i ∈ A, hybridT K (w i))) := Nat.add_le_add_left hthree _
    _ = _ := by ring

end Erdos360

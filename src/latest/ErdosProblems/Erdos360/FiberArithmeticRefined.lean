import ErdosProblems.Erdos360.FiberArithmetic

namespace Erdos360

open scoped BigOperators

def starMargin (K : ℕ) (w : ℕ → ℕ) (i : ℕ) : ℤ :=
  2 * (K : ℤ) - 3 * (w i : ℤ) + (hybridT K (w i) : ℤ)

def crossMargin (K : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ) (i : ℕ) : ℤ :=
  2 * (K : ℤ) - 3 * (w i : ℤ) +
    (if i ∈ Good then (hybridG K (w i) : ℤ) else 0)

def mixedMargin (K M : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ) (i : ℕ) : ℤ :=
  2 * crossMargin K Good w i + hybridX K M Good w i

lemma starMargin_nonneg {K : ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hi : w i ≤ K) : 0 ≤ starMargin K w i := by
  have ht := three_mul_le_two_mul_add_hybridT hi
  simp only [starMargin]
  omega

lemma crossMargin_good_nonneg {K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hi : w i ≤ K) (hiG : i ∈ Good) : 0 ≤ crossMargin K Good w i := by
  simp only [crossMargin, hybridG, if_pos hiG]
  omega

lemma high_mixed_base {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base : ℕ}
    (hMK : M < K) (hMhigh : 5 * K < 6 * M)
    (hbase : base ∈ Good) (hbasew : w base = M) :
    mixedMargin K M Good w base = 3 * (M : ℤ) := by
  simp only [mixedMargin, crossMargin, hybridX, hybridG, hybridA,
    hbasew, if_pos hbase, if_neg (by omega : ¬M < M)]
  have hMK' : M ≤ K := hMK.le
  omega

lemma high_mixed_regular_good {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hi : w i ≤ K) (hiG : i ∈ Good) :
    3 * (K : ℤ) ≤ 2 * mixedMargin K M Good w i := by
  simp only [mixedMargin, crossMargin, hybridX, hybridG,
    if_pos hiG]
  split_ifs <;> omega

lemma high_mixed_regular_bad {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hMK : 5 * K < 6 * M) (hi : w i ≤ K) (hiG : i ∉ Good)
    (hiHigh : M < w i) :
    3 * (K : ℤ) ≤ 2 * (mixedMargin K M Good w i +
      ((2 * hybridG K M + (hybridG K M - K)) : ℕ)) := by
  simp only [mixedMargin, crossMargin, hybridX, hybridG, hybridA,
    if_neg hiG, if_pos hiHigh, add_zero]
  omega

lemma high_mixed_regular_low {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hMK : 5 * K < 6 * M) (hiG : i ∉ Good) (hiLow : w i ≤ M) :
    3 * (K : ℤ) ≤ 2 * (mixedMargin K M Good w i +
      ((2 * hybridG K M + (hybridG K M - K)) : ℕ)) := by
  have hnot : ¬M < w i := by omega
  simp only [mixedMargin, crossMargin, hybridX, hybridG, hybridA,
    if_neg hiG, if_neg hnot, add_zero]
  omega

lemma high_mixed_sum_bound
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top M K : ℕ}
    (hcard : 6 ≤ A.card) (hGoodSub : Good ⊆ A)
    (hbaseA : base ∈ A) (htopA : top ∈ A)
    (hbase : base ∈ Good) (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hMhigh : 5 * K < 6 * M)
    (hmax : ∀ i ∈ A, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M) :
    let Bad := A \ Good
    let P := (2 * hybridG K M + (hybridG K M - K) : ℕ)
    7 * (K : ℤ) ≤
      (∑ i ∈ A, mixedMargin K M Good w i) +
        ((Bad.card - 1) * P : ℕ) := by
  classical
  dsimp only
  let Bad := A \ Good
  let P : ℕ := 2 * hybridG K M + (hybridG K M - K)
  let Q : ℕ → ℤ := fun i => mixedMargin K M Good w i +
    if i ∈ Bad.erase top then (P : ℤ) else 0
  let Other := (A.erase top).erase base
  have htopNotGood : top ∉ Good := by
    intro ht
    have := hGoodMax top ht
    omega
  have htopBad : top ∈ Bad := Finset.mem_sdiff.mpr ⟨htopA, htopNotGood⟩
  have htopne : top ≠ base := by
    intro h
    subst top
    omega
  have hbaseRest : base ∈ A.erase top := Finset.mem_erase.mpr ⟨htopne.symm, hbaseA⟩
  have hOtherCard : 4 ≤ Other.card := by
    dsimp only [Other]
    rw [Finset.card_erase_of_mem hbaseRest, Finset.card_erase_of_mem htopA]
    omega
  have hQtop : Q top = -(K : ℤ) := by
    simp only [Q, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      ↓reduceIte, mixedMargin, crossMargin, hybridX, hybridG, hybridA,
      htopw, if_neg htopNotGood, if_pos hMK, add_zero]
    omega
  have hQbase : Q base = 3 * (M : ℤ) := by
    have hbaseNotBad : base ∉ Bad := by
      intro hb
      exact (Finset.mem_sdiff.mp hb).2 hbase
    simp only [Q, Finset.mem_erase, hbaseNotBad, and_false, ↓reduceIte,
      high_mixed_base hMK hMhigh hbase hbasew, add_zero]
  have hQregular : ∀ i ∈ Other, 3 * (K : ℤ) ≤ 2 * Q i := by
    intro i hi
    have hiRest := Finset.mem_of_mem_erase hi
    have hiA := Finset.mem_of_mem_erase hiRest
    have hiNotTop : i ≠ top := (Finset.mem_erase.mp hiRest).1
    by_cases hiG : i ∈ Good
    · have hiNotBad : i ∉ Bad := by
        intro hb
        exact (Finset.mem_sdiff.mp hb).2 hiG
      simp only [Q, Finset.mem_erase, hiNotBad, and_false, ↓reduceIte, add_zero]
      exact high_mixed_regular_good (hmax i hiA) hiG
    · have hiBad : i ∈ Bad := Finset.mem_sdiff.mpr ⟨hiA, hiG⟩
      have hiBadErase : i ∈ Bad.erase top :=
        Finset.mem_erase.mpr ⟨hiNotTop, hiBad⟩
      simp only [Q, hiBadErase, ↓reduceIte]
      by_cases hiHigh : M < w i
      · exact high_mixed_regular_bad hMhigh (hmax i hiA) hiG hiHigh
      · exact high_mixed_regular_low hMhigh hiG (by omega)
  have hQsumOther :
      3 * (Other.card : ℤ) * (K : ℤ) ≤ 2 * ∑ i ∈ Other, Q i := by
    have hs : (∑ _i ∈ Other, 3 * (K : ℤ)) ≤
        ∑ i ∈ Other, 2 * Q i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hQregular i hi
    simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm] using hs
  have hQsplit : (∑ i ∈ A, Q i) =
      Q top + Q base + ∑ i ∈ Other, Q i := by
    have ht := Finset.sum_erase_add A Q htopA
    have hb := Finset.sum_erase_add (A.erase top) Q hbaseRest
    dsimp only [Other]
    omega
  have hQlower : 7 * (K : ℤ) ≤ ∑ i ∈ A, Q i := by
    rw [hQsplit, hQtop, hQbase]
    have hc : (4 : ℤ) ≤ Other.card := by exact_mod_cast hOtherCard
    nlinarith
  have hBadEraseSubA : Bad.erase top ⊆ A := by
    intro i hi
    exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hi)).1
  have hfilter : A.filter (fun i => i ∈ Bad.erase top) = Bad.erase top := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi => hi.2
    · exact fun hi => ⟨hBadEraseSubA hi, hi⟩
  have hQsum : (∑ i ∈ A, Q i) =
      (∑ i ∈ A, mixedMargin K M Good w i) +
        ((Bad.card - 1) * P : ℕ) := by
    simp only [Q, Finset.sum_add_distrib]
    rw [← Finset.sum_filter, hfilter]
    simp only [Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem htopBad]
    exact_mod_cast rfl
  rw [hQsum] at hQlower
  simpa only [Bad, P] using hQlower

lemma high_X_regular_good {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hi : w i ≤ K) (hiG : i ∈ Good) :
    (K : ℤ) ≤ 2 * hybridX K M Good w i := by
  simp only [hybridX, hybridG, hybridA, if_pos hiG]
  split_ifs <;> omega

lemma high_X_regular_bad {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hMhigh : 5 * K < 6 * M) (hi : w i ≤ K) (hiG : i ∉ Good)
    (hiHigh : M < w i) :
    (K : ℤ) ≤ 2 * (hybridX K M Good w i +
      ((hybridG K M - K : ℕ) : ℤ)) := by
  simp only [hybridX, hybridG, hybridA, if_neg hiG, if_pos hiHigh, add_zero]
  omega

lemma high_X_base {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base : ℕ}
    (hMK : M < K) (hMhigh : 5 * K < 6 * M)
    (hbase : base ∈ Good) (hbasew : w base = M) :
    hybridX K M Good w base = (M : ℤ) := by
  simp only [hybridX, hybridG, hybridA, hbasew, if_pos hbase,
    if_neg (by omega : ¬M < M)]
  omega

lemma high_X_sum_bound
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top M K : ℕ}
    (hcard : 6 ≤ A.card) (hGoodSub : Good ⊆ A)
    (hbaseA : base ∈ A) (htopA : top ∈ A)
    (hbase : base ∈ Good) (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hMhigh : 5 * K < 6 * M)
    (hmax : ∀ i ∈ A, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M)
    (hBadHigh : ∀ i ∈ A, i ∉ Good → M < w i) :
    let Bad := A \ Good
    3 * (K : ℤ) ≤
      (∑ i ∈ A, hybridX K M Good w i) +
        (((Bad.card - 1) * (hybridG K M - K) : ℕ) : ℤ) := by
  classical
  dsimp only
  let Bad := A \ Good
  let h : ℕ := hybridG K M - K
  let Q : ℕ → ℤ := fun i => hybridX K M Good w i +
    if i ∈ Bad.erase top then (h : ℤ) else 0
  let Other := (A.erase top).erase base
  have htopNotGood : top ∉ Good := by
    intro ht
    have := hGoodMax top ht
    omega
  have htopBad : top ∈ Bad := Finset.mem_sdiff.mpr ⟨htopA, htopNotGood⟩
  have htopne : top ≠ base := by
    intro heq
    subst top
    omega
  have hbaseRest : base ∈ A.erase top := Finset.mem_erase.mpr ⟨htopne.symm, hbaseA⟩
  have hOtherCard : 4 ≤ Other.card := by
    dsimp only [Other]
    rw [Finset.card_erase_of_mem hbaseRest, Finset.card_erase_of_mem htopA]
    omega
  have hQtop : Q top = (K : ℤ) := by
    simp only [Q, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      ↓reduceIte, hybridX, hybridG, hybridA, htopw,
      if_neg htopNotGood, if_pos hMK, add_zero]
    omega
  have hQbase : Q base = (M : ℤ) := by
    have hbaseNotBad : base ∉ Bad := by
      intro hb
      exact (Finset.mem_sdiff.mp hb).2 hbase
    simp only [Q, Finset.mem_erase, hbaseNotBad, and_false, ↓reduceIte,
      high_X_base hMK hMhigh hbase hbasew, add_zero]
  have hQregular : ∀ i ∈ Other, (K : ℤ) ≤ 2 * Q i := by
    intro i hi
    have hiRest := Finset.mem_of_mem_erase hi
    have hiA := Finset.mem_of_mem_erase hiRest
    have hiNotTop : i ≠ top := (Finset.mem_erase.mp hiRest).1
    by_cases hiG : i ∈ Good
    · have hiNotBad : i ∉ Bad := by
        intro hb
        exact (Finset.mem_sdiff.mp hb).2 hiG
      simp only [Q, Finset.mem_erase, hiNotBad, and_false, ↓reduceIte, add_zero]
      exact high_X_regular_good (hmax i hiA) hiG
    · have hiBad : i ∈ Bad := Finset.mem_sdiff.mpr ⟨hiA, hiG⟩
      have hiBadErase : i ∈ Bad.erase top :=
        Finset.mem_erase.mpr ⟨hiNotTop, hiBad⟩
      simp only [Q, hiBadErase, ↓reduceIte, h]
      exact high_X_regular_bad hMhigh (hmax i hiA) hiG (hBadHigh i hiA hiG)
  have hQsumOther :
      (Other.card : ℤ) * (K : ℤ) ≤ 2 * ∑ i ∈ Other, Q i := by
    have hs : (∑ _i ∈ Other, (K : ℤ)) ≤ ∑ i ∈ Other, 2 * Q i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hQregular i hi
    simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm] using hs
  have hQsplit : (∑ i ∈ A, Q i) =
      Q top + Q base + ∑ i ∈ Other, Q i := by
    have ht := Finset.sum_erase_add A Q htopA
    have hb := Finset.sum_erase_add (A.erase top) Q hbaseRest
    dsimp only [Other]
    omega
  have hQlower : 3 * (K : ℤ) ≤ ∑ i ∈ A, Q i := by
    rw [hQsplit, hQtop, hQbase]
    have hc : (4 : ℤ) ≤ Other.card := by exact_mod_cast hOtherCard
    nlinarith
  have hBadEraseSubA : Bad.erase top ⊆ A := by
    intro i hi
    exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hi)).1
  have hfilter : A.filter (fun i => i ∈ Bad.erase top) = Bad.erase top := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi => hi.2
    · exact fun hi => ⟨hBadEraseSubA hi, hi⟩
  have hQsum : (∑ i ∈ A, Q i) =
      (∑ i ∈ A, hybridX K M Good w i) +
        (((Bad.card - 1) * h : ℕ) : ℤ) := by
    simp only [Q, Finset.sum_add_distrib]
    rw [← Finset.sum_filter, hfilter]
    simp only [Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem htopBad]
    exact_mod_cast rfl
  rw [hQsum] at hQlower
  simpa only [Bad, h] using hQlower

def zMargin (K M : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ) (i : ℕ) : ℤ :=
  hybridX K M Good w i + starMargin K w i

def weightedMargin (K M : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ) (i : ℕ) : ℤ :=
  2 * hybridX K M Good w i + 3 * starMargin K w i

lemma weightedMargin_regular {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hi : w i ≤ K) (hreg : i ∈ Good ∨ M < w i) :
    2 * (K : ℤ) ≤ weightedMargin K M Good w i := by
  simp only [weightedMargin, starMargin, hybridX, hybridT, hybridG,
    hybridA, pairWeight, max_eq_left hi, min_eq_right hi,
    largestPairWeight, max_def]
  rcases hreg with hiG | hiHigh
  · simp only [if_pos hiG]
    split_ifs <;> omega
  · simp only [if_pos hiHigh]
    split_ifs <;> omega

lemma zMargin_good_lower {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i : ℕ}
    (hi : w i ≤ K) (hiG : i ∈ Good) :
    (K : ℤ) ≤ zMargin K M Good w i := by
  simp only [zMargin, starMargin, hybridX, hybridT, hybridG, hybridA,
    if_pos hiG, pairWeight, max_eq_left hi, min_eq_right hi,
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma zMargin_regular_two_thirds {K M : ℕ} {Good : Finset ℕ}
    {w : ℕ → ℕ} {i : ℕ} (hi : w i ≤ K)
    (hreg : i ∈ Good ∨ M < w i) :
    2 * (K : ℤ) ≤ 3 * zMargin K M Good w i := by
  rcases hreg with hiG | hiHigh
  · have h := zMargin_good_lower (M := M) hi hiG
    omega
  · simp only [zMargin, starMargin, hybridX, hybridT, hybridG,
      hybridA, pairWeight, max_eq_left hi, min_eq_right hi,
      largestPairWeight, max_def, if_pos hiHigh]
    split_ifs <;> omega

lemma zMargin_regular_middle {K M : ℕ} {Good : Finset ℕ}
    {w : ℕ → ℕ} {i : ℕ} (hi : w i ≤ K)
    (hMK : 2 * K < 3 * M) (hMhi : 4 * M < 3 * K)
    (hreg : i ∈ Good ∨ M < w i) :
    (4 * M : ℤ) - 2 * K ≤ zMargin K M Good w i := by
  rcases hreg with hiG | hiHigh
  · have h := zMargin_good_lower (M := M) hi hiG
    omega
  · simp only [zMargin, starMargin, hybridX, hybridT, hybridG,
      hybridA, pairWeight, max_eq_left hi, min_eq_right hi,
      largestPairWeight, max_def, if_pos hiHigh]
    split_ifs <;> omega

lemma zMargin_regular_high {K M : ℕ} {Good : Finset ℕ}
    {w : ℕ → ℕ} {i : ℕ} (hi : w i ≤ K)
    (hMhigh : 3 * K ≤ 4 * M) (hreg : i ∈ Good ∨ M < w i) :
    (K : ℤ) ≤ zMargin K M Good w i := by
  rcases hreg with hiG | hiHigh
  · exact zMargin_good_lower (M := M) hi hiG
  · simp only [zMargin, starMargin, hybridX, hybridT, hybridG,
      hybridA, pairWeight, max_eq_left hi, min_eq_right hi,
      largestPairWeight, max_def, if_pos hiHigh]
    split_ifs <;> omega

lemma zMargin_nonneg_low_regime {K M : ℕ} {Good : Finset ℕ}
    {w : ℕ → ℕ} {i : ℕ} (hi : w i ≤ K) (hMlow : 6 * M ≤ 5 * K)
    (hGoodMax : i ∈ Good → w i ≤ M) :
    0 ≤ zMargin K M Good w i := by
  by_cases hiG : i ∈ Good
  · have h := zMargin_good_lower (M := M) hi hiG
    omega
  · by_cases hiHigh : M < w i
    · have h := zMargin_regular_two_thirds (Good := Good) hi (Or.inr hiHigh)
      omega
    · simp only [zMargin, starMargin, hybridX, hybridT, hybridG,
        hybridA, if_neg hiG, if_neg hiHigh, add_zero, pairWeight,
        max_eq_left hi, min_eq_right hi, largestPairWeight, max_def]
      split_ifs <;> omega

lemma zMargin_base_low_one_below_three_quarters
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base i : ℕ}
    (hM : 4 * M < 3 * K) (hbase : base ∈ Good) (hbasew : w base = M)
    (hiG : i ∉ Good) (hiw : w i ≤ M) :
    2 * (K : ℤ) ≤ zMargin K M Good w base + zMargin K M Good w i := by
  have hiHigh : ¬M < w i := by omega
  simp only [zMargin, starMargin, hybridX, hybridT, hybridG, hybridA,
    hbasew, if_pos hbase, if_neg hiG, if_neg hiHigh, add_zero,
    pairWeight, max_eq_left (by omega : M ≤ K), min_eq_right (by omega : M ≤ K),
    max_eq_left (by omega : w i ≤ K), min_eq_right (by omega : w i ≤ K),
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma zMargin_base_low_two_first
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base i j : ℕ}
    (hM : 3 * M ≤ 2 * K) (hbase : base ∈ Good) (hbasew : w base = M)
    (hiG : i ∉ Good) (hiw : w i ≤ M)
    (hjG : j ∉ Good) (hjw : w j ≤ M) :
    8 * (K : ℤ) ≤ 3 * (zMargin K M Good w base +
      zMargin K M Good w i + zMargin K M Good w j) := by
  have hiHigh : ¬M < w i := by omega
  have hjHigh : ¬M < w j := by omega
  simp only [zMargin, starMargin, hybridX, hybridT, hybridG, hybridA,
    hbasew, if_pos hbase, if_neg hiG, if_neg hjG,
    if_neg hiHigh, if_neg hjHigh, add_zero, pairWeight,
    max_eq_left (by omega : M ≤ K), min_eq_right (by omega : M ≤ K),
    max_eq_left (by omega : w i ≤ K), min_eq_right (by omega : w i ≤ K),
    max_eq_left (by omega : w j ≤ K), min_eq_right (by omega : w j ≤ K),
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma zMargin_base_low_two_middle
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base i j : ℕ}
    (hMlo : 2 * K < 3 * M) (hMhi : 4 * M < 3 * K)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hiG : i ∉ Good) (hiw : w i ≤ M)
    (hjG : j ∉ Good) (hjw : w j ≤ M) :
    (4 * K : ℤ) - 2 * M ≤ zMargin K M Good w base +
      zMargin K M Good w i + zMargin K M Good w j := by
  have hiHigh : ¬M < w i := by omega
  have hjHigh : ¬M < w j := by omega
  simp only [zMargin, starMargin, hybridX, hybridT, hybridG, hybridA,
    hbasew, if_pos hbase, if_neg hiG, if_neg hjG,
    if_neg hiHigh, if_neg hjHigh, add_zero, pairWeight,
    max_eq_left (by omega : M ≤ K), min_eq_right (by omega : M ≤ K),
    max_eq_left (by omega : w i ≤ K), min_eq_right (by omega : w i ≤ K),
    max_eq_left (by omega : w j ≤ K), min_eq_right (by omega : w j ≤ K),
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma zMargin_base_low_one_high
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base i : ℕ}
    (hMlo : 3 * K ≤ 4 * M) (hMhi : 6 * M ≤ 5 * K)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hiG : i ∉ Good) (hiw : w i ≤ M) :
    (K : ℤ) ≤ zMargin K M Good w base + zMargin K M Good w i +
      ((hybridG K M - K : ℕ) : ℤ) := by
  have hiHigh : ¬M < w i := by omega
  simp only [zMargin, starMargin, hybridX, hybridT, hybridG, hybridA,
    hbasew, if_pos hbase, if_neg hiG, if_neg hiHigh, add_zero,
    pairWeight, max_eq_left (by omega : M ≤ K), min_eq_right (by omega : M ≤ K),
    max_eq_left (by omega : w i ≤ K), min_eq_right (by omega : w i ≤ K),
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma zMargin_base_low_two_high
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base i j : ℕ}
    (hMlo : 3 * K ≤ 4 * M) (hMhi : 6 * M ≤ 5 * K)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hiG : i ∉ Good) (hiw : w i ≤ M)
    (hjG : j ∉ Good) (hjw : w j ≤ M) :
    2 * (K : ℤ) ≤ zMargin K M Good w base +
      zMargin K M Good w i + zMargin K M Good w j +
      2 * ((hybridG K M - K : ℕ) : ℤ) := by
  have hiHigh : ¬M < w i := by omega
  have hjHigh : ¬M < w j := by omega
  simp only [zMargin, starMargin, hybridX, hybridT, hybridG, hybridA,
    hbasew, if_pos hbase, if_neg hiG, if_neg hjG,
    if_neg hiHigh, if_neg hjHigh, add_zero, pairWeight,
    max_eq_left (by omega : M ≤ K), min_eq_right (by omega : M ≤ K),
    max_eq_left (by omega : w i ≤ K), min_eq_right (by omega : w i ≤ K),
    max_eq_left (by omega : w j ≤ K), min_eq_right (by omega : w j ≤ K),
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma low_weighted_sum_bound
    (A Good : Finset ℕ) (w : ℕ → ℕ) {M K : ℕ}
    (hcard : 6 ≤ A.card) (hmax : ∀ i ∈ A, w i ≤ K)
    (hBadHigh : ∀ i ∈ A, i ∉ Good → M < w i) :
    12 * (K : ℤ) ≤ ∑ i ∈ A, weightedMargin K M Good w i := by
  have hs : (∑ _i ∈ A, 2 * (K : ℤ)) ≤
      ∑ i ∈ A, weightedMargin K M Good w i := by
    apply Finset.sum_le_sum
    intro i hi
    have hreg : i ∈ Good ∨ M < w i := by
      by_cases hiG : i ∈ Good
      · exact Or.inl hiG
      · exact Or.inr (hBadHigh i hi hiG)
    exact weightedMargin_regular (hmax i hi) hreg
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hc : (6 : ℤ) ≤ A.card := by exact_mod_cast hcard
  nlinarith

lemma starMargin_base_low_three
    {K M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base i j k : ℕ}
    (hMlow : 6 * M ≤ 5 * K)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hiG : i ∉ Good) (hiw : w i ≤ M)
    (hjG : j ∉ Good) (hjw : w j ≤ M)
    (hkG : k ∉ Good) (hkw : w k ≤ M) :
    2 * (K : ℤ) ≤ starMargin K w base + starMargin K w i +
      starMargin K w j + starMargin K w k := by
  simp only [starMargin, hybridT, hbasew, pairWeight,
    max_eq_left (by omega : M ≤ K), min_eq_right (by omega : M ≤ K),
    max_eq_left (by omega : w i ≤ K), min_eq_right (by omega : w i ≤ K),
    max_eq_left (by omega : w j ≤ K), min_eq_right (by omega : w j ≤ K),
    max_eq_left (by omega : w k ≤ K), min_eq_right (by omega : w k ≤ K),
    largestPairWeight, max_def]
  split_ifs <;> omega

lemma low_star_sum_bound
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base M K : ℕ}
    (hbaseA : base ∈ A) (hbase : base ∈ Good) (hbasew : w base = M)
    (hMlow : 6 * M ≤ 5 * K) (hmax : ∀ i ∈ A, w i ≤ K)
    (hLow3 : 3 ≤ (A.filter fun i => i ∉ Good ∧ w i ≤ M).card) :
    2 * (K : ℤ) ≤ ∑ i ∈ A, starMargin K w i := by
  classical
  let Low := A.filter fun i => i ∉ Good ∧ w i ≤ M
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hLow3
  obtain ⟨i, j, k, hij, hik, hjk, hSeq⟩ := Finset.card_eq_three.mp hScard
  have hiLow : i ∈ Low := hS (by simp [hSeq])
  have hjLow : j ∈ Low := hS (by simp [hSeq])
  have hkLow : k ∈ Low := hS (by simp [hSeq])
  have hi := (Finset.mem_filter.mp hiLow).2
  have hj := (Finset.mem_filter.mp hjLow).2
  have hk := (Finset.mem_filter.mp hkLow).2
  have hbaseNotS : base ∉ S := by
    intro hb
    have hbLow := hS hb
    exact (Finset.mem_filter.mp hbLow).2.1 hbase
  have htuple := starMargin_base_low_three hMlow hbase hbasew
    hi.1 hi.2 hj.1 hj.2 hk.1 hk.2
  have htupleSum : starMargin K w base + starMargin K w i +
      starMargin K w j + starMargin K w k =
      ∑ z ∈ insert base S, starMargin K w z := by
    rw [Finset.sum_insert hbaseNotS, hSeq]
    simp [hij, hik, hjk]
    ring
  have hsub : insert base S ⊆ A := by
    intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hbaseA
    · exact (Finset.mem_filter.mp (hS hz)).1
  have hnonneg : ∀ z ∈ A, 0 ≤ starMargin K w z := by
    intro z hz
    exact starMargin_nonneg (hmax z hz)
  have hsumle : (∑ z ∈ insert base S, starMargin K w z) ≤
      ∑ z ∈ A, starMargin K w z :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro z hz hznot
      exact hnonneg z hz)
  rw [← htupleSum] at hsumle
  exact htuple.trans hsumle

lemma low_z_sum_bound_one
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top M K : ℕ}
    (hcard : 6 ≤ A.card) (hGoodSub : Good ⊆ A)
    (hbaseA : base ∈ A) (htopA : top ∈ A)
    (hbase : base ∈ Good) (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hMlow : 6 * M ≤ 5 * K)
    (hmax : ∀ i ∈ A, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M)
    (hLowCard : (A.filter fun i => i ∉ Good ∧ w i ≤ M).card = 1) :
    let Bad := A \ Good
    5 * (K : ℤ) ≤ (∑ i ∈ A, zMargin K M Good w i) +
      (((Bad.card - 1) * (hybridG K M - K) : ℕ) : ℤ) := by
  classical
  dsimp only
  let Bad := A \ Good
  let Low := A.filter fun i => i ∉ Good ∧ w i ≤ M
  let Rest := (A.erase top).erase base
  let Reg := Rest \ Low
  obtain ⟨i, hLowEq⟩ := Finset.card_eq_one.mp hLowCard
  have hiLow : i ∈ Low := by simp [Low, hLowEq]
  have hi := (Finset.mem_filter.mp hiLow).2
  have hiA := (Finset.mem_filter.mp hiLow).1
  have htopNotGood : top ∉ Good := by
    intro ht
    have := hGoodMax top ht
    omega
  have htopBad : top ∈ Bad := Finset.mem_sdiff.mpr ⟨htopA, htopNotGood⟩
  have htopNotLow : top ∉ Low := by
    intro ht
    have := (Finset.mem_filter.mp ht).2.2
    omega
  have htopne : top ≠ base := by
    intro heq
    subst top
    omega
  have hbaseRest0 : base ∈ A.erase top :=
    Finset.mem_erase.mpr ⟨htopne.symm, hbaseA⟩
  have hbaseNotLow : base ∉ Low := by
    intro hb
    exact (Finset.mem_filter.mp hb).2.1 hbase
  have hLowSubRest : Low ⊆ Rest := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_erase.mpr ⟨by
      intro heq
      subst z
      exact hbaseNotLow hz, Finset.mem_erase.mpr ⟨by
        intro heq
        subst z
        exact htopNotLow hz, hz'.1⟩⟩
  have hpartRest : Low ∪ Reg = Rest := by
    dsimp only [Reg]
    exact Finset.union_sdiff_of_subset hLowSubRest
  have hdisj : Disjoint Low Reg := Finset.disjoint_sdiff
  have hRegCard : 3 ≤ Reg.card := by
    have hRestCard : Rest.card = A.card - 2 := by
      dsimp only [Rest]
      rw [Finset.card_erase_of_mem hbaseRest0, Finset.card_erase_of_mem htopA]
      omega
    have hcardReg : Reg.card = Rest.card - Low.card := by
      dsimp only [Reg]
      exact Finset.card_sdiff_of_subset hLowSubRest
    rw [hcardReg, hRestCard]
    have : Low.card = 1 := by simpa only [Low] using hLowCard
    omega
  have hreg : ∀ z ∈ Reg, z ∈ Good ∨ M < w z := by
    intro z hz
    have hzRest := Finset.mem_sdiff.mp hz
    have hzA := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzRest.1)
    by_cases hzG : z ∈ Good
    · exact Or.inl hzG
    · right
      by_contra hn
      exact hzRest.2 (Finset.mem_filter.mpr ⟨hzA, hzG, by omega⟩)
  have hztop : zMargin K M Good w top = (K : ℤ) := by
    simp only [zMargin, starMargin, hybridX, hybridT, hybridG, hybridA,
      htopw, if_neg htopNotGood, if_pos hMK, add_zero, pairWeight_self]
    omega
  have hsumSplit : (∑ z ∈ A, zMargin K M Good w z) =
      zMargin K M Good w top + zMargin K M Good w base +
        (∑ z ∈ Low, zMargin K M Good w z) +
          ∑ z ∈ Reg, zMargin K M Good w z := by
    have ht := Finset.sum_erase_add A (zMargin K M Good w) htopA
    have hb := Finset.sum_erase_add (A.erase top) (zMargin K M Good w) hbaseRest0
    have hp := Finset.sum_union hdisj (f := zMargin K M Good w)
    rw [hpartRest] at hp
    dsimp only [Rest] at hp ⊢
    omega
  have hBadTwo : 2 ≤ Bad.card := by
    have hsub : insert top {i} ⊆ Bad := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact htopBad
      · exact Finset.mem_sdiff.mpr ⟨hiA, hi.1⟩
    have hc := Finset.card_le_card hsub
    have hit : i ≠ top := by
      intro heq
      subst i
      omega
    have hpaircard : (insert top {i} : Finset ℕ).card = 2 := by
      simp [hit.symm]
    omega
  have hh : ((hybridG K M - K : ℕ) : ℤ) ≤
      (((Bad.card - 1) * (hybridG K M - K) : ℕ) : ℤ) := by
    exact_mod_cast (show hybridG K M - K ≤
      (Bad.card - 1) * (hybridG K M - K) by
        have : 1 ≤ Bad.card - 1 := by omega
        nlinarith)
  have hLowEq' : Low = {i} := by simpa only [Low] using hLowEq
  change 5 * (K : ℤ) ≤ (∑ i ∈ A, zMargin K M Good w i) +
    (((Bad.card - 1) * (hybridG K M - K) : ℕ) : ℤ)
  rw [hsumSplit, hztop, hLowEq']
  simp only [Finset.sum_singleton]
  by_cases hMthree : 4 * M < 3 * K
  · have htuple := zMargin_base_low_one_below_three_quarters
      hMthree hbase hbasew hi.1 hi.2
    have hregsum : 2 * (K : ℤ) ≤ ∑ z ∈ Reg, zMargin K M Good w z := by
      have hs : (∑ _z ∈ Reg, 2 * (K : ℤ)) ≤
          ∑ z ∈ Reg, 3 * zMargin K M Good w z := by
        apply Finset.sum_le_sum
        intro z hz
        exact zMargin_regular_two_thirds
          (hmax z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
            (Finset.mem_sdiff.mp hz).1))) (hreg z hz)
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hs
      have hc : (3 : ℤ) ≤ Reg.card := by exact_mod_cast hRegCard
      nlinarith
    nlinarith
  · have hMthree' : 3 * K ≤ 4 * M := by omega
    have htuple := zMargin_base_low_one_high hMthree' hMlow
      hbase hbasew hi.1 hi.2
    have hregsum : 3 * (K : ℤ) ≤ ∑ z ∈ Reg, zMargin K M Good w z := by
      have hs : (∑ _z ∈ Reg, (K : ℤ)) ≤
          ∑ z ∈ Reg, zMargin K M Good w z := by
        apply Finset.sum_le_sum
        intro z hz
        exact zMargin_regular_high
          (hmax z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
            (Finset.mem_sdiff.mp hz).1))) hMthree' (hreg z hz)
      simp only [Finset.sum_const, nsmul_eq_mul] at hs
      have hc : (3 : ℤ) ≤ Reg.card := by exact_mod_cast hRegCard
      nlinarith
    nlinarith

lemma low_z_sum_bound_two
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top M K : ℕ}
    (hcard : 6 ≤ A.card) (hGoodSub : Good ⊆ A)
    (hbaseA : base ∈ A) (htopA : top ∈ A)
    (hbase : base ∈ Good) (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hMlow : 6 * M ≤ 5 * K)
    (hmax : ∀ i ∈ A, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M)
    (hLowCard : (A.filter fun i => i ∉ Good ∧ w i ≤ M).card = 2) :
    let Bad := A \ Good
    5 * (K : ℤ) ≤ (∑ i ∈ A, zMargin K M Good w i) +
      (((Bad.card - 1) * (hybridG K M - K) : ℕ) : ℤ) := by
  classical
  dsimp only
  let Bad := A \ Good
  let Low := A.filter fun i => i ∉ Good ∧ w i ≤ M
  let Rest := (A.erase top).erase base
  let Reg := Rest \ Low
  obtain ⟨i, j, hij, hLowEq⟩ := Finset.card_eq_two.mp hLowCard
  have hiLow : i ∈ Low := by simp [Low, hLowEq]
  have hjLow : j ∈ Low := by simp [Low, hLowEq]
  have hi := (Finset.mem_filter.mp hiLow).2
  have hj := (Finset.mem_filter.mp hjLow).2
  have hiA := (Finset.mem_filter.mp hiLow).1
  have hjA := (Finset.mem_filter.mp hjLow).1
  have htopNotGood : top ∉ Good := by
    intro ht
    have := hGoodMax top ht
    omega
  have htopBad : top ∈ Bad := Finset.mem_sdiff.mpr ⟨htopA, htopNotGood⟩
  have htopNotLow : top ∉ Low := by
    intro ht
    have := (Finset.mem_filter.mp ht).2.2
    omega
  have htopne : top ≠ base := by
    intro heq
    subst top
    omega
  have hbaseRest0 : base ∈ A.erase top :=
    Finset.mem_erase.mpr ⟨htopne.symm, hbaseA⟩
  have hbaseNotLow : base ∉ Low := by
    intro hb
    exact (Finset.mem_filter.mp hb).2.1 hbase
  have hLowSubRest : Low ⊆ Rest := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_erase.mpr ⟨by
      intro heq
      subst z
      exact hbaseNotLow hz, Finset.mem_erase.mpr ⟨by
        intro heq
        subst z
        exact htopNotLow hz, hz'.1⟩⟩
  have hpartRest : Low ∪ Reg = Rest := by
    dsimp only [Reg]
    exact Finset.union_sdiff_of_subset hLowSubRest
  have hdisj : Disjoint Low Reg := Finset.disjoint_sdiff
  have hRegCard : 2 ≤ Reg.card := by
    have hRestCard : Rest.card = A.card - 2 := by
      dsimp only [Rest]
      rw [Finset.card_erase_of_mem hbaseRest0, Finset.card_erase_of_mem htopA]
      omega
    have hcardReg : Reg.card = Rest.card - Low.card := by
      dsimp only [Reg]
      exact Finset.card_sdiff_of_subset hLowSubRest
    rw [hcardReg, hRestCard]
    have : Low.card = 2 := by simpa only [Low] using hLowCard
    omega
  have hreg : ∀ z ∈ Reg, z ∈ Good ∨ M < w z := by
    intro z hz
    have hzRest := Finset.mem_sdiff.mp hz
    have hzA := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzRest.1)
    by_cases hzG : z ∈ Good
    · exact Or.inl hzG
    · right
      by_contra hn
      exact hzRest.2 (Finset.mem_filter.mpr ⟨hzA, hzG, by omega⟩)
  have hztop : zMargin K M Good w top = (K : ℤ) := by
    simp only [zMargin, starMargin, hybridX, hybridT, hybridG, hybridA,
      htopw, if_neg htopNotGood, if_pos hMK, add_zero, pairWeight_self]
    omega
  have hsumSplit : (∑ z ∈ A, zMargin K M Good w z) =
      zMargin K M Good w top + zMargin K M Good w base +
        (∑ z ∈ Low, zMargin K M Good w z) +
          ∑ z ∈ Reg, zMargin K M Good w z := by
    have ht := Finset.sum_erase_add A (zMargin K M Good w) htopA
    have hb := Finset.sum_erase_add (A.erase top) (zMargin K M Good w) hbaseRest0
    have hp := Finset.sum_union hdisj (f := zMargin K M Good w)
    rw [hpartRest] at hp
    dsimp only [Rest] at hp ⊢
    omega
  have hBadThree : 3 ≤ Bad.card := by
    have hsub : insert top {i, j} ⊆ Bad := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact htopBad
      · exact Finset.mem_sdiff.mpr ⟨hiA, hi.1⟩
      · exact Finset.mem_sdiff.mpr ⟨hjA, hj.1⟩
    have hc := Finset.card_le_card hsub
    have hit : i ≠ top := by intro heq; subst i; omega
    have hjt : j ≠ top := by intro heq; subst j; omega
    have hpaircard : (insert top {i, j} : Finset ℕ).card = 3 := by
      simp [hij, hit.symm, hjt.symm]
    omega
  have hh : 2 * ((hybridG K M - K : ℕ) : ℤ) ≤
      (((Bad.card - 1) * (hybridG K M - K) : ℕ) : ℤ) := by
    exact_mod_cast (show 2 * (hybridG K M - K) ≤
      (Bad.card - 1) * (hybridG K M - K) by
        have : 2 ≤ Bad.card - 1 := by omega
        nlinarith)
  have hLowEq' : Low = {i, j} := by simpa only [Low] using hLowEq
  change 5 * (K : ℤ) ≤ (∑ i ∈ A, zMargin K M Good w i) +
    (((Bad.card - 1) * (hybridG K M - K) : ℕ) : ℤ)
  rw [hsumSplit, hztop, hLowEq']
  have hijmem : i ∉ ({j} : Finset ℕ) := by simpa using hij
  rw [Finset.sum_insert hijmem, Finset.sum_singleton]
  rcases le_or_gt (3 * M) (2 * K) with hMfirst | hMfirst
  · have htuple := zMargin_base_low_two_first hMfirst hbase hbasew
      hi.1 hi.2 hj.1 hj.2
    have hregsum : 4 * (K : ℤ) ≤
        3 * ∑ z ∈ Reg, zMargin K M Good w z := by
      have hs : (∑ _z ∈ Reg, 2 * (K : ℤ)) ≤
          ∑ z ∈ Reg, 3 * zMargin K M Good w z := by
        apply Finset.sum_le_sum
        intro z hz
        exact zMargin_regular_two_thirds
          (hmax z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
            (Finset.mem_sdiff.mp hz).1))) (hreg z hz)
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hs
      have hc : (2 : ℤ) ≤ Reg.card := by exact_mod_cast hRegCard
      nlinarith
    nlinarith
  · rcases lt_or_ge (4 * M) (3 * K) with hMmiddle | hMhigh
    · have htuple := zMargin_base_low_two_middle hMfirst hMmiddle
        hbase hbasew hi.1 hi.2 hj.1 hj.2
      have hregsum : 2 * ((4 * M : ℤ) - 2 * K) ≤
          ∑ z ∈ Reg, zMargin K M Good w z := by
        have hs : (∑ _z ∈ Reg, ((4 * M : ℤ) - 2 * K)) ≤
            ∑ z ∈ Reg, zMargin K M Good w z := by
          apply Finset.sum_le_sum
          intro z hz
          exact zMargin_regular_middle
            (hmax z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
              (Finset.mem_sdiff.mp hz).1))) hMfirst hMmiddle (hreg z hz)
        simp only [Finset.sum_const, nsmul_eq_mul] at hs
        have hc : (2 : ℤ) ≤ Reg.card := by exact_mod_cast hRegCard
        have hp : 0 ≤ (4 * M : ℤ) - 2 * K := by omega
        nlinarith
      nlinarith
    · have htuple := zMargin_base_low_two_high hMhigh hMlow
        hbase hbasew hi.1 hi.2 hj.1 hj.2
      have hregsum : 2 * (K : ℤ) ≤
          ∑ z ∈ Reg, zMargin K M Good w z := by
        have hs : (∑ _z ∈ Reg, (K : ℤ)) ≤
            ∑ z ∈ Reg, zMargin K M Good w z := by
          apply Finset.sum_le_sum
          intro z hz
          exact zMargin_regular_high
            (hmax z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
              (Finset.mem_sdiff.mp hz).1))) hMhigh (hreg z hz)
        simp only [Finset.sum_const, nsmul_eq_mul] at hs
        have hc : (2 : ℤ) ≤ Reg.card := by exact_mod_cast hRegCard
        nlinarith
      nlinarith

lemma mixed_average_to_three {s S K C AA B : ℕ}
    (h : 9 * (S : ℤ) ≤ 6 * ((s - 1 : ℕ) : ℤ) * K + 2 * C + AA)
    (hC : C ≤ B) (hAA : AA ≤ B) :
    3 * S ≤ 2 * (s - 1) * K + B := by
  have hCz : (C : ℤ) ≤ B := by exact_mod_cast hC
  have hAAz : (AA : ℤ) ≤ B := by exact_mod_cast hAA
  let R : ℤ := 2 * ((s - 1 : ℕ) : ℤ) * K
  have h' : 9 * (S : ℤ) ≤ 3 * R + 2 * C + AA := by
    dsimp only [R]
    convert h using 1 <;> ring
  have hz : 3 * (S : ℤ) ≤ 2 * ((s - 1 : ℕ) : ℤ) * K + B := by
    change 3 * (S : ℤ) ≤ R + B
    omega
  exact_mod_cast hz

lemma weighted_average_to_three {s S K AA T B : ℕ}
    (h : 15 * (S : ℤ) ≤ 10 * ((s - 1 : ℕ) : ℤ) * K + 2 * AA + 3 * T)
    (hAA : AA ≤ B) (hT : T ≤ B) :
    3 * S ≤ 2 * (s - 1) * K + B := by
  have hAAz : (AA : ℤ) ≤ B := by exact_mod_cast hAA
  have hTz : (T : ℤ) ≤ B := by exact_mod_cast hT
  let R : ℤ := 2 * ((s - 1 : ℕ) : ℤ) * K
  have h' : 15 * (S : ℤ) ≤ 5 * R + 2 * AA + 3 * T := by
    dsimp only [R]
    convert h using 1 <;> ring
  have hz : 3 * (S : ℤ) ≤ 2 * ((s - 1 : ℕ) : ℤ) * K + B := by
    change 3 * (S : ℤ) ≤ R + B
    omega
  exact_mod_cast hz

lemma two_average_to_three {s S K AA T B : ℕ}
    (h : 6 * (S : ℤ) ≤ 4 * ((s - 1 : ℕ) : ℤ) * K + AA + T)
    (hAA : AA ≤ B) (hT : T ≤ B) :
    3 * S ≤ 2 * (s - 1) * K + B := by
  have hAAz : (AA : ℤ) ≤ B := by exact_mod_cast hAA
  have hTz : (T : ℤ) ≤ B := by exact_mod_cast hT
  let R : ℤ := 2 * ((s - 1 : ℕ) : ℤ) * K
  have h' : 6 * (S : ℤ) ≤ 2 * R + AA + T := by
    dsimp only [R]
    convert h using 1 <;> ring
  have hz : 3 * (S : ℤ) ≤ 2 * ((s - 1 : ℕ) : ℤ) * K + B := by
    change 3 * (S : ℤ) ≤ R + B
    omega
  exact_mod_cast hz

lemma star_sum_to_three {s S K T B : ℕ} (hs : 1 ≤ s)
    (h : 2 * (K : ℤ) ≤ 2 * (s : ℤ) * K - 3 * S + T)
    (hT : T ≤ B) :
    3 * S ≤ 2 * (s - 1) * K + B := by
  have hTz : (T : ℤ) ≤ B := by exact_mod_cast hT
  let R : ℤ := 2 * ((s - 1 : ℕ) : ℤ) * K
  have hR : R = 2 * (s : ℤ) * K - 2 * K := by
    dsimp only [R]
    rw [Nat.cast_sub hs]
    norm_num
    ring
  have h' : 3 * (S : ℤ) ≤ R + T := by
    rw [hR]
    omega
  have hz : 3 * (S : ℤ) ≤ 2 * ((s - 1 : ℕ) : ℤ) * K + B := by
    change 3 * (S : ℤ) ≤ R + B
    omega
  exact_mod_cast hz

lemma weighted_sum_expansion_to_three
    {s S K G AH T H AA B : ℕ} (hs : 1 ≤ s)
    (hw : 12 * (K : ℤ) ≤
      2 * (2 * (s : ℤ) * K - 3 * S + G + 2 * AH) +
        3 * (2 * (s : ℤ) * K - 3 * S + T))
    (hAA : (AA : ℤ) = G + H + (2 * (AH : ℤ) - K))
    (hH : 0 ≤ (H : ℤ)) (hAAB : AA ≤ B) (hTB : T ≤ B) :
    3 * S ≤ 2 * (s - 1) * K + B := by
  have hbase : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by
    rw [Nat.cast_sub hs]
    norm_num
  have hfive : 15 * (S : ℤ) ≤
      10 * ((s - 1 : ℕ) : ℤ) * K + 2 * AA + 3 * T := by
    rw [hbase, hAA]
    ring_nf at hw ⊢
    omega
  exact weighted_average_to_three hfive hAAB hTB

lemma z_sum_expansion_to_three
    {s S K G AH T H AA B : ℕ} (hs : 1 ≤ s)
    (hz : 5 * (K : ℤ) ≤
      (2 * (s : ℤ) * K - 3 * S + G + 2 * AH) +
        (2 * (s : ℤ) * K - 3 * S + T) + H)
    (hAA : (AA : ℤ) = G + H + (2 * (AH : ℤ) - K))
    (hAAB : AA ≤ B) (hTB : T ≤ B) :
    3 * S ≤ 2 * (s - 1) * K + B := by
  have hbase : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by
    rw [Nat.cast_sub hs]
    norm_num
  have hsix : 6 * (S : ℤ) ≤
      4 * ((s - 1 : ℕ) : ℤ) * K + AA + T := by
    rw [hbase, hAA]
    ring_nf at hz ⊢
    omega
  exact two_average_to_three hsix hAAB hTB

lemma hybrid_three_branch_arithmetic
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top M K : ℕ}
    (hcard : 6 ≤ A.card) (hGoodSub : Good ⊆ A)
    (hbaseA : base ∈ A) (htopA : top ∈ A)
    (hbase : base ∈ Good) (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hmax : ∀ i ∈ A, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M) :
    let Bad := A \ Good
    let G := ∑ i ∈ Good, hybridG K (w i)
    let AH := ∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i)
    let T := ∑ i ∈ A, hybridT K (w i)
    let C := G + (Bad.card - 1) * hybridG K M
    let AA := G + (Bad.card - 1) * (hybridG K M - K) + (2 * AH - K)
    5 * (∑ i ∈ A, w i) ≤
      2 * ((∑ i ∈ A, w i) + (A.card - 1) * K) +
        max C (max AA T) := by
  classical
  dsimp only
  let Bad := A \ Good
  let Low := A.filter fun i => i ∉ Good ∧ w i ≤ M
  let S := ∑ i ∈ A, w i
  let G := ∑ i ∈ Good, hybridG K (w i)
  let AH := ∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i)
  let T := ∑ i ∈ A, hybridT K (w i)
  let C := G + (Bad.card - 1) * hybridG K M
  let AA := G + (Bad.card - 1) * (hybridG K M - K) + (2 * AH - K)
  let B := max C (max AA T)
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
  have hcardPos : 1 ≤ A.card := by omega
  have hKleTwoAH : K ≤ 2 * AH := by omega
  have hGoodFilter : A.filter (fun i => i ∈ Good) = Good := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi => hi.2
    · exact fun hi => ⟨hGoodSub hi, hi⟩
  have hsumGood : (∑ i ∈ A,
      if i ∈ Good then (hybridG K (w i) : ℤ) else 0) = (G : ℤ) := by
    rw [← Finset.sum_filter, hGoodFilter]
    exact_mod_cast rfl
  have hsumHigh : (∑ i ∈ A,
      if M < w i then 2 * (hybridA K (w i) : ℤ) else 0) = 2 * (AH : ℤ) := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    exact_mod_cast rfl
  have hsumT : (∑ i ∈ A, (hybridT K (w i) : ℤ)) = (T : ℤ) := by
    exact_mod_cast rfl
  have hsumS : (∑ i ∈ A, (w i : ℤ)) = (S : ℤ) := by
    exact_mod_cast rfl
  have hsumCross : (∑ i ∈ A, crossMargin K Good w i) =
      2 * (A.card : ℤ) * K - 3 * (S : ℤ) + G := by
    simp only [crossMargin, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hsumGood, hsumS]
    ring
  have hsumX : (∑ i ∈ A, hybridX K M Good w i) =
      2 * (A.card : ℤ) * K - 3 * (S : ℤ) + G + 2 * AH := by
    simp only [hybridX, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hsumGood, hsumHigh, hsumS]
    ring
  have hsumStar : (∑ i ∈ A, starMargin K w i) =
      2 * (A.card : ℤ) * K - 3 * (S : ℤ) + T := by
    simp only [starMargin, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hsumT, hsumS]
    ring
  have hsumMixed : (∑ i ∈ A, mixedMargin K M Good w i) =
      2 * (∑ i ∈ A, crossMargin K Good w i) +
        ∑ i ∈ A, hybridX K M Good w i := by
    simp only [mixedMargin, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsumWeighted : (∑ i ∈ A, weightedMargin K M Good w i) =
      2 * (∑ i ∈ A, hybridX K M Good w i) +
        3 * ∑ i ∈ A, starMargin K w i := by
    simp only [weightedMargin, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsumZ : (∑ i ∈ A, zMargin K M Good w i) =
      (∑ i ∈ A, hybridX K M Good w i) +
        ∑ i ∈ A, starMargin K w i := by
    simp only [zMargin, Finset.sum_add_distrib]
  have hcastC : (C : ℤ) = (G : ℤ) +
      ((Bad.card - 1 : ℕ) : ℤ) * (hybridG K M : ℤ) := by
    dsimp only [C]
    push_cast only [Nat.cast_add, Nat.cast_mul]
  have hcastAA : (AA : ℤ) = (G : ℤ) +
      ((Bad.card - 1 : ℕ) : ℤ) * ((hybridG K M - K : ℕ) : ℤ) +
      (2 * (AH : ℤ) - K) := by
    dsimp only [AA]
    push_cast only [Nat.cast_add, Nat.cast_mul]
    rw [Nat.cast_sub hKleTwoAH]
    norm_num
  have hCBounds : C ≤ B := le_max_left _ _
  have hAABounds : AA ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hTBounds : T ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hthree : 3 * S ≤ 2 * (A.card - 1) * K + B := by
    by_cases hMhigh : 5 * K < 6 * M
    · have hmixed := high_mixed_sum_bound A Good w hcard hGoodSub
        hbaseA htopA hbase hbasew htopw hMK hMhigh hmax hGoodMax
      have hweighted : 9 * (S : ℤ) ≤
          6 * ((A.card - 1 : ℕ) : ℤ) * K + 2 * C + AA := by
        rw [Nat.cast_sub hcardPos]
        change 7 * (K : ℤ) ≤
          (∑ i ∈ A, mixedMargin K M Good w i) +
            (((Bad.card - 1) *
              (2 * hybridG K M + (hybridG K M - K)) : ℕ) : ℤ) at hmixed
        rw [hsumMixed, hsumCross, hsumX] at hmixed
        rw [hcastC, hcastAA]
        push_cast only [Nat.cast_add, Nat.cast_mul] at hmixed
        norm_num at hmixed ⊢
        ring_nf at hmixed ⊢
        nlinarith
      exact mixed_average_to_three hweighted hCBounds hAABounds
    · have hMlow : 6 * M ≤ 5 * K := by omega
      by_cases hLow3 : 3 ≤ Low.card
      · have hstar := low_star_sum_bound A Good w hbaseA hbase hbasew
          hMlow hmax (by simpa only [Low] using hLow3)
        rw [hsumStar] at hstar
        exact star_sum_to_three hcardPos hstar hTBounds
      · have hLowLe : Low.card ≤ 2 := by omega
        interval_cases hLc : Low.card
        · have hBadHigh : ∀ i ∈ A, i ∉ Good → M < w i := by
            intro i hiA hiG
            by_contra hn
            have hiLow : i ∈ Low := Finset.mem_filter.mpr ⟨hiA, hiG, by omega⟩
            have : Low = ∅ := Finset.card_eq_zero.mp hLc
            simpa [this] using hiLow
          have hw := low_weighted_sum_bound A Good w hcard hmax hBadHigh
          rw [hsumWeighted, hsumX, hsumStar] at hw
          let H := (Bad.card - 1) * (hybridG K M - K)
          have hcastAA' : (AA : ℤ) = G + H + (2 * (AH : ℤ) - K) := by
            rw [hcastAA]
            dsimp only [H]
            push_cast only [Nat.cast_mul]
          have hH : 0 ≤ (H : ℤ) := by positivity
          exact weighted_sum_expansion_to_three hcardPos hw hcastAA' hH
            hAABounds hTBounds
        · have hz := low_z_sum_bound_one A Good w hcard hGoodSub
            hbaseA htopA hbase hbasew htopw hMK hMlow hmax hGoodMax
            (by simpa only [Low] using hLc)
          rw [hsumZ, hsumX, hsumStar] at hz
          let H := (Bad.card - 1) * (hybridG K M - K)
          change 5 * (K : ℤ) ≤
            (2 * (A.card : ℤ) * K - 3 * S + G + 2 * AH) +
              (2 * (A.card : ℤ) * K - 3 * S + T) + (H : ℤ) at hz
          have hcastAA' : (AA : ℤ) = G + H + (2 * (AH : ℤ) - K) := by
            rw [hcastAA]
            dsimp only [H]
            push_cast only [Nat.cast_mul]
          exact z_sum_expansion_to_three hcardPos hz hcastAA'
            hAABounds hTBounds
        · have hz := low_z_sum_bound_two A Good w hcard hGoodSub
            hbaseA htopA hbase hbasew htopw hMK hMlow hmax hGoodMax
            (by simpa only [Low] using hLc)
          rw [hsumZ, hsumX, hsumStar] at hz
          let H := (Bad.card - 1) * (hybridG K M - K)
          change 5 * (K : ℤ) ≤
            (2 * (A.card : ℤ) * K - 3 * S + G + 2 * AH) +
              (2 * (A.card : ℤ) * K - 3 * S + T) + (H : ℤ) at hz
          have hcastAA' : (AA : ℤ) = G + H + (2 * (AH : ℤ) - K) := by
            rw [hcastAA]
            dsimp only [H]
            push_cast only [Nat.cast_mul]
          exact z_sum_expansion_to_three hcardPos hz hcastAA'
            hAABounds hTBounds
  dsimp only [S, B, C, AA, G, AH, T, Bad] at hthree ⊢
  calc
    5 * (∑ i ∈ A, w i) =
        2 * (∑ i ∈ A, w i) + 3 * (∑ i ∈ A, w i) := by ring
    _ ≤ 2 * (∑ i ∈ A, w i) +
        (2 * (A.card - 1) * K +
          max
            ((∑ i ∈ Good, hybridG K (w i)) +
              ((A \ Good).card - 1) * hybridG K M)
            (max
              ((∑ i ∈ Good, hybridG K (w i)) +
                ((A \ Good).card - 1) * (hybridG K M - K) +
                (2 * (∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i)) - K))
              (∑ i ∈ A, hybridT K (w i)))) :=
      Nat.add_le_add_left hthree _
    _ = _ := by ring

end Erdos360

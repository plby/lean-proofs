/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 448.

The mathematical proof and the endpoint-convention comparison with the
Erdős--Tenenbaum theorem are documented in tex/448.tex.
-/

import Util.Density

namespace Erdos448

open Filter
open scoped Topology BigOperators

/-- The number of dyadic half-open blocks occupied by divisors of n. -/
def tauPlus (n : ℕ) : ℕ :=
  (n.divisors.image (Nat.log 2)).card

/-- The upstream sanity check. -/
theorem tauPlus_six : tauPlus 6 = 3 := by
  decide

/-- The upstream sanity check. -/
theorem tauPlus_twelve : tauPlus 12 = 4 := by
  decide

/-- An image has no more elements than its source. -/
theorem tauPlus_le_tau (n : ℕ) : tauPlus n ≤ n.divisors.card :=
  Finset.card_image_le

/-- Every occupied dyadic block lies between zero and the block containing
the divisor n. -/
theorem tauPlus_le_log_add_one (n : ℕ) :
    tauPlus n ≤ Nat.log 2 n + 1 := by
  by_cases hn : n = 0
  · simp [hn, tauPlus]
  calc
    tauPlus n ≤ (Finset.range (Nat.log 2 n + 1)).card := by
      change (n.divisors.image (Nat.log 2)).card ≤
        (Finset.range (Nat.log 2 n + 1)).card
      apply Finset.card_le_card
      rw [Finset.image_subset_iff]
      intro d hd
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.log_mono_right (Nat.divisor_le hd))
    _ = Nat.log 2 n + 1 := Finset.card_range _

/-! ## Comparison with the convention in Erdős--Tenenbaum -/

/-- The nonnegative dyadic indices whose right-closed block
`(2^k, 2^(k+1)]` contains a divisor of `n`.  This is the convention used
in the 1981 paper. -/
def historicalIndices (n : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 n + 1)).filter fun k ↦
    ∃ d ∈ n.divisors, 2 ^ k < d ∧ d ≤ 2 ^ (k + 1)

theorem mem_historicalIndices_iff {n k : ℕ} :
    k ∈ historicalIndices n ↔
      ∃ d ∈ n.divisors, 2 ^ k < d ∧ d ≤ 2 ^ (k + 1) := by
  rw [historicalIndices, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with ⟨d, hd, hlower, _⟩
    have hpow_le_n : 2 ^ k ≤ n := hlower.le.trans (Nat.divisor_le hd)
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by decide) hpow_le_n)

/-- Number of historical, right-closed dyadic blocks occupied by divisors. -/
def tauPlusHistorical (n : ℕ) : ℕ :=
  (historicalIndices n).card

/-- Every historical occupied index is occupied in the formal convention.
At a right endpoint `d = 2^(k+1)`, the smaller divisor `2^k` supplies the
same formal index `k`. -/
theorem historicalIndices_subset_formal (n : ℕ) :
    historicalIndices n ⊆ n.divisors.image (Nat.log 2) := by
  intro k hk
  rw [mem_historicalIndices_iff] at hk
  rcases hk with ⟨d, hd, hlower, hupper⟩
  by_cases hstrict : d < 2 ^ (k + 1)
  · rw [Finset.mem_image]
    exact ⟨d, hd, Nat.log_eq_of_pow_le_of_lt_pow hlower.le hstrict⟩
  · have hd_eq : d = 2 ^ (k + 1) :=
      Nat.le_antisymm hupper (Nat.le_of_not_gt hstrict)
    have hn : n ≠ 0 := (Nat.mem_divisors.mp hd).2
    have hpow_dvd_n : 2 ^ k ∣ n := by
      apply dvd_trans (pow_dvd_pow 2 (Nat.le_add_right k 1))
      simpa [hd_eq] using Nat.dvd_of_mem_divisors hd
    have hpow_mem : 2 ^ k ∈ n.divisors :=
      Nat.mem_divisors.mpr ⟨hpow_dvd_n, hn⟩
    rw [Finset.mem_image]
    exact ⟨2 ^ k, hpow_mem, Nat.log_pow (by decide) k⟩

/-- The favorable endpoint comparison needed to transfer the 1981 theorem. -/
theorem tauPlusHistorical_le_tauPlus (n : ℕ) :
    tauPlusHistorical n ≤ tauPlus n := by
  exact Finset.card_le_card (historicalIndices_subset_formal n)

/-! ## The finite Cauchy--Schwarz reduction -/

/-- The sum of squared occupancies of the fibres of `block` on `D`. -/
def occupiedBinEnergy
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (D : Finset α) (block : α → β) : ℕ :=
  ∑ b ∈ D.image block, (D.filter fun a => block a = b).card ^ 2

/-- The number of unordered off-diagonal pairs in common occupied bins. -/
def sameBinUnorderedPairCount
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (D : Finset α) (block : α → β) : ℕ :=
  ∑ b ∈ D.image block,
    (D.filter fun a => block a = b).card.choose 2

private theorem nat_sq_eq_self_add_two_mul_choose_two (m : ℕ) :
    m ^ 2 = m + 2 * m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        m.succ ^ 2 = m ^ 2 + 2 * m + 1 := by
          simp only [Nat.succ_eq_add_one]
          ring
        _ = (m + 2 * m.choose 2) + 2 * m + 1 := by rw [ih]
        _ = m.succ + 2 * m.succ.choose 2 := by
          rw [show (2 : ℕ) = Nat.succ 1 by rfl, Nat.choose_succ_succ,
            Nat.choose_one_right]
          simp only [Nat.succ_eq_add_one]
          ring

theorem occupiedBinEnergy_eq_card_add_two_mul_unorderedPairCount
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (D : Finset α) (block : α → β) :
    occupiedBinEnergy D block =
      D.card + 2 * sameBinUnorderedPairCount D block := by
  rw [occupiedBinEnergy, sameBinUnorderedPairCount]
  simp_rw [nat_sq_eq_self_add_two_mul_choose_two]
  rw [Finset.sum_add_distrib]
  rw [← Finset.card_eq_sum_card_image block D]
  rw [Finset.mul_sum]

/-- Cauchy--Schwarz for the nonempty fibres of a map on a finite set. -/
theorem card_sq_le_card_image_mul_occupiedBinEnergy
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (D : Finset α) (block : α → β) :
    D.card ^ 2 ≤ (D.image block).card * occupiedBinEnergy D block := by
  rw [Finset.card_eq_sum_card_image block D]
  exact sq_sum_le_card_mul_sum_sq

theorem finite_bin_ratio_step
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (D : Finset α) (block : α → β) (hD : D.Nonempty) :
    (D.card : ℝ) / (D.image block).card ≤
      1 + 2 * (sameBinUnorderedPairCount D block : ℝ) / D.card := by
  have hDcard : (0 : ℝ) < D.card := by
    exact_mod_cast (Finset.card_pos.mpr hD)
  have hImage : (0 : ℝ) < (D.image block).card := by
    exact_mod_cast (Finset.card_pos.mpr (hD.image block))
  have hmainNat : D.card ^ 2 ≤ (D.image block).card *
      (D.card + 2 * sameBinUnorderedPairCount D block) := by
    calc
      D.card ^ 2 ≤ (D.image block).card * occupiedBinEnergy D block :=
        card_sq_le_card_image_mul_occupiedBinEnergy D block
      _ = (D.image block).card *
          (D.card + 2 * sameBinUnorderedPairCount D block) := by
        rw [occupiedBinEnergy_eq_card_add_two_mul_unorderedPairCount]
  have hmain : (D.card : ℝ) ^ 2 ≤ (D.image block).card *
      (D.card + 2 * sameBinUnorderedPairCount D block) := by
    exact_mod_cast hmainNat
  rw [show (1 : ℝ) +
      2 * (sameBinUnorderedPairCount D block : ℝ) / D.card =
      (D.card + 2 * sameBinUnorderedPairCount D block) / D.card by
        field_simp]
  apply (div_le_iff₀ hImage).2
  rw [div_mul_eq_mul_div,
    mul_comm (D.card + 2 * sameBinUnorderedPairCount D block : ℝ)]
  exact (le_div_iff₀ hDcard).2
    (by simpa [pow_two, mul_comm] using hmain)

/-- Unordered pairs of selected divisors occupying one formal dyadic block. -/
def selectedDyadicUnorderedPairCount (D : Finset ℕ) : ℕ :=
  sameBinUnorderedPairCount D (Nat.log 2)

theorem selectedDyadicBlocks_le_tauPlus {n : ℕ} {D : Finset ℕ}
    (hD : D ⊆ n.divisors) :
    (D.image (Nat.log 2)).card ≤ tauPlus n := by
  exact Finset.card_le_card (Finset.image_mono _ hD)

/-- The concrete four-fifths selected-mass form of the finite
Erdős--Tenenbaum reduction. -/
theorem four_fifths_tau_div_tauPlus_le_closePairs
    {n : ℕ} {D : Finset ℕ} (hn : n ≠ 0) (hD : D ⊆ n.divisors)
    (hmass : 4 * n.divisors.card ≤ 5 * D.card) :
    (4 / 5 : ℝ) * (n.divisors.card : ℝ) / tauPlus n ≤
      1 + 2 * (selectedDyadicUnorderedPairCount D : ℝ) / D.card := by
  have hDcard : 0 < D.card := by
    have htauCard : 0 < n.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
    omega
  have hDne : D.Nonempty := Finset.card_pos.mp hDcard
  have hTauPlus : (0 : ℝ) < tauPlus n := by
    exact_mod_cast Finset.card_pos.mpr
      ((Finset.nonempty_iff_ne_empty.mpr (by
        intro himage
        have : (Nat.log 2) 1 ∈ n.divisors.image (Nat.log 2) :=
          Finset.mem_image.mpr ⟨1, Nat.one_mem_divisors.mpr hn, rfl⟩
        simp [himage] at this)) :
        (n.divisors.image (Nat.log 2)).Nonempty)
  have hmassReal : (4 / 5 : ℝ) * (n.divisors.card : ℝ) ≤ D.card := by
    have hmass' : (4 : ℝ) * n.divisors.card ≤ 5 * D.card := by
      exact_mod_cast hmass
    linarith
  have hratio := finite_bin_ratio_step D (Nat.log 2) hDne
  calc
    (4 / 5 : ℝ) * (n.divisors.card : ℝ) / tauPlus n
        ≤ (D.card : ℝ) / tauPlus n := by
          exact (div_le_div_iff_of_pos_right hTauPlus).2 hmassReal
    _ ≤ (D.card : ℝ) / (D.image (Nat.log 2)).card := by
      have hblocks : (D.image (Nat.log 2)).card ≤ tauPlus n :=
        selectedDyadicBlocks_le_tauPlus hD
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (by exact_mod_cast Finset.card_pos.mpr (hDne.image (Nat.log 2)))
        (by exact_mod_cast hblocks)
    _ ≤ 1 + 2 * (selectedDyadicUnorderedPairCount D : ℝ) / D.card :=
      hratio

/-- A version whose close-pair statistic is normalized by the full divisor
count.  This is the form estimated by the analytic mean-value argument. -/
theorem four_fifths_tau_div_tauPlus_le_normalized_closePairs
    {n : ℕ} {D : Finset ℕ} (hn : n ≠ 0) (hD : D ⊆ n.divisors)
    (hmass : 4 * n.divisors.card ≤ 5 * D.card) :
    (4 / 5 : ℝ) * (n.divisors.card : ℝ) / tauPlus n ≤
      1 + (5 / 2 : ℝ) *
        (selectedDyadicUnorderedPairCount D : ℝ) / n.divisors.card := by
  have hbase := four_fifths_tau_div_tauPlus_le_closePairs hn hD hmass
  have htauNat : 0 < n.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  have htau : (0 : ℝ) < n.divisors.card := by exact_mod_cast htauNat
  have hDcardNat : 0 < D.card := by omega
  have hDcard : (0 : ℝ) < D.card := by exact_mod_cast hDcardNat
  have hmassReal :
      (4 : ℝ) * n.divisors.card ≤ 5 * D.card := by
    exact_mod_cast hmass
  have hpairs : (0 : ℝ) ≤ selectedDyadicUnorderedPairCount D :=
    Nat.cast_nonneg _
  have hpairRatio :
      2 * (selectedDyadicUnorderedPairCount D : ℝ) / D.card ≤
        (5 / 2 : ℝ) *
          (selectedDyadicUnorderedPairCount D : ℝ) / n.divisors.card := by
    rw [div_le_div_iff₀ hDcard htau]
    nlinarith
  exact hbase.trans (by linarith)

/-- The exceptional set occurring in the exact formal statement. -/
def smallRatioSet (ε : ℝ) : Set ℕ :=
  {n : ℕ | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}

/-- The analogous exceptional set for the right-closed convention. -/
def historicalSmallRatioSet (ε : ℝ) : Set ℕ :=
  {n : ℕ | (tauPlusHistorical n : ℝ) <
    ε * (n.divisors.card : ℝ)}

/-- The endpoint comparison has exactly the direction required by the
exceptional-set argument. -/
theorem smallRatioSet_subset_historical (ε : ℝ) :
    smallRatioSet ε ⊆ historicalSmallRatioSet ε := by
  intro n hn
  change (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ) at hn
  change (tauPlusHistorical n : ℝ) < ε * (n.divisors.card : ℝ)
  exact lt_of_le_of_lt (by exact_mod_cast tauPlusHistorical_le_tauPlus n) hn

/-- A set with a natural density has the same upper density. -/
lemma upperDensity_eq_of_hasDensity {S : Set ℕ} {d : ℝ}
    (hS : S.HasDensity d) : S.upperDensity = d := by
  simpa [Set.upperDensity] using hS.limsup_eq

lemma partialDensity_nonneg (S : Set ℕ) (x : ℕ) :
    0 ≤ S.partialDensity Set.univ x := by
  positivity

lemma partialDensity_nat_eq (S : Set ℕ) (x : ℕ) :
    S.partialDensity Set.univ x =
      (((S ∩ Set.Iio x).ncard : ℕ) : ℝ) / x := by
  simp [Set.partialDensity]

lemma partialDensity_nat_eq_filter (S : Set ℕ) [DecidablePred (· ∈ S)] (x : ℕ) :
    S.partialDensity Set.univ x =
      (((Finset.range x).filter fun n ↦ n ∈ S).card : ℝ) / x := by
  rw [partialDensity_nat_eq]
  have hset : S ∩ Set.Iio x =
      ↑((Finset.range x).filter fun n ↦ n ∈ S) := by
    ext n
    simp [and_comm]
  rw [hset, Set.ncard_coe_finset]

lemma partialDensity_mono {S T : Set ℕ} (hST : S ⊆ T) (x : ℕ) :
    S.partialDensity Set.univ x ≤ T.partialDensity Set.univ x := by
  rw [partialDensity_nat_eq, partialDensity_nat_eq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard
    (Set.inter_subset_inter_left (Set.Iio x) hST)

lemma partialDensity_union_le (S T : Set ℕ) (x : ℕ) :
    (S ∪ T).partialDensity Set.univ x ≤
      S.partialDensity Set.univ x + T.partialDensity Set.univ x := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  rw [Set.union_inter_distrib_right, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_union_le (S ∩ Set.Iio x) (T ∩ Set.Iio x)

private lemma partialDensity_isCobounded (S : Set ℕ) :
    IsCoboundedUnder (· ≤ ·) atTop
      (fun x : ℕ ↦ S.partialDensity Set.univ x) :=
  isCoboundedUnder_le_of_le atTop fun x ↦ partialDensity_nonneg S x

private lemma partialDensity_isBoundedAbove (S : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun x : ℕ ↦ S.partialDensity Set.univ x) :=
  isBoundedUnder_of_eventually_le <| Eventually.of_forall fun x ↦
    Set.partialDensity_le_one S Set.univ x

private lemma partialDensity_isBoundedBelow (S : Set ℕ) :
    IsBoundedUnder (fun x y : ℝ ↦ x ≥ y) atTop
      (fun x : ℕ ↦ S.partialDensity Set.univ x) :=
  isBoundedUnder_of_eventually_ge <| Eventually.of_forall fun x ↦
    partialDensity_nonneg S x

/-- Upper density is monotone under inclusion. -/
lemma upperDensity_mono {S T : Set ℕ} (hST : S ⊆ T) :
    S.upperDensity ≤ T.upperDensity := by
  unfold Set.upperDensity
  exact Filter.limsup_le_limsup
    (Eventually.of_forall fun x ↦ partialDensity_mono hST x)
    (partialDensity_isCobounded S) (partialDensity_isBoundedAbove T)

/-- Upper density is finitely subadditive. -/
lemma upperDensity_union_le (S T : Set ℕ) :
    (S ∪ T).upperDensity ≤ S.upperDensity + T.upperDensity := by
  unfold Set.upperDensity
  calc
    limsup (fun x ↦ (S ∪ T).partialDensity Set.univ x) atTop ≤
        limsup (fun x ↦ S.partialDensity Set.univ x +
          T.partialDensity Set.univ x) atTop := by
      exact Filter.limsup_le_limsup
        (Eventually.of_forall fun x ↦ partialDensity_union_le S T x)
        (partialDensity_isCobounded (S ∪ T))
        (isBoundedUnder_of_eventually_le <| Eventually.of_forall fun x ↦
          add_le_add (Set.partialDensity_le_one S Set.univ x)
            (Set.partialDensity_le_one T Set.univ x))
    _ ≤ limsup (fun x ↦ S.partialDensity Set.univ x) atTop +
        limsup (fun x ↦ T.partialDensity Set.univ x) atTop := by
      change limsup ((fun x ↦ S.partialDensity Set.univ x) +
          (fun x ↦ T.partialDensity Set.univ x)) atTop ≤ _
      exact limsup_add_le
        (partialDensity_isBoundedBelow S)
        (partialDensity_isBoundedAbove S)
        (partialDensity_isCobounded T)
        (partialDensity_isBoundedAbove T)

lemma card_filter_mul_le_sum (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    {t : ℝ} (x : ℕ) :
    (((Finset.range x).filter fun n ↦ t < f n).card : ℝ) * t ≤
      ∑ n ∈ Finset.range x, f n := by
  classical
  let s := (Finset.range x).filter fun n ↦ t < f n
  have hcard : s.card • t ≤ ∑ n ∈ s, f n :=
    Finset.card_nsmul_le_sum s f t fun n hn ↦
      le_of_lt (Finset.mem_filter.mp hn).2
  have hsub : (∑ n ∈ s, f n) ≤ ∑ n ∈ Finset.range x, f n :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn ↦ (Finset.mem_filter.mp hn).1) fun n _ _ ↦ hf n
  simpa [s, nsmul_eq_mul] using hcard.trans hsub

lemma partialDensity_superlevel_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    {K t : ℝ} (ht : 0 < t) {x : ℕ} (hx : 0 < x)
    (hsum : (∑ n ∈ Finset.range x, f n) ≤ K * x) :
    ({n : ℕ | t < f n} : Set ℕ).partialDensity Set.univ x ≤ K / t := by
  classical
  rw [partialDensity_nat_eq_filter]
  rw [div_le_div_iff₀ (Nat.cast_pos.mpr hx) ht]
  exact (card_filter_mul_le_sum f hf x).trans hsum

/-- Eventual linear control of a nonnegative first moment gives the upper
density form of Markov's inequality. -/
theorem upperDensity_superlevel_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    {K t : ℝ} (ht : 0 < t)
    (hsum : ∀ᶠ x in atTop, (∑ n ∈ Finset.range x, f n) ≤ K * x) :
    ({n : ℕ | t < f n} : Set ℕ).upperDensity ≤ K / t := by
  rw [Set.upperDensity]
  refine Filter.limsup_le_of_le (a := K / t) ?_ ?_
  · exact isCoboundedUnder_le_of_le atTop fun x ↦ by positivity
  · filter_upwards [hsum, eventually_gt_atTop 0] with x hxsum hx
    exact partialDensity_superlevel_le f hf ht hx hxsum

/-!
## Final density deduction from the fixed Erdős--Tenenbaum moment package

The analytic part of the argument supplies a good set `G`, a nonnegative
close-pair statistic `f`, and a linear first-moment constant `K`.  The
following lemma performs all remaining choices explicitly.
-/

theorem exists_strict_upperDensity_of_fixed_moment_package
    (G : Set ℕ) (f : ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hG : (Gᶜ).upperDensity ≤ 1 / 4)
    (hmoment : ∀ n ∈ G,
      (4 / 5 : ℝ) * (n.divisors.card : ℝ) / (tauPlus n : ℝ) ≤
        1 + f n)
    (hf : ∀ n, 0 ≤ f n)
    (hsum : ∀ᶠ x in atTop,
      (∑ n ∈ Finset.range x, f n) ≤ K * x) :
    ∃ ε : ℝ, 0 < ε ∧ (smallRatioSet ε).upperDensity < 1 := by
  let t : ℝ := 4 * K + 1
  let ε : ℝ := (2 / 5) / (1 + t)
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have hOneT : 0 < 1 + t := by linarith
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, ?_⟩
  have hsubset :
      smallRatioSet ε ⊆ Gᶜ ∪ {n : ℕ | t < f n} := by
    intro n hnsmall
    by_cases hnG : n ∈ G
    · right
      by_contra hnlarge
      have hfle : f n ≤ t := le_of_not_gt hnlarge
      have hn0 : n ≠ 0 := by
        intro hn
        subst n
        norm_num [smallRatioSet, tauPlus] at hnsmall
      have htauNat : 0 < n.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
      have htau : (0 : ℝ) < n.divisors.card := by
        exact_mod_cast htauNat
      have htauPlusNat : 0 < tauPlus n := by
        apply Finset.card_pos.mpr
        exact ⟨Nat.log 2 1,
          Finset.mem_image.mpr ⟨1, Nat.one_mem_divisors.mpr hn0, rfl⟩⟩
      have htauPlus : (0 : ℝ) < tauPlus n := by
        exact_mod_cast htauPlusNat
      have hmoment' :
          (4 / 5 : ℝ) * (n.divisors.card : ℝ) ≤
            (1 + f n) * (tauPlus n : ℝ) :=
        (div_le_iff₀ htauPlus).mp (hmoment n hnG)
      have hupper :
          (1 + f n) * (tauPlus n : ℝ) ≤
            (1 + t) * (tauPlus n : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      change (tauPlus n : ℝ) <
        ε * (n.divisors.card : ℝ) at hnsmall
      have hsmall' :
          (1 + t) * (tauPlus n : ℝ) <
            (2 / 5 : ℝ) * (n.divisors.card : ℝ) := by
        calc
          (1 + t) * (tauPlus n : ℝ) <
              (1 + t) * (ε * (n.divisors.card : ℝ)) :=
            mul_lt_mul_of_pos_left hnsmall hOneT
          _ = (2 / 5 : ℝ) * (n.divisors.card : ℝ) := by
            dsimp [ε]
            field_simp
      linarith
    · left
      exact hnG
  have hmarkov :
      ({n : ℕ | t < f n} : Set ℕ).upperDensity ≤ K / t :=
    upperDensity_superlevel_le f hf ht hsum
  have hratio : K / t < 1 / 4 := by
    apply (div_lt_iff₀ ht).2
    dsimp [t]
    linarith
  calc
    (smallRatioSet ε).upperDensity ≤
        (Gᶜ ∪ {n : ℕ | t < f n}).upperDensity :=
      upperDensity_mono hsubset
    _ ≤ (Gᶜ).upperDensity +
        ({n : ℕ | t < f n} : Set ℕ).upperDensity :=
      upperDensity_union_le _ _
    _ ≤ 1 / 4 + K / t := add_le_add hG hmarkov
    _ < 1 := by linarith

/-- The exact yes/no theorem follows as soon as one positive threshold has
exceptional set of upper density strictly below one. -/
theorem erdos_448_of_exists_strict_upperDensity
    (hET : ∃ ε : ℝ, 0 < ε ∧ (smallRatioSet ε).upperDensity < 1) :
    ¬ ∀ ε : ℝ, 0 < ε →
        {n : ℕ | (tauPlus n : ℝ) <
          ε * (n.divisors.card : ℝ)}.HasDensity 1 := by
  intro hall
  obtain ⟨ε, hε, hlt⟩ := hET
  have heq : (smallRatioSet ε).upperDensity = 1 :=
    upperDensity_eq_of_hasDensity (hall ε hε)
  linarith

end Erdos448

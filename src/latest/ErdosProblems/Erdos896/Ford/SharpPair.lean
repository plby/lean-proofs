/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.PairMultiplicity

/-!
# The sharp per-profile close-divisor-pair estimate

Non-diagonal divisor pairs are charged to the largest prime slot on which
the two divisors differ.  Once all other slots are fixed, that prime lies in
a factor-four interval.  The reciprocal-prime estimate for `(U,4U]`,
together with the double-exponential scale of the greedy endpoints, turns
this charge into Ford's exponential prefix potential.
-/

namespace Erdos896.Ford

open scoped BigOperators symmDiff

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Short public name for the concrete family defined in `ProfileMass`. -/
abbrev profileFamily := profileNumberFamily

theorem profileSelectionPrimes_subset_support
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    profileSelectionPrimes c ⊆ primeBlockSupport start blocks := by
  intro p hp
  obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr
    ⟨i.1, i.2, profileSelection_subset_block hc i.1 i.2 hp⟩

theorem primeFactors_profileSelectionProduct
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    (profileSelectionProduct c).primeFactors = profileSelectionPrimes c := by
  rw [profileSelectionProduct_eq_prod_primes hc]
  exact Nat.primeFactors_prod fun p hp ↦ prime_of_mem_profileSelectionPrimes hc hp

theorem mem_profileFamily_data
    {start blocks : ℕ} {b : ℕ → ℕ} {a : ℕ}
    (ha : a ∈ profileFamily start blocks b) :
    Squarefree a ∧ a.primeFactors ⊆ primeBlockSupport start blocks ∧
      a.primeFactors.card = profilePrimeCount blocks b := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
  refine ⟨squarefree_profileSelectionProduct hc, ?_, ?_⟩
  · rw [primeFactors_profileSelectionProduct hc]
    exact profileSelectionPrimes_subset_support hc
  · rw [primeFactors_profileSelectionProduct hc,
      profileSelectionPrimes_card hc]

theorem divisorCount_eq_two_pow_profilePrimeCount_of_mem_profileFamily
    {start blocks : ℕ} {b : ℕ → ℕ} {a : ℕ}
    (ha : a ∈ profileFamily start blocks b) :
    divisorCount a = 2 ^ profilePrimeCount blocks b := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
  exact divisorCount_profileSelectionProduct hc

/-! ## A factor-four slice of one greedy block -/

/-- The primes in one greedy block whose logarithms lie in a dyadic window
have reciprocal mass `O(2⁻ʲ)`.  This is the analytic estimate used after
all slots but the maximal differing one have been fixed. -/
theorem exists_primeBlock_dyadicLogSlice_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (x : ℝ),
      (∑ p ∈ (primeBlock j).filter
          (fun p : ℕ ↦ |Real.log (p : ℝ) - x| ≤ Real.log 2), (1 : ℝ) / p) ≤
        C * (1 / 2 : ℝ) ^ j := by
  obtain ⟨C, hC, hfour⟩ := exists_primeReciprocalIntervalSum_four_mul_le
  let K : ℝ := (C + 1) * primeBlockLogLowerConstant⁻¹
  have hK : 0 ≤ K := mul_nonneg (add_nonneg hC (by norm_num))
    (inv_nonneg.mpr primeBlockLogLowerConstant_pos.le)
  refine ⟨K, hK, fun j x ↦ ?_⟩
  let T := (primeBlock j).filter
    (fun p : ℕ ↦ |Real.log (p : ℝ) - x| ≤ Real.log 2)
  by_cases hT : T.Nonempty
  · let q := T.min' hT
    have hqT : q ∈ T := Finset.min'_mem T hT
    have hqBlock : q ∈ primeBlock j := (Finset.mem_filter.mp hqT).1
    have hqPrime : q.Prime := prime_of_mem_primeBlock hqBlock
    have hq2 : 2 ≤ q := hqPrime.two_le
    have hqlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hqPrime.one_lt)
    have hTsub : T ⊆ insert q
        (Nat.primesLE (4 * q) \ Nat.primesLE q) := by
      intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpPrime := prime_of_mem_primeBlock hpData.1
      by_cases hpq : p = q
      · simp [hpq]
      · have hqp : q < p := lt_of_le_of_ne (Finset.min'_le T p hp) (Ne.symm hpq)
        have hlogp : Real.log p ≤ Real.log q + 2 * Real.log 2 := by
          have hpAbs := (abs_le.mp hpData.2).2
          have hqAbs := (abs_le.mp (Finset.mem_filter.mp hqT).2).1
          linarith
        have hlog4q : Real.log q + 2 * Real.log 2 = Real.log (4 * q) := by
          have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqPrime.ne_zero
          push_cast
          rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hq0,
            show (4 : ℝ) = 2 * 2 by norm_num,
            Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
              (by norm_num : (2 : ℝ) ≠ 0)]
          ring
        have hp4q : p ≤ 4 * q := by
          have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
          have h4qR : (0 : ℝ) < (4 * q : ℕ) := by positivity
          have hR : (p : ℝ) ≤ (4 * q : ℕ) := by
            apply (Real.log_le_log_iff hpR h4qR).mp
            rw [show ((4 * q : ℕ) : ℝ) = 4 * (q : ℝ) by norm_num,
              ← hlog4q]
            exact hlogp
          exact_mod_cast hR
        simp only [Finset.mem_insert, Finset.mem_sdiff, Nat.mem_primesLE]
        exact Or.inr ⟨⟨hp4q, hpPrime⟩, fun h ↦ (not_le_of_gt hqp) h.1⟩
    have hsumSub :
        (∑ p ∈ T, (1 : ℝ) / p) ≤
          ∑ p ∈ insert q (Nat.primesLE (4 * q) \ Nat.primesLE q),
            (1 : ℝ) / p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hTsub
        (fun p hp hnot ↦ by positivity)
    have hqnot : q ∉ Nat.primesLE (4 * q) \ Nat.primesLE q := by
      intro h
      exact (Finset.mem_sdiff.mp h).2
        (Nat.mem_primesLE.mpr ⟨le_rfl, hqPrime⟩)
    have hfourq := hfour q hq2
    have hqterm : (1 : ℝ) / q ≤ 1 / Real.log q := by
      have hlogle : Real.log q ≤ q := Real.log_le_sub_one_of_pos
        (by exact_mod_cast hqPrime.pos) |>.trans (by norm_num)
      exact one_div_le_one_div_of_le hqlog hlogle
    have hlower : Real.log (primeBlockEndpoint j) ≤ Real.log q := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by
          exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
            (two_le_primeBlockEndpoint j)))
      · exact Set.mem_Ioi.mpr (by exact_mod_cast hqPrime.pos)
      · exact_mod_cast (primeBlockLower_lt_of_mem hqBlock).le
    have hinvlog : (1 : ℝ) / Real.log q ≤
        primeBlockLogLowerConstant⁻¹ * (1 / 2 : ℝ) ^ j := by
      calc
        (1 : ℝ) / Real.log q ≤
            1 / Real.log (primeBlockEndpoint j) :=
          one_div_le_one_div_of_le
            (Real.log_pos (by exact_mod_cast
              (lt_of_lt_of_le (by omega : 1 < 2)
                (two_le_primeBlockEndpoint j)))) hlower
        _ ≤ primeBlockLogLowerConstant⁻¹ * (1 / 2 : ℝ) ^ j :=
          one_div_log_endpoint_le_geometric j
    calc
      (∑ p ∈ (primeBlock j).filter
          (fun p : ℕ ↦ |Real.log (p : ℝ) - x| ≤ Real.log 2), (1 : ℝ) / p) =
          ∑ p ∈ T, (1 : ℝ) / p := rfl
      _ ≤ ∑ p ∈ insert q (Nat.primesLE (4 * q) \ Nat.primesLE q),
          (1 : ℝ) / p := hsumSub
      _ = (1 : ℝ) / q + primeReciprocalIntervalSum q (4 * q) := by
        rw [Finset.sum_insert hqnot]
        rfl
      _ ≤ (C + 1) * (1 / Real.log q) := by
        calc
          (1 : ℝ) / q + primeReciprocalIntervalSum q (4 * q) ≤
              1 / Real.log q + C / Real.log q := add_le_add hqterm hfourq
          _ = (C + 1) * (1 / Real.log q) := by ring
      _ ≤ (C + 1) *
          (primeBlockLogLowerConstant⁻¹ * (1 / 2 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hinvlog (add_nonneg hC (by norm_num))
      _ = K * (1 / 2 : ℝ) ^ j := by simp [K]; ring
  · have : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [T, this, hK]

/-! ## Ordered slots and the maximal-difference decomposition -/

/-- The zero-based position of a slot in the flattened block profile. -/
def profileSlotRank {blocks : ℕ} {b : ℕ → ℕ}
    (s : ProfileSlot blocks b) : ℕ :=
  (∑ i ∈ Finset.range s.1.1, b i) + s.2.1

theorem profileSlotRank_lt_prefix
    {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b) :
    profileSlotRank s < profilePrefixCount b (profileSlotBlock s) := by
  unfold profileSlotRank profilePrefixCount profileSlotBlock
  rw [Finset.sum_range_succ]
  exact Nat.add_lt_add_left s.2.2 _

theorem profileSlotRank_injective
    {blocks : ℕ} {b : ℕ → ℕ} :
    Function.Injective (@profileSlotRank blocks b) := by
  rintro ⟨i, r⟩ ⟨j, s⟩ hrs
  have hmono : ∀ {u v : ℕ}, u ≤ v →
      (∑ h ∈ Finset.range u, b h) ≤ ∑ h ∈ Finset.range v, b h := by
    intro u v huv
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono huv)
      (fun _ _ _ ↦ Nat.zero_le _)
  have hij : i.1 = j.1 := by
    rcases lt_trichotomy i.1 j.1 with hij | hij | hij
    · have hpre : (∑ h ∈ Finset.range (i.1 + 1), b h) ≤
          ∑ h ∈ Finset.range j.1, b h := hmono (by omega)
      have hrlt : (∑ h ∈ Finset.range i.1, b h) + r.1 <
          ∑ h ∈ Finset.range (i.1 + 1), b h := by
        rw [Finset.sum_range_succ]
        exact Nat.add_lt_add_left r.2 _
      have hranklt : profileSlotRank (Sigma.mk i r) <
          profileSlotRank (Sigma.mk j s) := by
        unfold profileSlotRank
        exact lt_of_lt_of_le (hrlt.trans_le hpre)
          (Nat.le_add_right _ _)
      exact False.elim ((ne_of_lt hranklt) hrs)
    · exact hij
    · have hpre : (∑ h ∈ Finset.range (j.1 + 1), b h) ≤
          ∑ h ∈ Finset.range i.1, b h := hmono (by omega)
      have hslt : (∑ h ∈ Finset.range j.1, b h) + s.1 <
          ∑ h ∈ Finset.range (j.1 + 1), b h := by
        rw [Finset.sum_range_succ]
        exact Nat.add_lt_add_left s.2 _
      have hranklt : profileSlotRank (Sigma.mk j s) <
          profileSlotRank (Sigma.mk i r) := by
        unfold profileSlotRank
        exact lt_of_lt_of_le (hslt.trans_le hpre)
          (Nat.le_add_right _ _)
      exact False.elim ((ne_of_gt hranklt) hrs)
  have hijFin : i = j := Fin.ext hij
  subst j
  have hrs' : (∑ h ∈ Finset.range i.1, b h) + r.1 =
      (∑ h ∈ Finset.range i.1, b h) + s.1 := by
    simpa only [profileSlotRank] using hrs
  have hrsVal : r.1 = s.1 := Nat.add_left_cancel hrs'
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hrsVal))

theorem card_profileSlot (blocks : ℕ) (b : ℕ → ℕ) :
    Fintype.card (ProfileSlot blocks b) = profilePrimeCount blocks b := by
  unfold profilePrimeCount
  rw [Fintype.card_sigma]
  simpa only [Fintype.card_fin] using Fin.sum_univ_eq_sum_range b blocks

private def profileRestTuples
    (start : ℕ) {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b) :
    Finset ({t : ProfileSlot blocks b // t ≠ s} → ℕ) :=
  Fintype.piFinset fun t ↦ primeBlock (start + profileSlotBlock t.1)

private theorem profileOrderedTuples_map_split
    (start : ℕ) {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b) :
    (profileOrderedTuples start blocks b).map
        (Equiv.funSplitAt s ℕ).toEmbedding =
      (primeBlock (start + profileSlotBlock s)).product
        (profileRestTuples start s) := by
  classical
  ext qr
  constructor
  · intro h
    obtain ⟨p, hp, hpeq⟩ := Finset.mem_map.mp h
    have hp' := Fintype.mem_piFinset.mp hp
    have hfst : qr.1 ∈ primeBlock (start + profileSlotBlock s) := by
      rw [← hpeq]
      exact hp' s
    have hsnd : qr.2 ∈ profileRestTuples start s := by
      apply Fintype.mem_piFinset.mpr
      intro t
      rw [← hpeq]
      exact hp' t.1
    exact Finset.mem_product.mpr ⟨hfst, hsnd⟩
  · intro h
    have h' := Finset.mem_product.mp h
    let p := (Equiv.funSplitAt s ℕ).symm qr
    have hp : p ∈ profileOrderedTuples start blocks b := by
      apply Fintype.mem_piFinset.mpr
      intro t
      by_cases hts : t = s
      · subst t
        simpa [p] using h'.1
      · have hr := Fintype.mem_piFinset.mp h'.2 ⟨t, hts⟩
        simpa [p, Equiv.funSplitAt, Equiv.piSplitAt, hts] using hr
    exact Finset.mem_map.mpr ⟨p, hp, by simp [p]⟩

private theorem sum_profileOrderedTuples_split
    (start : ℕ) {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b)
    (F : (ProfileSlot blocks b → ℕ) → ℝ) :
    (∑ p ∈ profileOrderedTuples start blocks b, F p) =
      ∑ q ∈ primeBlock (start + profileSlotBlock s),
        ∑ r ∈ profileRestTuples start s,
          F ((Equiv.funSplitAt s ℕ).symm (q, r)) := by
  classical
  calc
    (∑ p ∈ profileOrderedTuples start blocks b, F p) =
        ∑ qr ∈ (profileOrderedTuples start blocks b).map
          (Equiv.funSplitAt s ℕ).toEmbedding,
            F ((Equiv.funSplitAt s ℕ).symm qr) := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro p hp
      change F p = F ((Equiv.funSplitAt s ℕ).symm ((Equiv.funSplitAt s ℕ) p))
      rw [(Equiv.funSplitAt s ℕ).symm_apply_apply]
    _ = ∑ qr ∈ (primeBlock (start + profileSlotBlock s)).product
          (profileRestTuples start s),
            F ((Equiv.funSplitAt s ℕ).symm qr) := by
      rw [profileOrderedTuples_map_split start s]
    _ = ∑ q ∈ primeBlock (start + profileSlotBlock s),
        ∑ r ∈ profileRestTuples start s,
          F ((Equiv.funSplitAt s ℕ).symm (q, r)) := by
      change (∑ qr ∈ (primeBlock (start + profileSlotBlock s)) ×ˢ
          (profileRestTuples start s),
            F ((Equiv.funSplitAt s ℕ).symm qr)) = _
      rw [Finset.sum_product]

private def profileRestTupleWeight
    {blocks : ℕ} {b : ℕ → ℕ} {s : ProfileSlot blocks b}
    (r : {t : ProfileSlot blocks b // t ≠ s} → ℕ) : ℝ :=
  ∏ t, (1 : ℝ) / r t

private def profileRestMass
    (start : ℕ) {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b) : ℝ :=
  ∏ t : {t : ProfileSlot blocks b // t ≠ s},
    primeBlockMass (start + profileSlotBlock t.1)

private theorem sum_profileRestTupleWeight
    (start : ℕ) {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b) :
    (∑ r ∈ profileRestTuples start s, profileRestTupleWeight r) =
      profileRestMass start s := by
  classical
  unfold profileRestTupleWeight profileRestMass profileRestTuples
  exact (Finset.prod_univ_sum
    (fun t : {t : ProfileSlot blocks b // t ≠ s} ↦
      primeBlock (start + profileSlotBlock t.1))
    (fun _ p ↦ (1 : ℝ) / p)).symm

private theorem profileOrderedTupleWeight_split
    {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b)
    (q : ℕ) (r : {t : ProfileSlot blocks b // t ≠ s} → ℕ) :
    profileOrderedTupleWeight ((Equiv.funSplitAt s ℕ).symm (q, r)) =
      ((1 : ℝ) / q) * profileRestTupleWeight r := by
  classical
  unfold profileOrderedTupleWeight profileRestTupleWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ s]
  congr 1
  · simp only [Equiv.funSplitAt_symm_apply, dif_pos]
  · apply Finset.prod_congr rfl
    intro t ht
    simp only [Equiv.funSplitAt_symm_apply, dif_neg t.2]

private def profileRestDivisorLog
    {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b)
    (r : {t : ProfileSlot blocks b // t ≠ s} → ℕ)
    (Y : Finset (ProfileSlot blocks b)) : ℝ :=
  ∑ t ∈ Y.erase s,
    if h : t ≠ s then Real.log (r ⟨t, h⟩) else 0

private theorem profileOrderedDivisorLog_split
    {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b)
    (q : ℕ) (r : {t : ProfileSlot blocks b // t ≠ s} → ℕ)
    (Y : Finset (ProfileSlot blocks b)) :
    profileOrderedDivisorLog ((Equiv.funSplitAt s ℕ).symm (q, r)) Y =
      (if s ∈ Y then Real.log q else 0) + profileRestDivisorLog s r Y := by
  classical
  by_cases hs : s ∈ Y
  · rw [if_pos hs]
    unfold profileOrderedDivisorLog profileRestDivisorLog
    calc
      (∑ t ∈ Y, Real.log ((Equiv.funSplitAt s ℕ).symm (q, r) t)) =
          (∑ t ∈ Y.erase s,
            Real.log ((Equiv.funSplitAt s ℕ).symm (q, r) t)) +
            Real.log ((Equiv.funSplitAt s ℕ).symm (q, r) s) :=
        (Finset.sum_erase_add _ _ hs).symm
      _ = (∑ t ∈ Y.erase s,
            if h : t ≠ s then Real.log (r ⟨t, h⟩) else 0) + Real.log q := by
        congr 1
        · apply Finset.sum_congr rfl
          intro t ht
          have hts : t ≠ s := Finset.ne_of_mem_erase ht
          simp [Equiv.funSplitAt, Equiv.piSplitAt, hts]
        · simp [Equiv.funSplitAt, Equiv.piSplitAt]
      _ = Real.log q + ∑ t ∈ Y.erase s,
            if h : t ≠ s then Real.log (r ⟨t, h⟩) else 0 := by
        ring
  · rw [if_neg hs]
    unfold profileOrderedDivisorLog profileRestDivisorLog
    have herase : Y.erase s = Y := Finset.erase_eq_of_notMem hs
    rw [herase]
    simp only [zero_add]
    apply Finset.sum_congr rfl
    intro t ht
    have hts : t ≠ s := fun h ↦ hs (h ▸ ht)
    simp [Equiv.funSplitAt, Equiv.piSplitAt, hts]

private theorem exists_dyadic_center_of_mem_symmDiff
    {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b)
    {Y Z : Finset (ProfileSlot blocks b)} (hs : s ∈ Y ∆ Z)
    (r : {t : ProfileSlot blocks b // t ≠ s} → ℕ) :
    ∃ x : ℝ, ∀ q : ℕ,
      |profileOrderedDivisorLog ((Equiv.funSplitAt s ℕ).symm (q, r)) Y -
          profileOrderedDivisorLog ((Equiv.funSplitAt s ℕ).symm (q, r)) Z| ≤
          Real.log 2 →
        |Real.log q - x| ≤ Real.log 2 := by
  rw [Finset.mem_symmDiff] at hs
  rcases hs with ⟨hsY, hsZ⟩ | ⟨hsZ, hsY⟩
  · refine ⟨profileRestDivisorLog s r Z - profileRestDivisorLog s r Y,
      fun q hq ↦ ?_⟩
    rw [profileOrderedDivisorLog_split, profileOrderedDivisorLog_split,
      if_pos hsY, if_neg hsZ] at hq
    convert hq using 1 <;> ring_nf
  · refine ⟨profileRestDivisorLog s r Y - profileRestDivisorLog s r Z,
      fun q hq ↦ ?_⟩
    rw [profileOrderedDivisorLog_split, profileOrderedDivisorLog_split,
      if_neg hsY, if_pos hsZ] at hq
    have heq : Real.log q -
          (profileRestDivisorLog s r Y - profileRestDivisorLog s r Z) =
        -(0 + profileRestDivisorLog s r Y -
          (Real.log q + profileRestDivisorLog s r Z)) := by ring
    rw [heq, abs_neg]
    exact hq

/-- The set of slots no later than `s` in flattened profile order. -/
private def profileInitialSlots {blocks : ℕ} {b : ℕ → ℕ}
    (s : ProfileSlot blocks b) : Finset (ProfileSlot blocks b) :=
  Finset.univ.filter fun t ↦ profileSlotRank t ≤ profileSlotRank s

private theorem card_profileInitialSlots_le
    {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b) :
    (profileInitialSlots s).card ≤ profileSlotRank s + 1 := by
  classical
  have h := Finset.card_le_card_of_injOn profileSlotRank
    (s := profileInitialSlots s)
    (t := Finset.range (profileSlotRank s + 1))
    (fun t ht ↦ by
      change profileSlotRank t ∈ Finset.range (profileSlotRank s + 1)
      rw [Finset.mem_range]
      exact Nat.lt_succ_iff.mpr (Finset.mem_filter.mp ht).2)
    profileSlotRank_injective.injOn
  simpa using h

/-- `s` is the last slot at which the two divisor subsets differ. -/
private def profileLastDiffAt {blocks : ℕ} {b : ℕ → ℕ}
    (s : ProfileSlot blocks b)
    (YZ : Finset (ProfileSlot blocks b) × Finset (ProfileSlot blocks b)) : Prop :=
  s ∈ YZ.1 ∆ YZ.2 ∧
    ∀ t ∈ YZ.1 ∆ YZ.2, profileSlotRank t ≤ profileSlotRank s

private theorem exists_profileLastDiffAt
    {blocks : ℕ} {b : ℕ → ℕ}
    {Y Z : Finset (ProfileSlot blocks b)} (hYZ : Y ≠ Z) :
    ∃ s, profileLastDiffAt s (Y, Z) := by
  classical
  have hne : (Y ∆ Z).Nonempty := by
    rw [Finset.symmDiff_nonempty]
    exact hYZ
  obtain ⟨s, hs, hmax⟩ :=
    Finset.exists_max_image (Y ∆ Z) profileSlotRank hne
  exact ⟨s, hs, hmax⟩

private def profileLastDiffPairs {blocks : ℕ} {b : ℕ → ℕ}
    (s : ProfileSlot blocks b) :
    Finset (Finset (ProfileSlot blocks b) × Finset (ProfileSlot blocks b)) :=
  ((Finset.univ.powerset).product (Finset.univ.powerset)).filter
    (profileLastDiffAt s)

private theorem mem_eq_outside_initial_of_lastDiffAt
    {blocks : ℕ} {b : ℕ → ℕ}
    {s t : ProfileSlot blocks b}
    {YZ : Finset (ProfileSlot blocks b) × Finset (ProfileSlot blocks b)}
    (hlast : profileLastDiffAt s YZ) (ht : t ∉ profileInitialSlots s) :
    (t ∈ YZ.1 ↔ t ∈ YZ.2) := by
  classical
  by_contra hne
  have hdiff : t ∈ YZ.1 ∆ YZ.2 := by
    rw [Finset.mem_symmDiff]
    tauto
  have hle := hlast.2 t hdiff
  exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)

private theorem card_profileLastDiffPairs_le
    {blocks : ℕ} {b : ℕ → ℕ} (s : ProfileSlot blocks b) :
    (profileLastDiffPairs s).card ≤
      2 ^ profilePrimeCount blocks b * 2 ^ (profileSlotRank s + 1) := by
  classical
  let encode :
      (Finset (ProfileSlot blocks b) × Finset (ProfileSlot blocks b)) →
        (Finset (ProfileSlot blocks b) × Finset (ProfileSlot blocks b)) :=
    fun YZ ↦ (YZ.1, YZ.2 ∩ profileInitialSlots s)
  have hmap : Set.MapsTo encode (profileLastDiffPairs s : Set _)
      (((Finset.univ : Finset (ProfileSlot blocks b)).powerset).product
        ((profileInitialSlots s).powerset) : Set _) := by
    intro YZ hYZ
    change encode YZ ∈ ((Finset.univ : Finset (ProfileSlot blocks b)).powerset).product
      ((profileInitialSlots s).powerset)
    rw [Finset.product_eq_sprod]
    simpa only [encode] using Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩
  have hinj : (profileLastDiffPairs s : Set _).InjOn encode := by
    intro YZ hYZ UV hUV heq
    change (YZ.1, YZ.2 ∩ profileInitialSlots s) =
      (UV.1, UV.2 ∩ profileInitialSlots s) at heq
    have hlastYZ : profileLastDiffAt s YZ := (Finset.mem_filter.mp hYZ).2
    have hlastUV : profileLastDiffAt s UV := (Finset.mem_filter.mp hUV).2
    have hfst : YZ.1 = UV.1 := (Prod.mk.inj heq).1
    have hsnd : YZ.2 ∩ profileInitialSlots s =
        UV.2 ∩ profileInitialSlots s := (Prod.mk.inj heq).2
    apply Prod.ext hfst
    ext t
    by_cases ht : t ∈ profileInitialSlots s
    · have := Finset.ext_iff.mp hsnd t
      simpa [ht] using this
    · have hYZeq := mem_eq_outside_initial_of_lastDiffAt hlastYZ ht
      have hUVeq := mem_eq_outside_initial_of_lastDiffAt hlastUV ht
      calc
        (t ∈ YZ.2) ↔ t ∈ YZ.1 := hYZeq.symm
        _ ↔ t ∈ UV.1 := by rw [hfst]
        _ ↔ t ∈ UV.2 := hUVeq
  calc
    (profileLastDiffPairs s).card ≤
        (((Finset.univ : Finset (ProfileSlot blocks b)).powerset).product
          ((profileInitialSlots s).powerset)).card :=
      Finset.card_le_card_of_injOn encode hmap hinj
    _ = 2 ^ profilePrimeCount blocks b *
        2 ^ (profileInitialSlots s).card := by
      rw [Finset.product_eq_sprod, Finset.card_product,
        Finset.card_powerset, Finset.card_powerset,
        Finset.card_univ]
      congr 1
      exact congrArg (fun n : ℕ ↦ 2 ^ n) (card_profileSlot blocks b)
    _ ≤ 2 ^ profilePrimeCount blocks b * 2 ^ (profileSlotRank s + 1) := by
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) (card_profileInitialSlots_le s))

private def profileCloseLastDiffPairs
    {blocks : ℕ} {b : ℕ → ℕ}
    (p : ProfileSlot blocks b → ℕ) (s : ProfileSlot blocks b) :
    Finset (Finset (ProfileSlot blocks b) × Finset (ProfileSlot blocks b)) :=
  (profileLastDiffPairs s).filter fun YZ ↦
    |profileOrderedDivisorLog p YZ.1 - profileOrderedDivisorLog p YZ.2| ≤
      Real.log 2

private theorem fixed_rest_lastDiff_mass_le
    {K : ℝ}
    (hK : 0 ≤ K)
    (hslice : ∀ (j : ℕ) (x : ℝ),
      (∑ p ∈ (primeBlock j).filter
          (fun p : ℕ ↦ |Real.log (p : ℝ) - x| ≤ Real.log 2),
          (1 : ℝ) / p) ≤ K * (1 / 2 : ℝ) ^ j)
    (start : ℕ) {blocks : ℕ} {b : ℕ → ℕ}
    (s : ProfileSlot blocks b)
    (r : {t : ProfileSlot blocks b // t ≠ s} → ℕ) :
    (∑ q ∈ primeBlock (start + profileSlotBlock s),
      (1 : ℝ) / q *
        ((profileCloseLastDiffPairs
          ((Equiv.funSplitAt s ℕ).symm (q, r)) s).card : ℝ)) ≤
      K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s) *
        (2 ^ profilePrimeCount blocks b * 2 ^ (profileSlotRank s + 1) : ℕ) := by
  classical
  have hsliceYZ : ∀ YZ ∈ profileLastDiffPairs s,
      (∑ q ∈ (primeBlock (start + profileSlotBlock s)).filter
        (fun q : ℕ ↦ |profileOrderedDivisorLog
            ((Equiv.funSplitAt s ℕ).symm (q, r)) YZ.1 -
          profileOrderedDivisorLog
            ((Equiv.funSplitAt s ℕ).symm (q, r)) YZ.2| ≤ Real.log 2),
        (1 : ℝ) / q) ≤
        K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s) := by
    intro YZ hYZ
    have hlast : profileLastDiffAt s YZ := (Finset.mem_filter.mp hYZ).2
    obtain ⟨x, hx⟩ := exists_dyadic_center_of_mem_symmDiff s hlast.1 r
    calc
      (∑ q ∈ (primeBlock (start + profileSlotBlock s)).filter
          (fun q : ℕ ↦ |profileOrderedDivisorLog
              ((Equiv.funSplitAt s ℕ).symm (q, r)) YZ.1 -
            profileOrderedDivisorLog
              ((Equiv.funSplitAt s ℕ).symm (q, r)) YZ.2| ≤ Real.log 2),
          (1 : ℝ) / q) ≤
          ∑ q ∈ (primeBlock (start + profileSlotBlock s)).filter
            (fun q : ℕ ↦ |Real.log (q : ℝ) - x| ≤ Real.log 2),
            (1 : ℝ) / q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rw [Finset.mem_filter] at hq ⊢
          exact ⟨hq.1, hx q hq.2⟩
        · intro q hq hnot
          positivity
      _ ≤ K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s) :=
        hslice (start + profileSlotBlock s) x
  calc
    (∑ q ∈ primeBlock (start + profileSlotBlock s),
      (1 : ℝ) / q *
        ((profileCloseLastDiffPairs
          ((Equiv.funSplitAt s ℕ).symm (q, r)) s).card : ℝ)) =
        ∑ YZ ∈ profileLastDiffPairs s,
          ∑ q ∈ (primeBlock (start + profileSlotBlock s)).filter
            (fun q : ℕ ↦ |profileOrderedDivisorLog
                ((Equiv.funSplitAt s ℕ).symm (q, r)) YZ.1 -
              profileOrderedDivisorLog
                ((Equiv.funSplitAt s ℕ).symm (q, r)) YZ.2| ≤ Real.log 2),
            (1 : ℝ) / q := by
      simp only [profileCloseLastDiffPairs, Finset.card_filter,
        Nat.cast_sum, Nat.cast_one, mul_one, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro YZ hYZ
      by_cases hclose : |profileOrderedDivisorLog
          ((Equiv.funSplitAt s ℕ).symm (q, r)) YZ.1 -
        profileOrderedDivisorLog
          ((Equiv.funSplitAt s ℕ).symm (q, r)) YZ.2| ≤ Real.log 2
      · simp [hclose]
      · simp [hclose]
    _ ≤ ∑ _YZ ∈ profileLastDiffPairs s,
        K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s) := by
      exact Finset.sum_le_sum fun YZ hYZ ↦ hsliceYZ YZ hYZ
    _ = ((profileLastDiffPairs s).card : ℝ) *
        (K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s)) := by simp
    _ ≤ (2 ^ profilePrimeCount blocks b *
          2 ^ (profileSlotRank s + 1) : ℕ) *
        (K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_profileLastDiffPairs_le s
      · exact mul_nonneg hK (pow_nonneg (by norm_num) _)
    _ = K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s) *
        (2 ^ profilePrimeCount blocks b * 2 ^ (profileSlotRank s + 1) : ℕ) := by
      ring

private theorem card_profileOrderedOffDiagonalPairs_le_sum_lastDiff
    {blocks : ℕ} {b : ℕ → ℕ} (p : ProfileSlot blocks b → ℕ) :
    (profileOrderedOffDiagonalPairs p).card ≤
      ∑ s, (profileCloseLastDiffPairs p s).card := by
  classical
  let U := Finset.univ.biUnion (profileCloseLastDiffPairs p)
  have hsub : profileOrderedOffDiagonalPairs p ⊆ U := by
    intro YZ hYZ
    have hoff := Finset.mem_filter.mp hYZ
    have hclose := Finset.mem_filter.mp hoff.1
    obtain ⟨s, hs⟩ := exists_profileLastDiffAt hoff.2
    apply Finset.mem_biUnion.mpr
    refine ⟨s, Finset.mem_univ s, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hclose.1, hs⟩, hclose.2⟩
  calc
    (profileOrderedOffDiagonalPairs p).card ≤ U.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ s, (profileCloseLastDiffPairs p s).card := by
      exact Finset.card_biUnion_le

private theorem profileOrderedOffDiagonalMass_le_sum_lastDiff
    (start blocks : ℕ) (b : ℕ → ℕ) :
    profileOrderedOffDiagonalMass start blocks b ≤
      ∑ s : ProfileSlot blocks b,
        ∑ p ∈ profileOrderedTuples start blocks b,
          profileOrderedTupleWeight p *
            ((profileCloseLastDiffPairs p s).card : ℝ) := by
  classical
  unfold profileOrderedOffDiagonalMass
  calc
    (∑ p ∈ profileOrderedTuples start blocks b,
        profileOrderedTupleWeight p *
          ((profileOrderedOffDiagonalPairs p).card : ℝ)) ≤
        ∑ p ∈ profileOrderedTuples start blocks b,
          profileOrderedTupleWeight p *
            (∑ s : ProfileSlot blocks b,
              ((profileCloseLastDiffPairs p s).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast card_profileOrderedOffDiagonalPairs_le_sum_lastDiff p
      · unfold profileOrderedTupleWeight
        positivity
    _ = ∑ s : ProfileSlot blocks b,
        ∑ p ∈ profileOrderedTuples start blocks b,
          profileOrderedTupleWeight p *
            ((profileCloseLastDiffPairs p s).card : ℝ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]

private theorem fixed_slot_lastDiff_mass_le
    {K : ℝ} (hK : 0 ≤ K)
    (hslice : ∀ (j : ℕ) (x : ℝ),
      (∑ p ∈ (primeBlock j).filter
          (fun p : ℕ ↦ |Real.log (p : ℝ) - x| ≤ Real.log 2),
          (1 : ℝ) / p) ≤ K * (1 / 2 : ℝ) ^ j)
    (start : ℕ) {blocks : ℕ} {b : ℕ → ℕ}
    (s : ProfileSlot blocks b) :
    (∑ p ∈ profileOrderedTuples start blocks b,
      profileOrderedTupleWeight p *
        ((profileCloseLastDiffPairs p s).card : ℝ)) ≤
      profileRestMass start s *
        (K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s) *
          (2 ^ profilePrimeCount blocks b * 2 ^ (profileSlotRank s + 1) : ℕ)) := by
  classical
  rw [sum_profileOrderedTuples_split start s]
  simp_rw [profileOrderedTupleWeight_split]
  calc
    (∑ q ∈ primeBlock (start + profileSlotBlock s),
        ∑ r ∈ profileRestTuples start s,
          ((1 : ℝ) / q * profileRestTupleWeight r) *
            ((profileCloseLastDiffPairs
              ((Equiv.funSplitAt s ℕ).symm (q, r)) s).card : ℝ)) =
        ∑ r ∈ profileRestTuples start s,
          profileRestTupleWeight r *
            (∑ q ∈ primeBlock (start + profileSlotBlock s),
              (1 : ℝ) / q *
                ((profileCloseLastDiffPairs
                  ((Equiv.funSplitAt s ℕ).symm (q, r)) s).card : ℝ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ ∑ r ∈ profileRestTuples start s,
        profileRestTupleWeight r *
          (K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s) *
            (2 ^ profilePrimeCount blocks b *
              2 ^ (profileSlotRank s + 1) : ℕ)) := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left
      · exact fixed_rest_lastDiff_mass_le hK hslice start s r
      · unfold profileRestTupleWeight
        positivity
    _ = profileRestMass start s *
        (K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s) *
          (2 ^ profilePrimeCount blocks b * 2 ^ (profileSlotRank s + 1) : ℕ)) := by
      rw [← Finset.sum_mul, sum_profileRestTupleWeight]

private def profileOrderedTotalMass
    (start blocks : ℕ) (b : ℕ → ℕ) : ℝ :=
  ∏ s : ProfileSlot blocks b,
    primeBlockMass (start + profileSlotBlock s)

private theorem profileOrderedTotalMass_eq_factorial_mul_tupleMass
    (start blocks : ℕ) (b : ℕ → ℕ) :
    profileOrderedTotalMass start blocks b =
      (profileFactorial blocks b : ℝ) * profileTupleMass start blocks b := by
  classical
  have hslots : profileOrderedTotalMass start blocks b =
      ∏ i ∈ Finset.range blocks, primeBlockMass (start + i) ^ b i := by
    unfold profileOrderedTotalMass
    rw [Fintype.prod_sigma]
    simp only [profileSlotBlock, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    exact Fin.prod_univ_eq_prod_range
      (fun i ↦ primeBlockMass (start + i) ^ b i) blocks
  rw [hslots]
  unfold profileFactorial profileTupleMass
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hfac : ((b i).factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem profileOrderedTotalMass_eq_block_mul_rest
    (start : ℕ) {blocks : ℕ} {b : ℕ → ℕ}
    (s : ProfileSlot blocks b) :
    profileOrderedTotalMass start blocks b =
      primeBlockMass (start + profileSlotBlock s) * profileRestMass start s := by
  classical
  unfold profileOrderedTotalMass profileRestMass
  exact Fintype.prod_eq_mul_prod_subtype_ne _ s

private theorem profileRestMass_le_three_mul_total
    (start : ℕ) {blocks : ℕ} {b : ℕ → ℕ}
    (s : ProfileSlot blocks b) :
    profileRestMass start s ≤ 3 * profileOrderedTotalMass start blocks b := by
  have hrest : 0 ≤ profileRestMass start s := by
    unfold profileRestMass
    apply Finset.prod_nonneg
    intro t ht
    exact primeBlockMass_nonneg _
  have hblock : (1 / 3 : ℝ) ≤
      primeBlockMass (start + profileSlotBlock s) :=
    (one_third_lt_primeBlockMass _).le
  calc
    profileRestMass start s =
        3 * ((1 / 3 : ℝ) * profileRestMass start s) := by ring
    _ ≤ 3 * (primeBlockMass (start + profileSlotBlock s) *
        profileRestMass start s) := by gcongr
    _ = 3 * profileOrderedTotalMass start blocks b := by
      rw [profileOrderedTotalMass_eq_block_mul_rest]

private theorem sum_two_pow_profileSlotRank_block_le
    {blocks : ℕ} {b : ℕ → ℕ} (i : Fin blocks) :
    (∑ r : Fin (b i),
      (2 : ℝ) ^ (profileSlotRank (Sigma.mk i r) + 1)) ≤
      2 * (2 : ℝ) ^ profilePrefixCount b i := by
  classical
  let A := ∑ h ∈ Finset.range i.1, b h
  have hgeom : (∑ r ∈ Finset.range (b i), (2 : ℝ) ^ r) =
      (2 : ℝ) ^ b i - 1 := by
    have h := geom_sum_mul (2 : ℝ) (b i)
    norm_num at h ⊢
    exact h
  change (∑ r : Fin (b i), (2 : ℝ) ^ (A + r.1 + 1)) ≤
    2 * (2 : ℝ) ^ profilePrefixCount b i
  rw [Fin.sum_univ_eq_sum_range
    (fun r ↦ (2 : ℝ) ^ (A + r + 1)) (b i)]
  calc
    (∑ r ∈ Finset.range (b i),
        (2 : ℝ) ^ (A + r + 1)) =
        (2 : ℝ) ^ (A + 1) *
          ∑ r ∈ Finset.range (b i), (2 : ℝ) ^ r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [show A + r + 1 = (A + 1) + r by omega, pow_add]
    _ = (2 : ℝ) ^ (A + 1) * ((2 : ℝ) ^ b i - 1) := by
      rw [hgeom]
    _ ≤ (2 : ℝ) ^ (A + 1) * (2 : ℝ) ^ b i := by
      exact mul_le_mul_of_nonneg_left (by linarith)
        (pow_nonneg (by norm_num) _)
    _ = 2 * (2 : ℝ) ^ profilePrefixCount b i := by
      unfold profilePrefixCount A
      rw [Finset.sum_range_succ]
      calc
        (2 : ℝ) ^ (∑ h ∈ Finset.range ↑i, b h + 1) * (2 : ℝ) ^ b ↑i =
            (2 : ℝ) ^ ((∑ h ∈ Finset.range ↑i, b h + 1) + b i) :=
          (pow_add _ _ _).symm
        _ = (2 : ℝ) ^ (1 + ((∑ h ∈ Finset.range ↑i, b h) + b i)) := by
          congr 1
          omega
        _ = (2 : ℝ) ^ 1 *
            (2 : ℝ) ^ ((∑ h ∈ Finset.range ↑i, b h) + b i) :=
          pow_add _ _ _
        _ = 2 * (2 : ℝ) ^ ((∑ h ∈ Finset.range ↑i, b h) + b i) := by
          norm_num

private theorem sum_profileSlot_geometric_le_prefixPotential
    (blocks : ℕ) (b : ℕ → ℕ) :
    (∑ s : ProfileSlot blocks b,
      (2 : ℝ) ^ (profileSlotRank s + 1) /
        (2 : ℝ) ^ profileSlotBlock s) ≤
      2 * profilePrefixPotential blocks b := by
  classical
  rw [Fintype.sum_sigma]
  unfold profilePrefixPotential
  rw [← Fin.sum_univ_eq_sum_range
    (fun i ↦ (2 : ℝ) ^ profilePrefixCount b i / (2 : ℝ) ^ i) blocks]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    (∑ r : Fin (b i),
        (2 : ℝ) ^ (profileSlotRank (Sigma.mk i r) + 1) /
          (2 : ℝ) ^ profileSlotBlock (Sigma.mk i r)) =
        (∑ r : Fin (b i),
          (2 : ℝ) ^ (profileSlotRank (Sigma.mk i r) + 1)) /
            (2 : ℝ) ^ i.1 := by
      simp only [profileSlotBlock, Finset.sum_div]
    _ ≤ (2 * (2 : ℝ) ^ profilePrefixCount b i) /
        (2 : ℝ) ^ i.1 := by
      exact div_le_div_of_nonneg_right
        (sum_two_pow_profileSlotRank_block_le i)
        (by positivity)
    _ = 2 * ((2 : ℝ) ^ profilePrefixCount b i / (2 : ℝ) ^ i.1) := by
      ring

private theorem profileOrderedOffDiagonalMass_le_sharp
    {K : ℝ} (hK : 0 ≤ K)
    (hslice : ∀ (j : ℕ) (x : ℝ),
      (∑ p ∈ (primeBlock j).filter
          (fun p : ℕ ↦ |Real.log (p : ℝ) - x| ≤ Real.log 2),
          (1 : ℝ) / p) ≤ K * (1 / 2 : ℝ) ^ j)
    (start blocks : ℕ) (b : ℕ → ℕ) :
    profileOrderedOffDiagonalMass start blocks b ≤
      6 * K * (2 : ℝ) ^ profilePrimeCount blocks b *
        profileOrderedTotalMass start blocks b * (1 / (2 : ℝ) ^ start) *
          profilePrefixPotential blocks b := by
  classical
  have htotal : 0 ≤ profileOrderedTotalMass start blocks b := by
    unfold profileOrderedTotalMass
    apply Finset.prod_nonneg
    intro s hs
    exact primeBlockMass_nonneg _
  have hcommon : 0 ≤
      3 * profileOrderedTotalMass start blocks b * K *
        (2 : ℝ) ^ profilePrimeCount blocks b * (1 / (2 : ℝ) ^ start) := by
    positivity
  calc
    profileOrderedOffDiagonalMass start blocks b ≤
        ∑ s : ProfileSlot blocks b,
          ∑ p ∈ profileOrderedTuples start blocks b,
            profileOrderedTupleWeight p *
              ((profileCloseLastDiffPairs p s).card : ℝ) :=
      profileOrderedOffDiagonalMass_le_sum_lastDiff start blocks b
    _ ≤ ∑ s : ProfileSlot blocks b,
        profileRestMass start s *
          (K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s) *
            (2 ^ profilePrimeCount blocks b *
              2 ^ (profileSlotRank s + 1) : ℕ)) := by
      exact Finset.sum_le_sum fun s _ ↦
        fixed_slot_lastDiff_mass_le hK hslice start s
    _ ≤ ∑ s : ProfileSlot blocks b,
        (3 * profileOrderedTotalMass start blocks b) *
          (K * (1 / 2 : ℝ) ^ (start + profileSlotBlock s) *
            (2 ^ profilePrimeCount blocks b *
              2 ^ (profileSlotRank s + 1) : ℕ)) := by
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_right (profileRestMass_le_three_mul_total start s)
      positivity
    _ = (3 * profileOrderedTotalMass start blocks b * K *
          (2 : ℝ) ^ profilePrimeCount blocks b *
            (1 / (2 : ℝ) ^ start)) *
        ∑ s : ProfileSlot blocks b,
          (2 : ℝ) ^ (profileSlotRank s + 1) /
            (2 : ℝ) ^ profileSlotBlock s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      push_cast
      rw [pow_add]
      simp only [one_div, inv_pow]
      ring
    _ ≤ (3 * profileOrderedTotalMass start blocks b * K *
          (2 : ℝ) ^ profilePrimeCount blocks b *
            (1 / (2 : ℝ) ^ start)) *
        (2 * profilePrefixPotential blocks b) := by
      exact mul_le_mul_of_nonneg_left
        (sum_profileSlot_geometric_le_prefixPotential blocks b) hcommon
    _ = 6 * K * (2 : ℝ) ^ profilePrimeCount blocks b *
        profileOrderedTotalMass start blocks b * (1 / (2 : ℝ) ^ start) *
          profilePrefixPotential blocks b := by ring

/-! ## The sharp actual-family estimate -/

/-- Ford's sharp per-profile Lemma 4.7 estimate.  The diagonal is exact;
the entire off-diagonal contribution is charged to the maximal differing
prime slot and hence carries only the geometric factor `2⁻ˢᵗᵃʳᵗ` times the
prefix potential. -/
theorem exists_fordSharpPairConstant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (start blocks : ℕ) (b : ℕ → ℕ),
      weightedDyadicPairMass (profileNumberFamily start blocks b) ≤
        (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
        C * (2 : ℝ) ^ profilePrimeCount blocks b *
          profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
            profilePrefixPotential blocks b := by
  obtain ⟨K, hK, hslice⟩ := exists_primeBlock_dyadicLogSlice_le
  refine ⟨6 * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro start blocks b
  rw [weightedDyadicPairMass_profileNumberFamily_eq_diagonal_add_offDiagonal]
  suffices hoff : profileOffDiagonalMass start blocks b ≤
      (6 * K) * (2 : ℝ) ^ profilePrimeCount blocks b *
        profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
          profilePrefixPotential blocks b by
    simpa only [add_comm] using
      add_le_add_left hoff
        ((2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b)
  let F : ℝ := profileFactorial blocks b
  have hF : 0 < F := by
    dsimp [F]
    exact_mod_cast (by
      unfold profileFactorial
      exact Finset.prod_pos fun i hi ↦ Nat.factorial_pos _)
  have hbridge : F * profileOffDiagonalMass start blocks b ≤
      profileOrderedOffDiagonalMass start blocks b := by
    exact profileFactorial_mul_profileOffDiagonalMass_le_ordered start blocks b
  have hordered :=
    profileOrderedOffDiagonalMass_le_sharp hK hslice start blocks b
  have hscaled : F * profileOffDiagonalMass start blocks b ≤
      F * ((6 * K) * (2 : ℝ) ^ profilePrimeCount blocks b *
        profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
          profilePrefixPotential blocks b) := by
    calc
      F * profileOffDiagonalMass start blocks b ≤
          profileOrderedOffDiagonalMass start blocks b := hbridge
      _ ≤ 6 * K * (2 : ℝ) ^ profilePrimeCount blocks b *
          profileOrderedTotalMass start blocks b * (1 / (2 : ℝ) ^ start) *
            profilePrefixPotential blocks b := hordered
      _ = F * ((6 * K) * (2 : ℝ) ^ profilePrimeCount blocks b *
          profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
            profilePrefixPotential blocks b) := by
        rw [profileOrderedTotalMass_eq_factorial_mul_tupleMass]
        change 6 * K * (2 : ℝ) ^ profilePrimeCount blocks b *
            (F * profileTupleMass start blocks b) *
              (1 / (2 : ℝ) ^ start) * profilePrefixPotential blocks b = _
        ring
  exact (mul_le_mul_iff_right₀ hF).mp hscaled

end

end Erdos896.Ford

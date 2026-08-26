import ErdosProblems.Erdos380.CutoffSieve
import ErdosProblems.Erdos380.PrimeCounts
import ErdosProblems.Erdos380.EventualIntervalPrime

/-!
# Long smooth intervals from the elementary large sieve

Use primes of size comparable to the square root of the counting cutoff.
An interval of smooth integers avoids one consecutive block of residues
for each such prime. The one-prime-subset sieve gives a power saving in
the interval length; no theorem on gaps between primes is required.
-/

open scoped BigOperators Function

namespace Erdos380

lemma residueClassSurvivors_card_le_sum_ratio
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i))) (m₀ N : ℕ)
    (hproduct : ∀ i j, modulus i * modulus j ≤ N)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    ((residueClassSurvivors vanishing m₀ N).card : ℝ) ≤
      ((N : ℝ) + N) / ∑ i, residueRemovalRatio modulus vanishing i := by
  classical
  let family := (Finset.univ : Finset I).image (fun i => ({i} : Finset I))
  have hfamily : ∀ T : selectedSubsets family, ∃ i : I, T.1 = {i} := by
    intro T
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp T.2
    exact ⟨i, hi.symm⟩
  have hnon : Nonempty (selectedSubsets family) := by
    let i : I := Classical.arbitrary I
    exact ⟨⟨{i}, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩⟩
  have hprod : ∀ T U : selectedSubsets family,
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N := by
    intro T U
    obtain ⟨i, hi⟩ := hfamily T
    obtain ⟨j, hj⟩ := hfamily U
    simpa only [hi, hj, Finset.prod_singleton] using hproduct i j
  have h := residueClassSurvivors_card_le_selected_ratio modulus hcoprime vanishing
    family m₀ N hnon hprod hnonempty hproper
  have hsum : (∑ T : selectedSubsets family, ∏ i ∈ T.1,
      residueRemovalRatio modulus vanishing i) = ∑ i, residueRemovalRatio modulus vanishing i := by
    rw [Finset.sum_coe_sort family
      (fun T : Finset I => ∏ i ∈ T, residueRemovalRatio modulus vanishing i)]
    dsimp [family]
    rw [Finset.sum_image]
    · simp
    · intro i _ j _ h
      simpa only [Finset.singleton_inj] using h
  rwa [hsum] at h

noncomputable def forwardShiftResidues (q H : ℕ) : Finset (ZMod q) := by
  classical
  exact (Finset.range H).image fun j : ℕ => -(j : ZMod q)

lemma forwardShiftResidues_card {q H : ℕ} (hH : H ≤ q) :
    (forwardShiftResidues q H).card = H := by
  classical
  calc
    (forwardShiftResidues q H).card = (Finset.range H).card := by
      unfold forwardShiftResidues
      apply Finset.card_image_of_injOn
      intro i hi j hj hij
      have heq : (i : ZMod q) = (j : ZMod q) := neg_injective hij
      have hmod := congrArg ZMod.val heq
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ((Finset.mem_range.mp hi).trans_le hH),
        Nat.mod_eq_of_lt ((Finset.mem_range.mp hj).trans_le hH)] using hmod
    _ = H := Finset.card_range H

def smoothRunStarts (N H T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => ∀ j ∈ Finset.range H, largestPrimeFactor (n + j) ≤ T

theorem smoothRunStarts_card_le_of_prime_count {N H T : ℕ}
    (hT : 2 ≤ T) (hH : 0 < H) (hHT : H ≤ T) (hN : N ≤ 4 * T ^ 2)
    (hcount : ((T : ℝ) / Real.log T) / 10 ≤ ((dyadicPrimes T).card : ℝ)) :
    ((smoothRunStarts N H T).card : ℝ) ≤ 160 * (T : ℝ) ^ 2 * Real.log T / H := by
  classical
  let Q := dyadicPrimes T
  have hqprime (q : Q) : q.1.Prime := (Finset.mem_filter.mp q.2).2
  have hqlo (q : Q) : T < q.1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp q.2).1).1
  have hqhi (q : Q) : q.1 ≤ 2 * T := (Finset.mem_Ioc.mp (Finset.mem_filter.mp q.2).1).2
  have hTR : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hQpos : 0 < Q.card := by
    have h : (0 : ℝ) < (Q.card : ℝ) :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < ((T : ℝ) / Real.log T) / 10) hcount
    exact_mod_cast h
  letI : Nonempty Q := (Finset.card_pos.mp hQpos).coe_sort
  letI : ∀ q : Q, NeZero q.1 := fun q => ⟨(hqprime q).ne_zero⟩
  let vanish : ∀ q : Q, Finset (ZMod q.1) := fun q => forwardShiftResidues q.1 H
  have hcoprime : Pairwise (Nat.Coprime on fun q : Q => q.1) := by
    intro q r hqr
    exact (Nat.coprime_primes (hqprime q) (hqprime r)).mpr (Subtype.coe_ne_coe.mpr hqr)
  have hvcard (q : Q) : (vanish q).card = H :=
    forwardShiftResidues_card (hHT.trans (hqlo q).le)
  have hsieve := residueClassSurvivors_card_le_sum_ratio
    (fun q : Q => q.1) hcoprime vanish 0 (4 * T ^ 2)
    (fun q r => (Nat.mul_le_mul (hqhi q) (hqhi r)).trans_eq (by ring))
    (fun q => Finset.card_pos.mp (by rw [hvcard q]; exact hH))
    (fun q => by rw [hvcard q]; exact hHT.trans_lt (hqlo q))
  have hsubset : smoothRunStarts N H T ⊆ residueClassSurvivors vanish 0 (4 * T ^ 2) := by
    intro n hn
    obtain ⟨hnrange, hnsmooth⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnrange
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
    intro q hres
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hres
    have hzero : ((n + j : ℕ) : ZMod q.1) = 0 := by
      rw [Nat.cast_add, ← heq]
      exact neg_add_cancel _
    have hdiv := (ZMod.natCast_eq_zero_iff (n + j) q.1).mp hzero
    have hle := (prime_le_largestPrimeFactor (by omega : n + j ≠ 0) (hqprime q) hdiv).trans
      (hnsmooth j hj)
    exact (not_le_of_gt (hqlo q)) hle
  have hsum : (H : ℝ) / (20 * Real.log T) ≤
      ∑ q : Q, residueRemovalRatio (fun q : Q => q.1) vanish q := by
    have hterm (q : Q) : (H : ℝ) / (2 * T) ≤
        residueRemovalRatio (fun q : Q => q.1) vanish q := by
      unfold residueRemovalRatio
      rw [hvcard q]
      apply div_le_div_of_nonneg_left hHR.le
      · exact_mod_cast Nat.sub_pos_of_lt (hHT.trans_lt (hqlo q))
      · exact_mod_cast (Nat.sub_le q.1 H).trans (hqhi q)
    calc
      (H : ℝ) / (20 * Real.log T) =
          (((T : ℝ) / Real.log T) / 10) * ((H : ℝ) / (2 * T)) := by
        field_simp
        ring
      _ ≤ (Q.card : ℝ) * ((H : ℝ) / (2 * T)) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = ∑ _q : Q, (H : ℝ) / (2 * T) := by simp
      _ ≤ _ := Finset.sum_le_sum fun q _ => hterm q
  calc
    ((smoothRunStarts N H T).card : ℝ) ≤
        (residueClassSurvivors vanish 0 (4 * T ^ 2)).card := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ _ := hsieve
    _ ≤ (((4 * T ^ 2 : ℕ) : ℝ) + (4 * T ^ 2 : ℕ)) / ((H : ℝ) / (20 * Real.log T)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsum
    _ = _ := by push_cast; field_simp; ring

theorem exists_uniform_smoothRunStarts_card_bound : ∃ T₀ : ℕ, ∀ T ≥ T₀,
    ∀ N H : ℕ, 0 < H → H ≤ T → N ≤ 4 * T ^ 2 →
      ((smoothRunStarts N H T).card : ℝ) ≤ 160 * (T : ℝ) ^ 2 * Real.log T / H := by
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp eventually_dyadicPrimes_card_bounds
  refine ⟨max 2 T₁, ?_⟩
  intro T hT N H hH hHT hN
  exact smoothRunStarts_card_le_of_prime_count ((le_max_left _ _).trans hT) hH hHT hN
    (hT₁ T ((le_max_right _ _).trans hT)).1

noncomputable def longBadPointsUpTo (N H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n => ∃ u v : ℕ,
    BadInterval u v ∧ u ≤ n ∧ n ≤ v ∧ 2 * H ≤ v - u + 1

lemma longBadPointsUpTo_card_le_smoothRunStarts {u₀ N H T : ℕ}
    (hanchor : ∀ u v : ℕ, u₀ ≤ u → BadInterval u v →
      ∃ a ∈ Finset.Icc u v, intervalPrime u v ^ 2 ∣ a ∧
        largestPrimeFactor a = intervalPrime u v)
    (hH : 0 < H) (hNT : 2 * N ≤ T ^ 2) :
    (longBadPointsUpTo N H).card ≤ 2 * u₀ + 2 * (smoothRunStarts N H T).card := by
  classical
  let S := smoothRunStarts N H T
  have hsub : longBadPointsUpTo N H ⊆ Finset.Icc 1 (2 * u₀) ∪
      (S ∪ S.image (fun a => a + H - 1)) := by
    intro n hn
    obtain ⟨hnrange, u, v, hbad, hun, hnv, hlen⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnrange
    by_cases hnsmall : n ≤ 2 * u₀
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hn1, hnsmall⟩)
    have hratio := hbad.right_lt_two_mul_left
    have hu₀ : u₀ ≤ u := by omega
    obtain ⟨a, ha, hdiv, _⟩ := hanchor u v hu₀ hbad
    obtain ⟨hua, hav⟩ := Finset.mem_Icc.mp ha
    have hapos : 0 < a := by have := hbad.1; omega
    have hQsq : intervalPrime u v ^ 2 ≤ T ^ 2 :=
      (Nat.le_of_dvd hapos hdiv).trans (by omega)
    have hQT : intervalPrime u v ≤ T := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hQsq
    have hsmooth : ∀ m ∈ Finset.Icc u v, largestPrimeFactor m ≤ T := by
      intro m hm
      exact (largestPrimeFactor_mono_dvd (intervalProduct_pos hbad.1).ne'
        (dvd_intervalProduct hm)).trans hQT
    apply Finset.mem_union_right
    by_cases hright : n + H - 1 ≤ v
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, ?_⟩
      intro j hj
      have hjH := Finset.mem_range.mp hj
      exact hsmooth (n + j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨n + 1 - H, ?_, by omega⟩
      apply Finset.mem_filter.mpr
      have hleft : u ≤ n + 1 - H := by omega
      refine ⟨Finset.mem_Icc.mpr ⟨by have := hbad.1; omega, by omega⟩, ?_⟩
      intro j hj
      have hjH := Finset.mem_range.mp hj
      exact hsmooth (n + 1 - H + j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  calc
    (longBadPointsUpTo N H).card ≤
        (Finset.Icc 1 (2 * u₀) ∪ (S ∪ S.image (fun a => a + H - 1))).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (2 * u₀)).card + (S ∪ S.image (fun a => a + H - 1)).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.Icc 1 (2 * u₀)).card + (S.card + (S.image (fun a => a + H - 1)).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ 2 * u₀ + (S.card + S.card) := by
      have himage : (S.image (fun a => a + H - 1)).card ≤ S.card := Finset.card_image_le
      simp only [Nat.card_Icc] at *
      omega
    _ = _ := by dsimp [S]; omega

/-- Long bad intervals are negligible by a direct large-sieve estimate.
The constants and thresholds are unconditional; there is no prime-gap
hypothesis. The endpoint of a witnessing interval may exceed `N`. -/
theorem exists_uniform_longBadPoints_card_bound : ∃ E T₀ : ℕ, ∀ T ≥ T₀,
    ∀ N H : ℕ, 0 < H → H ≤ T → 2 * N ≤ T ^ 2 →
      ((longBadPointsUpTo N H).card : ℝ) ≤
        E + 320 * (T : ℝ) ^ 2 * Real.log T / H := by
  obtain ⟨u₀, hanchor⟩ := exists_badInterval_square_anchor_threshold
  obtain ⟨T₀, hT₀⟩ := exists_uniform_smoothRunStarts_card_bound
  refine ⟨2 * u₀, T₀, ?_⟩
  intro T hT N H hH hHT hNT
  have h₁ := longBadPointsUpTo_card_le_smoothRunStarts hanchor hH hNT
  have h₂ := hT₀ T hT N H hH hHT (by omega)
  have h₁R : ((longBadPointsUpTo N H).card : ℝ) ≤
      (2 * u₀ : ℕ) + 2 * ((smoothRunStarts N H T).card : ℝ) := by exact_mod_cast h₁
  calc
    _ ≤ _ := h₁R
    _ ≤ ((2 * u₀ : ℕ) : ℝ) + 2 * (160 * (T : ℝ) ^ 2 * Real.log T / H) := by gcongr
    _ = _ := by ring

theorem exists_longBadPoints_card_bound : ∃ E N₀ : ℕ, ∀ N ≥ N₀,
    ∀ H : ℕ, 0 < H → H ^ 2 ≤ 2 * N →
      ((longBadPointsUpTo N H).card : ℝ) ≤ E + 7680 * (N : ℝ) * Real.log N / H := by
  obtain ⟨E, T₀, hbound⟩ := exists_uniform_longBadPoints_card_bound
  refine ⟨E, max 2 (T₀ ^ 2), ?_⟩
  intro N hN H hH hHN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hT₀ : T₀ ^ 2 ≤ 2 * N := ((le_max_right _ _).trans hN).trans (by omega)
  let T := Nat.sqrt (2 * N) + 1
  have hT : T₀ ≤ T := (Nat.le_sqrt'.mpr hT₀).trans (by dsimp [T]; omega)
  have hHT : H ≤ T := (Nat.le_sqrt'.mpr hHN).trans (by dsimp [T]; omega)
  have hNT : 2 * N ≤ T ^ 2 := (Nat.succ_le_succ_sqrt' (2 * N)).trans' (by omega)
  have hsq : T ^ 2 ≤ 8 * N := by
    have h₁ := Nat.sqrt_le' (2 * N)
    have h₂ := Nat.sqrt_le_self (2 * N)
    dsimp [T]
    nlinarith
  have hTN : T ≤ 4 * N := by
    have h := Nat.sqrt_le_self (2 * N)
    dsimp [T]
    omega
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogT : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ T by dsimp [T]; omega))
  have hlog : Real.log (T : ℝ) ≤ 3 * Real.log N := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < T by dsimp [T]; omega))
      (show (T : ℝ) ≤ 4 * N by exact_mod_cast hTN)
    have h₂ : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num)
      (by exact_mod_cast hN2)
    rw [Real.log_mul (by norm_num) (by exact_mod_cast (by omega : N ≠ 0)), Real.log_four_eq] at h
    linarith
  have hsqR : (T : ℝ) ^ 2 ≤ 8 * N := by exact_mod_cast hsq
  have h := hbound T hT N H hH hHT hNT
  calc
    _ ≤ E + 320 * (T : ℝ) ^ 2 * Real.log T / H := h
    _ ≤ E + 320 * (8 * N : ℝ) * (3 * Real.log N) / H := by gcongr
    _ = _ := by ring

end Erdos380

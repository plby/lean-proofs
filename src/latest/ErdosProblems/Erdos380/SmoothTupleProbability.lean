import ErdosProblems.Erdos380.SmoothShiftMass

/-! # A uniform smooth-interval probability bound on prime products -/

open scoped BigOperators Classical

namespace Erdos380

def signedShift (ε : ℤˣ) {H : ℕ} (j : Fin H) : ℤ :=
  (ε : ℤ) * (j.val + 1 : ℕ)

lemma signedShift_natAbs (ε : ℤˣ) {H : ℕ} (j : Fin H) :
    (signedShift ε j).natAbs = j.val + 1 := by
  simp only [signedShift, Int.natAbs_mul, Int.natAbs_natCast,
    Int.isUnit_iff_natAbs_eq.mp ε.isUnit, one_mul]

lemma signedShift_ne_zero (ε : ℤˣ) {H : ℕ} (j : Fin H) : signedShift ε j ≠ 0 := by
  apply Int.natAbs_ne_zero.mp
  rw [signedShift_natAbs]
  omega

noncomputable def smallShiftMassSum (s : Fin 10 → Finset ℕ) (T H c : ℕ) (ε : ℤˣ)
    (f : ∀ i, s i) : ℝ :=
  ∑ j : Fin H, normalizedSmallPrimeMass (smallShiftPrimes T (signedShift ε j)) T c
    (signedShift ε j) (tupleNaturalProduct s f)

def SmoothShiftEvent (s : Fin 10 → Finset ℕ) (T H c D : ℕ) (ε : ℤˣ) (L : ℝ)
    (f : ∀ i, s i) : Prop :=
  ∀ j : Fin H, ∃ n : ℕ, 0 < n ∧
    (n : ℤ) = (c * tupleNaturalProduct s f : ℕ) + signedShift ε j ∧
    largestPrimeFactor n ≤ T ^ 110 ∧ (∀ d : ℕ, d ^ 2 ∣ n → d ≤ D) ∧ L ≤ Real.log n

lemma sum_largeShiftPrimeCount (s : Fin 10 → Finset ℕ) (T H c : ℕ) (ε : ℤˣ)
    (f : ∀ i, s i) :
    (∑ j : Fin H, largeShiftPrimeCount T (T ^ 110) c (tupleNaturalProduct s f) (signedShift ε j)) =
      shiftedPrimeHitCount s (mixingModulusPrimes T) H c ε f := by
  simp only [largeShiftPrimeCount, smallPrimeDivisibilityEvent, signedShift,
    shiftedPrimeHitCount, mixingModulusPrimes]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd : (p : ℤ) ∣ (c * tupleNaturalProduct s f : ℕ) + (ε : ℤ) * (j.val + 1 : ℕ) <;>
    simp [hd]

lemma SmoothShiftEvent.log_mass_bound
    {s : Fin 10 → Finset ℕ} {T H c D : ℕ} {ε : ℤˣ} {L : ℝ} {f : ∀ i, s i}
    (hevent : SmoothShiftEvent s T H c D ε L f) (hT : 2 ≤ T) (hD : 0 < D) :
    (H : ℝ) * L ≤ (H : ℝ) * (2 * Real.log D + Real.log H) +
      Real.log T * smallShiftMassSum s T H c ε f +
      (110 * Real.log T) * shiftedPrimeHitCount s (mixingModulusPrimes T) H c ε f := by
  have hpoint (j : Fin H) : L ≤ 2 * Real.log D + Real.log H +
      Real.log T * normalizedSmallPrimeMass (smallShiftPrimes T (signedShift ε j)) T c
        (signedShift ε j) (tupleNaturalProduct s f) +
      Real.log (T ^ 110 : ℕ) * largeShiftPrimeCount T (T ^ 110) c (tupleNaturalProduct s f) (signedShift ε j) := by
    obtain ⟨n, hn, heq, hsmooth, hsq, hL⟩ := hevent j
    have hmass := smooth_shift_log_le_masses hn hD hsq hT (signedShift_ne_zero ε j) heq hsmooth
    have hlog : Real.log ((signedShift ε j).natAbs : ℝ) ≤ Real.log (H : ℝ) := by
      rw [signedShift_natAbs]
      exact Real.log_le_log (by positivity) (by exact_mod_cast (by have := j.isLt; omega : j.val + 1 ≤ H))
    linarith
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin H))) (fun j _ => hpoint j)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, smallShiftMassSum, sum_largeShiftPrimeCount,
    Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, mul_add] using hsum

lemma SmoothShiftEvent.small_or_large
    {s : Fin 10 → Finset ℕ} {T H c D : ℕ} {ε : ℤˣ} {L U : ℝ} {f : ∀ i, s i}
    (hevent : SmoothShiftEvent s T H c D ε L f) (hT : 2 ≤ T) (hD : 0 < D)
    (hL : 2 * Real.log D + Real.log H + 111 * U * Real.log T ≤ L) :
    (H : ℝ) * U ≤ smallShiftMassSum s T H c ε f ∨
      (H : ℝ) * U ≤ shiftedPrimeHitCount s (mixingModulusPrimes T) H c ε f := by
  have hmass := hevent.log_mass_bound hT hD
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  by_contra h
  push Not at h
  have hsmall := mul_lt_mul_of_pos_left h.1 hlog
  have hlarge := mul_lt_mul_of_pos_left h.2 (show 0 < 110 * Real.log (T : ℝ) by positivity)
  have hthreshold := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ H by positivity)
  nlinarith

theorem exists_uniform_smallShiftMassSum_tail :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ N : Fin 10 → ℕ,
      (∀ i, T ^ 90 ≤ N i) → (∀ i, N i ≤ T ^ 110) → ∀ H : ℕ, 0 < H →
      ∀ c : ℕ, ∀ ε : ℤˣ, ∀ U : ℝ, 0 < U →
      ((Finset.univ.filter fun f : ∀ i, dyadicPrimes (N i) => (H : ℝ) * U ≤
        smallShiftMassSum (fun i => dyadicPrimes (N i)) T H c ε f).card : ℝ) /
        (Fintype.card (∀ i, dyadicPrimes (N i)) : ℝ) ≤ K / U ^ 50 := by
  obtain ⟨K, hK, T₁, hm⟩ := exists_uniform_smallPrime_tuple_moment
  refine ⟨K, hK, max 2 T₁, ?_⟩
  intro T hT N hlow hhigh H hH c ε U hU
  letI : Nonempty (Fin H) := ⟨⟨0, hH⟩⟩
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hmoment := hm T ((le_max_right _ _).trans hT) N hlow hhigh c
  convert
    finite_sum_fiftieth_tail_le (Finset.univ : Finset (Fin H)) Finset.univ_nonempty Finset.univ
      (fun j f => normalizedSmallPrimeMass (smallShiftPrimes T (signedShift ε j)) T c
        (signedShift ε j) (tupleNaturalProduct (fun i => dyadicPrimes (N i)) f)) K
      (fun j _ f _ => normalizedSmallPrimeMass_nonneg _ hT2 c _ _)
      (fun j _ => hmoment (signedShift ε j) (smallShiftPrimes T (signedShift ε j))
        (Finset.filter_subset _ _) (fun p hp => (Finset.mem_filter.mp hp).2)) hU using 1
  simp only [Finset.card_univ, Fintype.card_fin, smallShiftMassSum]
  rfl

lemma finite_probability_union_bound {Ω : Type*} (s : Finset Ω) (A B E : Ω → Prop)
    (hE : ∀ ω ∈ s, E ω → A ω ∨ B ω) :
    ((s.filter E).card : ℝ) / (s.card : ℝ) ≤
      ((s.filter A).card : ℝ) / (s.card : ℝ) + ((s.filter B).card : ℝ) / (s.card : ℝ) := by
  classical
  have hsub : s.filter E ⊆ s.filter A ∪ s.filter B := by
    intro ω hω
    obtain ⟨hωs, hωE⟩ := Finset.mem_filter.mp hω
    rcases hE ω hωs hωE with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hωs, ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hωs, hb⟩)
  have hc : (s.filter E).card ≤ (s.filter A).card + (s.filter B).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

/-- The finite probability estimate for a smooth interval adjacent to a
ten-prime product. Every size condition and square-divisor exception is
explicit. No smooth-number asymptotic or prime-gap result is used here. -/
theorem exists_uniform_smoothShift_probability_bound :
    ∃ C K U₀ : ℝ, 0 < C ∧ 0 < K ∧ 0 < U₀ ∧ ∃ T₀ : ℕ,
      ∀ T ≥ T₀, ∀ N : Fin 10 → ℕ,
      (∀ i, T ^ 90 ≤ N i) → (∀ i, N i ≤ T ^ 110) →
      ∀ H : ℕ, 0 < H → H ≤ T → (H : ℝ) * (C * (Real.log T ^ 5 / (T : ℝ))) ≤ 1 →
      ∀ c D : ℕ, 0 < D → ∀ ε : ℤˣ, ∀ U L : ℝ, U₀ ≤ U → (H : ℝ) ≤ U ^ 48 →
      2 * Real.log D + Real.log H + 111 * U * Real.log T ≤ L →
      ((Finset.univ.filter fun f : ∀ i, dyadicPrimes (N i) =>
        SmoothShiftEvent (fun i => dyadicPrimes (N i)) T H c D ε L f).card : ℝ) /
        (Fintype.card (∀ i, dyadicPrimes (N i)) : ℝ) ≤ K / ((H : ℝ) * U ^ 2) := by
  obtain ⟨C, Kl, U₀, hC, hKl, hU₀, Tl, hl⟩ := exists_uniform_shifted_prime_hit_tail
  obtain ⟨Ks, hKs, Ts, hs⟩ := exists_uniform_smallShiftMassSum_tail
  refine ⟨C, Ks + Kl, U₀, hC, by positivity, hU₀, max 2 (max Tl Ts), ?_⟩
  intro T hT N hlow hhigh H hH hHT hmix c D hD ε U L hU hHU hL
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hTl : Tl ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTs : Ts ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hUpos : 0 < U := hU₀.trans_le hU
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hsmall := hs T hTs N hlow hhigh H hH c ε U hUpos
  have hlarge := hl T hTl N hlow hhigh H hH hHT hmix c ε U hU
  have hunion := finite_probability_union_bound
    (Finset.univ : Finset (∀ i, dyadicPrimes (N i)))
    (fun f => (H : ℝ) * U ≤ smallShiftMassSum (fun i => dyadicPrimes (N i)) T H c ε f)
    (fun f => (H : ℝ) * U ≤ shiftedPrimeHitCount (fun i => dyadicPrimes (N i))
      (mixingModulusPrimes T) H c ε f)
    (SmoothShiftEvent (fun i => dyadicPrimes (N i)) T H c D ε L)
    (fun f _ hf => hf.small_or_large hT2 hD hL)
  simp only [Finset.card_univ] at hunion
  have hsmall' : Ks / U ^ 50 ≤ Ks / ((H : ℝ) * U ^ 2) := by
    apply div_le_div_of_nonneg_left hKs.le (by positivity)
    calc
      (H : ℝ) * U ^ 2 ≤ U ^ 48 * U ^ 2 := mul_le_mul_of_nonneg_right hHU (by positivity)
      _ = U ^ 50 := by rw [← pow_add]
  exact hunion.trans ((add_le_add (hsmall.trans hsmall') hlarge).trans (by rw [add_div]))

end Erdos380

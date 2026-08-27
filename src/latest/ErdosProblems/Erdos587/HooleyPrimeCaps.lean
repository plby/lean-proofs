import ErdosProblems.Erdos587.HooleyPrimeChoices

/-!
# Divisor caps at all prime prefixes

The normalized prefix restrictions are downward closed. Mertens turns
them into the logarithmic divisor cap required by the moment induction,
and the finite maximal inequality controls their discarded mass.
-/

open scoped BigOperators

namespace Erdos587

lemma squarefree_prime_finset_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp r hr hpr => ?_)
    (fun p hp => (hS p hp).squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hS p hp) (hS r hr)).mpr hpr

lemma card_divisors_eq_two_pow_primeFactors {n : ℕ} (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn.ne_zero]
  calc
    _ = ∏ _p ∈ n.primeFactors, 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := Finset.prod_const _

noncomputable def deltaReciprocalMeanConstant : ℝ :=
  Classical.choose (exists_squarefree_divisorPower_log_bound 0)

lemma deltaReciprocalMeanConstant_pos : 0 < deltaReciprocalMeanConstant :=
  (Classical.choose_spec (exists_squarefree_divisorPower_log_bound 0)).1

lemma delta_prime_eulerProduct_le {x : ℕ} (hx : 2 ≤ x) (S : Finset ℕ)
    (hS : S ⊆ Nat.primesLE x) :
    (∏ p ∈ S, (1 + (1 : ℝ) / p)) ≤ deltaReciprocalMeanConstant * Real.log (x : ℝ) := by
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primesLE.mp (hS hp)).2
  have hsf := squarefree_prime_finset_prod S hprime
  have h := (Classical.choose_spec (exists_squarefree_divisorPower_log_bound 0)).2
    x (∏ p ∈ S, p) hx hsf
  change (∏ p ∈ S, p : ℕ).primeFactors ⊆ Nat.primesLE x →
    (∑ n ∈ (∏ p ∈ S, p : ℕ).divisors, (n.divisors.card : ℝ) ^ 0 / n) ≤
      deltaReciprocalMeanConstant * Real.log (x : ℝ) ^ (2 ^ 0 : ℕ) at h
  simp only [pow_zero, pow_one, Nat.primeFactors_prod hprime] at h
  have hbound := h hS
  rw [sum_reciprocal_divisors_eq_eulerProduct hsf, Nat.primeFactors_prod hprime] at hbound
  exact hbound

lemma deltaPrimeChoiceMass_eq {P : List ℕ} (hP : P.Nodup) :
    deltaChoiceMass (deltaPrimeWeights P) = ∏ p ∈ P.toFinset, (1 + (1 : ℝ) / p) := by
  unfold deltaChoiceMass deltaPrimeWeights
  rw [List.map_map, List.prod_toFinset _ hP]
  rfl

lemma deltaPrimePrefixNormalizer_le {P : List ℕ} (hP : P.Nodup) (k : ℕ)
    {x : ℕ} (hx : 2 ≤ x) (hsub : (P.take k).toFinset ⊆ Nat.primesLE x) :
    deltaPrimePrefixNormalizer P k ≤ deltaReciprocalMeanConstant * Real.log (x : ℝ) := by
  unfold deltaPrimePrefixNormalizer
  rw [← List.prod_toFinset _ hP.take]
  apply le_trans _ (delta_prime_eulerProduct_le hx _ hsub)
  apply Finset.prod_le_prod
  · intro p hp
    exact (deltaChoiceNormalizer_pos (by positivity)).le
  · intro p hp
    exact deltaChoiceNormalizer_le_one_add (by positivity)

def MeetsDeltaPrimePrefixes (P : List ℕ) (A : ℝ) (n : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ P.length →
    (2 : ℝ) ^ (n.primeFactors ∩ (P.take k).toFinset).card ≤
      A * deltaPrimePrefixNormalizer P k

lemma meetsDeltaPrimePrefixes_one (P : List ℕ) {A : ℝ} (hA : 1 ≤ A) :
    MeetsDeltaPrimePrefixes P A 1 := by
  intro k hk
  simpa only [Nat.primeFactors_one, Finset.empty_inter, Finset.card_empty, pow_zero] using
    one_le_mul_of_one_le_of_one_le hA (one_le_deltaPrimePrefixNormalizer P k)

lemma MeetsDeltaPrimePrefixes.of_dvd {P : List ℕ} {A : ℝ} {m n : ℕ}
    (h : MeetsDeltaPrimePrefixes P A n) (hn : n ≠ 0) (hmn : m ∣ n) :
    MeetsDeltaPrimePrefixes P A m := by
  intro k hk
  have hsub : m.primeFactors ∩ (P.take k).toFinset ⊆
      n.primeFactors ∩ (P.take k).toFinset := by
    intro p hp
    obtain ⟨hpm, hpk⟩ := Finset.mem_inter.mp hp
    exact Finset.mem_inter.mpr ⟨Nat.primeFactors_mono hmn hn hpm, hpk⟩
  apply le_trans _ (h k hk)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hsub)

lemma exists_sorted_cutoff_prefix (P : List ℕ) (hP : P.Pairwise (· ≤ ·)) (x : ℕ) :
    ∃ k ≤ P.length, (P.take k).toFinset = P.toFinset.filter (fun p => p < x) := by
  induction P with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons p P ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hP
    by_cases hp : p < x
    · obtain ⟨k, hk, heq⟩ := ih htail
      refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
      simp only [List.take_succ_cons, List.toFinset_cons, Finset.filter_insert,
        hp, if_true, heq]
    · refine ⟨0, Nat.zero_le _, ?_⟩
      simp only [List.take_zero, List.toFinset_nil]
      symm
      apply Finset.eq_empty_of_forall_notMem
      intro r hr
      obtain ⟨hrP, hrx⟩ := Finset.mem_filter.mp hr
      rcases List.mem_cons.mp (List.mem_toFinset.mp hrP) with rfl | hrP
      · exact hp hrx
      · have hpr := hhead r hrP
        omega

lemma MeetsDeltaPrimePrefixes.divisor_cap {P : List ℕ} (hP : P.Nodup)
    (hsorted : P.Pairwise (· ≤ ·)) {X : ℕ} (hPset : P.toFinset = X.primesBelow)
    {A : ℝ} (hA : 0 ≤ A) {n x : ℕ} (hx : 2 ≤ x) (hxX : x ≤ X)
    (hn : n ∈ deltaSmoothNumbers x) (h : MeetsDeltaPrimePrefixes P A n) :
    (n.divisors.card : ℝ) ≤ deltaReciprocalMeanConstant * A * Real.log (x : ℝ) := by
  obtain ⟨k, hk, hprefix⟩ := exists_sorted_cutoff_prefix P hsorted x
  have hprefix' : (P.take k).toFinset = x.primesBelow := by
    rw [hprefix, hPset]
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesBelow]
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · exact fun h => ⟨⟨h.1.trans_le hxX, h.2⟩, h.1⟩
  have hsf := (mem_deltaSmoothNumbers.mp hn).1
  have hsub : n.primeFactors ⊆ (P.take k).toFinset := by
    rw [hprefix']
    exact (mem_deltaSmoothNumbers.mp hn).2
  have hcap := h k hk
  rw [Finset.inter_eq_left.mpr hsub] at hcap
  have hmean := deltaPrimePrefixNormalizer_le hP k hx (by
    rw [hprefix']
    intro p hp
    obtain ⟨hpx, hp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpx.le, hp⟩)
  calc
    _ = (2 : ℝ) ^ n.primeFactors.card := by
      exact_mod_cast card_divisors_eq_two_pow_primeFactors hsf
    _ ≤ A * deltaPrimePrefixNormalizer P k := hcap
    _ ≤ A * (deltaReciprocalMeanConstant * Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_left hmean hA
    _ = _ := by ring

open Classical in
/-- The actual squarefree reciprocal mass discarded by all prime-prefix
restrictions is at most the total Euler mass divided by the threshold. -/
theorem deltaPrimePrefixes_exceptional_mass_le {P : List ℕ} (hP : P.Nodup)
    {X : ℕ} (hPset : P.toFinset = X.primesBelow) {A : ℝ} (hA : 0 < A) :
    (∑ n ∈ (deltaSmoothNumbers X).filter (fun n => ¬ MeetsDeltaPrimePrefixes P A n),
      (1 : ℝ) / n) ≤ deltaChoiceMass (deltaPrimeWeights P) / A := by
  let prod := fun s : DeltaPrimeChoice P => ∏ p ∈ deltaPrimeChoiceSet P s, p
  let D := Finset.univ.filter (fun s : DeltaPrimeChoice P => ¬ MeetsDeltaPrimePrefixes P A (prod s))
  have hcover : (deltaSmoothNumbers X).filter (fun n => ¬ MeetsDeltaPrimePrefixes P A n) ⊆
      D.image prod := by
    intro n hn
    obtain ⟨hnS, hbad⟩ := Finset.mem_filter.mp hn
    obtain ⟨hsf, hsub⟩ := mem_deltaSmoothNumbers.mp hnS
    rw [← hPset] at hsub
    obtain ⟨s, hs⟩ := exists_deltaPrimeChoiceSet P n.primeFactors hsub
    have hprod : prod s = n := by
      dsimp only [prod]
      rw [hs, Nat.prod_primeFactors_of_squarefree hsf]
    exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr
      ⟨Finset.mem_univ s, hprod.symm ▸ hbad⟩, hprod⟩
  have hcross (s : DeltaPrimeChoice P) (hbad : ¬ MeetsDeltaPrimePrefixes P A (prod s)) :
      ∃ k ≤ (deltaPrimeWeights P).length,
        A ≤ deltaChoicePrefixValue (deltaPrimeWeights P) 1 s k := by
    have hprime : ∀ p ∈ deltaPrimeChoiceSet P s, p.Prime := by
      intro p hp
      have hmem := deltaPrimeChoiceSet_subset P s hp
      rw [hPset] at hmem
      exact (Nat.mem_primesBelow.mp hmem).2
    have hfp : (prod s).primeFactors = deltaPrimeChoiceSet P s := Nat.primeFactors_prod hprime
    unfold MeetsDeltaPrimePrefixes at hbad
    push Not at hbad
    obtain ⟨k, hk, hfail⟩ := hbad
    refine ⟨k, by simpa only [deltaPrimeWeights, List.length_map] using hk, ?_⟩
    rw [deltaPrimeChoicePrefixValue_eq hP, one_mul]
    have hnorm : 0 < deltaPrimePrefixNormalizer P k :=
      lt_of_lt_of_le zero_lt_one (one_le_deltaPrimePrefixNormalizer P k)
    apply (le_div_iff₀ hnorm).mpr
    simpa only [hfp] using hfail.le
  calc
    _ ≤ ∑ n ∈ D.image prod, (1 : ℝ) / n :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => by positivity)
    _ ≤ ∑ s ∈ D, (1 : ℝ) / prod s :=
      Finset.sum_image_le_of_nonneg (fun n _ => by positivity)
    _ = ∑ s : DeltaPrimeChoice P,
        if ¬ MeetsDeltaPrimePrefixes P A (prod s) then deltaChoiceWeight (deltaPrimeWeights P) s
          else 0 := by
      dsimp only [D]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s hs
      rw [deltaPrimeChoiceWeight_eq hP]
    _ ≤ ∑ s : DeltaPrimeChoice P,
        if ∃ k ≤ (deltaPrimeWeights P).length,
            A ≤ deltaChoicePrefixValue (deltaPrimeWeights P) 1 s k then
          deltaChoiceWeight (deltaPrimeWeights P) s else 0 := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hbad : ¬ MeetsDeltaPrimePrefixes P A (prod s)
      · rw [if_pos hbad, if_pos (hcross s hbad)]
      · simp only [hbad, if_false]
        split_ifs
        · exact deltaChoiceWeight_nonneg (by
            intro a ha
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
            positivity) s
        · exact le_rfl
    _ ≤ _ := deltaChoice_prefix_maximal (by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      positivity) hA

end Erdos587

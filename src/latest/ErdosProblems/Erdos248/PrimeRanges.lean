import ErdosProblems.Erdos248.Mass

/-!
# Erdős Problem 248: deterministic prime-range bookkeeping

The analytic argument only has to control two finite prime ranges.  Tiny
prime divisors are inherited from the shift because the sampled integer is
zero modulo the primorial, while prime divisors above the largest sieve
radius are bounded just from the size of the integer.
-/

noncomputable section

open scoped ArithmeticFunction.omega BigOperators

namespace Erdos248

def omegaLE (m y : ℕ) : ℕ :=
  (m.primeFactors.filter fun p => p ≤ y).card

def omegaBetween (m lo hi : ℕ) : ℕ :=
  (m.primeFactors.filter fun p => lo < p ∧ p ≤ hi).card

def omegaAbove (m y : ℕ) : ℕ :=
  (m.primeFactors.filter fun p => y < p).card

theorem omega_eq_le_add_between_add_above (m lo hi : ℕ) (hlohi : lo ≤ hi) :
    ω m = omegaLE m lo + omegaBetween m lo hi + omegaAbove m hi := by
  rw [omega_eq_primeFactors_card]
  classical
  let A := m.primeFactors.filter fun p => p ≤ lo
  let B := m.primeFactors.filter fun p => lo < p ∧ p ≤ hi
  let C := m.primeFactors.filter fun p => hi < p
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    have hpA' := Finset.mem_filter.mp hpA
    have hpB' := Finset.mem_filter.mp hpB
    omega
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro p hpAB hpC
    have hpC' := Finset.mem_filter.mp hpC
    rcases Finset.mem_union.mp hpAB with hpA | hpB
    · have hpA' := Finset.mem_filter.mp hpA
      omega
    · have hpB' := Finset.mem_filter.mp hpB
      omega
  have hcover : m.primeFactors = (A ∪ B) ∪ C := by
    ext p
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      by_cases hplo : p ≤ lo
      · exact Or.inl (Or.inl ⟨hp, hplo⟩)
      · by_cases hphi : p ≤ hi
        · exact Or.inl (Or.inr ⟨hp, Nat.lt_of_not_ge hplo, hphi⟩)
        · exact Or.inr ⟨hp, Nat.lt_of_not_ge hphi⟩
    · rintro ((⟨hp, _⟩ | ⟨hp, _, _⟩) | ⟨hp, _⟩) <;> exact hp
  calc
    m.primeFactors.card = ((A ∪ B) ∪ C).card :=
      congrArg Finset.card hcover
    _ = A.card + B.card + C.card := by
      rw [Finset.card_union_of_disjoint hABC,
        Finset.card_union_of_disjoint hAB]
    _ = omegaLE m lo + omegaBetween m lo hi + omegaAbove m hi := by
      rfl

theorem omegaLE_mono {m a b : ℕ} (hab : a ≤ b) :
    omegaLE m a ≤ omegaLE m b := by
  unfold omegaLE
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.trans hab⟩

theorem omegaLE_le_self (m y : ℕ) : omegaLE m y ≤ y := by
  unfold omegaLE
  calc
    (m.primeFactors.filter fun p => p ≤ y).card ≤
        (Finset.Icc 1 y).card := by
      apply Finset.card_le_card
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hp'.1).one_le, hp'.2⟩
    _ = y := by simp

theorem omegaLE_tiny_le_omega_shift {n k w : ℕ}
    (hk : 0 < k) (hW : primorial w ∣ n) :
    omegaLE (n + k) w ≤ ω k := by
  rw [omega_eq_primeFactors_card]
  unfold omegaLE
  apply Finset.card_le_card
  intro p hp
  have hpf := Finset.mem_filter.mp hp
  have hpPrime := Nat.prime_of_mem_primeFactors hpf.1
  have hpk : p ∣ k :=
    (prime_dvd_add_iff_of_primorial_dvd hW hpPrime hpf.2).mp
      (Nat.dvd_of_mem_primeFactors hpf.1)
  exact Nat.mem_primeFactors.mpr ⟨hpPrime, hpk, hk.ne'⟩

theorem omegaLE_max_tiny_shift_le {n k w : ℕ}
    (hk : 0 < k) (hW : primorial w ∣ n) :
    omegaLE (n + k) (max w k) ≤ ω k + k := by
  unfold omegaLE
  rw [omega_eq_primeFactors_card]
  let A := (n + k).primeFactors.filter fun p => p ≤ w
  let B := (n + k).primeFactors.filter fun p => w < p ∧ p ≤ k
  have hcover :
      (n + k).primeFactors.filter (fun p => p ≤ max w k) ⊆ A ∪ B := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    by_cases hpw : p ≤ w
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp'.1, hpw⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hp'.1, Nat.lt_of_not_ge hpw, (le_max_iff.mp hp'.2).resolve_left hpw⟩)
  calc
    ((n + k).primeFactors.filter fun p => p ≤ max w k).card ≤
        (A ∪ B).card := Finset.card_le_card hcover
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ ≤ k.primeFactors.card + k := by
      apply Nat.add_le_add
      · simpa only [A, omegaLE, omega_eq_primeFactors_card] using
          (omegaLE_tiny_le_omega_shift hk hW)
      · calc
          B.card ≤ (Finset.Icc 1 k).card := by
            apply Finset.card_le_card
            intro p hp
            have hp' := Finset.mem_filter.mp hp
            exact Finset.mem_Icc.mpr
              ⟨(Nat.prime_of_mem_primeFactors hp'.1).one_le, hp'.2.2⟩
          _ = k := by simp
    _ = ω k + k := by rw [omega_eq_primeFactors_card]

theorem sieveWeight_ne_zero_primorial_dvd {K n : ℕ}
    (hn : sieveWeight K n ≠ 0) :
    primorial (tinyCutoff K) ∣ n := by
  unfold sieveWeight preSieveModulus at hn
  unfold BoundedGaps.Maynard.preSievedSquareDivisorWeight at hn
  split at hn
  next hmod => exact Nat.modEq_zero_iff_dvd.mp hmod
  next => simp at hn

theorem omegaLE_max_of_sieveWeight_ne_zero {K n k : ℕ}
    (hk : 0 < k) (hn : sieveWeight K n ≠ 0) :
    omegaLE (n + k) (max (tinyCutoff K) k) ≤ ω k + k := by
  exact omegaLE_max_tiny_shift_le hk
    (sieveWeight_ne_zero_primorial_dvd hn)

theorem omegaAbove_lt_of_lt_pow {m y t : ℕ} (hm : 0 < m)
    (hsize : m < (y + 1) ^ t) :
    omegaAbove m y < t := by
  let S := m.primeFactors.filter fun p => y < p
  have hSprod : (y + 1) ^ S.card ≤ ∏ p ∈ S, p := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro p hp
      exact Nat.zero_le _
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
  have hsubset : S ⊆ m.primeFactors := Finset.filter_subset _ _
  have hdiv : (∏ p ∈ S, p) ∣ m :=
    (Finset.prod_dvd_prod_of_subset S m.primeFactors id hsubset).trans
      (Nat.prod_primeFactors_dvd m)
  have hprodle : (∏ p ∈ S, p) ≤ m := Nat.le_of_dvd hm hdiv
  by_contra hnot
  have ht : t ≤ S.card := Nat.le_of_not_gt hnot
  have hpow : (y + 1) ^ t ≤ (y + 1) ^ S.card :=
    Nat.pow_le_pow_right (by omega) ht
  have : (y + 1) ^ t ≤ m := hpow.trans (hSprod.trans hprodle)
  exact (Nat.not_le_of_gt hsize) this

theorem largestRadius_pow_hundred {K : ℕ} (hK : 0 < K) :
    shiftRadius K 1 ^ 100 = intervalStart K := by
  rw [shiftRadius, ← pow_mul, intervalStart,
    intervalExponent_eq_pow_mul_shiftExponent (K := K) (k := 1)
      (by omega : 1 ≤ K)]
  congr 1
  norm_num
  ring

theorem four_le_largestRadius {K : ℕ} (hK : 0 < K) :
    4 ≤ shiftRadius K 1 := by
  unfold shiftRadius
  have hexp : 2 ≤ 100 ^ (100 * K - 1) := by
    have hne : 100 * K - 1 ≠ 0 := by omega
    have h := Nat.one_lt_pow hne (show 1 < (100 : ℕ) by norm_num)
    omega
  simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hexp

theorem three_intervalStart_lt_largestRadius_pow_101 {K : ℕ}
    (hK : 0 < K) :
    3 * intervalStart K < shiftRadius K 1 ^ 101 := by
  rw [show 101 = 100 + 1 by norm_num, pow_add,
    largestRadius_pow_hundred hK, pow_one]
  have hx : 0 < intervalStart K := intervalStart_pos K
  have hR : 3 < shiftRadius K 1 := (four_le_largestRadius hK)
  nlinarith

theorem add_lt_three_intervalStart {K n k : ℕ} (hn : n < 2 * intervalStart K)
    (hk : k ≤ intervalExponent K) :
    n + k < 3 * intervalStart K := by
  have hMx : intervalExponent K < intervalStart K := by
    unfold intervalStart
    exact (intervalExponent K).lt_two_pow_self
  omega

theorem omegaAbove_largestRadius_lt_101 {K n k : ℕ} (hK : 0 < K)
    (hnlow : intervalStart K ≤ n) (hn : n < 2 * intervalStart K)
    (hk : k ≤ intervalExponent K) :
    omegaAbove (n + k) (shiftRadius K 1) < 101 := by
  apply omegaAbove_lt_of_lt_pow (by
    exact (intervalStart_pos K).trans_le (hnlow.trans (Nat.le_add_right n k)))
  exact (add_lt_three_intervalStart hn hk).trans
    (three_intervalStart_lt_largestRadius_pow_101 hK) |>.trans_le
      (Nat.pow_le_pow_left (by omega) 101)

theorem omega_le_self {m : ℕ} (hm : 0 < m) : ω m ≤ m := by
  rw [omega_eq_primeFactors_card]
  calc
    m.primeFactors.card ≤ (Finset.Icc 1 m).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hp).one_le,
          Nat.le_of_dvd hm (Nat.dvd_of_mem_primeFactors hp)⟩
    _ = m := by simp

theorem omega_le_three_ranges (m a c : ℕ) :
    ω m ≤ omegaLE m a + omegaBetween m a c + omegaAbove m c := by
  rw [omega_eq_primeFactors_card]
  unfold omegaLE omegaBetween omegaAbove
  let A := m.primeFactors.filter fun p => p ≤ a
  let B := m.primeFactors.filter fun p => a < p ∧ p ≤ c
  let C := m.primeFactors.filter fun p => c < p
  have hcover : m.primeFactors ⊆ (A ∪ B) ∪ C := by
    intro p hp
    by_cases hpa : p ≤ a
    · exact Finset.mem_union_left C
        (Finset.mem_union_left B (Finset.mem_filter.mpr ⟨hp, hpa⟩))
    · by_cases hpc : p ≤ c
      · exact Finset.mem_union_left C
          (Finset.mem_union_right A (Finset.mem_filter.mpr
            ⟨hp, Nat.lt_of_not_ge hpa, hpc⟩))
      · exact Finset.mem_union_right (A ∪ B)
          (Finset.mem_filter.mpr ⟨hp, Nat.lt_of_not_ge hpc⟩)
  calc
    m.primeFactors.card ≤ ((A ∪ B) ∪ C).card :=
      Finset.card_le_card hcover
    _ ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    _ ≤ (A.card + B.card) + C.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _

theorem omega_le_four_ranges (m a b c : ℕ) :
    ω m ≤ omegaLE m a + omegaBetween m a b +
      omegaBetween m b c + omegaAbove m c := by
  rw [omega_eq_primeFactors_card]
  unfold omegaLE omegaBetween omegaAbove
  let A := m.primeFactors.filter fun p => p ≤ a
  let B := m.primeFactors.filter fun p => a < p ∧ p ≤ b
  let C := m.primeFactors.filter fun p => b < p ∧ p ≤ c
  let D := m.primeFactors.filter fun p => c < p
  have hcover : m.primeFactors ⊆ ((A ∪ B) ∪ C) ∪ D := by
    intro p hp
    by_cases hpa : p ≤ a
    · exact Finset.mem_union_left D (Finset.mem_union_left C
        (Finset.mem_union_left B (Finset.mem_filter.mpr ⟨hp, hpa⟩)))
    · by_cases hpb : p ≤ b
      · exact Finset.mem_union_left D (Finset.mem_union_left C
          (Finset.mem_union_right A (Finset.mem_filter.mpr
            ⟨hp, Nat.lt_of_not_ge hpa, hpb⟩)))
      · by_cases hpc : p ≤ c
        · exact Finset.mem_union_left D (Finset.mem_union_right (A ∪ B)
            (Finset.mem_filter.mpr ⟨hp, Nat.lt_of_not_ge hpb, hpc⟩))
        · exact Finset.mem_union_right ((A ∪ B) ∪ C)
            (Finset.mem_filter.mpr ⟨hp, Nat.lt_of_not_ge hpc⟩)
  calc
    m.primeFactors.card ≤ (((A ∪ B) ∪ C) ∪ D).card :=
      Finset.card_le_card hcover
    _ ≤ ((A ∪ B) ∪ C).card + D.card := Finset.card_union_le _ _
    _ ≤ ((A ∪ B).card + C.card) + D.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((A.card + B.card) + C.card) + D.card := by
      gcongr
      exact Finset.card_union_le _ _

theorem tinyCutoff_le_shiftRadius {K k : ℕ} (hK : 0 < K) (hk : k ≤ K) :
    tinyCutoff K ≤ shiftRadius K k := by
  apply Nat.pow_le_pow_right (by norm_num)
  have hKpow : K ≤ 100 ^ K := by
    exact K.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_left (by norm_num) K)
  calc
    100 * K ≤ 100 * 100 ^ K := Nat.mul_le_mul_left 100 hKpow
    _ = 100 ^ (K + 1) := by rw [pow_succ']
    _ ≤ 100 ^ (100 * K - k) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

theorem shiftRadius_le_largest {K k : ℕ} (hk1 : 1 ≤ k) :
    shiftRadius K k ≤ shiftRadius K 1 := by
  unfold shiftRadius
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.pow_le_pow_right (by norm_num)
  omega

theorem omega_near_le_deterministic_add_ranges {K n k : ℕ} (hK : 0 < K)
    (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hnlow : intervalStart K ≤ n) (hnhigh : n < 2 * intervalStart K)
    (hnweight : sieveWeight K n ≠ 0) :
    ω (n + k) ≤ 2 * k +
      omegaBetween (n + k) (tinyCutoff K) (shiftRadius K k) +
      omegaBetween (n + k) (shiftRadius K k) (shiftRadius K 1) + 100 := by
  have hranges := omega_le_four_ranges (n + k) (tinyCutoff K)
    (shiftRadius K k) (shiftRadius K 1)
  have htiny := omegaLE_max_of_sieveWeight_ne_zero hk1 hnweight
  have hmax : max (tinyCutoff K) k = tinyCutoff K :=
    max_eq_left (hkK.trans (K_le_tinyCutoff K))
  rw [hmax] at htiny
  have hkomega : ω k ≤ k := omega_le_self hk1
  have hKM : K ≤ intervalExponent K := by
    unfold intervalExponent
    calc
      K ≤ 2 ^ K := K.lt_two_pow_self.le
      _ ≤ 100 ^ K := Nat.pow_le_pow_left (by norm_num) K
      _ ≤ 100 ^ (100 * K) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have habove := omegaAbove_largestRadius_lt_101 hK hnlow hnhigh
    (hkK.trans hKM)
  omega

theorem omega_far_le_deterministic_add_range {K n k : ℕ} (hK : 0 < K)
    (hk1 : 1 ≤ k) (hkM : k ≤ intervalExponent K)
    (hnlow : intervalStart K ≤ n) (hnhigh : n < 2 * intervalStart K)
    (hnweight : sieveWeight K n ≠ 0) :
    ω (n + k) ≤ 2 * k +
      omegaBetween (n + k) (max (tinyCutoff K) k) (shiftRadius K 1) + 100 := by
  have hranges := omega_le_three_ranges (n + k)
    (max (tinyCutoff K) k) (shiftRadius K 1)
  have htiny := omegaLE_max_of_sieveWeight_ne_zero hk1 hnweight
  have hkomega : ω k ≤ k := omega_le_self hk1
  have habove := omegaAbove_largestRadius_lt_101 hK hnlow hnhigh hkM
  omega

end Erdos248

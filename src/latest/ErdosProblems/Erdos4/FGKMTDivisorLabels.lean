import ErdosProblems.Erdos4.DivisorCoefficients
import ErdosProblems.Erdos4.FGKMTRationalMoments

/-! Exact conversion between prime labels and coprime squarefree divisor tuples. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients Classical

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

omit [DecidableEq P] in
theorem label_product_over_primeFactors {M : Type*} [CommMonoid M]
    (ell : P → ℕ) (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {u : ℕ} (hu : u ≠ 0) (hcover : ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (f : ℕ → M) :
    (∏ p, if ell p ∣ u then f (ell p) else 1) = ∏ q ∈ u.primeFactors, f q := by
  rw [← Finset.prod_filter]
  apply Finset.prod_bij (fun p _ => ell p)
  · intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p, (Finset.mem_filter.mp hp).2, hu⟩
  · intro p hp q hq hpq
    exact hinj hpq
  · intro q hq
    obtain ⟨p, hp⟩ := hcover q hq
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hp⟩
    rw [hp]
    exact Nat.dvd_of_mem_primeFactors hq
  · intro p hp
    rfl

theorem label_totient_primeFactors {u : ℕ} (hu : Squarefree u) :
    Nat.totient u = ∏ p ∈ u.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hu,
    Nat.div_self hu.ne_zero.bot_lt, one_mul]

omit [DecidableEq P] in
theorem prime_dvd_coordinateDivisor_iff (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (a : P → Option (Fin k)) (p : P) (i : Fin k) :
    ell p ∣ coordinateDivisor ell a i ↔ a p = some i := by
  unfold coordinateDivisor
  rw [(Nat.prime_iff.mp (hprime p)).dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, _, hq⟩
    by_cases ha : a q = some i
    · rw [if_pos ha] at hq
      have hpq := hinj ((Nat.prime_dvd_prime_iff_eq (hprime p) (hprime q)).mp hq)
      simpa only [hpq] using ha
    · rw [if_neg ha] at hq
      exact ((hprime p).not_dvd_one hq).elim
  · intro ha
    exact ⟨p, Finset.mem_univ p, by rw [if_pos ha]⟩

omit [DecidableEq P] in
theorem coordinateDivisor_primeFactors_covered (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (a : P → Option (Fin k)) (i : Fin k) :
    ∀ q ∈ (coordinateDivisor ell a i).primeFactors, ∃ p, ell p = q := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hdiv := Nat.dvd_of_mem_primeFactors hq
  unfold coordinateDivisor at hdiv
  obtain ⟨p, _, hp⟩ := (Nat.prime_iff.mp hqp).dvd_finsetProd_iff _ |>.mp hdiv
  by_cases ha : a p = some i
  · rw [if_pos ha] at hp
    exact ⟨p, ((Nat.prime_dvd_prime_iff_eq hqp (hprime p)).mp hp).symm⟩
  · rw [if_neg ha] at hp
    exact (hqp.not_dvd_one hp).elim

omit [DecidableEq P] in
theorem coordinateDivisor_squarefree (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (a : P → Option (Fin k)) (i : Fin k) : Squarefree (coordinateDivisor ell a i) := by
  unfold coordinateDivisor
  rw [← Finset.prod_filter]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p _ q _ hpq => ?_)
    (fun p _ => (hprime p).squarefree)
  change IsRelPrime (ell p) (ell q)
  rw [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hprime p) (hprime q)).mpr (fun heq => hpq (hinj heq))

omit [DecidableEq P] in
theorem coordinateDivisor_coprime (ell : P → ℕ) {W : ℕ}
    (hcop : ∀ p, (ell p).Coprime W) (a : P → Option (Fin k)) (i : Fin k) :
    (coordinateDivisor ell a i).Coprime W := by
  unfold coordinateDivisor
  apply Nat.Coprime.prod_left
  intro p _
  split_ifs
  · exact hcop p
  · exact Nat.coprime_one_left W

theorem totient_coordinateDivisor (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (a : P → Option (Fin k)) (i : Fin k) :
    (coordinateDivisor ell a i).totient = ∏ p, if a p = some i then ell p - 1 else 1 := by
  rw [label_totient_primeFactors (coordinateDivisor_squarefree ell hprime hinj a i)]
  rw [← label_product_over_primeFactors ell hprime hinj
    (coordinateDivisor_pos ell (fun p => (hprime p).pos) a i).ne'
    (coordinateDivisor_primeFactors_covered ell hprime a i) (fun q => q - 1)]
  simp_rw [prime_dvd_coordinateDivisor_iff ell hprime hinj]

theorem normalization_sq_eq_totient_product (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (a : P → Option (Fin k)) :
    normalization ell a ^ 2 = ∏ i : Fin k, ((coordinateDivisor ell a i).totient : ℝ)⁻¹ := by
  simp_rw [totient_coordinateDivisor ell hprime hinj, Nat.cast_prod, ← Finset.prod_inv_distrib]
  rw [Finset.prod_comm]
  unfold normalization
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  cases ha : a p with
  | none => simp [localWeight]
  | some j =>
    have hnonneg : 0 ≤ (ell p : ℝ) - 1 := by
      have hh : (1 : ℝ) ≤ ell p := by exact_mod_cast (hprime p).one_le
      linarith
    rw [localWeight, inv_pow, Real.sq_sqrt hnonneg]
    simp only [Option.some.injEq, Nat.cast_ite, Nat.cast_one, apply_ite (Inv.inv : ℝ → ℝ), inv_one]
    rw [Finset.prod_ite_eq]
    simp only [Finset.mem_univ, if_true, Nat.cast_sub (hprime p).one_le, Nat.cast_one]

theorem normalization_sq_eq_harmonic_product (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell) {W : ℕ}
    (hcop : ∀ p, (ell p).Coprime W) (a : P → Option (Fin k)) :
    normalization ell a ^ 2 = ∏ i : Fin k, squarefreeHarmonicWeight W (coordinateDivisor ell a i) := by
  rw [normalization_sq_eq_totient_product ell hprime hinj]
  apply Finset.prod_congr rfl
  intro i _
  rw [squarefreeHarmonicWeight, if_pos ⟨coordinateDivisor_squarefree ell hprime hinj a i,
    coordinateDivisor_coprime ell hcop a i⟩, one_div]

omit [DecidableEq P] in
theorem coordinateDivisor_injective (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell) :
    Function.Injective (coordinateDivisor (k := k) ell) := by
  intro a b hab
  have hiff (p : P) (i : Fin k) : a p = some i ↔ b p = some i := by
    rw [← prime_dvd_coordinateDivisor_iff ell hprime hinj a p i,
      ← prime_dvd_coordinateDivisor_iff ell hprime hinj b p i, hab]
  funext p
  cases ha : a p with
  | none =>
    cases hb : b p with
    | none => rfl
    | some i =>
      have hi := (hiff p i).mpr hb
      rw [ha] at hi
      cases hi
  | some i => exact ((hiff p i).mp ha).symm

noncomputable def labelOfTuple (ell : P → ℕ) (d : Fin k → ℕ) (p : P) : Option (Fin k) :=
  if h : ∃ i, ell p ∣ d i then some h.choose else none

omit [Fintype P] [DecidableEq P] in
theorem labelOfTuple_eq_some_iff (ell : P → ℕ) (hprime : ∀ p, (ell p).Prime)
    (d : Fin k → ℕ) (hcop : Pairwise (fun i j => (d i).Coprime (d j)))
    (p : P) (i : Fin k) : labelOfTuple ell d p = some i ↔ ell p ∣ d i := by
  unfold labelOfTuple
  split_ifs with h
  · constructor
    · intro heq
      exact (Option.some.inj heq) ▸ h.choose_spec
    · intro hi
      congr 1
      by_contra hne
      have hh := (hcop hne).of_dvd h.choose_spec hi
      exact (hprime p).ne_one (by simpa using hh)
  · constructor
    · intro heq
      exact heq.elim
    · intro hi
      exact (h ⟨i, hi⟩).elim

theorem coordinateDivisor_labelOfTuple (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (d : Fin k → ℕ) (hcop : Pairwise (fun i j => (d i).Coprime (d j)))
    (hsq : ∀ i, Squarefree (d i))
    (hcover : ∀ i q, q ∈ (d i).primeFactors → ∃ p, ell p = q) (i : Fin k) :
    coordinateDivisor ell (labelOfTuple ell d) i = d i := by
  unfold coordinateDivisor
  simp_rw [labelOfTuple_eq_some_iff ell hprime d hcop]
  calc
    _ = ∏ q ∈ (d i).primeFactors, q := by
      simpa only [id_eq] using
        label_product_over_primeFactors ell hprime hinj (hsq i).ne_zero (hcover i) id
    _ = d i := Nat.prod_primeFactors_of_squarefree (hsq i)

end Erdos4.FGKMT

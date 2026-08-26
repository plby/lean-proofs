/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierIncidence

/-!
# Surjectivity of the prime-choice divisor reconstruction

Every squarefree four-tuple at the prime cutoff, with coprimality between
different coordinates in each affine family, comes from exactly one
prime-choice function. No Fourier weight or limiting argument is assumed.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem exists_primePairState_of_nonempty (L R : Prop) (h : L ∨ R) :
    ∃ r : Fin 3, (primePairStateLeft r ↔ L) ∧ (primePairStateRight r ↔ R) := by
  classical
  by_cases hL : L
  · by_cases hR : R
    · exact ⟨2, by simp [primePairStateLeft, primePairStateRight, hL, hR]⟩
    · exact ⟨0, by simp [primePairStateLeft, primePairStateRight, hL, hR]⟩
  · have hR := h.resolve_left hL
    exact ⟨1, by simp [primePairStateLeft, primePairStateRight, hL, hR]⟩

theorem exists_primePairChoice_of_unique_coordinate {ι : Type*}
    (I : ι → Bool → Prop)
    (huniq : ∀ i j, (∃ b, I i b) → (∃ b, I j b) → i = j) :
    ∃ c : Option (ι × Fin 3), ∀ i b, primePairChoiceIncidence c i b ↔ I i b := by
  classical
  by_cases hactive : ∃ i b, I i b
  · obtain ⟨i, b, hi⟩ := hactive
    have hflags : I i false ∨ I i true := by cases b <;> simp_all
    obtain ⟨r, hleft, hright⟩ := exists_primePairState_of_nonempty _ _ hflags
    refine ⟨some (i, r), ?_⟩
    intro j a
    by_cases hji : j = i
    · subst j
      cases a with
      | false => simpa [primePairChoiceIncidence] using hleft
      | true => simpa [primePairChoiceIncidence] using hright
    · have hn : ¬I j a := fun hj ↦ hji (huniq j i ⟨a, hj⟩ ⟨b, hi⟩)
      simp [primePairChoiceIncidence, Ne.symm hji, hn]
  · refine ⟨none, ?_⟩
    intro i b
    have hn : ¬I i b := fun hi ↦ hactive ⟨i, b, hi⟩
    simp [primePairChoiceIncidence, hn]

def WithinFamilyDivisorCoprime {ι : Type*} (d : (ι ⊕ ι) → Bool → ℕ) : Prop :=
  (∀ i j, i ≠ j → ∀ a b, (d (.inl i) a).Coprime (d (.inl j) b)) ∧
    (∀ i j, i ≠ j → ∀ a b, (d (.inr i) a).Coprime (d (.inr j) b))

theorem prime_coordinate_unique_of_coprime {ι : Type*}
    (d : ι → Bool → ℕ) (hcop : ∀ i j, i ≠ j → ∀ a b, (d i a).Coprime (d j b))
    {p : ℕ} (hp : p.Prime) :
    ∀ i j, (∃ b, p ∣ d i b) → (∃ b, p ∣ d j b) → i = j := by
  intro i j hi hj
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  by_contra hij
  have hg := Nat.dvd_gcd ha hb
  rw [(hcop i j hij a b).gcd_eq_one] at hg
  exact hp.not_dvd_one hg

theorem exists_doubledPrimeChoice_of_prime_divisibility {ι : Type*}
    (d : (ι ⊕ ι) → Bool → ℕ) (hcop : WithinFamilyDivisorCoprime d)
    {p : ℕ} (hp : p.Prime) :
    ∃ c : DoubledPrimeChoice ι,
      ∀ i b, doubledPrimeChoiceIncidence c i b ↔ p ∣ d i b := by
  obtain ⟨a, ha⟩ := exists_primePairChoice_of_unique_coordinate
    (fun i b ↦ p ∣ d (.inl i) b)
    (prime_coordinate_unique_of_coprime (fun i ↦ d (.inl i)) hcop.1 hp)
  obtain ⟨b, hb⟩ := exists_primePairChoice_of_unique_coordinate
    (fun i b ↦ p ∣ d (.inr i) b)
    (prime_coordinate_unique_of_coprime (fun i ↦ d (.inr i)) hcop.2 hp)
  refine ⟨(doubledPrimeChoicePairEquiv ι).symm (a, b), ?_⟩
  intro i r
  cases i with
  | inl i => simpa only [doubledPrimeChoiceIncidence, Equiv.apply_symm_apply] using ha i r
  | inr i => simpa only [doubledPrimeChoiceIncidence, Equiv.apply_symm_apply] using hb i r

theorem exists_doubledPrimeChoiceDivisor_eq {ι : Type*}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (d : (ι ⊕ ι) → Bool → ℕ)
    (hsq : ∀ i b, Squarefree (d i b))
    (hdiv : ∀ i b, d i b ∣ ∏ p ∈ P, p)
    (hcop : WithinFamilyDivisorCoprime d) :
    ∃ c : P → DoubledPrimeChoice ι, doubledPrimeChoiceDivisor P c = d := by
  classical
  have hlocal : ∀ p : P, ∃ c : DoubledPrimeChoice ι,
      ∀ i b, doubledPrimeChoiceIncidence c i b ↔ p.val ∣ d i b :=
    fun p ↦ exists_doubledPrimeChoice_of_prime_divisibility d hcop (hP p p.property)
  choose c hc using hlocal
  refine ⟨c, ?_⟩
  funext i b
  have hselected : selectedCutoffPrimes P c (fun a ↦ doubledPrimeChoiceIncidence a i b) =
      (d i b).primeFactors := by
    ext p
    by_cases hpP : p ∈ P
    · rw [mem_selectedCutoffPrimes P c _ ⟨p, hpP⟩, hc ⟨p, hpP⟩]
      simp [Nat.mem_primeFactors, hP p hpP, (hsq i b).ne_zero]
    · apply iff_of_false
      · exact fun hp ↦ hpP (selectedCutoffPrimes_subset P c _ hp)
      · intro hp
        have hsub := Nat.primeFactors_mono (hdiv i b) (primeFinsetProduct_pos P hP).ne'
        have hp' := hsub hp
        rw [Nat.primeFactors_prod hP] at hp'
        exact hpP hp'
  rw [doubledPrimeChoiceDivisor, hselected, Nat.prod_primeFactors_of_squarefree (hsq i b)]

theorem primePairChoiceIncidence_unique {ι : Type*} {c : Option (ι × Fin 3)}
    {i j : ι} {a b : Bool}
    (hi : primePairChoiceIncidence c i a) (hj : primePairChoiceIncidence c j b) : i = j := by
  obtain ⟨r, hr, _⟩ := hi
  obtain ⟨s, hs, _⟩ := hj
  exact congrArg Prod.fst (Option.some.inj (hr.symm.trans hs))

theorem doubledPrimeChoiceDivisor_withinFamilyCoprime {ι : Type*}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c : P → DoubledPrimeChoice ι) :
    WithinFamilyDivisorCoprime (doubledPrimeChoiceDivisor P c) := by
  have hlocal (f : ι → ι ⊕ ι)
      (huniq : ∀ (v : DoubledPrimeChoice ι) i j a b,
        doubledPrimeChoiceIncidence v (f i) a →
        doubledPrimeChoiceIncidence v (f j) b → i = j) :
      ∀ i j, i ≠ j → ∀ a b,
        (doubledPrimeChoiceDivisor P c (f i) a).Coprime
          (doubledPrimeChoiceDivisor P c (f j) b) := by
    intro i j hij a b
    apply Nat.coprime_of_dvd
    intro p hp hpi hpj
    have hpP := (prime_dvd_primeFinsetProduct_iff P hP hp).mp
      (hpi.trans (doubledPrimeChoiceDivisor_dvd P c (f i) a))
    exact hij (huniq (c ⟨p, hpP⟩) i j a b
      ((prime_dvd_doubledPrimeChoiceDivisor_iff P hP c (f i) a ⟨p, hpP⟩).mp hpi)
      ((prime_dvd_doubledPrimeChoiceDivisor_iff P hP c (f j) b ⟨p, hpP⟩).mp hpj))
  constructor
  · exact hlocal Sum.inl fun v i j a b hi hj ↦ primePairChoiceIncidence_unique hi hj
  · exact hlocal Sum.inr fun v i j a b hi hj ↦ primePairChoiceIncidence_unique hi hj

def doubledCutoffDivisorTuples (ι : Type*) [Fintype ι] (P : Finset ℕ) :
    Finset ((ι ⊕ ι) → Bool → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : ι ⊕ ι ↦
    Fintype.piFinset fun _ : Bool ↦ (∏ p ∈ P, p).divisors).filter WithinFamilyDivisorCoprime

theorem mem_doubledCutoffDivisorTuples {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (d : (ι ⊕ ι) → Bool → ℕ) :
    d ∈ doubledCutoffDivisorTuples ι P ↔
      (∀ i b, d i b ∣ ∏ p ∈ P, p) ∧ WithinFamilyDivisorCoprime d := by
  classical
  simp [doubledCutoffDivisorTuples, Fintype.mem_piFinset, Nat.mem_divisors,
    (primeFinsetProduct_pos P hP).ne']

theorem doubledCutoffDivisorTuples_eq_image {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    doubledCutoffDivisorTuples ι P =
      (Finset.univ : Finset (P → DoubledPrimeChoice ι)).image (doubledPrimeChoiceDivisor P) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨hdiv, hcop⟩ := (mem_doubledCutoffDivisorTuples P hP d).mp hd
    have hsq : ∀ i b, Squarefree (d i b) := fun i b ↦
      (primeFinsetProduct_squarefree P hP).squarefree_of_dvd (hdiv i b)
    obtain ⟨c, hc⟩ := exists_doubledPrimeChoiceDivisor_eq P hP d hsq hdiv hcop
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩
  · intro hd
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
    exact (mem_doubledCutoffDivisorTuples P hP _).mpr
      ⟨doubledPrimeChoiceDivisor_dvd P c,
        doubledPrimeChoiceDivisor_withinFamilyCoprime P hP c⟩

theorem sum_doubledCutoffDivisorTuples {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (F : ((ι ⊕ ι) → Bool → ℕ) → M) :
    (∑ d ∈ doubledCutoffDivisorTuples ι P, F d) =
      ∑ c : P → DoubledPrimeChoice ι, F (doubledPrimeChoiceDivisor P c) := by
  classical
  rw [doubledCutoffDivisorTuples_eq_image P hP]
  exact Finset.sum_image fun c hc d hd h ↦ doubledPrimeChoiceDivisor_injective P hP h

end

end Erdos4b

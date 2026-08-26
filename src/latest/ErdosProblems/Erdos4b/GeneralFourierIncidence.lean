/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPrimeSubsets

/-!
# Reconstructing divisor tuples from prime-local choices

The four divisor tuples are genuine positive squarefree natural numbers.
Prime divisibility recovers every choice, so the reconstruction has no
multiplicities. This is the arithmetic reindexing for a finite Euler sum.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def primePairChoiceIncidence {ι : Type*} (c : Option (ι × Fin 3))
    (i : ι) (right : Bool) : Prop :=
  ∃ r, c = some (i, r) ∧
    (if right then primePairStateRight r else primePairStateLeft r)

theorem primePairChoiceIncidence_exists {ι : Type*}
    (c : Option (ι × Fin 3)) (i : ι) :
    (∃ b, primePairChoiceIncidence c i b) ↔ ∃ r, c = some (i, r) := by
  constructor
  · rintro ⟨b, r, h, _⟩
    exact ⟨r, h⟩
  · rintro ⟨r, rfl⟩
    rcases primePairState_nonempty r with h | h
    · exact ⟨false, r, rfl, h⟩
    · exact ⟨true, r, rfl, h⟩

theorem primePairChoice_eq_of_incidence {ι : Type*}
    {c d : Option (ι × Fin 3)}
    (h : ∀ i b, primePairChoiceIncidence c i b ↔ primePairChoiceIncidence d i b) :
    c = d := by
  cases c with
  | none =>
      cases d with
      | none => rfl
      | some v =>
          obtain ⟨i, r⟩ := v
          obtain ⟨b, hb⟩ := (primePairChoiceIncidence_exists (some (i, r)) i).mpr ⟨r, rfl⟩
          have hc := (h i b).mpr hb
          simp [primePairChoiceIncidence] at hc
  | some v =>
      obtain ⟨i, r⟩ := v
      obtain ⟨b, hb⟩ := (primePairChoiceIncidence_exists (some (i, r)) i).mpr ⟨r, rfl⟩
      obtain ⟨s, rfl⟩ := (primePairChoiceIncidence_exists d i).mp ⟨b, (h i b).mp hb⟩
      have hleft := h i false
      have hright := h i true
      fin_cases r <;> fin_cases s <;>
        simp_all [primePairChoiceIncidence, primePairStateLeft, primePairStateRight]

def doubledPrimeChoicePairEquiv (ι : Type*) :
    DoubledPrimeChoice ι ≃ (Option (ι × Fin 3) × Option (ι × Fin 3)) where
  toFun
    | none => (none, none)
    | some (.inl a) => (some a, none)
    | some (.inr (.inl b)) => (none, some b)
    | some (.inr (.inr ((i, j), (r, s)))) => (some (i, r), some (j, s))
  invFun
    | (none, none) => none
    | (some a, none) => some (.inl a)
    | (none, some b) => some (.inr (.inl b))
    | (some (i, r), some (j, s)) => some (.inr (.inr ((i, j), (r, s))))
  left_inv := by
    rintro (_ | (a | (b | ⟨⟨i, j⟩, ⟨r, s⟩⟩))) <;> rfl
  right_inv := by
    rintro ⟨(_ | ⟨i, r⟩), (_ | ⟨j, s⟩)⟩ <;> rfl

def doubledPrimeChoiceIncidence {ι : Type*}
    (c : DoubledPrimeChoice ι) : (ι ⊕ ι) → Bool → Prop
  | .inl i, b => primePairChoiceIncidence ((doubledPrimeChoicePairEquiv ι c).1) i b
  | .inr j, b => primePairChoiceIncidence ((doubledPrimeChoicePairEquiv ι c).2) j b

theorem doubledPrimeChoice_eq_of_incidence {ι : Type*}
    {c d : DoubledPrimeChoice ι}
    (h : ∀ i b, doubledPrimeChoiceIncidence c i b ↔ doubledPrimeChoiceIncidence d i b) :
    c = d := by
  apply (doubledPrimeChoicePairEquiv ι).injective
  apply Prod.ext
  · exact primePairChoice_eq_of_incidence fun i b ↦ h (.inl i) b
  · exact primePairChoice_eq_of_incidence fun i b ↦ h (.inr i) b

theorem doubledPrimeChoiceIncidence_exists_iff {ι : Type*} (c : DoubledPrimeChoice ι) :
    (∃ i b, doubledPrimeChoiceIncidence c i b) ↔ c ≠ none := by
  constructor
  · rintro ⟨i, b, hi⟩ rfl
    cases i <;> simp [doubledPrimeChoiceIncidence, doubledPrimeChoicePairEquiv,
      primePairChoiceIncidence] at hi
  · intro hc
    by_contra h
    apply hc
    apply doubledPrimeChoice_eq_of_incidence
    intro i b
    have hn : ¬doubledPrimeChoiceIncidence c i b := fun hi ↦ h ⟨i, b, hi⟩
    have hnone : ¬doubledPrimeChoiceIncidence (none : DoubledPrimeChoice ι) i b := by
      cases i <;> simp [doubledPrimeChoiceIncidence, doubledPrimeChoicePairEquiv,
        primePairChoiceIncidence]
    exact iff_of_false hn hnone

def selectedCutoffPrimes {α : Type*} (P : Finset ℕ)
    (c : P → α) (I : α → Prop) : Finset ℕ := by
  classical
  exact P.filter fun p ↦ ∃ hp : p ∈ P, I (c ⟨p, hp⟩)

theorem selectedCutoffPrimes_subset {α : Type*} (P : Finset ℕ)
    (c : P → α) (I : α → Prop) : selectedCutoffPrimes P c I ⊆ P := by
  classical
  exact Finset.filter_subset _ _

theorem mem_selectedCutoffPrimes {α : Type*} (P : Finset ℕ)
    (c : P → α) (I : α → Prop) (p : P) :
    p.val ∈ selectedCutoffPrimes P c I ↔ I (c p) := by
  classical
  simp [selectedCutoffPrimes, p.property]

theorem prod_selectedCutoffPrimes {α M : Type*} [CommMonoid M]
    (P : Finset ℕ) (c : P → α) (I : α → Prop) [DecidablePred I] (f : ℕ → M) :
    (∏ p ∈ selectedCutoffPrimes P c I, f p) =
      ∏ p : P, if I (c p) then f p else 1 := by
  classical
  rw [← Finset.prod_coe_sort (selectedCutoffPrimes P c I) f]
  rw [← Finset.prod_filter]
  apply Finset.prod_bij (fun p _ ↦ (⟨p.val, selectedCutoffPrimes_subset P c I p.property⟩ : P))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_selectedCutoffPrimes P c I _).mp p.property
  · intro p hp q hq h
    exact Subtype.ext (congrArg (fun x : P ↦ x.val) h)
  · intro p hp
    have hi := (Finset.mem_filter.mp hp).2
    exact ⟨⟨p.val, (mem_selectedCutoffPrimes P c I p).mpr hi⟩, Finset.mem_univ _, rfl⟩
  · intro p hp
    rfl

def doubledPrimeChoiceDivisor {ι : Type*} (P : Finset ℕ)
    (c : P → DoubledPrimeChoice ι) (i : ι ⊕ ι) (b : Bool) : ℕ :=
  ∏ p ∈ selectedCutoffPrimes P c (fun a ↦ doubledPrimeChoiceIncidence a i b), p

theorem doubledPrimeChoiceDivisor_pos {ι : Type*} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (c : P → DoubledPrimeChoice ι) (i : ι ⊕ ι) (b : Bool) :
    0 < doubledPrimeChoiceDivisor P c i b :=
  primeFinsetProduct_pos _ fun p hp ↦ hP p (selectedCutoffPrimes_subset P c _ hp)

theorem doubledPrimeChoiceDivisor_squarefree {ι : Type*} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (c : P → DoubledPrimeChoice ι) (i : ι ⊕ ι) (b : Bool) :
    Squarefree (doubledPrimeChoiceDivisor P c i b) :=
  primeFinsetProduct_squarefree _ fun p hp ↦ hP p (selectedCutoffPrimes_subset P c _ hp)

theorem doubledPrimeChoiceDivisor_dvd {ι : Type*} (P : Finset ℕ)
    (c : P → DoubledPrimeChoice ι) (i : ι ⊕ ι) (b : Bool) :
    doubledPrimeChoiceDivisor P c i b ∣ ∏ p ∈ P, p :=
  Finset.prod_dvd_prod_of_subset _ _ id (selectedCutoffPrimes_subset P c _)

theorem prime_dvd_doubledPrimeChoiceDivisor_iff {ι : Type*} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (c : P → DoubledPrimeChoice ι)
    (i : ι ⊕ ι) (b : Bool) (p : P) :
    p.val ∣ doubledPrimeChoiceDivisor P c i b ↔ doubledPrimeChoiceIncidence (c p) i b := by
  rw [doubledPrimeChoiceDivisor,
    prime_dvd_primeFinsetProduct_iff _
      (fun q hq ↦ hP q (selectedCutoffPrimes_subset P c _ hq)) (hP p p.property),
    mem_selectedCutoffPrimes]

theorem doubledPrimeChoiceDivisor_injective {ι : Type*}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Function.Injective (doubledPrimeChoiceDivisor (ι := ι) P) := by
  intro c d h
  funext p
  apply doubledPrimeChoice_eq_of_incidence
  intro i b
  rw [← prime_dvd_doubledPrimeChoiceDivisor_iff P hP c i b p,
    ← prime_dvd_doubledPrimeChoiceDivisor_iff P hP d i b p, h]

theorem lcm_doubledPrimeChoiceDivisor {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c : P → DoubledPrimeChoice ι) :
    (Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
        (fun ib ↦ doubledPrimeChoiceDivisor P c ib.1 ib.2) =
      ∏ p ∈ selectedCutoffPrimes P c (· ≠ none), p := by
  classical
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro ib hib
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    have hpP := selectedCutoffPrimes_subset P c _ hp
    apply (mem_selectedCutoffPrimes P c (· ≠ none) ⟨p, hpP⟩).mpr
    apply (doubledPrimeChoiceIncidence_exists_iff _).mp
    exact ⟨ib.1, ib.2, (mem_selectedCutoffPrimes P c _ ⟨p, hpP⟩).mp hp⟩
  · apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      change IsRelPrime p q
      rw [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes
        (hP p (selectedCutoffPrimes_subset P c _ hp))
        (hP q (selectedCutoffPrimes_subset P c _ hq))).mpr hpq
    · intro p hp
      have hpP := selectedCutoffPrimes_subset P c _ hp
      have hactive := (mem_selectedCutoffPrimes P c (· ≠ none) ⟨p, hpP⟩).mp hp
      obtain ⟨i, b, hi⟩ := (doubledPrimeChoiceIncidence_exists_iff _).mpr hactive
      exact ((prime_dvd_doubledPrimeChoiceDivisor_iff P hP c i b ⟨p, hpP⟩).mpr hi).trans
        (Finset.dvd_lcm (Finset.mem_univ (i, b)))

end

end Erdos4b

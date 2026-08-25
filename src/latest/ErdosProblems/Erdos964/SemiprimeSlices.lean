import ErdosProblems.Erdos964.SemiprimeIntervals

/-!
# Prime slices of a semiprime interval

The smaller and larger prime supports are separated, so multiplication is
injective on their product. These identities retain exact integer endpoints.
-/

namespace Erdos964

open scoped BigOperators

def primeProductInterval (P Q : Finset ℕ) (x y : ℕ) : Finset ℕ :=
  (primeProductBlock P Q y).filter (fun n => x < n)

def primeSlice (Q : Finset ℕ) (p x y : ℕ) : Finset ℕ :=
  Q.filter (fun r => x < p * r ∧ p * r ≤ y)

theorem sum_primeProductInterval {V : Type*} [AddCommMonoid V]
    (P Q : Finset ℕ) (x y : ℕ) (w : ℕ → V)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r) :
    (∑ n ∈ primeProductInterval P Q x y, w n) =
      ∑ p ∈ P, ∑ r ∈ primeSlice Q p x y, w (p * r) := by
  rw [primeProductInterval, Finset.sum_filter,
    sum_primeProductBlock P Q y _ hP hQ hsep]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_filter]
  congr 1
  ext r
  simp only [primeSlice, Finset.mem_filter]
  tauto

theorem mem_primeProductInterval (P Q : Finset ℕ) (x y m : ℕ) :
    m ∈ primeProductInterval P Q x y ↔
      ∃ p ∈ P, ∃ r ∈ Q, x < p * r ∧ p * r ≤ y ∧ p * r = m := by
  simp only [primeProductInterval, primeProductBlock, Finset.mem_filter,
    Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨⟨p, r, ⟨⟨hp, hr⟩, hhi⟩, rfl⟩, hlo⟩
    exact ⟨p, hp, r, hr, hlo, hhi, rfl⟩
  · rintro ⟨p, hp, r, hr, hlo, hhi, rfl⟩
    exact ⟨⟨p, r, ⟨⟨hp, hr⟩, hhi⟩, rfl⟩, hlo⟩

theorem semiprimeScaleInterval_eq_primeProductInterval (P : Finset ℕ)
    (L x y : ℕ) (hxy : x ≤ y) :
    semiprimeScaleInterval P L x y =
      primeProductInterval P ((Finset.Ioc L (L ^ 2)).filter Nat.Prime) x y := by
  rw [semiprimeScaleInterval_eq_filter P L x y hxy]
  rfl

theorem sum_primeProductInterval_coprime {V : Type*} [AddCommMonoid V]
    (P Q : Finset ℕ) (x y u : ℕ) (w : ℕ → V)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r)
    (hQu : ∀ r ∈ Q, ¬ r ∣ u) :
    (∑ n ∈ (primeProductInterval P Q x y).filter (fun n => n.Coprime u), w n) =
      ∑ p ∈ P.filter (fun p => ¬ p ∣ u), ∑ r ∈ primeSlice Q p x y, w (p * r) := by
  rw [Finset.sum_filter, sum_primeProductInterval P Q x y _ hP hQ hsep,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpu : p ∣ u
  · have hnot : ¬ p.Coprime u := (hP p hp).coprime_iff_not_dvd.not.mpr (by simpa)
    simp only [hpu, not_true_eq_false, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro r _
    simp only [Nat.coprime_mul_iff_left, hnot, false_and, ↓reduceIte]
  · simp only [hpu, not_false_eq_true, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro r hr
    have hru := (hQ r (Finset.mem_filter.mp hr).1).coprime_iff_not_dvd.mpr
      (hQu r (Finset.mem_filter.mp hr).1)
    have hcop : (p * r).Coprime u :=
      Nat.coprime_mul_iff_left.mpr ⟨(hP p hp).coprime_iff_not_dvd.mpr hpu, hru⟩
    exact if_pos hcop

theorem finiteCoprimeCount_primeProductInterval (P Q : Finset ℕ) (x y u : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r) (hQu : ∀ r ∈ Q, ¬ r ∣ u) :
    finiteCoprimeCount (primeProductInterval P Q x y) u =
      ∑ p ∈ P.filter (fun p => ¬ p ∣ u), (primeSlice Q p x y).card := by
  have h := sum_primeProductInterval_coprime P Q x y u (fun _ => (1 : ℕ))
    hP hQ hsep hQu
  simpa only [finiteCoprimeCount, Finset.sum_const, smul_eq_mul, mul_one] using h

theorem sum_primeProductInterval_split {V : Type*} [AddCommMonoid V]
    (P Q : Finset ℕ) (x y u : ℕ) (w : ℕ → V)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r) (hQu : ∀ r ∈ Q, ¬ r ∣ u) :
    (∑ n ∈ primeProductInterval P Q x y, w n) =
      (∑ n ∈ (primeProductInterval P Q x y).filter (fun n => n.Coprime u), w n) +
      ∑ p ∈ P.filter (fun p => p ∣ u), ∑ r ∈ primeSlice Q p x y, w (p * r) := by
  rw [sum_primeProductInterval P Q x y w hP hQ hsep,
    sum_primeProductInterval_coprime P Q x y u w hP hQ hsep hQu]
  exact (Finset.sum_filter_add_sum_filter_not P (fun p => ¬ p ∣ u) _).symm.trans
    (by simp only [not_not])

end Erdos964

import Mathlib

/-!
# The finite Buchstab identity

This is the exact elementary sieve decomposition used at the start of
Section 2 of Li's paper. It does not assert the analytic estimates needed
for primes in almost all short intervals.
-/

namespace Erdos421

def RoughAt (n z : ℕ) : Prop := ∀ p, p.Prime → p < z → ¬ p ∣ n

theorem roughAt_iff_minFac {n z : ℕ} : RoughAt n z ↔ n = 1 ∨ z ≤ n.minFac := by
  rw [Nat.le_minFac]
  unfold RoughAt
  constructor
  · intro h p hp hpn
    exact le_of_not_gt (fun hpz ↦ h p hp hpz hpn)
  · intro h p hp hpz hpn
    exact hpz.not_ge (h p hp hpn)

theorem RoughAt.mono {n w z : ℕ} (h : RoughAt n z) (hwz : w ≤ z) : RoughAt n w :=
  fun p hp hpw ↦ h p hp (hpw.trans_le hwz)

noncomputable def sifted (C : Finset ℕ) (z : ℕ) : Finset ℕ := by
  classical
  exact C.filter (fun n ↦ RoughAt n z)

def sievePrimes (w z : ℕ) : Finset ℕ := (Finset.Ico w z).filter Nat.Prime

def leastPrimeSlice (C : Finset ℕ) (p : ℕ) : Finset ℕ :=
  C.filter (fun n ↦ n ≠ 1 ∧ n.minFac = p)

theorem buchstab_partition (C : Finset ℕ) {w z : ℕ} (hwz : w ≤ z) :
    sifted C w = sifted C z ∪ (sievePrimes w z).biUnion (leastPrimeSlice C) := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨hnC, hnw⟩ := Finset.mem_filter.mp hn
    by_cases hnz : RoughAt n z
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnC, hnz⟩)
    · have hn1 : n ≠ 1 := by
        intro hn1
        exact hnz (roughAt_iff_minFac.mpr (Or.inl hn1))
      have hlow : w ≤ n.minFac := (roughAt_iff_minFac.mp hnw).resolve_left hn1
      have hhigh : n.minFac < z := by
        by_contra h
        exact hnz (roughAt_iff_minFac.mpr (Or.inr (by omega)))
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨n.minFac,
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlow, hhigh⟩, Nat.minFac_prime hn1⟩,
        Finset.mem_filter.mpr ⟨hnC, hn1, rfl⟩⟩)
  · intro hn
    rcases Finset.mem_union.mp hn with hn | hn
    · obtain ⟨hnC, hnz⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hnC, hnz.mono hwz⟩
    · obtain ⟨p, hp, hn⟩ := Finset.mem_biUnion.mp hn
      obtain ⟨hnC, _, hnp⟩ := Finset.mem_filter.mp hn
      have hwp := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
      exact Finset.mem_filter.mpr ⟨hnC, roughAt_iff_minFac.mpr (Or.inr (hnp ▸ hwp))⟩

theorem leastPrimeSlice_disjoint (C : Finset ℕ) {p q : ℕ} (hpq : p ≠ q) :
    Disjoint (leastPrimeSlice C p) (leastPrimeSlice C q) := by
  apply Finset.disjoint_left.mpr
  intro n hnp hnq
  exact hpq ((Finset.mem_filter.mp hnp).2.2.symm.trans (Finset.mem_filter.mp hnq).2.2)

theorem sifted_disjoint_slices (C : Finset ℕ) (w z : ℕ) :
    Disjoint (sifted C z) ((sievePrimes w z).biUnion (leastPrimeSlice C)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  obtain ⟨p, hp, hnp⟩ := Finset.mem_biUnion.mp hn'
  have hpz := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2
  have hpprime := (Finset.mem_filter.mp hp).2
  have hmin := (Finset.mem_filter.mp hnp).2.2
  have hdiv : p ∣ n := hmin ▸ Nat.minFac_dvd n
  exact (Finset.mem_filter.mp hn).2 p hpprime hpz hdiv

theorem buchstab_card_slices (C : Finset ℕ) {w z : ℕ} (hwz : w ≤ z) :
    (sifted C w).card = (sifted C z).card +
      ∑ p ∈ sievePrimes w z, (leastPrimeSlice C p).card := by
  classical
  rw [buchstab_partition C hwz, Finset.card_union_of_disjoint (sifted_disjoint_slices C w z),
    Finset.card_biUnion]
  intro p _ q _ hpq
  exact leastPrimeSlice_disjoint C hpq

def sieveCofactors (C : Finset ℕ) (p : ℕ) : Finset ℕ :=
  (C.filter (fun n ↦ p ∣ n)).image (fun n ↦ n / p)

theorem mem_sieveCofactors {C : Finset ℕ} {p d : ℕ} (hp : 0 < p) :
    d ∈ sieveCofactors C p ↔ p * d ∈ C := by
  constructor
  · intro hd
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hnC, hpn⟩ := Finset.mem_filter.mp hn
    rwa [Nat.mul_div_cancel' hpn]
  · intro hd
    exact Finset.mem_image.mpr ⟨p * d, Finset.mem_filter.mpr ⟨hd, dvd_mul_right p d⟩,
      Nat.mul_div_right d hp⟩

theorem minFac_mul_rough {p d : ℕ} (hp : p.Prime) (hd : RoughAt d p) :
    (p * d).minFac = p := by
  apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p d))
  have hn1 : p * d ≠ 1 := by
    intro h
    exact hp.ne_one (Nat.eq_one_of_mul_eq_one_right h)
  apply (roughAt_iff_minFac.mp ?_).resolve_left hn1
  intro q hq hqp hdiv
  rcases hq.dvd_mul.mp hdiv with hdiv | hdiv
  · rcases (Nat.dvd_prime hp).mp hdiv with h | h
    · exact hq.ne_one h
    · omega
  · exact hd q hq hqp hdiv

theorem leastPrimeSlice_eq_image (C : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    leastPrimeSlice C p = (sifted (sieveCofactors C p) p).image (fun d ↦ p * d) := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨hnC, _, hmin⟩ := Finset.mem_filter.mp hn
    have hdiv : p ∣ n := hmin ▸ Nat.minFac_dvd n
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hdiv
    refine Finset.mem_image.mpr ⟨n / p, Finset.mem_filter.mpr ⟨?_, ?_⟩, hmul⟩
    · apply (mem_sieveCofactors hp.pos).mpr
      rwa [hmul]
    · intro q hq hqp hqn
      have hqn' : q ∣ n := hqn.trans (Nat.div_dvd_of_dvd hdiv)
      have hle := Nat.minFac_le_of_dvd hq.two_le hqn'
      rw [hmin] at hle
      omega
  · intro hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hdC, hdrough⟩ := Finset.mem_filter.mp hd
    refine Finset.mem_filter.mpr
      ⟨(mem_sieveCofactors hp.pos).mp hdC, ?_, minFac_mul_rough hp hdrough⟩
    intro h
    exact hp.ne_one (Nat.eq_one_of_mul_eq_one_right h)

/-- Buchstab's exact finite identity, with the least prime removed. -/
theorem buchstab_identity (C : Finset ℕ) {w z : ℕ} (hwz : w ≤ z) :
    (sifted C w).card = (sifted C z).card +
      ∑ p ∈ sievePrimes w z, (sifted (sieveCofactors C p) p).card := by
  classical
  rw [buchstab_card_slices C hwz]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime := (Finset.mem_filter.mp hp).2
  rw [leastPrimeSlice_eq_image C hpprime, Finset.card_image_of_injective]
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left hpprime.pos hab

end Erdos421

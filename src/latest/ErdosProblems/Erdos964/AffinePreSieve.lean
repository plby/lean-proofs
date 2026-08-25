import ErdosProblems.Erdos964.AffineSieveSupport

/-!
# Pre-sieving an admissible affine family

Admissibility supplies one residue class avoiding any finite set of primes.
A sufficiently large primorial also covers every prime dividing a leading
coefficient or a nonzero pairwise determinant.
-/

namespace Erdos964

open scoped BigOperators Function

theorem exists_affine_preSieveResidue {ι : Type*} (A B : ι → ℕ) (P : Finset ℕ)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (hP : ∀ p ∈ P, p.Prime) :
    ∃ v : ℕ, v < ∏ p ∈ P, p ∧
      ∀ i, (A i * v + B i).Coprime (∏ p ∈ P, p) := by
  classical
  have hchoices : ∀ p ∈ P, ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i :=
    fun p hp => hadm p (hP p hp)
  choose a ha using hchoices
  let residues : ℕ → ℕ := fun p => if hp : p ∈ P then a p hp else 0
  have hnonzero : ∀ p ∈ P, p ≠ 0 := fun p hp => (hP p hp).ne_zero
  have hpairwise : Set.Pairwise (P : Set ℕ) (Nat.Coprime on id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  let v := Nat.chineseRemainderOfFinset residues id P hnonzero hpairwise
  refine ⟨v, Nat.chineseRemainderOfFinset_lt_prod residues id hnonzero hpairwise, ?_⟩
  intro i
  apply Nat.Coprime.prod_right
  intro p hp
  apply Nat.Coprime.symm
  apply (hP p hp).coprime_iff_not_dvd.mpr
  intro hpv
  have hv : (v : ℕ) ≡ a p hp [MOD p] := by
    simpa only [residues, dif_pos hp, id_eq] using v.property p hp
  have hform := ((hv.mul_left (A i)).add_right (B i)).symm.trans
    (Nat.modEq_zero_iff_dvd.mpr hpv)
  exact ha p hp i (Nat.modEq_zero_iff_dvd.mp hform)

theorem exists_affine_preSieveResidue_primorial {ι : Type*} (A B : ι → ℕ)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i) (D₀ : ℕ) :
    ∃ v : ℕ, v < primorial D₀ ∧ ∀ i, (A i * v + B i).Coprime (primorial D₀) := by
  simpa only [← primorial_eq_prod_primesLE] using
    exists_affine_preSieveResidue A B D₀.primesLE hadm
      (fun _ hp => Nat.prime_of_mem_primesLE hp)

theorem affine_preSieve_coprime_of_modEq {a b v W n : ℕ}
    (hnv : n ≡ v [MOD W]) (hv : (a * v + b).Coprime W) :
    (a * n + b).Coprime W := by
  by_contra hnot
  obtain ⟨p, hp, hpn, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hform := Nat.ModEq.of_dvd hpW ((hnv.mul_left a).add_right b)
  have hpv := Nat.modEq_zero_iff_dvd.mp
    (hform.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpn))
  exact (hp.coprime_iff_not_dvd.mp ((hv.coprime_dvd_right hpW).symm)) hpv

theorem covers_affine_leading_primes_primorial {ι : Type*} (A : ι → ℕ) (D₀ : ℕ)
    (hA : ∀ i, 0 < A i) (hbound : ∀ i, A i ≤ D₀) :
    CoversAffineLeadingPrimes A (primorial D₀) := by
  intro i p hp hpi
  exact hp.dvd_primorial_iff.mpr ((Nat.le_of_dvd (hA i) hpi).trans (hbound i))

theorem covers_affine_determinant_primes_primorial {ι : Type*}
    (A B : ι → ℕ) (D₀ : ℕ)
    (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hbound : ∀ i j, Nat.dist (A i * B j) (A j * B i) ≤ D₀) :
    CoversAffineDeterminantPrimes A B (primorial D₀) := by
  intro i j hij p hp hpd
  exact hp.dvd_primorial_iff.mpr
    ((Nat.le_of_dvd (Nat.dist_pos_of_ne (hne i j hij)) hpd).trans (hbound i j))

end Erdos964

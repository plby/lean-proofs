import ErdosProblems.Erdos964.AffineNormalization

/-!
# The local density of a normalized affine triple

Outside the normalization primes, the three roots are distinct. The
product of the forms therefore has exactly three roots modulo a prime;
admissibility forces every such prime to exceed three.
-/

namespace Erdos964

open scoped BigOperators

def affineProductRoots (A B : Fin 3 → ℕ) (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter (fun n => p ∣ ∏ i, (A i * n + B i))

theorem affineRoot_injective (A B : Fin 3 → ℕ) (p : ℕ) (hp : p.Prime)
    (hA : ∀ i, (A i).Coprime p)
    (hdet : ∀ i j, i ≠ j → ¬ p ∣ Nat.dist (A i * B j) (A j * B i)) :
    Function.Injective (fun i => affineRoot (A i) (B i) p) := by
  intro i j heq
  change affineRoot (A i) (B i) p = affineRoot (A j) (B j) p at heq
  by_contra hij
  have hpi := affineRoot_dvd (A i) (B i) p hp.pos (hA i)
  have hpj : p ∣ A j * affineRoot (A i) (B i) p + B j := by
    rw [heq]
    exact affineRoot_dvd (A j) (B j) p hp.pos (hA j)
  exact hdet i j hij
    (common_affine_divisor_dvd_determinant _ _ _ _ _ _ hpi hpj)

theorem affineProductRoots_eq_image (A B : Fin 3 → ℕ) (p : ℕ) (hp : p.Prime)
    (hA : ∀ i, (A i).Coprime p) :
    affineProductRoots A B p = Finset.univ.image (fun i => affineRoot (A i) (B i) p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hrootlt (i : Fin 3) : affineRoot (A i) (B i) p < p := ZMod.val_lt _
  ext n
  constructor
  · intro hn
    have hn' := Finset.mem_filter.mp hn
    obtain ⟨i, _, hpi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hn'.2
    have hmod := (modEq_affineRoot_iff (A i) (B i) p n hp.pos (hA i)).mpr hpi
    have heq : n = affineRoot (A i) (B i) p := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt (Finset.mem_range.mp hn'.1),
        Nat.mod_eq_of_lt (hrootlt i)] using hmod
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩
  · intro hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hrootlt i),
      (hp.prime.dvd_finsetProd_iff _).mpr
        ⟨i, Finset.mem_univ i, affineRoot_dvd (A i) (B i) p hp.pos (hA i)⟩⟩

theorem affineProductRoots_card (A B : Fin 3 → ℕ) (p : ℕ) (hp : p.Prime)
    (hA : ∀ i, (A i).Coprime p)
    (hdet : ∀ i j, i ≠ j → ¬ p ∣ Nat.dist (A i * B j) (A j * B i)) :
    (affineProductRoots A B p).card = 3 := by
  rw [affineProductRoots_eq_image A B p hp hA,
    Finset.card_image_of_injective _ (affineRoot_injective A B p hp hA hdet)]
  simp

theorem affineProductRoots_card_lt_of_admissible (A B : Fin 3 → ℕ) (p : ℕ) (hp : p.Prime)
    (hadm : ∃ t : ℕ, ∀ i, ¬ p ∣ A i * t + B i) :
    (affineProductRoots A B p).card < p := by
  obtain ⟨t, ht⟩ := hadm
  have htrange : t % p ∈ Finset.range p := Finset.mem_range.mpr (Nat.mod_lt t hp.pos)
  have htmod : t % p ≡ t [MOD p] := by simp [Nat.ModEq]
  have hnot : t % p ∉ affineProductRoots A B p := by
    intro hmem
    obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff _).mp (Finset.mem_filter.mp hmem).2
    have hform := (htmod.mul_left (A i)).add_right (B i)
    exact ht i (Nat.modEq_zero_iff_dvd.mp
      (hform.symm.trans (Nat.modEq_zero_iff_dvd.mpr hi)))
  have hstrict : affineProductRoots A B p ⊂ Finset.range p := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    exact hnot (heq.symm ▸ htrange)
  simpa only [Finset.card_range] using Finset.card_lt_card hstrict

theorem normalized_affineProductRoots_card (A B : Fin 3 → ℕ) (v p : ℕ)
    (hp : p.Prime) (hpM : ¬ p ∣ affineNormalizationModulus A B) :
    (affineProductRoots (fun i => A i * affineNormalizationModulus A B)
      (fun i => A i * v + B i) p).card = 3 := by
  apply affineProductRoots_card _ _ p hp
  · intro i
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    exact hpM ((normalized_leading_prime_support A B i p hp).mp h)
  · intro i j hij h
    exact hpM (normalized_determinant_prime_support A B v i j hij p hp h)

theorem small_prime_dvd_affine_normalization (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (p : ℕ) (hp : p.Prime) (hp3 : p ≤ 3) : p ∣ affineNormalizationModulus A B := by
  by_contra hpM
  obtain ⟨v, hv⟩ := exists_affine_avoiding_modulus A B (affineNormalizationModulus A B)
    (affineNormalizationModulus_pos A B hA hne) hadm
  have hcount := affineProductRoots_card_lt_of_admissible _ _ p hp
    (affine_progression_admissible A B _ v hv hadm p hp)
  rw [normalized_affineProductRoots_card A B v p hp hpM] at hcount
  omega

end Erdos964

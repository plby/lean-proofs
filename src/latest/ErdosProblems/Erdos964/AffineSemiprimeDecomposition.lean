import ErdosProblems.Erdos964.SemiprimeSlices
import ErdosProblems.Erdos964.MultiplicationProgressions
import ErdosProblems.Erdos964.ScalarSemiprimeSupport

/-!
# Exact decomposition of the affine semiprime count

The count splits into the part coprime to the sieve divisor and the slices
whose smaller prime divides it. On those slices the modulus loses that prime.
-/

namespace Erdos964

open scoped BigOperators

def affineDivisorParameters (A B : Fin 3 → ℕ) (N u : ℕ) : Finset ℕ :=
  (Finset.Ico N (2 * N)).filter (fun n => u ∣ ∏ i, (A i * n + B i))

def affineDivisorValueCount (A B : Fin 3 → ℕ) (j : Fin 3)
    (N u : ℕ) (S : Finset ℕ) : ℕ :=
  ((affineDivisorParameters A B N u).filter (fun n => A j * n + B j ∈ S)).card

theorem affineDivisorValueCount_eq_fibers (A B : Fin 3 → ℕ) (j : Fin 3)
    (N u : ℕ) (S : Finset ℕ) :
    affineDivisorValueCount A B j N u S =
      ∑ m ∈ S, ((affineDivisorParameters A B N u).filter
        (fun n => A j * n + B j = m)).card := by
  exact (Finset.sum_card_fiberwise_eq_card_filter
    (affineDivisorParameters A B N u) S (fun n => A j * n + B j)).symm

theorem affineDivisorValueCount_mul_image (A B : Fin 3 → ℕ) (j : Fin 3)
    (N u p : ℕ) (hp : 0 < p) (T : Finset ℕ) :
    affineDivisorValueCount A B j N u (T.image (fun r => p * r)) =
      ∑ r ∈ T, ((affineDivisorParameters A B N u).filter
        (fun n => A j * n + B j = p * r)).card := by
  rw [affineDivisorValueCount_eq_fibers, Finset.sum_image]
  intro r _ s _ hrs
  exact Nat.eq_of_mul_eq_mul_left hp hrs

theorem affineDivisorValueCount_filter_coprime (A B : Fin 3 → ℕ) (j : Fin 3)
    (N u : ℕ) (S : Finset ℕ) :
    affineDivisorValueCount A B j N u (S.filter (fun m => m.Coprime u)) =
      affineCoprimeValueCount A B j N u S := by
  unfold affineDivisorValueCount affineDivisorParameters affineCoprimeValueCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Nat.coprime_comm]
  tauto

theorem affineDivisorValueCount_prime_slice_strip (A B : Fin 3 → ℕ) (j : Fin 3)
    (N u p : ℕ) (hu : Squarefree u) (hp : p.Prime) (hpu : p ∣ u)
    (T : Finset ℕ) (hT : ∀ r ∈ T, r.Prime ∧ ¬ r ∣ u) :
    affineDivisorValueCount A B j N u (T.image (fun r => p * r)) =
      affineCoprimeValueCount A B j N (u / p) (T.image (fun r => p * r)) := by
  unfold affineDivisorValueCount affineDivisorParameters affineCoprimeValueCount
  congr 1
  ext n
  simp only [Finset.mem_filter]
  by_cases hn : A j * n + B j ∈ T.image (fun r => p * r)
  · obtain ⟨r, hr, hvalue⟩ := Finset.mem_image.mp hn
    have hdiv := affine_semiprime_scalar_divisor_iff A B j n u p r
      hu hp (hT r hr).1 (hT r hr).2 hvalue.symm
    rw [Nat.gcd_eq_right hpu] at hdiv
    simp only [hn, and_true, hdiv]
  · simp only [hn, and_false]

theorem affineDivisorValueCount_semiprime_split (A B : Fin 3 → ℕ) (j : Fin 3)
    (N u x y : ℕ) (hu : Squarefree u) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r) (hQu : ∀ r ∈ Q, ¬ r ∣ u) :
    affineDivisorValueCount A B j N u (primeProductInterval P Q x y) =
      affineCoprimeValueCount A B j N u (primeProductInterval P Q x y) +
      ∑ p ∈ P.filter (fun p => p ∣ u), affineCoprimeValueCount A B j N (u / p)
        ((primeSlice Q p x y).image (fun r => p * r)) := by
  rw [affineDivisorValueCount_eq_fibers,
    sum_primeProductInterval_split P Q x y u _ hP hQ hsep hQu,
    ← affineDivisorValueCount_eq_fibers, affineDivisorValueCount_filter_coprime]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  rw [← affineDivisorValueCount_mul_image A B j N u p (hP p hp'.1).pos]
  apply affineDivisorValueCount_prime_slice_strip A B j N u p hu (hP p hp'.1) hp'.2
  intro r hr
  have hrQ := (Finset.mem_filter.mp hr).1
  exact ⟨hQ r hrQ, hQu r hrQ⟩

end Erdos964

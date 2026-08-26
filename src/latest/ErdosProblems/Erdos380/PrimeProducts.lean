import ErdosProblems.Erdos380.Core
import Mathlib.Data.List.Permutation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Products of tuples of primes

Unique factorization bounds the number of ordered prime tuples with a fixed
product by a factorial. This is the coefficient bound used when a character
sum over primes is raised to a fixed power.
-/

open scoped BigOperators

namespace Erdos380

noncomputable section

/-- The product of an ordered tuple drawn from a finite set of naturals. -/
def tupleProduct (s : Finset ℕ) (k : ℕ) (f : Fin k → s) : ℕ :=
  ∏ i, (f i).val

/-- All products of ordered tuples from `s`. -/
def primeProductSupport (s : Finset ℕ) (k : ℕ) : Finset ℕ :=
  Finset.univ.image (tupleProduct s k)

/-- Number of ordered tuples whose product is `n`. -/
def productMultiplicity (s : Finset ℕ) (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin k → s => tupleProduct s k f = n).card

lemma prime_tuple_perm_of_product_eq {s : Finset ℕ} {k : ℕ}
    (hs : ∀ p ∈ s, p.Prime) {f g : Fin k → s}
    (hfg : tupleProduct s k f = tupleProduct s k g) :
    (List.ofFn fun i => (f i).val).Perm (List.ofFn fun i => (g i).val) := by
  have hf : ∀ p ∈ List.ofFn (fun i => (f i).val), p.Prime := by
    rw [List.forall_mem_ofFn_iff]
    exact fun i => hs _ (f i).property
  have hg : ∀ p ∈ List.ofFn (fun i => (g i).val), p.Prime := by
    rw [List.forall_mem_ofFn_iff]
    exact fun i => hs _ (g i).property
  exact (Nat.primeFactorsList_unique
    (by simpa only [List.prod_ofFn, tupleProduct] using hfg) hf).trans
    (Nat.primeFactorsList_unique (List.prod_ofFn) hg).symm

lemma tuple_list_injective (s : Finset ℕ) (k : ℕ) :
    Function.Injective (fun f : Fin k → s => List.ofFn fun i => (f i).val) := by
  intro f g hfg
  have h := List.ofFn_injective hfg
  funext i
  exact Subtype.ext (congrFun h i)

/-- No product has more than `k!` ordered representations by `k` primes. -/
lemma productMultiplicity_le_factorial {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (k n : ℕ) : productMultiplicity s k n ≤ k.factorial := by
  classical
  let t := Finset.univ.filter fun f : Fin k → s => tupleProduct s k f = n
  change t.card ≤ k.factorial
  rcases t.eq_empty_or_nonempty with ht | ⟨g, hg⟩
  · simp [ht]
  have hgprod : tupleProduct s k g = n := (Finset.mem_filter.mp hg).2
  let l := List.ofFn fun i => (g i).val
  calc
    t.card ≤ l.permutations.toFinset.card := by
      apply Finset.card_le_card_of_injOn
        (fun f : Fin k → s => List.ofFn fun i => (f i).val)
      · intro f hf
        apply List.mem_toFinset.mpr
        apply List.mem_permutations.mpr
        exact prime_tuple_perm_of_product_eq hs
          ((Finset.mem_filter.mp hf).2.trans hgprod.symm)
      · exact (tuple_list_injective s k).injOn
    _ ≤ l.permutations.length := List.toFinset_card_le _
    _ = k.factorial := by simp [l, List.length_permutations]

/-- Summing all multiplicities counts all tuples. -/
lemma sum_productMultiplicity (s : Finset ℕ) (k : ℕ) :
    ∑ n ∈ primeProductSupport s k, productMultiplicity s k n = s.card ^ k := by
  classical
  have h := Finset.card_eq_sum_card_image (tupleProduct s k)
    (Finset.univ : Finset (Fin k → s))
  simpa [primeProductSupport, productMultiplicity] using h.symm

/-- The squared coefficient energy loses only a factorial. -/
lemma sum_productMultiplicity_sq_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (k : ℕ) :
    ∑ n ∈ primeProductSupport s k, productMultiplicity s k n ^ 2 ≤
      k.factorial * s.card ^ k := by
  calc
    _ ≤ ∑ n ∈ primeProductSupport s k, k.factorial * productMultiplicity s k n := by
      apply Finset.sum_le_sum
      intro n _hn
      simpa [pow_two] using
        Nat.mul_le_mul_right (productMultiplicity s k n)
          (productMultiplicity_le_factorial hs k n)
    _ = k.factorial * s.card ^ k := by rw [← Finset.mul_sum, sum_productMultiplicity]

/-- Grouping an arbitrary weight according to the tuple product. -/
lemma sum_tupleProduct_eq {s : Finset ℕ} (k : ℕ) {R : Type*} [Semiring R]
    (F : ℕ → R) :
    (∑ f : Fin k → s, F (tupleProduct s k f)) =
      ∑ n ∈ primeProductSupport s k, (productMultiplicity s k n : R) * F n := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to
    (fun f (_ : f ∈ (Finset.univ : Finset (Fin k → s))) =>
      Finset.mem_image_of_mem (tupleProduct s k) (Finset.mem_univ f))
    (fun f => F (tupleProduct s k f))
  rw [← h]
  apply Finset.sum_congr rfl
  intro n _hn
  calc
    _ = ∑ _f ∈ Finset.univ.filter (fun f : Fin k → s => tupleProduct s k f = n), F n := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [(Finset.mem_filter.mp hf).2]
    _ = _ := by simp [productMultiplicity]

/-- Powering a multiplicative sum produces the prime-product coefficients. -/
lemma sum_monoidHom_pow (s : Finset ℕ) (k : ℕ) {R : Type*} [CommSemiring R]
    (χ : ℕ →* R) :
    (∑ p ∈ s, χ p) ^ k =
      ∑ n ∈ primeProductSupport s k, (productMultiplicity s k n : R) * χ n := by
  classical
  calc
    (∑ p ∈ s, χ p) ^ k = ∏ _i : Fin k, ∑ p : s, χ p.val := by
      rw [← Finset.sum_subtype s (by simp) (fun p => χ p)]
      simp
    _ = ∑ f : Fin k → s, ∏ i, χ (f i).val := Fintype.prod_sum _
    _ = ∑ f : Fin k → s, χ (tupleProduct s k f) := by
      simp only [tupleProduct, map_prod]
    _ = _ := sum_tupleProduct_eq k χ

lemma primeProductSupport_subset_Ioc {s : Finset ℕ} {P k : ℕ}
    (hs : ∀ p ∈ s, p.Prime) (hP : ∀ p ∈ s, p ≤ P) :
    primeProductSupport s k ⊆ Finset.Ioc 0 (P ^ k) := by
  classical
  intro n hn
  obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp hn
  apply Finset.mem_Ioc.mpr
  constructor
  · exact Finset.prod_pos fun i _ => (hs _ (f i).property).pos
  · calc
      tupleProduct s k f ≤ ∏ _i : Fin k, P :=
        Finset.prod_le_prod' fun i _ => hP _ (f i).property
      _ = P ^ k := by simp

end

end Erdos380

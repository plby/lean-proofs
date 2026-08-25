import ErdosProblems.Erdos157.AuxiliaryModuli

/-! Unordered distinct prime triples and the disjointness of their product fibers. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

noncomputable def primeSetProduct {n : ℕ} (s : Finset (PrimeDegree K n)) : K[X] :=
  ∏ f ∈ s, f.1.1

theorem primeSetProduct_monic {n : ℕ} (s : Finset (PrimeDegree K n)) : (primeSetProduct s).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro f _
  exact f.1.monic

theorem primeSetProduct_natDegree {n : ℕ} (s : Finset (PrimeDegree K n)) :
    (primeSetProduct s).natDegree = s.card * n := by
  unfold primeSetProduct
  rw [Polynomial.natDegree_prod_of_monic]
  · simp only [MonicDegreeEq.natDegree, Finset.sum_const_nat]
  · intro f _; exact f.1.monic

theorem prime_dvd_primeSetProduct_iff {n : ℕ} (f : PrimeDegree K n) (s : Finset (PrimeDegree K n)) :
    f.1.1 ∣ primeSetProduct s ↔ f ∈ s := by
  classical
  constructor
  · intro hdvd
    obtain ⟨g, hg, hfg⟩ := f.2.prime.dvd_finsetProd_iff (fun g : PrimeDegree K n => g.1.1) |>.mp hdvd
    have heq : f = g := Subtype.ext (Subtype.ext (Polynomial.eq_of_monic_of_associated
      f.1.monic g.1.monic (f.2.associated_of_dvd g.2 hfg)))
    simpa only [heq] using hg
  · intro hf
    exact Finset.dvd_prod_of_mem _ hf

theorem primeSetProduct_injective (n : ℕ) :
    Function.Injective (primeSetProduct (K := K) (n := n)) := by
  intro s t h
  ext f
  rw [← prime_dvd_primeSetProduct_iff, ← prime_dvd_primeSetProduct_iff, h]

abbrev PrimeTriple (K : Type*) [Field K] (n : ℕ) :=
  {s : Finset (PrimeDegree K n) // s.card = 3}

noncomputable instance primeTripleFintype (n : ℕ) : Fintype (PrimeTriple K n) := Fintype.ofFinite _

noncomputable def PrimeTriple.product {n : ℕ} (T : PrimeTriple K n) : K[X] := primeSetProduct T.1

theorem PrimeTriple.product_monic {n : ℕ} (T : PrimeTriple K n) : T.product.Monic :=
  primeSetProduct_monic T.1

theorem PrimeTriple.product_natDegree {n : ℕ} (T : PrimeTriple K n) : T.product.natDegree = 3 * n := by
  rw [PrimeTriple.product, primeSetProduct_natDegree, T.2]

theorem PrimeTriple.product_injective (n : ℕ) :
    Function.Injective (PrimeTriple.product (K := K) (n := n)) := by
  intro s t h
  exact Subtype.ext (primeSetProduct_injective n h)

/-- After removing a shared prime, both remaining products have degree `2n`. -/
theorem PrimeTriple.eq_of_shared_factor_residue {n : ℕ} (g : K[X])
    (hdeg : 2 * n < g.natDegree) (U V : PrimeTriple K n) (f : PrimeDegree K n)
    (hfU : f ∈ U.1) (hfV : f ∈ V.1) (hcoprime : IsCoprime g f.1.1)
    (hres : AdjoinRoot.mk g U.product = AdjoinRoot.mk g V.product) : U = V := by
  classical
  have hU : f.1.1 * primeSetProduct (U.1.erase f) = U.product :=
    Finset.mul_prod_erase _ _ hfU
  have hV : f.1.1 * primeSetProduct (V.1.erase f) = V.product :=
    Finset.mul_prod_erase _ _ hfV
  have hdiv : g ∣ f.1.1 * (primeSetProduct (U.1.erase f) - primeSetProduct (V.1.erase f)) := by
    have h := AdjoinRoot.mk_eq_mk.mp hres
    rw [← hU, ← hV, ← mul_sub] at h
    exact h
  have hdiv' := hcoprime.dvd_of_dvd_mul_left hdiv
  have hUdeg : (primeSetProduct (U.1.erase f)).natDegree = 2 * n := by
    rw [primeSetProduct_natDegree, Finset.card_erase_of_mem hfU, U.2]
  have hVdeg : (primeSetProduct (V.1.erase f)).natDegree = 2 * n := by
    rw [primeSetProduct_natDegree, Finset.card_erase_of_mem hfV, V.2]
  have hlt : (primeSetProduct (U.1.erase f) - primeSetProduct (V.1.erase f)).natDegree < g.natDegree := by
    exact (Polynomial.natDegree_sub_le _ _).trans_lt (by rw [hUdeg, hVdeg, max_self]; exact hdeg)
  have heq := sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_natDegree_lt hdiv' hlt)
  apply PrimeTriple.product_injective n
  rw [← hU, ← hV, heq]

theorem PrimeTriple.residue_fiber_pairwise_disjoint {n : ℕ} (g : K[X])
    (hdeg : 2 * n < g.natDegree) (hcoprime : ∀ f : PrimeDegree K n, IsCoprime g f.1.1)
    (a : AdjoinRoot g) :
    Set.Pairwise {T : PrimeTriple K n | AdjoinRoot.mk g T.product = a}
      (fun U V => Disjoint U.1 V.1) := by
  intro U hU V hV hne
  rw [Finset.disjoint_left]
  intro f hfU hfV
  exact hne (PrimeTriple.eq_of_shared_factor_residue g hdeg U V f hfU hfV
    (hcoprime f) (hU.trans hV.symm))

end Erdos157.Elementary.PolynomialCharacters

import ErdosProblems.Erdos157.ShortPrefixPrimes
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Odd-degree auxiliary moduli over a finite field of characteristic two. -/

namespace Erdos157.Elementary

instance two_isPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev CoefficientField := GaloisField 2 1024

noncomputable instance coefficientFieldFintype : Fintype CoefficientField := Fintype.ofFinite _
noncomputable instance coefficientFieldDecidableEq : DecidableEq CoefficientField := Classical.decEq _

theorem card_coefficientField : Fintype.card CoefficientField = 2 ^ 1024 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 1024 (by decide)

namespace AuxiliaryModuli

open Polynomial

variable (K : Type*) [Field K] [Finite K] [CharP K 2]

theorem exists_monic_irreducible_natDegree (n : ℕ) (hn : n ≠ 0) :
    ∃ f : K[X], f.Monic ∧ Irreducible f ∧ f.natDegree = n := by
  let : NeZero n := ⟨hn⟩
  let E := FiniteField.Extension K 2 n
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top K E
  have hi : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly K α, minpoly.monic hi, minpoly.irreducible hi, ?_⟩
  calc
    _ = Module.finrank K E := (Field.primitive_element_iff_minpoly_natDegree_eq K α).mp hα
    _ = n := FiniteField.finrank_extension K 2 n

noncomputable def factor (i : ℕ) : K[X] :=
  (exists_monic_irreducible_natDegree K (2 * i + 1) (by omega)).choose

theorem factor_monic (i : ℕ) : (factor K i).Monic :=
  (exists_monic_irreducible_natDegree K (2 * i + 1) (by omega)).choose_spec.1

theorem factor_irreducible (i : ℕ) : Irreducible (factor K i) :=
  (exists_monic_irreducible_natDegree K (2 * i + 1) (by omega)).choose_spec.2.1

theorem factor_natDegree (i : ℕ) : (factor K i).natDegree = 2 * i + 1 :=
  (exists_monic_irreducible_natDegree K (2 * i + 1) (by omega)).choose_spec.2.2

theorem factor_coprime {i j : ℕ} (hij : i ≠ j) : IsCoprime (factor K i) (factor K j) := by
  rw [(factor_irreducible K i).coprime_iff_not_dvd]
  intro hdvd
  have heq := Polynomial.eq_of_monic_of_associated (factor_monic K i) (factor_monic K j)
    ((factor_irreducible K i).associated_of_dvd (factor_irreducible K j) hdvd)
  have hdeg := congrArg Polynomial.natDegree heq
  rw [factor_natDegree, factor_natDegree] at hdeg
  omega

noncomputable def product (k : ℕ) : K[X] := ∏ i ∈ Finset.range k, factor K i

theorem product_monic (k : ℕ) : (product K k).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i _
  exact factor_monic K i

theorem product_natDegree (k : ℕ) : (product K k).natDegree = k ^ 2 := by
  have hsum : ∑ i ∈ Finset.range k, (2 * i + 1) = k ^ 2 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  unfold product
  rw [Polynomial.natDegree_prod_of_monic]
  · simpa only [factor_natDegree] using hsum
  · intro i _; exact factor_monic K i

theorem factor_dvd_product {i k : ℕ} (hi : i < k) : factor K i ∣ product K k := by
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi)

theorem product_dvd {k : ℕ} {f : K[X]} (h : ∀ i < k, factor K i ∣ f) : product K k ∣ f := by
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij; exact factor_coprime K hij
  · intro i hi; exact h i (Finset.mem_range.mp hi)

theorem product_dvd_product {h k : ℕ} (hhk : h ≤ k) : product K h ∣ product K k := by
  apply product_dvd
  intro i hi
  exact factor_dvd_product K (lt_of_lt_of_le hi hhk)

noncomputable abbrev ResidueField (i : ℕ) := AdjoinRoot (factor K i)

noncomputable instance factorIrreducibleFact (i : ℕ) : Fact (Irreducible (factor K i)) :=
  ⟨factor_irreducible K i⟩

noncomputable instance residueFieldModuleFinite (i : ℕ) : Module.Finite K (ResidueField K i) :=
  (factor_monic K i).finite_adjoinRoot

noncomputable instance residueFieldFinite (i : ℕ) : Finite (ResidueField K i) :=
  Module.finite_of_finite K

theorem residueField_natCard (i : ℕ) : Nat.card (ResidueField K i) = Nat.card K ^ (2 * i + 1) := by
  classical
  let : Fintype K := Fintype.ofFinite _
  rw [PolynomialCharacters.natCard_adjoinRoot _ (factor_monic K i), factor_natDegree,
    Nat.card_eq_fintype_card]

theorem residueField_units_natCard (i : ℕ) :
    Nat.card (ResidueField K i)ˣ = Nat.card K ^ (2 * i + 1) - 1 := by
  rw [Nat.card_units, residueField_natCard]

noncomputable abbrev factorIdeal (i : ℕ) : Ideal K[X] := Ideal.span {factor K i}

theorem factorIdeals_pairwise (k : ℕ) :
    Pairwise (fun i j : Fin k => IsCoprime (factorIdeal K i) (factorIdeal K j)) := by
  intro i j hij
  rw [factorIdeal, factorIdeal, Ideal.isCoprime_span_singleton_iff]
  exact factor_coprime K (fun h => hij (Fin.ext h))

theorem factorIdeals_iInf (k : ℕ) :
    (⨅ i : Fin k, factorIdeal K i) = Ideal.span {product K k} := by
  rw [show (⨅ i : Fin k, factorIdeal K i) = Ideal.span {∏ i : Fin k, factor K i} by
    exact Ideal.iInf_span_singleton (fun i j hij => factor_coprime K (fun h => hij (Fin.ext h)))]
  rw [Fin.prod_univ_eq_prod_range]
  rfl

noncomputable def quotientEquiv (k : ℕ) :
    AdjoinRoot (product K k) ≃+* (∀ i : Fin k, ResidueField K i) :=
  (Ideal.quotientEquivAlgOfEq K (factorIdeals_iInf K k).symm).toRingEquiv.trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i : Fin k => factorIdeal K i)
      (factorIdeals_pairwise K k))

theorem quotientEquiv_mk_apply (k : ℕ) (f : K[X]) (i : Fin k) :
    quotientEquiv K k (AdjoinRoot.mk (product K k) f) i = AdjoinRoot.mk (factor K i) f := by
  have hfirst : (Ideal.quotientEquivAlgOfEq K (factorIdeals_iInf K k).symm).toRingEquiv
      (Ideal.Quotient.mk (Ideal.span {product K k}) f) =
        Ideal.Quotient.mk (⨅ i : Fin k, factorIdeal K i) f :=
    Ideal.quotientEquivAlgOfEq_mk K (factorIdeals_iInf K k).symm f
  exact (congrArg (fun a => Ideal.quotientInfToPiQuotient
    (fun j : Fin k => factorIdeal K j) a i) hfirst).trans
      (Ideal.quotientInfToPiQuotient_mk' (fun j : Fin k => factorIdeal K j) f i)

noncomputable def quotientUnitsEquiv (k : ℕ) :
    (AdjoinRoot (product K k))ˣ ≃* (∀ i : Fin k, (ResidueField K i)ˣ) :=
  (Units.mapEquiv (quotientEquiv K k).toMulEquiv).trans MulEquiv.piUnits

theorem quotientUnitsEquiv_val_apply (k : ℕ) (u : (AdjoinRoot (product K k))ˣ) (i : Fin k) :
    ↑(quotientUnitsEquiv K k u i) = quotientEquiv K k ↑u i := rfl

theorem quotient_units_natCard (k : ℕ) :
    Nat.card (AdjoinRoot (product K k))ˣ =
      ∏ i ∈ Finset.range k, (Nat.card K ^ (2 * i + 1) - 1) := by
  rw [Nat.card_congr (quotientUnitsEquiv K k).toEquiv, Nat.card_pi]
  simp_rw [residueField_units_natCard]
  exact Fin.prod_univ_eq_prod_range (fun i => Nat.card K ^ (2 * i + 1) - 1) k

theorem card_even : Even (Nat.card K) := by
  let : Fintype K := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.even_iff]
  exact FiniteField.even_card_of_char_two (ringChar.eq K 2)

theorem residueField_units_card_odd (i : ℕ) : Odd (Nat.card (ResidueField K i)ˣ) := by
  rw [residueField_units_natCard]
  apply Nat.Even.sub_odd (Nat.one_le_pow _ _ (Nat.succ_le_of_lt Nat.card_pos))
  · exact (Nat.even_pow.mpr ⟨card_even K, by omega⟩)
  · exact odd_one

theorem quotient_units_card_odd (k : ℕ) : Odd (Nat.card (AdjoinRoot (product K k))ˣ) := by
  rw [quotient_units_natCard]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ]
    exact ih.mul (by simpa only [residueField_units_natCard] using residueField_units_card_odd K k)

theorem factor_not_dvd_even_prime {n : ℕ} (hn : Even n)
    (f : PolynomialCharacters.PrimeDegree K n) (i : ℕ) : ¬factor K i ∣ f.1.1 := by
  intro hdvd
  have heq := Polynomial.eq_of_monic_of_associated (factor_monic K i) f.1.monic
    ((factor_irreducible K i).associated_of_dvd f.2 hdvd)
  have hdeg := congrArg Polynomial.natDegree heq
  rw [factor_natDegree, f.1.natDegree] at hdeg
  rw [← hdeg] at hn
  exact (Nat.not_even_iff_odd.mpr (by exact ⟨i, by omega⟩)) hn

theorem product_isCoprime_even_prime {n : ℕ} (hn : Even n)
    (f : PolynomialCharacters.PrimeDegree K n) (k : ℕ) : IsCoprime (product K k) f.1.1 := by
  apply IsCoprime.prod_left
  intro i _
  exact (factor_irreducible K i).coprime_iff_not_dvd.mpr (factor_not_dvd_even_prime K hn f i)

theorem eventually_prefix_prime_lower [Fintype K] :
    ∀ᶠ k in Filter.atTop, ∀ a : (AdjoinRoot (product K (prefixLength k)))ˣ,
      (Fintype.card K : ℝ) ^ levelDegree k /
          (2 * (levelDegree k : ℝ) * Nat.card (AdjoinRoot (product K (prefixLength k)))ˣ) ≤
        PolynomialCharacters.primeProgressionCount (product K (prefixLength k)) (levelDegree k) ↑a := by
  classical
  filter_upwards [eventually_shortPrefix_prime_lower (K := K)] with k hk
  exact hk _ (product_monic K _) (product_natDegree K _) (quotient_units_card_odd K _)

end AuxiliaryModuli
end Erdos157.Elementary

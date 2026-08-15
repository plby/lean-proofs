/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalArtinPolynomial
import ErdosProblems.Erdos387.RationalLocalEuler
import ErdosProblems.Erdos387.RationalMonicFactors

/-!
# Coefficients of the rational finite Euler product

Expanding the geometric local factors produces degree-weighted irreducible
multiplicities.  Unique factorization then identifies these with monic
polynomials, and complete multiplicativity identifies the product weight
with `polynomialWeight`.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators

namespace RationalWeil

variable {K R : Type*} [Field K] [Fintype K] [CommRing R] {N n : Nat}

/-- The standard lower-coefficient parametrization of monic degree-`n`
polynomials. -/
noncomputable def monicCoefficientEquiv
    {K : Type*} [Field K] (n : ℕ) :
    {F : K[X] // F.Monic ∧ F.natDegree = n} ≃ (Fin n → K) :=
  (monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv

noncomputable instance instFintypeMonicNatDegree
    {K : Type*} [Field K] [Fintype K] (n : ℕ) :
    Fintype {F : K[X] // F.Monic ∧ F.natDegree = n} :=
  Fintype.ofEquiv (Fin n → K) (monicCoefficientEquiv n).symm

theorem monicPolynomial_spec
    {K : Type*} [Field K] (n : ℕ) (c : Fin n → K) :
    (monicPolynomial n c).Monic ∧
      (monicPolynomial n c).natDegree = n := by
  have hlt := mem_degreeLT.mp (lowerPolynomial_mem n c)
  refine ⟨monic_X_pow_add hlt, ?_⟩
  rw [monicPolynomial, natDegree_add_eq_left_of_degree_lt]
  · simp
  · simpa using hlt

theorem monicCoefficientEquiv_symm_apply
    {K : Type*} [Field K] (n : ℕ) (c : Fin n → K) :
    ((monicCoefficientEquiv n).symm c).1 = monicPolynomial n c := by
  rfl

noncomputable instance weightedFactorsFintype :
    Fintype
      {m : MonicIrreducibleLE K N →₀ Nat // monicFactorWeight m = n} := by
  classical
  exact (Finsupp.finite_of_nat_weight_eq
    (fun P : MonicIrreducibleLE K N ↦ P.poly.natDegree)
    (fun P ↦ P.natDegree_pos.ne') n).fintype

noncomputable def multiplicativeFactorWeight
    (w : MonicIrreducibleLE K N → R)
    (m : MonicIrreducibleLE K N →₀ Nat) : R :=
  ∏ P, w P ^ m P

theorem prod_map_toMultiset_eq_multiplicativeFactorWeight
    (w : MonicIrreducibleLE K N → R)
    (m : MonicIrreducibleLE K N →₀ Nat) :
    (m.toMultiset.map w).prod = multiplicativeFactorWeight w m := by
  rw [multiplicativeFactorWeight, ← Finsupp.prod_pow]
  induction m using Finsupp.induction with
  | zero => simp [Finsupp.toMultiset_zero]
  | @single_add P e f hP he ih =>
      rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, ih]
      calc
        (Multiset.map w (Finsupp.toMultiset (Finsupp.single P e))).prod *
            f.prod (fun Q a ↦ w Q ^ a) =
            w P ^ e * f.prod (fun Q a ↦ w Q ^ a) := by
          rw [Finsupp.toMultiset_single, Multiset.map_nsmul,
            Multiset.map_singleton, Multiset.prod_nsmul,
            Multiset.prod_singleton]
        _ = (Finsupp.single P e).prod (fun Q a ↦ w Q ^ a) *
              f.prod (fun Q a ↦ w Q ^ a) := by
          rw [Finsupp.prod_single_index]
          exact pow_zero _
        _ = (Finsupp.single P e + f).prod (fun Q a ↦ w Q ^ a) := by
          symm
          exact Finsupp.prod_add_index' (fun _ ↦ pow_zero _)
            (fun _ _ _ ↦ pow_add _ _ _)

noncomputable def degreeScaledIndex
    (m : MonicIrreducibleLE K N →₀ Nat) :
    MonicIrreducibleLE K N →₀ Nat :=
  Finsupp.onFinset Finset.univ
    (fun P ↦ P.poly.natDegree * m P) (by simp)

@[simp]
theorem degreeScaledIndex_apply
    (m : MonicIrreducibleLE K N →₀ Nat)
    (P : MonicIrreducibleLE K N) :
    degreeScaledIndex m P = P.poly.natDegree * m P := by
  simp [degreeScaledIndex]

noncomputable def degreeUnscaledIndex
    (l : MonicIrreducibleLE K N →₀ Nat) :
    MonicIrreducibleLE K N →₀ Nat :=
  Finsupp.onFinset Finset.univ
    (fun P ↦ l P / P.poly.natDegree) (by simp)

@[simp]
theorem degreeUnscaledIndex_apply
    (l : MonicIrreducibleLE K N →₀ Nat)
    (P : MonicIrreducibleLE K N) :
    degreeUnscaledIndex l P = l P / P.poly.natDegree := by
  simp [degreeUnscaledIndex]

theorem degreeUnscaledIndex_scaled
    (m : MonicIrreducibleLE K N →₀ Nat) :
    degreeUnscaledIndex (degreeScaledIndex m) = m := by
  ext P
  simp [Nat.mul_div_cancel_left _ P.natDegree_pos]

theorem degreeScaledIndex_unscaled
    (l : MonicIrreducibleLE K N →₀ Nat)
    (hl : ∀ P, P.poly.natDegree ∣ l P) :
    degreeScaledIndex (degreeUnscaledIndex l) = l := by
  ext P
  simp only [degreeScaledIndex_apply, degreeUnscaledIndex_apply]
  rw [mul_comm, Nat.div_mul_cancel (hl P)]

private theorem sum_degreeScaledIndex
    (m : MonicIrreducibleLE K N →₀ Nat) :
    ∑ P, degreeScaledIndex m P = monicFactorWeight m := by
  classical
  rw [monicFactorWeight, Finsupp.weight_apply,
    Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro P hP
    simp [mul_comm]
  · intro P
    simp

private theorem weight_degreeUnscaledIndex
    (l : MonicIrreducibleLE K N →₀ Nat)
    (hl : ∀ P, P.poly.natDegree ∣ l P) :
    monicFactorWeight (degreeUnscaledIndex l) = ∑ P, l P := by
  classical
  rw [monicFactorWeight, Finsupp.weight_apply,
    Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro P hP
    simp only [degreeUnscaledIndex_apply, nsmul_eq_mul]
    exact Nat.div_mul_cancel (hl P)
  · intro P
    simp

theorem coeff_localEulerProduct_eq_sum_weightedFactors
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.coeff n
        (∏ P : MonicIrreducibleLE K N,
          localEuler P.poly.natDegree (w P)) =
      ∑ m : {m : MonicIrreducibleLE K N →₀ Nat //
          monicFactorWeight m = n},
        multiplicativeFactorWeight w m.1 := by
  classical
  rw [PowerSeries.coeff_prod]
  let good : Finset (MonicIrreducibleLE K N →₀ Nat) :=
    (Finset.finsuppAntidiag Finset.univ n).filter
      (fun l ↦ ∀ P, P.poly.natDegree ∣ l P)
  have hterm (l : MonicIrreducibleLE K N →₀ Nat) :
      (∏ P, PowerSeries.coeff (l P)
        (localEuler P.poly.natDegree (w P))) =
        if (∀ P, P.poly.natDegree ∣ l P) then
          ∏ P, w P ^ (l P / P.poly.natDegree) else 0 := by
    by_cases hl : ∀ P, P.poly.natDegree ∣ l P
    · rw [if_pos hl]
      apply Finset.prod_congr rfl
      intro P hP
      rw [coeff_localEuler (w P) P.natDegree_pos.ne', if_pos (hl P)]
    · rw [if_neg hl]
      push Not at hl
      obtain ⟨P, hP⟩ := hl
      apply Finset.prod_eq_zero (Finset.mem_univ P)
      rw [coeff_localEuler (w P) P.natDegree_pos.ne', if_neg hP]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  change (∑ l ∈ good, ∏ P, w P ^ (l P / P.poly.natDegree)) = _
  symm
  apply Finset.sum_bij
      (fun m _ ↦ degreeScaledIndex m.1)
  · intro m hm
    simp only [good, Finset.mem_filter, Finset.mem_finsuppAntidiag]
    refine ⟨⟨?_, Finset.subset_univ _⟩, ?_⟩
    · rw [sum_degreeScaledIndex]
      exact m.2
    · intro P
      simp
  · intro a ha b hb hab
    apply Subtype.ext
    simpa only [degreeUnscaledIndex_scaled] using
      congrArg degreeUnscaledIndex hab
  · intro l hl
    simp only [good, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hl
    let m : MonicIrreducibleLE K N →₀ Nat := degreeUnscaledIndex l
    have hm : monicFactorWeight m = n := by
      rw [weight_degreeUnscaledIndex l hl.2, ← hl.1.1]
    refine ⟨⟨m, hm⟩, Finset.mem_univ _, ?_⟩
    exact degreeScaledIndex_unscaled l hl.2
  · intro m hm
    simp [multiplicativeFactorWeight,
      Nat.mul_div_cancel_left _ (MonicIrreducibleLE.natDegree_pos _)]

variable [DecidableEq K]

theorem coeff_localEulerProduct_eq_sum_monic
    (hnN : n ≤ N) (w : MonicIrreducibleLE K N → R) :
    PowerSeries.coeff n
        (∏ P : MonicIrreducibleLE K N,
          localEuler P.poly.natDegree (w P)) =
      ∑ F : {F : K[X] // F.Monic ∧ F.natDegree = n},
        multiplicativeFactorWeight w (monicFactorization hnN F) := by
  rw [coeff_localEulerProduct_eq_sum_weightedFactors]
  apply Fintype.sum_equiv (weightedFactorsEquivMonic hnN)
  intro m
  congr 1
  apply monicFactorProduct_injective
  rw [monicFactorProduct_factorization]
  rfl

/-! ## Specialization to the rational simple-pole weight -/

theorem polynomialWeight_one
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) :
    polynomialWeight coeff (1 : (ZMod p)[X]) = 1 := by
  have havoid : AvoidsPoleSupport coeff (1 : (ZMod p)[X]) := by
    intro r hr
    simp
  rw [polynomialWeight, if_pos havoid]
  simp [logarithmicDerivativePhase]

theorem polynomialWeight_multiset_prod
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (s : Multiset (ZMod p)[X]) :
    polynomialWeight coeff s.prod =
      (s.map (polynomialWeight coeff)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [polynomialWeight_one]
  | cons F s ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
        polynomialWeight_mul, ih]

theorem multiplicativeFactorWeight_polynomialWeight
    {p : ℕ} [NeZero p] [Fact p.Prime] {N : ℕ}
    (coeff : ZMod p → ZMod p)
    (m : MonicIrreducibleLE (ZMod p) N →₀ Nat) :
    multiplicativeFactorWeight
        (fun P ↦ polynomialWeight coeff P.poly) m =
      polynomialWeight coeff (monicFactorProduct m) := by
  let s : Multiset (ZMod p)[X] :=
    m.toMultiset.map MonicIrreducibleLE.poly
  calc
    multiplicativeFactorWeight
        (fun P ↦ polynomialWeight coeff P.poly) m =
        (m.toMultiset.map
          (fun P ↦ polynomialWeight coeff P.poly)).prod :=
      (prod_map_toMultiset_eq_multiplicativeFactorWeight _ m).symm
    _ = (s.map (polynomialWeight coeff)).prod := by
      simp only [s, Multiset.map_map, Function.comp_apply]
    _ = polynomialWeight coeff s.prod :=
      (polynomialWeight_multiset_prod coeff s).symm
    _ = polynomialWeight coeff (monicFactorProduct m) := rfl

theorem sum_polynomialWeight_monic_eq_monicWeightSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (n : ℕ) :
    (∑ F : {F : (ZMod p)[X] // F.Monic ∧ F.natDegree = n},
      polynomialWeight coeff F.1) = monicWeightSum coeff n := by
  rw [monicWeightSum]
  let e := monicCoefficientEquiv (K := ZMod p) n
  calc
    (∑ F : {F : (ZMod p)[X] // F.Monic ∧ F.natDegree = n},
        polynomialWeight coeff F.1) =
        ∑ c : Fin n → ZMod p,
          polynomialWeight coeff (e.symm c).1 := by
      exact (e.symm.sum_comp (fun F ↦ polynomialWeight coeff F.1)).symm
    _ = ∑ c : Fin n → ZMod p,
        polynomialWeight coeff (monicPolynomial n c) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [monicCoefficientEquiv_symm_apply]

theorem coeff_localEulerProduct_polynomialWeight_eq_monicWeightSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {N n : ℕ} (hnN : n ≤ N) :
    PowerSeries.coeff n
        (∏ P : MonicIrreducibleLE (ZMod p) N,
          localEuler P.poly.natDegree (polynomialWeight coeff P.poly)) =
      monicWeightSum coeff n := by
  classical
  rw [coeff_localEulerProduct_eq_sum_monic hnN]
  calc
    (∑ F : {F : (ZMod p)[X] // F.Monic ∧ F.natDegree = n},
        multiplicativeFactorWeight
          (fun P ↦ polynomialWeight coeff P.poly)
          (monicFactorization hnN F)) =
        ∑ F : {F : (ZMod p)[X] // F.Monic ∧ F.natDegree = n},
          polynomialWeight coeff F.1 := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [multiplicativeFactorWeight_polynomialWeight,
        monicFactorProduct_factorization]
    _ = monicWeightSum coeff n :=
      sum_polynomialWeight_monic_eq_monicWeightSum coeff n

end RationalWeil

end Erdos387

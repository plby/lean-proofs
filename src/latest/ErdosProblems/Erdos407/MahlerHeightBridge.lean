/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.PolynomialHeights
import ErdosProblems.Erdos407.Primitive
import ErdosProblems.Erdos407.RothIndex

/-!
# A one-variable coefficient-height bound

This file supplies the arithmetic one-variable estimate used at the base of
the binary Roth argument.  A rational polynomial is rescaled to the primitive
integral polynomial determined by its coefficient tuple.  The primitive
integer linear polynomial of a rational root then divides that integral
polynomial with the full root multiplicity.  Multiplicativity of Mahler
measure and the elementary `ℓ¹` coefficient bound give the result.
-/

namespace Erdos407.MahlerHeightBridge

open scoped BigOperators

noncomputable section

open Erdos407 PolynomialHeights

/-- The support of a one-variable polynomial is canonically the support of
its image as an `MvPolynomial` in the unique variable `Fin 1`. -/
def supportEquiv (p : Polynomial ℚ) :
    ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm p).support ≃ p.support where
  toFun J := ⟨J.1 default, by
    refine Polynomial.mem_support_iff.mpr ?_
    simpa only [MvPolynomial.coeff_uniqueAlgEquiv_symm] using
      MvPolynomial.mem_support_iff.mp J.2⟩
  invFun n := ⟨Finsupp.single default n.1, by
    refine MvPolynomial.mem_support_iff.mpr ?_
    simpa only [MvPolynomial.coeff_uniqueAlgEquiv_symm, Finsupp.single_eq_same] using
      Polynomial.mem_support_iff.mp n.2⟩
  left_inv J := by
    apply Subtype.ext
    exact (Finsupp.unique_single J.1).symm
  right_inv n := by
    apply Subtype.ext
    simp only [Finsupp.single_eq_same]

/-- In one variable, the multivariate projective coefficient height is the
height of the usual polynomial coefficient tuple indexed by its support. -/
theorem projectiveCoeffHeight_uniqueAlgEquiv_symm (p : Polynomial ℚ) :
    projectiveCoeffHeight ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm p) =
      Height.logHeight (fun n : p.support ↦ p.coeff n.1) := by
  let P := (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm p
  rw [projectiveCoeffHeight_eq_logHeight_coeffTuple]
  calc
    Height.logHeight (coeffTuple P) =
        Height.logHeight (coeffTuple P ∘ (supportEquiv p).symm) := by
      rw [Height.logHeight_comp_equiv]
    _ = Height.logHeight (fun n : p.support ↦ p.coeff n.1) := by
      congr 1
      funext n
      change MvPolynomial.coeff (Finsupp.single default n.1) P = p.coeff n.1
      rw [MvPolynomial.coeff_uniqueAlgEquiv_symm, Finsupp.single_eq_same]

/-- The primitive integral coefficient tuple attached to `p`. -/
def primitiveCoeffs (p : Polynomial ℚ) : p.support → ℤ :=
  Primitive.normalize (fun n : p.support ↦ p.coeff n.1)

/-- The integral polynomial reconstructed from the primitive coefficient
tuple. -/
def primitivePolynomial (p : Polynomial ℚ) : Polynomial ℤ :=
  ∑ n : p.support, Polynomial.monomial n.1 (primitiveCoeffs p n)

/-- The rational scale relating `p` to `primitivePolynomial p`. -/
def primitiveScale (p : Polynomial ℚ) : ℚ :=
  Primitive.normalizationScale (fun n : p.support ↦ p.coeff n.1)

private theorem coeffTuple_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) :
    (fun n : p.support ↦ p.coeff n.1) ≠ 0 := by
  obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr hp
  exact Function.ne_iff.mpr ⟨⟨n, hn⟩, Polynomial.mem_support_iff.mp hn⟩

theorem primitiveScale_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) :
    primitiveScale p ≠ 0 := by
  exact Primitive.normalizationScale_ne_zero (coeffTuple_ne_zero hp)

theorem primitiveCoeffs_primitive {p : Polynomial ℚ} (hp : p ≠ 0) :
    Primitive.IsPrimitive (primitiveCoeffs p) := by
  exact Primitive.normalize_primitive (coeffTuple_ne_zero hp)

theorem primitiveCoeffs_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) :
    primitiveCoeffs p ≠ 0 := (primitiveCoeffs_primitive hp).ne_zero

@[simp] theorem primitivePolynomial_coeff_of_mem {p : Polynomial ℚ}
    {n : ℕ} (hn : n ∈ p.support) :
    (primitivePolynomial p).coeff n = primitiveCoeffs p ⟨n, hn⟩ := by
  classical
  rw [primitivePolynomial]
  rw [show (∑ b : p.support,
      Polynomial.monomial b.1 (primitiveCoeffs p b)).coeff n =
      ∑ b : p.support,
        (Polynomial.monomial b.1 (primitiveCoeffs p b)).coeff n by
    simpa using (map_sum (Polynomial.lcoeff ℤ n)
      (fun b : p.support ↦ Polynomial.monomial b.1 (primitiveCoeffs p b))
      Finset.univ)]
  rw [Fintype.sum_eq_single ⟨n, hn⟩]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro b hbn
    rw [Polynomial.coeff_monomial, if_neg]
    exact fun h => hbn (Subtype.ext h)

@[simp] theorem primitivePolynomial_coeff_of_not_mem {p : Polynomial ℚ}
    {n : ℕ} (hn : n ∉ p.support) :
    (primitivePolynomial p).coeff n = 0 := by
  classical
  rw [primitivePolynomial]
  rw [show (∑ b : p.support,
      Polynomial.monomial b.1 (primitiveCoeffs p b)).coeff n =
      ∑ b : p.support,
        (Polynomial.monomial b.1 (primitiveCoeffs p b)).coeff n by
    simpa using (map_sum (Polynomial.lcoeff ℤ n)
      (fun b : p.support ↦ Polynomial.monomial b.1 (primitiveCoeffs p b))
      Finset.univ)]
  apply Finset.sum_eq_zero
  intro b hb
  rw [Polynomial.coeff_monomial, if_neg]
  exact fun h => hn (by simpa [h] using b.2)

theorem primitivePolynomial_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) :
    primitivePolynomial p ≠ 0 := by
  obtain ⟨n, hn⟩ := Function.ne_iff.mp (primitiveCoeffs_ne_zero hp)
  intro hq
  have := congrArg (fun q : Polynomial ℤ ↦ q.coeff n.1) hq
  rw [primitivePolynomial_coeff_of_mem n.2, Polynomial.coeff_zero] at this
  exact hn this

/-- Every coordinate of the normalized tuple remains nonzero, because the
tuple is indexed by the support of `p`. -/
theorem primitiveCoeffs_ne_zero_apply {p : Polynomial ℚ} (hp : p ≠ 0)
    (n : p.support) : primitiveCoeffs p n ≠ 0 := by
  intro hn
  have hcoord := congrFun
    (Primitive.eq_normalizationScale_smul
      (fun n : p.support ↦ p.coeff n.1)) n
  have hcoeff := Polynomial.mem_support_iff.mp n.2
  apply hcoeff
  have hcoord' : p.coeff n.1 =
      primitiveScale p * (primitiveCoeffs p n : ℚ) := by
    simpa only [primitiveScale, primitiveCoeffs, Pi.smul_apply, smul_eq_mul,
      Primitive.intCastVec_apply] using hcoord
  rw [hcoord', hn]
  simp

/-- The reconstructed integral polynomial has exactly the original support. -/
theorem primitivePolynomial_support {p : Polynomial ℚ} (hp : p ≠ 0) :
    (primitivePolynomial p).support = p.support := by
  classical
  ext n
  by_cases hn : n ∈ p.support
  · rw [Polynomial.mem_support_iff, primitivePolynomial_coeff_of_mem hn]
    simpa only [hn, iff_true] using primitiveCoeffs_ne_zero_apply hp ⟨n, hn⟩
  · rw [Polynomial.mem_support_iff, primitivePolynomial_coeff_of_not_mem hn]
    simp only [ne_eq, not_true_eq_false, hn, iff_false]

/-- The integral coefficient tuple has gcd one. -/
theorem primitiveCoeffs_gcd_eq_one {p : Polynomial ℚ} (hp : p ≠ 0) :
    Finset.univ.gcd (primitiveCoeffs p) = 1 := by
  obtain ⟨u, hu⟩ := primitiveCoeffs_primitive hp
  have hdvd : Finset.univ.gcd (primitiveCoeffs p) ∣ (1 : ℤ) := by
    rw [← hu]
    apply Finset.dvd_sum
    intro n hn
    exact dvd_mul_of_dvd_right (Finset.gcd_dvd hn) _
  rw [← Finset.normalize_gcd, normalize_eq_one]
  exact isUnit_iff_dvd_one.mpr hdvd

/-- Supremum norm of the primitive integral coefficient tuple. -/
def coeffSup (p : Polynomial ℚ) : ℤ :=
  ⨆ n : p.support, |primitiveCoeffs p n|

theorem coeffSup_pos {p : Polynomial ℚ} (hp : p ≠ 0) : 0 < coeffSup p := by
  obtain ⟨n, hn⟩ := Function.ne_iff.mp (primitiveCoeffs_ne_zero hp)
  have hle : |primitiveCoeffs p n| ≤ coeffSup p :=
    Finite.le_ciSup (fun i : p.support ↦ |primitiveCoeffs p i|) n
  have hpos : 0 < |primitiveCoeffs p n| := abs_pos.mpr hn
  exact hpos.trans_le hle

/-- Projective coefficient height is the logarithm of the supremum norm of
the primitive integral coefficient tuple. -/
theorem projectiveCoeffHeight_eq_log_coeffSup {p : Polynomial ℚ} (hp : p ≠ 0) :
    projectiveCoeffHeight ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm p) =
      Real.log ((coeffSup p : ℤ) : ℝ) := by
  let x : p.support → ℚ := fun n ↦ p.coeff n.1
  let z : p.support → ℤ := primitiveCoeffs p
  letI : Nonempty p.support := Finset.nonempty_coe_sort.mpr
    (Polynomial.support_nonempty.mpr hp)
  have hs : primitiveScale p ≠ 0 := primitiveScale_ne_zero hp
  calc
    projectiveCoeffHeight ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm p) =
        Height.logHeight x := projectiveCoeffHeight_uniqueAlgEquiv_symm p
    _ = Height.logHeight (Primitive.intCastVec z) := by
      rw [show x = primitiveScale p • Primitive.intCastVec z by
        exact Primitive.eq_normalizationScale_smul x]
      exact Height.logHeight_smul_eq_logHeight _ hs
    _ = Real.log ((coeffSup p : ℤ) : ℝ) := by
      change Height.logHeight (((↑) : ℤ → ℚ) ∘ z) =
        Real.log ((coeffSup p : ℤ) : ℝ)
      simpa only [z, coeffSup, primitiveCoeffs] using
        Rat.logHeight_eq_max_abs_of_gcd_eq_one (primitiveCoeffs_gcd_eq_one hp)

/-- Reconstructing the normalized coefficient tuple changes the polynomial
only by the common nonzero rational scale. -/
theorem eq_C_mul_map_primitivePolynomial (p : Polynomial ℚ) :
    p = Polynomial.C (primitiveScale p) *
      (primitivePolynomial p).map (Int.castRingHom ℚ) := by
  classical
  ext n
  by_cases hn : n ∈ p.support
  · have hcoord := congrFun
      (Primitive.eq_normalizationScale_smul
        (fun n : p.support ↦ p.coeff n.1)) ⟨n, hn⟩
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map,
      primitivePolynomial_coeff_of_mem hn]
    change p.coeff n = primitiveScale p * (primitiveCoeffs p ⟨n, hn⟩ : ℚ)
    simpa only [primitiveScale, primitiveCoeffs, Pi.smul_apply, smul_eq_mul,
      Primitive.intCastVec_apply] using hcoord
  · rw [Polynomial.notMem_support_iff.mp hn]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map,
      primitivePolynomial_coeff_of_not_mem hn]
    change (0 : ℚ) = primitiveScale p * (0 : ℚ)
    simp

/-- The Mahler height of the primitive integral representative is bounded by
the projective coefficient height plus the logarithm of the support size. -/
theorem mahlerHeight_primitivePolynomial_le {p : Polynomial ℚ} (hp : p ≠ 0) :
    RothIndex.mahlerHeight (primitivePolynomial p) ≤
      Real.log (p.support.card : ℝ) +
        projectiveCoeffHeight ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm p) := by
  let q : Polynomial ℤ := primitivePolynomial p
  let qC : Polynomial ℂ := q.map (Int.castRingHom ℂ)
  have hq : q ≠ 0 := primitivePolynomial_ne_zero hp
  have hqC : qC ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (R := ℤ) (S := ℂ) Int.cast_injective).mpr hq
  have hsupp : qC.support = p.support := by
    calc
      qC.support = q.support := Polynomial.support_map_of_injective q Int.cast_injective
      _ = p.support := primitivePolynomial_support hp
  have hsum : qC.sum (fun _ a ↦ ‖a‖) ≤
      (p.support.card : ℝ) * ((coeffSup p : ℤ) : ℝ) := by
    rw [Polynomial.sum_def, hsupp]
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_id] using
      p.support.sum_le_card_nsmul
        (fun n ↦ ‖qC.coeff n‖)
        (((coeffSup p : ℤ) : ℝ)) (fun n hn ↦ by
          have hle : |primitiveCoeffs p ⟨n, hn⟩| ≤ coeffSup p :=
            Finite.le_ciSup
              (fun i : p.support ↦ |primitiveCoeffs p i|) ⟨n, hn⟩
          change ‖((primitivePolynomial p).map
            (Int.castRingHom ℂ)).coeff n‖ ≤ _
          rw [Polynomial.coeff_map, primitivePolynomial_coeff_of_mem hn]
          change ‖(primitiveCoeffs p ⟨n, hn⟩ : ℂ)‖ ≤ _
          rw [Complex.norm_intCast]
          exact_mod_cast hle)
  have hmeasure : qC.mahlerMeasure ≤
      (p.support.card : ℝ) * ((coeffSup p : ℤ) : ℝ) :=
    (Polynomial.mahlerMeasure_le_sum_norm_coeff qC).trans hsum
  have hcard : 0 < (p.support.card : ℝ) := by
    exact_mod_cast (Polynomial.support_nonempty.mpr hp).card_pos
  have hsup : 0 < (((coeffSup p : ℤ) : ℝ)) := by
    exact_mod_cast coeffSup_pos hp
  rw [RothIndex.mahlerHeight, Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
  change Real.log qC.mahlerMeasure ≤ _
  calc
    Real.log qC.mahlerMeasure ≤
        Real.log ((p.support.card : ℝ) * ((coeffSup p : ℤ) : ℝ)) :=
      Real.log_le_log (Polynomial.mahlerMeasure_pos_of_ne_zero hqC) hmeasure
    _ = Real.log (p.support.card : ℝ) +
        Real.log ((coeffSup p : ℤ) : ℝ) := by
      rw [Real.log_mul hcard.ne' hsup.ne']
    _ = Real.log (p.support.card : ℝ) +
        projectiveCoeffHeight
          ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm p) := by
      rw [projectiveCoeffHeight_eq_log_coeffSup hp]

/-! ## The primitive linear polynomial of a rational point -/

/-- The primitive integral linear polynomial whose root is `β`. -/
def rationalLinearPolynomial (β : ℚ) : Polynomial ℤ :=
  RothIndex.integerLinearPolynomial (β.den : ℤ) (-β.num)

theorem rationalLinearPolynomial_ne_zero (β : ℚ) :
    rationalLinearPolynomial β ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun q : Polynomial ℤ ↦ q.coeff 1) h
  have hden : (β.den : ℤ) ≠ 0 := by exact_mod_cast β.den_nz
  apply hden
  change (Polynomial.C (β.den : ℤ) * Polynomial.X +
    Polynomial.C (-β.num)).coeff 1 = 0 at hcoeff
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_one, Polynomial.coeff_C] at hcoeff
  simpa using hcoeff

/-- The coefficients `den β` and `-num β` are coprime. -/
theorem rationalLinearPolynomial_primitive (β : ℚ) :
    (rationalLinearPolynomial β).IsPrimitive := by
  intro c hc
  have hall := (Polynomial.C_dvd_iff_dvd_coeff c
    (rationalLinearPolynomial β)).mp hc
  have hnum : c ∣ β.num := by
    have h := hall 0
    simp only [rationalLinearPolynomial, RothIndex.integerLinearPolynomial,
      Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_zero, mul_zero, Polynomial.coeff_C_zero,
      zero_add] at h
    simpa using h
  have hden : c ∣ (β.den : ℤ) := by
    have h := hall 1
    change c ∣ (Polynomial.C (β.den : ℤ) * Polynomial.X +
      Polynomial.C (-β.num)).coeff 1 at h
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_one, Polynomial.coeff_C] at h
    simpa using h
  exact (Rat.isCoprime_num_den β).isUnit_of_dvd' hnum hden

/-- Over `ℚ`, the primitive integral linear polynomial is a nonzero constant
multiple of the usual monic factor. -/
theorem map_rationalLinearPolynomial (β : ℚ) :
    (rationalLinearPolynomial β).map (Int.castRingHom ℚ) =
      Polynomial.C (β.den : ℚ) * (Polynomial.X - Polynomial.C β) := by
  simp only [rationalLinearPolynomial, RothIndex.integerLinearPolynomial,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  have hβ : (β.den : ℚ) * β = β.num := by
    rw [mul_comm, Rat.mul_den_eq_num]
  rw [mul_sub, ← Polynomial.C_mul, hβ]
  rw [sub_eq_add_neg]
  norm_num

/-- Its Mahler height is exactly the logarithmic height of the rational root. -/
theorem mahlerHeight_rationalLinearPolynomial (β : ℚ) :
    RothIndex.mahlerHeight (rationalLinearPolynomial β) = Height.logHeight₁ β := by
  rw [rationalLinearPolynomial,
    RothIndex.mahlerHeight_integerLinearPolynomial
      (show (β.den : ℤ) ≠ 0 by exact_mod_cast β.den_nz),
    Rat.logHeight₁_eq_log_max]
  congr 1
  norm_num [max_comm]

private theorem isPrimitive_pow {P : Polynomial ℤ} (hP : P.IsPrimitive) :
    ∀ e : ℕ, (P ^ e).IsPrimitive
  | 0 => by simpa using (Polynomial.isPrimitive_one : (1 : Polynomial ℤ).IsPrimitive)
  | e + 1 => by
      rw [pow_succ]
      exact (isPrimitive_pow hP e).mul hP

/-- Multiplication by the nonzero normalization scale does not change root
multiplicity. -/
theorem rootMultiplicity_map_primitivePolynomial {p : Polynomial ℚ}
    (hp : p ≠ 0) (β : ℚ) :
    ((primitivePolynomial p).map (Int.castRingHom ℚ)).rootMultiplicity β =
      p.rootMultiplicity β := by
  let qQ := (primitivePolynomial p).map (Int.castRingHom ℚ)
  have hqQ : qQ ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (R := ℤ) (S := ℚ)
      Int.cast_injective).mpr (primitivePolynomial_ne_zero hp)
  have hs : primitiveScale p ≠ 0 := primitiveScale_ne_zero hp
  have hprod : Polynomial.C (primitiveScale p) * qQ ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hs) hqQ
  have hmul := Polynomial.rootMultiplicity_mul (x := β) hprod
  have hscale : (Polynomial.C (primitiveScale p)).rootMultiplicity β = 0 :=
    Polynomial.rootMultiplicity_C _ _
  calc
    qQ.rootMultiplicity β =
        (Polynomial.C (primitiveScale p) * qQ).rootMultiplicity β := by
      rw [hmul, hscale, zero_add]
    _ = p.rootMultiplicity β := by
      rw [← eq_C_mul_map_primitivePolynomial p]

/-- The full power of the primitive rational-root factor divides the
primitive integral representative. -/
theorem rationalLinearPolynomial_pow_rootMultiplicity_dvd
    {p : Polynomial ℚ} (hp : p ≠ 0) (β : ℚ) :
    rationalLinearPolynomial β ^ p.rootMultiplicity β ∣
      primitivePolynomial p := by
  let qQ := (primitivePolynomial p).map (Int.castRingHom ℚ)
  let e := p.rootMultiplicity β
  have hmonic : (Polynomial.X - Polynomial.C β) ^ e ∣ qQ := by
    have hroot := Polynomial.pow_rootMultiplicity_dvd qQ β
    rwa [rootMultiplicity_map_primitivePolynomial hp β] at hroot
  have hden : (β.den : ℚ) ≠ 0 := by exact_mod_cast β.den_nz
  have hu : IsUnit ((Polynomial.C (β.den : ℚ)) ^ e) :=
    (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hden)).pow e
  have hmap :
      (rationalLinearPolynomial β ^ e).map (Int.castRingHom ℚ) ∣ qQ := by
    rw [Polynomial.map_pow, map_rationalLinearPolynomial, mul_pow]
    exact hu.mul_left_dvd.mpr hmonic
  exact (isPrimitive_pow (rationalLinearPolynomial_primitive β) e)
    |>.dvd_of_fraction_map_dvd_fraction_map hmap

/-- A polynomial with degree at most `r` has logarithmic support size at
most `r`.  This deliberately coarse form is convenient in Roth estimates. -/
theorem log_card_support_le_natDegreeBound {p : Polynomial ℚ} (hp : p ≠ 0)
    {r : ℕ} (hdeg : p.natDegree ≤ r) :
    Real.log (p.support.card : ℝ) ≤ (r : ℝ) := by
  have hsubset : p.support ⊆ Finset.range (r + 1) := by
    intro n hn
    rw [Finset.mem_range]
    exact (Polynomial.le_natDegree_of_mem_supp n hn).trans_lt
      (hdeg.trans_lt (Nat.lt_succ_self r))
  have hcardNat : p.support.card ≤ r + 1 := by
    simpa using Finset.card_le_card hsubset
  have hcardPos : 0 < (p.support.card : ℝ) := by
    exact_mod_cast (Polynomial.support_nonempty.mpr hp).card_pos
  have hcardReal : (p.support.card : ℝ) ≤ (r + 1 : ℕ) := by
    exact_mod_cast hcardNat
  calc
    Real.log (p.support.card : ℝ) ≤ Real.log ((r + 1 : ℕ) : ℝ) :=
      Real.log_le_log hcardPos hcardReal
    _ ≤ ((r + 1 : ℕ) : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    _ = (r : ℝ) := by push_cast; ring

/-- **One-variable multiplicity-height inequality.**  A rational root of a
nonzero rational polynomial, counted with multiplicity, consumes at most the
projective coefficient height plus the degree bound. -/
theorem rootMultiplicity_mul_logHeight₁_le
    {p : Polynomial ℚ} (hp : p ≠ 0) (β : ℚ) {r : ℕ}
    (hdeg : p.natDegree ≤ r) :
    (p.rootMultiplicity β : ℝ) * Height.logHeight₁ β ≤
      projectiveCoeffHeight
          ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm p) + (r : ℝ) := by
  have hfactor := RothIndex.nat_mul_mahlerHeight_le_of_pow_dvd
    (rationalLinearPolynomial_ne_zero β)
    (primitivePolynomial_ne_zero hp)
    (rationalLinearPolynomial_pow_rootMultiplicity_dvd hp β)
  rw [mahlerHeight_rationalLinearPolynomial] at hfactor
  calc
    (p.rootMultiplicity β : ℝ) * Height.logHeight₁ β ≤
        RothIndex.mahlerHeight (primitivePolynomial p) := hfactor
    _ ≤ Real.log (p.support.card : ℝ) +
        projectiveCoeffHeight
          ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm p) :=
      mahlerHeight_primitivePolynomial_le hp
    _ ≤ projectiveCoeffHeight
          ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm p) + (r : ℝ) := by
      linarith [log_card_support_le_natDegreeBound hp hdeg]

/-- The same estimate stated directly for an `MvPolynomial` in one variable. -/
theorem uniqueAlgEquiv_rootMultiplicity_mul_logHeight₁_le
    {P : MvPolynomial (Fin 1) ℚ} (hP : P ≠ 0) (β : ℚ) {r : ℕ}
    (hdeg : (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) P).natDegree ≤ r) :
    ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) P).rootMultiplicity β : ℝ) *
        Height.logHeight₁ β ≤ projectiveCoeffHeight P + (r : ℝ) := by
  have h := rootMultiplicity_mul_logHeight₁_le
    ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).injective.ne hP) β hdeg
  rw [(MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm_apply_apply] at h
  exact h

#print axioms rootMultiplicity_mul_logHeight₁_le
#print axioms uniqueAlgEquiv_rootMultiplicity_mul_logHeight₁_le

end
end Erdos407.MahlerHeightBridge

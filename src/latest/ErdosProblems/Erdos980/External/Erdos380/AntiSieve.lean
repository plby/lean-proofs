import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveGaussSum
import BoundedGaps.BombieriVinogradov.Analytic.ReducedFractionFrequencies
import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.ConsecutiveInterval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.QuotientRing

/-!
# The finite Fourier uncertainty estimate for Erdős problem 380

This file starts the formalization of Tao's Lemma 2.7.  The theorem below
is its one-modulus form: if a function on `ZMod q` vanishes on `omega`
residue classes, its nonconstant Fourier energy is at least
`omega / (q - omega)` times the square of its total mass.
-/

open scoped BigOperators Function

namespace Erdos380

private lemma norm_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (∑ _i ∈ s, (1 : ℝ) ^ 2) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s
        (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
    _ = (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by simp

/-- The residue classes outside a prescribed vanishing set. -/
def survivingResidues {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) :
    Finset (ZMod q) := Finset.univ \ vanishing

lemma card_survivingResidues {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) :
    (survivingResidues vanishing).card = q - vanishing.card := by
  classical
  rw [survivingResidues, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

lemma sum_eq_sum_survivingResidues_of_eq_zero
    {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) (f : ZMod q → ℂ)
    (hvanish : ∀ x ∈ vanishing, f x = 0) :
    ∑ x : ZMod q, f x = ∑ x ∈ survivingResidues vanishing, f x := by
  classical
  rw [survivingResidues]
  symm
  exact Finset.sum_subset (Finset.sdiff_subset :
    Finset.univ \ vanishing ⊆ (Finset.univ : Finset (ZMod q))) fun x _hx hxnot => by
      have hx : x ∈ vanishing := by simpa using hxnot
      exact hvanish x hx

lemma sum_norm_sq_eq_sum_survivingResidues_of_eq_zero
    {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) (f : ZMod q → ℂ)
    (hvanish : ∀ x ∈ vanishing, f x = 0) :
    ∑ x : ZMod q, ‖f x‖ ^ 2 =
      ∑ x ∈ survivingResidues vanishing, ‖f x‖ ^ 2 := by
  classical
  rw [survivingResidues]
  symm
  exact Finset.sum_subset (Finset.sdiff_subset :
    Finset.univ \ vanishing ⊆ (Finset.univ : Finset (ZMod q))) fun x _hx hxnot => by
      have hx : x ∈ vanishing := by simpa using hxnot
      simp [hvanish x hx]

/-! ## The Fourier certificate used in the product uncertainty lemma -/

/-- The mean-zero residue mask
`omega - q * 1_vanishing` from Tao's proof of Lemma 2.7. -/
noncomputable def residueMask {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) (x : ZMod q) : ℂ :=
  (vanishing.card : ℂ) - (q : ℂ) * if x ∈ vanishing then 1 else 0

@[simp]
lemma residueMask_of_mem {q : ℕ} [NeZero q]
    {vanishing : Finset (ZMod q)} {x : ZMod q} (hx : x ∈ vanishing) :
    residueMask vanishing x = (vanishing.card : ℂ) - q := by
  simp [residueMask, hx]

@[simp]
lemma residueMask_of_notMem {q : ℕ} [NeZero q]
    {vanishing : Finset (ZMod q)} {x : ZMod q} (hx : x ∉ vanishing) :
    residueMask vanishing x = (vanishing.card : ℂ) := by
  simp [residueMask, hx]

/-- The residue mask has mean zero. -/
lemma sum_residueMask {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) :
    ∑ x : ZMod q, residueMask vanishing x = 0 := by
  classical
  simp only [residueMask, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  have hindicator :
      (∑ x : ZMod q, if x ∈ vanishing then (1 : ℂ) else 0) =
        (vanishing.card : ℂ) := by simp
  rw [← Finset.mul_sum, hindicator]
  simp only [Finset.card_univ, ZMod.card]
  ring

/-- Fourier coefficient of the normalized residue mask. -/
noncomputable def residueMaskCoefficient {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) (a : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * ZMod.dft (residueMask vanishing) a

@[simp]
lemma residueMaskCoefficient_zero {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) :
    residueMaskCoefficient vanishing 0 = 0 := by
  rw [residueMaskCoefficient, ZMod.dft_apply_zero, sum_residueMask]
  simp

/-- Fourier inversion of the residue mask, with the normalization placed
in the coefficient rather than in the additive character. -/
lemma residueMask_eq_sum_coeff_mul_stdAddChar
    {q : ℕ} [NeZero q] (vanishing : Finset (ZMod q)) (x : ZMod q) :
    residueMask vanishing x =
      ∑ a : ZMod q, residueMaskCoefficient vanishing a *
        ZMod.stdAddChar (a * x) := by
  have h := congrFun
    (ZMod.dft.symm_apply_apply (residueMask vanishing)) x
  rw [ZMod.invDFT_apply] at h
  rw [← h]
  simp only [residueMaskCoefficient, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

lemma norm_sq_residueMask {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) (x : ZMod q) :
    ‖residueMask vanishing x‖ ^ 2 =
      if x ∈ vanishing then
        ((q - vanishing.card : ℕ) : ℝ) ^ 2
      else (vanishing.card : ℝ) ^ 2 := by
  classical
  have hcard : vanishing.card ≤ q := by
    simpa using Finset.card_le_univ vanishing
  by_cases hx : x ∈ vanishing
  · simp only [hx, if_pos, residueMask_of_mem]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Nat.cast_sub hcard]
    norm_num
    ring
  · simp only [hx]
    rw [residueMask_of_notMem hx]
    norm_num

/-- Exact physical-space energy of the mean-zero residue mask. -/
lemma sum_norm_sq_residueMask {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) :
    (∑ x : ZMod q, ‖residueMask vanishing x‖ ^ 2) =
      (q : ℝ) * vanishing.card * (q - vanishing.card : ℕ) := by
  classical
  have hcard : vanishing.card ≤ q := by
    simpa using Finset.card_le_univ vanishing
  have hnotcard :
      ((Finset.univ : Finset (ZMod q)).filter
        (fun x => x ∉ vanishing)).card = q - vanishing.card := by
    rw [← card_survivingResidues vanishing]
    congr 1
    ext x
    simp [survivingResidues]
  simp_rw [norm_sq_residueMask]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  rw [hnotcard]
  push_cast [Nat.cast_sub hcard]
  ring

/-- Parseval gives the exact coefficient energy occurring in Tao's
uncertainty principle. -/
lemma sum_norm_sq_residueMaskCoefficient {q : ℕ} [NeZero q]
    (vanishing : Finset (ZMod q)) :
    (∑ a : ZMod q, ‖residueMaskCoefficient vanishing a‖ ^ 2) =
      (vanishing.card : ℝ) * (q - vanishing.card : ℕ) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  calc
    (∑ a : ZMod q, ‖residueMaskCoefficient vanishing a‖ ^ 2) =
        ((q : ℝ)⁻¹) ^ 2 *
          ∑ a : ZMod q, ‖ZMod.dft (residueMask vanishing) a‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      simp only [residueMaskCoefficient, norm_mul, norm_inv,
        Complex.norm_natCast, mul_pow]
    _ = ((q : ℝ)⁻¹) ^ 2 *
        ((q : ℝ) * ∑ x : ZMod q, ‖residueMask vanishing x‖ ^ 2) := by
      rw [BoundedGaps.Maynard.sum_norm_sq_dft]
    _ = (vanishing.card : ℝ) * (q - vanishing.card : ℕ) := by
      rw [sum_norm_sq_residueMask]
      field_simp

/-! ## Tensoring the Fourier certificate over coprime CRT components -/

/-- A tuple of residue classes for a finite family of moduli. -/
abbrev residueVectors {I : Type*} (modulus : I → ℕ) :=
  ∀ i, ZMod (modulus i)

/-- Product of the one-coordinate mean-zero masks. -/
noncomputable def productResidueMask
    {I : Type*} [Fintype I] {modulus : I → ℕ}
    [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (x : residueVectors modulus) : ℂ :=
  ∏ i, residueMask (vanishing i) (x i)

/-- Product of the normalized Fourier coefficients of the coordinate
masks. -/
noncomputable def productResidueMaskCoefficient
    {I : Type*} [Fintype I] {modulus : I → ℕ}
    [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (a : residueVectors modulus) : ℂ :=
  ∏ i, residueMaskCoefficient (vanishing i) (a i)

/-- The additive character on the product of the CRT components. -/
noncomputable def productResidueAddChar
    {I : Type*} [Fintype I] {modulus : I → ℕ}
    [∀ i, NeZero (modulus i)]
    (a x : residueVectors modulus) : ℂ :=
  ∏ i, ZMod.stdAddChar (a i * x i)

/-- Fourier expansion of the product mask. -/
lemma productResidueMask_eq_fourierExpansion
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (x : residueVectors modulus) :
    productResidueMask vanishing x =
      ∑ a : residueVectors modulus,
        productResidueMaskCoefficient vanishing a *
          productResidueAddChar a x := by
  classical
  calc
    productResidueMask vanishing x =
        ∏ i, ∑ a : ZMod (modulus i),
          residueMaskCoefficient (vanishing i) a *
            ZMod.stdAddChar (a * x i) := by
      unfold productResidueMask
      apply Finset.prod_congr rfl
      intro i _hi
      exact residueMask_eq_sum_coeff_mul_stdAddChar (vanishing i) (x i)
    _ = ∑ a : residueVectors modulus,
        ∏ i, residueMaskCoefficient (vanishing i) (a i) *
          ZMod.stdAddChar (a i * x i) := by
      rw [Finset.prod_univ_sum]
      simp
    _ = ∑ a : residueVectors modulus,
        productResidueMaskCoefficient vanishing a *
          productResidueAddChar a x := by
      apply Finset.sum_congr rfl
      intro a _ha
      simp only [productResidueMaskCoefficient, productResidueAddChar,
        Finset.prod_mul_distrib]

/-- A product coefficient vanishes as soon as one component frequency is
zero. -/
lemma productResidueMaskCoefficient_eq_zero_of_exists_eq_zero
    {I : Type*} [Fintype I] {modulus : I → ℕ}
    [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (a : residueVectors modulus) (hzero : ∃ i, a i = 0) :
    productResidueMaskCoefficient vanishing a = 0 := by
  classical
  obtain ⟨i, hi⟩ := hzero
  unfold productResidueMaskCoefficient
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [hi] using residueMaskCoefficient_zero (vanishing i)

/-- Exact factorization of the product-mask Fourier energy. -/
lemma sum_norm_sq_productResidueMaskCoefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i))) :
    (∑ a : residueVectors modulus,
        ‖productResidueMaskCoefficient vanishing a‖ ^ 2) =
      ∏ i, ((vanishing i).card : ℝ) *
        ((modulus i - (vanishing i).card : ℕ) : ℝ) := by
  classical
  calc
    (∑ a : residueVectors modulus,
        ‖productResidueMaskCoefficient vanishing a‖ ^ 2) =
        ∑ a : residueVectors modulus,
          ∏ i, ‖residueMaskCoefficient (vanishing i) (a i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _ha
      simp only [productResidueMaskCoefficient, norm_prod,
        Finset.prod_pow]
    _ = ∏ i, ∑ a : ZMod (modulus i),
        ‖residueMaskCoefficient (vanishing i) a‖ ^ 2 := by
      rw [Finset.prod_univ_sum]
      simp
    _ = ∏ i, ((vanishing i).card : ℝ) *
        ((modulus i - (vanishing i).card : ℕ) : ℝ) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact sum_norm_sq_residueMaskCoefficient (vanishing i)

/-- Frequencies that are nonzero in every CRT component. -/
noncomputable def allNonzeroResidueFrequencies
    {I : Type*} [Fintype I] [DecidableEq I] {modulus : I → ℕ}
    [∀ i, NeZero (modulus i)] :
    Finset (residueVectors modulus) := by
  classical
  exact Finset.univ.filter fun a => ∀ i, a i ≠ 0

/-- Fourier sum of a function on a product of residue rings. -/
noncomputable def productResidueFourierSum
    {I : Type*} [Fintype I] [DecidableEq I] {modulus : I → ℕ}
    [∀ i, NeZero (modulus i)]
    (f : residueVectors modulus → ℂ) (a : residueVectors modulus) : ℂ :=
  ∑ x, f x * productResidueAddChar a x

lemma productResidueMask_of_avoids
    {I : Type*} [Fintype I] {modulus : I → ℕ}
    [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (x : residueVectors modulus) (hx : ∀ i, x i ∉ vanishing i) :
    productResidueMask vanishing x =
      ∏ i, ((vanishing i).card : ℂ) := by
  classical
  unfold productResidueMask
  apply Finset.prod_congr rfl
  intro i _hi
  exact residueMask_of_notMem (hx i)

/-- Multiplying by the product mask does not change a function that
vanishes whenever any coordinate lies in its prescribed vanishing set,
apart from the constant factor `∏ omega(q)`. -/
lemma productResidueMask_weighted_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ}
    [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (f : residueVectors modulus → ℂ)
    (hvanish : ∀ x, (∃ i, x i ∈ vanishing i) → f x = 0) :
    (∏ i, ((vanishing i).card : ℂ)) * ∑ x, f x =
      ∑ x, f x * productResidueMask vanishing x := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases havoid : ∀ i, x i ∉ vanishing i
  · rw [productResidueMask_of_avoids vanishing x havoid]
    ring
  · push Not at havoid
    have hfx : f x = 0 := hvanish x havoid
    simp [hfx]

/-- The tensor-product Fourier expansion paired against a function. -/
lemma productResidueMask_pairing_eq_fourierPairing
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (f : residueVectors modulus → ℂ) :
    (∑ x, f x * productResidueMask vanishing x) =
      ∑ a, productResidueMaskCoefficient vanishing a *
        productResidueFourierSum f a := by
  classical
  simp_rw [productResidueMask_eq_fourierExpansion vanishing]
  unfold productResidueFourierSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- Frequencies outside `allNonzeroResidueFrequencies` have zero mask
coefficient and can be deleted from the pairing. -/
lemma productResidueFourierPairing_eq_sum_allNonzero
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (f : residueVectors modulus → ℂ) :
    (∑ a, productResidueMaskCoefficient vanishing a *
        productResidueFourierSum f a) =
      ∑ a ∈ allNonzeroResidueFrequencies,
        productResidueMaskCoefficient vanishing a *
          productResidueFourierSum f a := by
  classical
  symm
  unfold allNonzeroResidueFrequencies
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a _ha hnot
  have hnotAll : ¬ ∀ i, a i ≠ 0 := by
    intro hall
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
  push Not at hnotAll
  rw [productResidueMaskCoefficient_eq_zero_of_exists_eq_zero
    vanishing a hnotAll]
  simp

/-- The complete Fourier certificate behind Montgomery's product
uncertainty principle. -/
theorem productResidue_fourier_certificate
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (f : residueVectors modulus → ℂ)
    (hvanish : ∀ x, (∃ i, x i ∈ vanishing i) → f x = 0) :
    (∏ i, ((vanishing i).card : ℂ)) * ∑ x, f x =
      ∑ a ∈ allNonzeroResidueFrequencies,
        productResidueMaskCoefficient vanishing a *
          productResidueFourierSum f a := by
  rw [productResidueMask_weighted_sum vanishing f hvanish,
    productResidueMask_pairing_eq_fourierPairing,
    productResidueFourierPairing_eq_sum_allNonzero]

private lemma norm_sum_mul_sq_le
    {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have hnorm :
      ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖a i * b i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
        simp_rw [Complex.norm_mul]
  calc
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
        (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
        mul_nonneg (norm_nonneg (a i)) (norm_nonneg (b i)))).mpr hnorm
    _ ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖)

/-- Montgomery's product uncertainty principle in a denominator-free form.
This is the Cauchy--Schwarz conclusion of Tao's Lemma 2.7 on the product of
the CRT residue rings. -/
theorem montgomery_uncertainty_product_cross
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (f : residueVectors modulus → ℂ)
    (hvanish : ∀ x, (∃ i, x i ∈ vanishing i) → f x = 0) :
    (∏ i, ((vanishing i).card : ℝ)) ^ 2 * ‖∑ x, f x‖ ^ 2 ≤
      (∏ i, ((vanishing i).card : ℝ) *
          ((modulus i - (vanishing i).card : ℕ) : ℝ)) *
        ∑ a ∈ allNonzeroResidueFrequencies,
          ‖productResidueFourierSum f a‖ ^ 2 := by
  classical
  have hcertificate :=
    productResidue_fourier_certificate vanishing f hvanish
  have hcauchy := norm_sum_mul_sq_le
    (allNonzeroResidueFrequencies (modulus := modulus))
    (productResidueMaskCoefficient vanishing)
    (productResidueFourierSum f)
  rw [← hcertificate] at hcauchy
  have hleft :
      ‖(∏ i, ((vanishing i).card : ℂ)) * ∑ x, f x‖ ^ 2 =
        (∏ i, ((vanishing i).card : ℝ)) ^ 2 *
          ‖∑ x, f x‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    congr 1
    rw [norm_prod]
    simp only [Complex.norm_natCast]
  have hcoeff :
      (∑ a ∈ allNonzeroResidueFrequencies,
          ‖productResidueMaskCoefficient vanishing a‖ ^ 2) ≤
        ∏ i, ((vanishing i).card : ℝ) *
          ((modulus i - (vanishing i).card : ℕ) : ℝ) := by
    calc
      (∑ a ∈ allNonzeroResidueFrequencies,
          ‖productResidueMaskCoefficient vanishing a‖ ^ 2) ≤
          ∑ a, ‖productResidueMaskCoefficient vanishing a‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro a _ha _hnot
        positivity
      _ = ∏ i, ((vanishing i).card : ℝ) *
          ((modulus i - (vanishing i).card : ℕ) : ℝ) :=
        sum_norm_sq_productResidueMaskCoefficient vanishing
  rw [hleft] at hcauchy
  exact hcauchy.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))

/-- Montgomery's product uncertainty principle with Tao's exact product of
ratios.  Positivity assumptions merely exclude the vacuous zero-denominator
cases. -/
theorem montgomery_uncertainty_product
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (f : residueVectors modulus → ℂ)
    (hvanish : ∀ x, (∃ i, x i ∈ vanishing i) → f x = 0)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    (∏ i, ((vanishing i).card : ℝ) /
        ((modulus i - (vanishing i).card : ℕ) : ℝ)) *
        ‖∑ x, f x‖ ^ 2 ≤
      ∑ a ∈ allNonzeroResidueFrequencies,
        ‖productResidueFourierSum f a‖ ^ 2 := by
  classical
  let W : ℝ := ∏ i, ((vanishing i).card : ℝ)
  let D : ℝ := ∏ i,
    ((modulus i - (vanishing i).card : ℕ) : ℝ)
  let E : ℝ := ∑ a ∈ allNonzeroResidueFrequencies,
    ‖productResidueFourierSum f a‖ ^ 2
  let F : ℝ := ‖∑ x, f x‖ ^ 2
  have hWpos : 0 < W := by
    unfold W
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast (Finset.card_pos.mpr (hnonempty i))
  have hDpos : 0 < D := by
    unfold D
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast Nat.sub_pos_of_lt (hproper i)
  have hcross :=
    montgomery_uncertainty_product_cross vanishing f hvanish
  have hcoefficient :
      (∏ i, ((vanishing i).card : ℝ) *
          ((modulus i - (vanishing i).card : ℕ) : ℝ)) = W * D := by
    unfold W D
    exact Finset.prod_mul_distrib
  have hcancel : W * F ≤ D * E := by
    apply le_of_mul_le_mul_left (a := W) _ hWpos
    calc
      W * (W * F) = W ^ 2 * F := by ring
      _ ≤ (W * D) * E := by
        simpa only [W, D, E, F, hcoefficient] using hcross
      _ = W * (D * E) := by ring
  have hratio : W / D * F ≤ E := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hDpos]
    simpa [mul_comm] using hcancel
  have hprodRatio :
      (∏ i, ((vanishing i).card : ℝ) /
          ((modulus i - (vanishing i).card : ℕ) : ℝ)) = W / D := by
    unfold W D
    rw [Finset.prod_div_distrib]
  simpa only [hprodRatio, E, F] using hratio

/-! ## Returning from residue vectors to finitely supported integer sums -/

/-- The tuple of residue classes of a natural number. -/
def residueVectorOfNat
    {I : Type*} (modulus : I → ℕ) (n : ℕ) :
    residueVectors modulus := fun i => (n : ZMod (modulus i))

/-- Collect a finitely supported integer function by its complete tuple of
residue classes. -/
noncomputable def collectedResidueMass
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (support : Finset ℕ) (g : ℕ → ℂ)
    (r : residueVectors modulus) : ℂ := by
  classical
  exact ∑ n ∈ support, if residueVectorOfNat modulus n = r then g n else 0

lemma sum_collectedResidueMass
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (support : Finset ℕ) (g : ℕ → ℂ) :
    (∑ r : residueVectors modulus,
        collectedResidueMass support g r) = ∑ n ∈ support, g n := by
  classical
  unfold collectedResidueMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  simp

lemma collectedResidueMass_eq_zero_of_coordinate_mem
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (support : Finset ℕ) (g : ℕ → ℂ)
    (hg : ∀ n ∈ support, (∃ i, (n : ZMod (modulus i)) ∈ vanishing i) →
      g n = 0)
    (r : residueVectors modulus)
    (hr : ∃ i, r i ∈ vanishing i) :
    collectedResidueMass support g r = 0 := by
  classical
  unfold collectedResidueMass
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hnr : residueVectorOfNat modulus n = r
  · obtain ⟨i, hi⟩ := hr
    have hcoord : (n : ZMod (modulus i)) = r i := by
      simpa [residueVectorOfNat] using congrFun hnr i
    have hremoved : ∃ i, (n : ZMod (modulus i)) ∈ vanishing i := by
      refine ⟨i, ?_⟩
      rwa [hcoord]
    have hgn : g n = 0 := hg n hn hremoved
    simp [hnr, hgn]
  · simp [hnr]

lemma productResidueFourierSum_collectedResidueMass
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (support : Finset ℕ) (g : ℕ → ℂ)
    (a : residueVectors modulus) :
    productResidueFourierSum (collectedResidueMass support g) a =
      ∑ n ∈ support, g n *
        productResidueAddChar a (residueVectorOfNat modulus n) := by
  classical
  unfold productResidueFourierSum collectedResidueMass
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [ite_mul, zero_mul]
  simp

/-- Tao's Montgomery uncertainty lemma for an integer function supported
on a finite set, reindexed by the nonzero frequencies in each modulus
component.  Pairwise coprimality is only needed later, to prove that these
frequencies are distinct points of the circle. -/
theorem montgomery_uncertainty_integer_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (support : Finset ℕ) (g : ℕ → ℂ)
    (hg : ∀ n ∈ support, (∃ i, (n : ZMod (modulus i)) ∈ vanishing i) →
      g n = 0)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    (∏ i, ((vanishing i).card : ℝ) /
        ((modulus i - (vanishing i).card : ℕ) : ℝ)) *
        ‖∑ n ∈ support, g n‖ ^ 2 ≤
      ∑ a ∈ allNonzeroResidueFrequencies,
        ‖∑ n ∈ support, g n *
          productResidueAddChar a (residueVectorOfNat modulus n)‖ ^ 2 := by
  have h := montgomery_uncertainty_product vanishing
    (collectedResidueMass support g)
    (collectedResidueMass_eq_zero_of_coordinate_mem
      vanishing support g hg) hnonempty hproper
  simpa only [sum_collectedResidueMass,
    productResidueFourierSum_collectedResidueMass] using h

/-! ## Product frequencies as points of the additive circle -/

/-- The circle point `∑_i a_i / q_i` attached to a tuple of residue
frequencies. -/
noncomputable def productResidueFrequencyPoint
    {I : Type*} [Fintype I] {modulus : I → ℕ}
    [∀ i, NeZero (modulus i)]
    (a : residueVectors modulus) : UnitAddCircle :=
  ∑ i, ZMod.toAddCircle (a i)

/-- The product additive character is evaluation at the corresponding
circle point. -/
lemma productResidueAddChar_residueVectorOfNat
    {I : Type*} [Fintype I] {modulus : I → ℕ}
    [∀ i, NeZero (modulus i)]
    (a : residueVectors modulus) (n : ℕ) :
    productResidueAddChar a (residueVectorOfNat modulus n) =
      BoundedGaps.Maynard.unitAddCircleAddChar
        (n • productResidueFrequencyPoint a) := by
  classical
  calc
    productResidueAddChar a (residueVectorOfNat modulus n) =
        ∏ i, ZMod.stdAddChar (n • a i) := by
      unfold productResidueAddChar residueVectorOfNat
      apply Finset.prod_congr rfl
      intro i _hi
      congr 1
      simp [nsmul_eq_mul, mul_comm]
    _ = ∏ i, ZMod.stdAddChar (a i) ^ n := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact AddChar.map_nsmul_eq_pow _ _ _
    _ = (∏ i, ZMod.stdAddChar (a i)) ^ n := by
      rw [Finset.prod_pow]
    _ = BoundedGaps.Maynard.unitAddCircleAddChar
        (productResidueFrequencyPoint a) ^ n := by
      congr 1
      unfold productResidueFrequencyPoint
      symm
      let ψ := BoundedGaps.Maynard.unitAddCircleAddChar
      have hmapSum (s : Finset I) :
          ψ (∑ i ∈ s, ZMod.toAddCircle (a i)) =
            ∏ i ∈ s, ψ (ZMod.toAddCircle (a i)) := by
        induction s using Finset.induction_on with
        | empty => simp [ψ]
        | @insert i s hi ih =>
            simp only [Finset.sum_insert hi, Finset.prod_insert hi,
              AddChar.map_add_eq_mul, ih]
      calc
        ψ (∑ i, ZMod.toAddCircle (a i)) =
            ∏ i, ψ (ZMod.toAddCircle (a i)) := hmapSum Finset.univ
        _ = ∏ i, ZMod.stdAddChar (a i) := by rfl
    _ = BoundedGaps.Maynard.unitAddCircleAddChar
        (n • productResidueFrequencyPoint a) := by
      symm
      exact AddChar.map_nsmul_eq_pow _ _ _

open scoped Function in
/-- A natural number which is `1` in one CRT component and `0` in all
others. -/
noncomputable def crtSelectorNat
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) (hcoprime : Pairwise (Nat.Coprime on modulus))
    (i : I) : ℕ :=
  ((ZMod.prodEquivPi modulus hcoprime).symm
    (Pi.single i (1 : ZMod (modulus i)))).val

open scoped Function in
lemma residueVectorOfNat_crtSelectorNat
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus)) (i j : I) :
    residueVectorOfNat modulus (crtSelectorNat modulus hcoprime i) j =
      (Pi.single i (1 : ZMod (modulus i)) : residueVectors modulus) j := by
  classical
  letI : NeZero (∏ i, modulus i) := ⟨by
    exact Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (modulus i)⟩
  let e := ZMod.prodEquivPi modulus hcoprime
  let b : ZMod (∏ i, modulus i) :=
    e.symm (Pi.single i (1 : ZMod (modulus i)))
  have hcoordinate := congrFun
    (e.apply_symm_apply (Pi.single i (1 : ZMod (modulus i)))) j
  have hbval : ((b.val : ℕ) : ZMod (∏ i, modulus i)) = b :=
    ZMod.natCast_zmod_val b
  change ((b.val : ℕ) : ZMod (modulus j)) = _
  calc
    ((b.val : ℕ) : ZMod (modulus j)) =
        ZMod.castHom (Finset.dvd_prod_of_mem modulus (Finset.mem_univ j)) _
          ((b.val : ℕ) : ZMod (∏ i, modulus i)) := by simp
    _ = ZMod.castHom (Finset.dvd_prod_of_mem modulus (Finset.mem_univ j)) _ b := by
      rw [hbval]
    _ = (Pi.single i (1 : ZMod (modulus i)) : residueVectors modulus) j := by
      simpa only [e, b, ZMod.prodEquivPi_apply] using hcoordinate

open scoped Function in
lemma productResidueAddChar_crtSelectorNat
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (a : residueVectors modulus) (i : I) :
    productResidueAddChar a
        (residueVectorOfNat modulus (crtSelectorNat modulus hcoprime i)) =
      ZMod.stdAddChar (a i) := by
  classical
  unfold productResidueAddChar
  rw [Finset.prod_eq_single i]
  · rw [residueVectorOfNat_crtSelectorNat modulus hcoprime i i,
      Pi.single_eq_same]
    simp
  · intro j _hj hji
    rw [residueVectorOfNat_crtSelectorNat modulus hcoprime i j,
      Pi.single_eq_of_ne hji]
    simp
  · simp

open scoped Function in
/-- Pairwise coprimality makes the product frequencies distinct points of
the circle. -/
theorem productResidueFrequencyPoint_injective
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus)) :
    Function.Injective
      (productResidueFrequencyPoint : residueVectors modulus → UnitAddCircle) := by
  classical
  intro a b hab
  funext i
  let n := crtSelectorNat modulus hcoprime i
  have hcharacter := congrArg
    (fun z : UnitAddCircle =>
      BoundedGaps.Maynard.unitAddCircleAddChar (n • z)) hab
  rw [← productResidueAddChar_residueVectorOfNat a n,
    ← productResidueAddChar_residueVectorOfNat b n,
    productResidueAddChar_crtSelectorNat modulus hcoprime a i,
    productResidueAddChar_crtSelectorNat modulus hcoprime b i] at hcharacter
  exact ZMod.injective_stdAddChar hcharacter

open scoped Function in
/-- Distinct product frequencies are separated by the reciprocal of the
product modulus. -/
theorem one_div_prod_le_dist_productResidueFrequencyPoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    {a b : residueVectors modulus} (hab : a ≠ b) :
    (1 : ℝ) / (∏ i, modulus i : ℕ) ≤
      dist (productResidueFrequencyPoint a)
        (productResidueFrequencyPoint b) := by
  classical
  let Q : ℕ := ∏ i, modulus i
  have hQpos : 0 < Q := by
    unfold Q
    exact Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (modulus i))
  have hpointZero (u : residueVectors modulus) :
      Q • productResidueFrequencyPoint u = 0 := by
    unfold productResidueFrequencyPoint
    rw [← Finset.sum_nsmul]
    apply Finset.sum_eq_zero
    intro i _hi
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem modulus (Finset.mem_univ i)
    change (∏ i, modulus i) • ZMod.toAddCircle (u i) = 0
    rw [hc, mul_nsmul]
    have hinner : modulus i • ZMod.toAddCircle (u i) = 0 := by
      rw [← map_nsmul]
      simp
    rw [hinner, nsmul_zero]
  have hdiffZero :
      Q • (productResidueFrequencyPoint a -
        productResidueFrequencyPoint b) = 0 := by
    rw [nsmul_sub, hpointZero, hpointZero, sub_zero]
  have hfinite : IsOfFinAddOrder
      (productResidueFrequencyPoint a - productResidueFrequencyPoint b) :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨Q, hQpos, hdiffZero⟩
  have hdiff :
      productResidueFrequencyPoint a - productResidueFrequencyPoint b ≠ 0 :=
    sub_ne_zero.mpr ((productResidueFrequencyPoint_injective
      modulus hcoprime).ne hab)
  have horder :
      addOrderOf (productResidueFrequencyPoint a -
        productResidueFrequencyPoint b) ≤ Q :=
    addOrderOf_le_of_nsmul_eq_zero hQpos hdiffZero
  have hunit :
      (1 : ℝ) ≤
        (addOrderOf (productResidueFrequencyPoint a -
          productResidueFrequencyPoint b) : ℝ) *
          ‖productResidueFrequencyPoint a -
            productResidueFrequencyPoint b‖ := by
    simpa [nsmul_eq_mul] using
      AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder hfinite hdiff
  have hQposReal : (0 : ℝ) < Q := by exact_mod_cast hQpos
  rw [dist_eq_norm]
  rw [div_le_iff₀ hQposReal]
  calc
    (1 : ℝ) ≤
        (addOrderOf (productResidueFrequencyPoint a -
          productResidueFrequencyPoint b) : ℝ) *
          ‖productResidueFrequencyPoint a -
            productResidueFrequencyPoint b‖ := hunit
    _ ≤ (Q : ℝ) * ‖productResidueFrequencyPoint a -
          productResidueFrequencyPoint b‖ := by
      gcongr
    _ = ‖productResidueFrequencyPoint a -
          productResidueFrequencyPoint b‖ * Q := by ring

/-! ## Frequencies assembled over all subsets of a fixed cardinality -/

/-- The finite type of subsets of `I` having cardinality `k`. -/
abbrev fixedCardSubsets (I : Type*) [Fintype I] (k : ℕ) :=
  {s : Finset I // s.card = k}

/-- A nonzero product frequency on one `k`-element subset of the full
modulus family. -/
abbrev kSubsetResidueFrequencies
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] (k : ℕ) :=
  Σ T : fixedCardSubsets I k,
    {a : residueVectors (fun i : {i // i ∈ T.1} => modulus i.1) //
      a ∈ allNonzeroResidueFrequencies}

/-- Extend a frequency on a subset by zero in every unselected CRT
component. -/
noncomputable def extendKSubsetResidueFrequency
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] {k : ℕ}
    (u : kSubsetResidueFrequencies modulus k) : residueVectors modulus :=
  fun i => if hi : i ∈ u.1.1 then u.2.1 ⟨i, hi⟩ else 0

/-- The circle point associated to a subset frequency, viewed in the full
CRT family by extension by zero. -/
noncomputable def kSubsetResidueFrequencyPoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] {k : ℕ}
    (u : kSubsetResidueFrequencies modulus k) : UnitAddCircle :=
  productResidueFrequencyPoint (extendKSubsetResidueFrequency modulus u)

/-- Extending a subset frequency by zero does not change its circle
point. -/
lemma productResidueFrequencyPoint_extendKSubsetResidueFrequency
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] {k : ℕ}
    (u : kSubsetResidueFrequencies modulus k) :
    kSubsetResidueFrequencyPoint modulus u =
      productResidueFrequencyPoint u.2.1 := by
  classical
  unfold kSubsetResidueFrequencyPoint productResidueFrequencyPoint
    extendKSubsetResidueFrequency
  let F : I → UnitAddCircle := fun i =>
    ZMod.toAddCircle (if hi : i ∈ u.1.1 then u.2.1 ⟨i, hi⟩ else 0)
  change (∑ i : I, F i) = ∑ i : {i // i ∈ u.1.1}, ZMod.toAddCircle (u.2.1 i)
  calc
    (∑ i : I, F i) = ∑ i ∈ u.1.1, F i := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) fun i _hi hiT => by
        simp [F, hiT]
    _ = ∑ i : {i // i ∈ u.1.1}, F i :=
      Finset.sum_subtype u.1.1 (by simp) F
    _ = ∑ i : {i // i ∈ u.1.1}, ZMod.toAddCircle (u.2.1 i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [F, i.2]

/-- Extension by zero remembers both the chosen subset and all its
nonzero component frequencies. -/
theorem extendKSubsetResidueFrequency_injective
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] {k : ℕ} :
    Function.Injective
      (extendKSubsetResidueFrequency modulus :
        kSubsetResidueFrequencies modulus k → residueVectors modulus) := by
  classical
  rintro ⟨T, a⟩ ⟨U, b⟩ hab
  have ha : ∀ i, a.1 i ≠ 0 := by
    simpa only [allNonzeroResidueFrequencies, Finset.mem_filter,
      Finset.mem_univ, true_and] using a.2
  have hb : ∀ i, b.1 i ≠ 0 := by
    simpa only [allNonzeroResidueFrequencies, Finset.mem_filter,
      Finset.mem_univ, true_and] using b.2
  have hTUfin : T.1 = U.1 := by
    ext i
    constructor
    · intro hiT
      by_contra hiU
      have hiEq := congrFun hab i
      have hz : a.1 ⟨i, hiT⟩ = 0 := by
        simpa [extendKSubsetResidueFrequency, hiT, hiU] using hiEq
      exact ha ⟨i, hiT⟩ hz
    · intro hiU
      by_contra hiT
      have hiEq := congrFun hab i
      have hz : b.1 ⟨i, hiU⟩ = 0 := by
        simpa [extendKSubsetResidueFrequency, hiT, hiU] using hiEq.symm
      exact hb ⟨i, hiU⟩ hz
  have hTU : T = U := Subtype.ext hTUfin
  subst U
  have hab' : a = b := by
    apply Subtype.ext
    funext i
    have hiEq := congrFun hab i.1
    simpa [extendKSubsetResidueFrequency, i.2] using hiEq
  rw [hab']

/-- Subset frequencies give distinct points of the additive circle. -/
theorem kSubsetResidueFrequencyPoint_injective
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus)) {k : ℕ} :
    Function.Injective
      (kSubsetResidueFrequencyPoint modulus :
        kSubsetResidueFrequencies modulus k → UnitAddCircle) := by
  intro a b hab
  apply extendKSubsetResidueFrequency_injective modulus
  apply productResidueFrequencyPoint_injective modulus hcoprime
  exact hab

/-- A circle frequency supported on `S` is annihilated by the product of
the moduli in `S`. -/
lemma prod_nsmul_productResidueFrequencyPoint_eq_zero_of_eq_zero_outside
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (S : Finset I) (a : residueVectors modulus)
    (ha : ∀ i, i ∉ S → a i = 0) :
    (∏ i ∈ S, modulus i) • productResidueFrequencyPoint a = 0 := by
  classical
  unfold productResidueFrequencyPoint
  rw [← Finset.sum_nsmul]
  apply Finset.sum_eq_zero
  intro i _hi
  by_cases hiS : i ∈ S
  · obtain ⟨c, hc⟩ :=
      Finset.dvd_prod_of_mem (fun j => modulus j) hiS
    change (∏ j ∈ S, modulus j) • ZMod.toAddCircle (a i) = 0
    rw [hc, mul_nsmul]
    have hzero : modulus i • ZMod.toAddCircle (a i) = 0 := by
      rw [← map_nsmul]
      simp
    rw [hzero, nsmul_zero]
  · rw [ha i hiS]
    simp

private lemma prod_union_le_mul_prod
    {I : Type*} [DecidableEq I] (f : I → ℕ)
    (hf : ∀ i, 1 ≤ f i) (S T : Finset I) :
    (∏ i ∈ S ∪ T, f i) ≤ (∏ i ∈ S, f i) * (∏ i ∈ T, f i) := by
  calc
    (∏ i ∈ S ∪ T, f i) =
        (∏ i ∈ S, f i) * (∏ i ∈ T \ S, f i) := by
      rw [← Finset.prod_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union]
    _ ≤ (∏ i ∈ S, f i) * (∏ i ∈ T, f i) := by
      have hsub : (∏ i ∈ T \ S, f i) ≤ ∏ i ∈ T, f i :=
        Finset.prod_le_prod_of_subset_of_one_le'
          (s := T \ S) (t := T) (f := f) Finset.sdiff_subset
          (fun i _hi _ => hf i)
      exact Nat.mul_le_mul_left _ hsub

/-- Frequencies belonging to possibly different `k`-subsets are
`1 / N`-separated whenever the product of the two subset moduli is at most
`N`.  This is the cross-subset spacing step in Tao's Corollary 2.8. -/
theorem one_div_le_dist_kSubsetResidueFrequencyPoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus)) {k N : ℕ}
    (hproduct : ∀ T U : fixedCardSubsets I k,
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N)
    {a b : kSubsetResidueFrequencies modulus k} (hab : a ≠ b) :
    (1 : ℝ) / N ≤
      dist (kSubsetResidueFrequencyPoint modulus a)
        (kSubsetResidueFrequencyPoint modulus b) := by
  classical
  let S : Finset I := a.1.1 ∪ b.1.1
  let Q : ℕ := ∏ i ∈ S, modulus i
  have hmodpos : ∀ i, 0 < modulus i :=
    fun i => Nat.pos_of_ne_zero (NeZero.ne (modulus i))
  have hQpos : 0 < Q := by
    unfold Q S
    exact Finset.prod_pos fun i _ => hmodpos i
  have hQle : Q ≤ N := by
    calc
      Q ≤ (∏ i ∈ a.1.1, modulus i) *
          (∏ i ∈ b.1.1, modulus i) := by
        exact prod_union_le_mul_prod modulus (fun i => hmodpos i)
          a.1.1 b.1.1
      _ ≤ N := hproduct a.1 b.1
  have hNpos : 0 < N := lt_of_lt_of_le hQpos hQle
  have haOutside : ∀ i, i ∉ S →
      extendKSubsetResidueFrequency modulus a i = 0 := by
    intro i hiS
    have hiA : i ∉ a.1.1 := fun hi => hiS (Finset.mem_union_left _ hi)
    simp [extendKSubsetResidueFrequency, hiA]
  have hbOutside : ∀ i, i ∉ S →
      extendKSubsetResidueFrequency modulus b i = 0 := by
    intro i hiS
    have hiB : i ∉ b.1.1 := fun hi => hiS (Finset.mem_union_right _ hi)
    simp [extendKSubsetResidueFrequency, hiB]
  have haZero : Q • kSubsetResidueFrequencyPoint modulus a = 0 := by
    exact prod_nsmul_productResidueFrequencyPoint_eq_zero_of_eq_zero_outside
      modulus S (extendKSubsetResidueFrequency modulus a) haOutside
  have hbZero : Q • kSubsetResidueFrequencyPoint modulus b = 0 := by
    exact prod_nsmul_productResidueFrequencyPoint_eq_zero_of_eq_zero_outside
      modulus S (extendKSubsetResidueFrequency modulus b) hbOutside
  have hdiffZero : Q • (kSubsetResidueFrequencyPoint modulus a -
      kSubsetResidueFrequencyPoint modulus b) = 0 := by
    rw [nsmul_sub, haZero, hbZero, sub_zero]
  have hfinite : IsOfFinAddOrder
      (kSubsetResidueFrequencyPoint modulus a -
        kSubsetResidueFrequencyPoint modulus b) :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨Q, hQpos, hdiffZero⟩
  have hdiff : kSubsetResidueFrequencyPoint modulus a -
      kSubsetResidueFrequencyPoint modulus b ≠ 0 :=
    sub_ne_zero.mpr ((kSubsetResidueFrequencyPoint_injective
      modulus hcoprime).ne hab)
  have horder : addOrderOf (kSubsetResidueFrequencyPoint modulus a -
      kSubsetResidueFrequencyPoint modulus b) ≤ Q :=
    addOrderOf_le_of_nsmul_eq_zero hQpos hdiffZero
  have hunit : (1 : ℝ) ≤
      (addOrderOf (kSubsetResidueFrequencyPoint modulus a -
        kSubsetResidueFrequencyPoint modulus b) : ℝ) *
        ‖kSubsetResidueFrequencyPoint modulus a -
          kSubsetResidueFrequencyPoint modulus b‖ := by
    simpa [nsmul_eq_mul] using
      AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder hfinite hdiff
  have hQdist : (1 : ℝ) / Q ≤
      dist (kSubsetResidueFrequencyPoint modulus a)
        (kSubsetResidueFrequencyPoint modulus b) := by
    have hQposReal : (0 : ℝ) < Q := by exact_mod_cast hQpos
    rw [dist_eq_norm, div_le_iff₀ hQposReal]
    calc
      (1 : ℝ) ≤
          (addOrderOf (kSubsetResidueFrequencyPoint modulus a -
            kSubsetResidueFrequencyPoint modulus b) : ℝ) *
            ‖kSubsetResidueFrequencyPoint modulus a -
              kSubsetResidueFrequencyPoint modulus b‖ := hunit
      _ ≤ (Q : ℝ) * ‖kSubsetResidueFrequencyPoint modulus a -
            kSubsetResidueFrequencyPoint modulus b‖ := by
        gcongr
      _ = ‖kSubsetResidueFrequencyPoint modulus a -
            kSubsetResidueFrequencyPoint modulus b‖ * Q := by ring
  have hQleReal : (Q : ℝ) ≤ N := by exact_mod_cast hQle
  exact (one_div_le_one_div_of_le (by exact_mod_cast hQpos) hQleReal).trans hQdist

open scoped Function in
/-- The fixed-family large-sieve consequence of Montgomery uncertainty on
a consecutive interval.  The large-sieve constant is exactly interval
length plus the product modulus. -/
theorem montgomery_uncertainty_Ioc_le_largeSieve
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (m0 N : ℕ) (g : ℕ → ℂ)
    (hg : ∀ n ∈ Finset.Ioc m0 (m0 + N),
      (∃ i, (n : ZMod (modulus i)) ∈ vanishing i) → g n = 0)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    (∏ i, ((vanishing i).card : ℝ) /
        ((modulus i - (vanishing i).card : ℕ) : ℝ)) *
        ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 ≤
      ((N : ℝ) + (∏ i, modulus i : ℕ)) *
        ∑ n ∈ Finset.Ioc m0 (m0 + N), ‖g n‖ ^ 2 := by
  classical
  let Q : ℕ := ∏ i, modulus i
  have hQpos : 0 < Q := by
    unfold Q
    exact Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (modulus i))
  let A := {a // a ∈
    (allNonzeroResidueFrequencies (modulus := modulus))}
  let point : A → UnitAddCircle := fun a =>
    productResidueFrequencyPoint a.1
  have hdelta : (0 : ℝ) < 1 / (Q : ℝ) := by positivity
  have hsep : ∀ r s : A, r ≠ s →
      (1 : ℝ) / (Q : ℝ) ≤ dist (point r) (point s) := by
    intro r s hrs
    apply one_div_prod_le_dist_productResidueFrequencyPoint
      modulus hcoprime
    exact Subtype.coe_injective.ne hrs
  have hlarge :=
    BoundedGaps.Maynard.sum_norm_sq_unitAddCircleAddChar_Ioc_le
      point hdelta hsep m0 N g
  have hinvDelta : ((1 : ℝ) / (Q : ℝ))⁻¹ = (Q : ℝ) := by
    have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQpos.ne'
    field_simp
  have huncertainty := montgomery_uncertainty_integer_sum
    vanishing (Finset.Ioc m0 (m0 + N)) g hg hnonempty hproper
  calc
    (∏ i, ((vanishing i).card : ℝ) /
        ((modulus i - (vanishing i).card : ℕ) : ℝ)) *
        ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 ≤
        ∑ a ∈ allNonzeroResidueFrequencies,
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            productResidueAddChar a (residueVectorOfNat modulus n)‖ ^ 2 :=
      huncertainty
    _ = ∑ a : A,
        ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
          BoundedGaps.Maynard.unitAddCircleAddChar (n • point a)‖ ^ 2 := by
      change
        (∑ a ∈ allNonzeroResidueFrequencies,
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            productResidueAddChar a (residueVectorOfNat modulus n)‖ ^ 2) =
        ∑ a : {a // a ∈ allNonzeroResidueFrequencies},
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            BoundedGaps.Maynard.unitAddCircleAddChar
              (n • productResidueFrequencyPoint a.1)‖ ^ 2
      calc
        _ = ∑ a : {a // a ∈ allNonzeroResidueFrequencies},
            ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
              productResidueAddChar a.1
                (residueVectorOfNat modulus n)‖ ^ 2 := by
          symm
          exact Finset.sum_coe_sort
            (allNonzeroResidueFrequencies (modulus := modulus))
            (fun a : residueVectors modulus =>
              ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                productResidueAddChar a
                  (residueVectorOfNat modulus n)‖ ^ 2)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a _ha
          apply congrArg fun z : ℂ => ‖z‖ ^ 2
          apply Finset.sum_congr rfl
          intro n _hn
          rw [productResidueAddChar_residueVectorOfNat]
    _ ≤ ((N : ℝ) + (Q : ℝ)) *
        ∑ n ∈ Finset.Ioc m0 (m0 + N), ‖g n‖ ^ 2 := by
      simpa only [hinvDelta] using hlarge
    _ = ((N : ℝ) + (∏ i, modulus i : ℕ)) *
        ∑ n ∈ Finset.Ioc m0 (m0 + N), ‖g n‖ ^ 2 := by rfl

/-! ## The powerset aggregation in Tao's Corollary 2.8 -/

/-- The positive ratio contributed by one modulus to Montgomery's
uncertainty lower bound. -/
noncomputable def residueRemovalRatio
    {I : Type*} (modulus : I → ℕ)
    (vanishing : ∀ i, Finset (ZMod (modulus i))) (i : I) : ℝ :=
  ((vanishing i).card : ℝ) /
    ((modulus i - (vanishing i).card : ℕ) : ℝ)

/-- Sum Montgomery uncertainty over all `k`-element subsets and apply one
large-sieve inequality to the resulting cross-subset frequency family.
The hypothesis on products is the square-root cutoff in Corollary 2.8,
written without a natural-number square root. -/
theorem montgomery_uncertainty_powerset_Ioc_le_largeSieve
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (k m0 N : ℕ) (hsubsets : Nonempty (fixedCardSubsets I k))
    (hproduct : ∀ T U : fixedCardSubsets I k,
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N)
    (g : ℕ → ℂ)
    (hg : ∀ n ∈ Finset.Ioc m0 (m0 + N),
      (∃ i, (n : ZMod (modulus i)) ∈ vanishing i) → g n = 0)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    (∑ T : fixedCardSubsets I k,
        ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
        ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 ≤
      ((N : ℝ) + N) *
        ∑ n ∈ Finset.Ioc m0 (m0 + N), ‖g n‖ ^ 2 := by
  classical
  let A := kSubsetResidueFrequencies modulus k
  let point : A → UnitAddCircle :=
    kSubsetResidueFrequencyPoint modulus
  let T₀ : fixedCardSubsets I k := Classical.choice hsubsets
  have hT₀pos : 0 < ∏ i ∈ T₀.1, modulus i :=
    Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (modulus i))
  have hNpos : 0 < N :=
    lt_of_lt_of_le (Nat.mul_pos hT₀pos hT₀pos) (hproduct T₀ T₀)
  have hdelta : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hsep : ∀ r s : A, r ≠ s →
      (1 : ℝ) / N ≤ dist (point r) (point s) := by
    intro r s hrs
    exact one_div_le_dist_kSubsetResidueFrequencyPoint
      modulus hcoprime hproduct hrs
  have huncertainty (T : fixedCardSubsets I k) :
      (∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 ≤
        ∑ a : {a : residueVectors
            (fun i : {i // i ∈ T.1} => modulus i.1) //
            a ∈ allNonzeroResidueFrequencies},
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            BoundedGaps.Maynard.unitAddCircleAddChar
              (n • point ⟨T, a⟩)‖ ^ 2 := by
    have hlocal := montgomery_uncertainty_integer_sum
      (modulus := fun i : {i // i ∈ T.1} => modulus i.1)
      (fun i => vanishing i.1) (Finset.Ioc m0 (m0 + N)) g
      (by
        intro n hn hremoved
        obtain ⟨i, hi⟩ := hremoved
        exact hg n hn ⟨i.1, hi⟩)
      (fun i => hnonempty i.1) (fun i => hproper i.1)
    calc
      (∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 =
          (∏ i : {i // i ∈ T.1},
            residueRemovalRatio modulus vanishing i.1) *
            ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 := by
        rw [Finset.prod_coe_sort]
      _ ≤ ∑ a ∈ allNonzeroResidueFrequencies,
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            productResidueAddChar a
              (residueVectorOfNat
                (fun i : {i // i ∈ T.1} => modulus i.1) n)‖ ^ 2 := by
        simpa only [residueRemovalRatio] using hlocal
      _ = ∑ a : {a : residueVectors
            (fun i : {i // i ∈ T.1} => modulus i.1) //
            a ∈ allNonzeroResidueFrequencies},
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            BoundedGaps.Maynard.unitAddCircleAddChar
              (n • point ⟨T, a⟩)‖ ^ 2 := by
        simp_rw [point,
          productResidueFrequencyPoint_extendKSubsetResidueFrequency]
        calc
          (∑ a ∈ allNonzeroResidueFrequencies,
              ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                productResidueAddChar a
                  (residueVectorOfNat
                    (fun i : {i // i ∈ T.1} => modulus i.1) n)‖ ^ 2) =
              ∑ a ∈ allNonzeroResidueFrequencies,
                ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                  BoundedGaps.Maynard.unitAddCircleAddChar
                    (n • productResidueFrequencyPoint a)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply congrArg fun z : ℂ => ‖z‖ ^ 2
            apply Finset.sum_congr rfl
            intro n _hn
            rw [productResidueAddChar_residueVectorOfNat]
          _ = ∑ a : {a : residueVectors
                (fun i : {i // i ∈ T.1} => modulus i.1) //
                a ∈ allNonzeroResidueFrequencies},
              ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                BoundedGaps.Maynard.unitAddCircleAddChar
                  (n • productResidueFrequencyPoint a.1)‖ ^ 2 := by
            symm
            exact Finset.sum_coe_sort
              (allNonzeroResidueFrequencies
                (modulus := fun i : {i // i ∈ T.1} => modulus i.1))
              (fun a : residueVectors
                  (fun i : {i // i ∈ T.1} => modulus i.1) =>
                ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                  BoundedGaps.Maynard.unitAddCircleAddChar
                    (n • productResidueFrequencyPoint a)‖ ^ 2)
  have hsumUncertainty :
      (∑ T : fixedCardSubsets I k,
          ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 ≤
        ∑ a : A,
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            BoundedGaps.Maynard.unitAddCircleAddChar (n • point a)‖ ^ 2 := by
    rw [Finset.sum_mul]
    calc
      (∑ T : fixedCardSubsets I k,
          (∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
            ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2) ≤
          ∑ T : fixedCardSubsets I k,
            ∑ a : {a : residueVectors
                (fun i : {i // i ∈ T.1} => modulus i.1) //
                a ∈ allNonzeroResidueFrequencies},
              ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                BoundedGaps.Maynard.unitAddCircleAddChar
                  (n • point ⟨T, a⟩)‖ ^ 2 := by
        exact Finset.sum_le_sum fun T _hT => huncertainty T
      _ = ∑ a : A,
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            BoundedGaps.Maynard.unitAddCircleAddChar (n • point a)‖ ^ 2 := by
        rw [Fintype.sum_sigma]
  have hlarge :=
    BoundedGaps.Maynard.sum_norm_sq_unitAddCircleAddChar_Ioc_le
      point hdelta hsep m0 N g
  have hinvDelta : ((1 : ℝ) / (N : ℝ))⁻¹ = (N : ℝ) := by
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
    field_simp
  exact hsumUncertainty.trans (by
    simpa only [hinvDelta] using hlarge)

/-! ## A concrete finite residue-class sieve bound -/

/-- The integers in a consecutive interval avoiding every specified set
of residue classes. -/
noncomputable def residueClassSurvivors
    {I : Type*} [Fintype I] [DecidableEq I]
    {modulus : I → ℕ} [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (m0 N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc m0 (m0 + N)).filter fun n =>
    ∀ i, (n : ZMod (modulus i)) ∉ vanishing i

/-- The direct fixed-family residue-class sieve inequality, before
cancelling the number of survivors. -/
theorem residueClassSurvivors_ratio_mul_sq_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (m0 N : ℕ)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    (∏ i, ((vanishing i).card : ℝ) /
        ((modulus i - (vanishing i).card : ℕ) : ℝ)) *
        (residueClassSurvivors vanishing m0 N).card ^ 2 ≤
      ((N : ℝ) + (∏ i, modulus i : ℕ)) *
        (residueClassSurvivors vanishing m0 N).card := by
  classical
  let E := residueClassSurvivors vanishing m0 N
  let g : ℕ → ℂ := fun n => if n ∈ E then 1 else 0
  have hg : ∀ n ∈ Finset.Ioc m0 (m0 + N),
      (∃ i, (n : ZMod (modulus i)) ∈ vanishing i) → g n = 0 := by
    intro n hn hremoved
    have hnE : n ∉ E := by
      intro hnE
      have havoid := (Finset.mem_filter.mp hnE).2
      obtain ⟨i, hi⟩ := hremoved
      exact havoid i hi
    simp [g, hnE]
  have hlarge := montgomery_uncertainty_Ioc_le_largeSieve
    modulus hcoprime vanishing m0 N g hg hnonempty hproper
  have hEsubset : E ⊆ Finset.Ioc m0 (m0 + N) := by
    intro n hn
    have hn' := hn
    simp only [E, residueClassSurvivors, Finset.mem_filter] at hn'
    exact hn'.1
  have hfilter :
      (Finset.Ioc m0 (m0 + N)).filter (fun n => n ∈ E) = E := by
    ext n
    constructor
    · intro hn
      exact (Finset.mem_filter.mp hn).2
    · intro hn
      exact Finset.mem_filter.mpr ⟨hEsubset hn, hn⟩
  have hsum : (∑ n ∈ Finset.Ioc m0 (m0 + N), g n) = (E.card : ℂ) := by
    change (∑ n ∈ Finset.Ioc m0 (m0 + N),
      if n ∈ E then (1 : ℂ) else 0) = (E.card : ℂ)
    rw [Finset.sum_boole, hfilter]
  have hnorm (n : ℕ) :
      ‖g n‖ ^ 2 = if n ∈ E then (1 : ℝ) else 0 := by
    by_cases hn : n ∈ E <;> simp [g, hn]
  have henergy :
      (∑ n ∈ Finset.Ioc m0 (m0 + N), ‖g n‖ ^ 2) = (E.card : ℝ) := by
    simp_rw [hnorm]
    rw [Finset.sum_boole, hfilter]
  rw [hsum, henergy] at hlarge
  simpa only [E, Complex.norm_natCast] using hlarge

/-- The fixed-family sieve bound after cancellation. -/
theorem residueClassSurvivors_card_le_div_ratio
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (m0 N : ℕ)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    ((residueClassSurvivors vanishing m0 N).card : ℝ) ≤
      ((N : ℝ) + (∏ i, modulus i : ℕ)) /
        (∏ i, ((vanishing i).card : ℝ) /
          ((modulus i - (vanishing i).card : ℕ) : ℝ)) := by
  classical
  let R : ℝ := ∏ i, ((vanishing i).card : ℝ) /
    ((modulus i - (vanishing i).card : ℕ) : ℝ)
  let C : ℝ := (N : ℝ) + (∏ i, modulus i : ℕ)
  let M : ℝ := (residueClassSurvivors vanishing m0 N).card
  have hRpos : 0 < R := by
    unfold R
    apply Finset.prod_pos
    intro i _hi
    exact div_pos
      (by exact_mod_cast Finset.card_pos.mpr (hnonempty i))
      (by exact_mod_cast Nat.sub_pos_of_lt (hproper i))
  change M ≤ C / R
  by_cases hMzero : M = 0
  · rw [hMzero]
    positivity
  · have hMpos : 0 < M := lt_of_le_of_ne (by positivity) (Ne.symm hMzero)
    have hraw := residueClassSurvivors_ratio_mul_sq_le
      modulus hcoprime vanishing m0 N hnonempty hproper
    have hcancel : R * M ≤ C := by
      apply le_of_mul_le_mul_right _ hMpos
      simpa only [R, C, M, pow_two, mul_assoc] using hraw
    exact (le_div_iff₀ hRpos).2 (by simpa only [mul_comm] using hcancel)

/-- Corollary 2.8 specialized to the indicator of the integers surviving
all prescribed residue-class deletions. -/
theorem residueClassSurvivors_powerset_ratio_mul_sq_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (k m0 N : ℕ) (hsubsets : Nonempty (fixedCardSubsets I k))
    (hproduct : ∀ T U : fixedCardSubsets I k,
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    (∑ T : fixedCardSubsets I k,
        ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
        (residueClassSurvivors vanishing m0 N).card ^ 2 ≤
      ((N : ℝ) + N) *
        (residueClassSurvivors vanishing m0 N).card := by
  classical
  let E := residueClassSurvivors vanishing m0 N
  let g : ℕ → ℂ := fun n => if n ∈ E then 1 else 0
  have hg : ∀ n ∈ Finset.Ioc m0 (m0 + N),
      (∃ i, (n : ZMod (modulus i)) ∈ vanishing i) → g n = 0 := by
    intro n _hn hremoved
    have hnE : n ∉ E := by
      intro hnE
      have havoid := (Finset.mem_filter.mp hnE).2
      obtain ⟨i, hi⟩ := hremoved
      exact havoid i hi
    simp [g, hnE]
  have hlarge := montgomery_uncertainty_powerset_Ioc_le_largeSieve
    modulus hcoprime vanishing k m0 N hsubsets hproduct g hg
      hnonempty hproper
  have hEsubset : E ⊆ Finset.Ioc m0 (m0 + N) := by
    intro n hn
    have hn' := hn
    simp only [E, residueClassSurvivors, Finset.mem_filter] at hn'
    exact hn'.1
  have hfilter :
      (Finset.Ioc m0 (m0 + N)).filter (fun n => n ∈ E) = E := by
    ext n
    constructor
    · intro hn
      exact (Finset.mem_filter.mp hn).2
    · intro hn
      exact Finset.mem_filter.mpr ⟨hEsubset hn, hn⟩
  have hsum : (∑ n ∈ Finset.Ioc m0 (m0 + N), g n) = (E.card : ℂ) := by
    change (∑ n ∈ Finset.Ioc m0 (m0 + N),
      if n ∈ E then (1 : ℂ) else 0) = (E.card : ℂ)
    rw [Finset.sum_boole, hfilter]
  have hnorm (n : ℕ) :
      ‖g n‖ ^ 2 = if n ∈ E then (1 : ℝ) else 0 := by
    by_cases hn : n ∈ E <;> simp [g, hn]
  have henergy :
      (∑ n ∈ Finset.Ioc m0 (m0 + N), ‖g n‖ ^ 2) = (E.card : ℝ) := by
    simp_rw [hnorm]
    rw [Finset.sum_boole, hfilter]
  rw [hsum, henergy] at hlarge
  simpa only [E, Complex.norm_natCast] using hlarge

/-- The cardinality form of Corollary 2.8, after cancelling one factor of
the survivor count. -/
theorem residueClassSurvivors_card_le_powerset_ratio
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (k m0 N : ℕ) (hsubsets : Nonempty (fixedCardSubsets I k))
    (hproduct : ∀ T U : fixedCardSubsets I k,
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    ((residueClassSurvivors vanishing m0 N).card : ℝ) ≤
      ((N : ℝ) + N) /
        (∑ T : fixedCardSubsets I k,
          ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) := by
  classical
  let R : ℝ := ∑ T : fixedCardSubsets I k,
    ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i
  let C : ℝ := (N : ℝ) + N
  let M : ℝ := (residueClassSurvivors vanishing m0 N).card
  have hratioPos (i : I) : 0 < residueRemovalRatio modulus vanishing i := by
    unfold residueRemovalRatio
    exact div_pos
      (by exact_mod_cast Finset.card_pos.mpr (hnonempty i))
      (by exact_mod_cast Nat.sub_pos_of_lt (hproper i))
  let T₀ : fixedCardSubsets I k := Classical.choice hsubsets
  have hRpos : 0 < R := by
    unfold R
    apply Finset.sum_pos
    · intro T _hT
      exact Finset.prod_pos fun i _ => hratioPos i
    · exact ⟨T₀, Finset.mem_univ _⟩
  change M ≤ C / R
  by_cases hMzero : M = 0
  · rw [hMzero]
    positivity
  · have hMpos : 0 < M := lt_of_le_of_ne (by positivity) (Ne.symm hMzero)
    have hraw := residueClassSurvivors_powerset_ratio_mul_sq_le
      modulus hcoprime vanishing k m0 N hsubsets hproduct
        hnonempty hproper
    have hcancel : R * M ≤ C := by
      apply le_of_mul_le_mul_right _ hMpos
      simpa only [R, C, M, pow_two, mul_assoc] using hraw
    exact (le_div_iff₀ hRpos).2 (by simpa only [mul_comm] using hcancel)

/-! ## A finite elementary-symmetric lower bound -/

/-- If every ordered `k`-tuple drawn from `J` can be enlarged to a
`k`-element subset whose squarefree weight dominates the tuple weight,
then the `k`th power of the mass of `J` is at most `k^k` times the `k`th
elementary symmetric sum.  This separates the bookkeeping part of Tao's
trimmed elementary-symmetric argument from the construction of the
enlarging subset. -/
theorem sum_pow_le_pow_mul_powersetCard_prod_of_tuple_extension
    {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ℝ) (J : Finset I) (k : ℕ)
    (hw : ∀ i, 0 ≤ w i)
    (hextend : ∀ p ∈ Fintype.piFinset (fun _ : Fin k => J),
      ∃ U ∈ (Finset.univ : Finset I).powersetCard k,
        (∀ j, p j ∈ U) ∧ (∏ j, w (p j)) ≤ ∏ i ∈ U, w i) :
    (∑ i ∈ J, w i) ^ k ≤
      (k : ℝ) ^ k *
        ∑ U ∈ (Finset.univ : Finset I).powersetCard k,
          ∏ i ∈ U, w i := by
  classical
  let P := Fintype.piFinset (fun _ : Fin k => J)
  let K := (Finset.univ : Finset I).powersetCard k
  rw [Finset.sum_pow']
  calc
    (∑ p ∈ P, ∏ j, w (p j)) ≤
        ∑ p ∈ P, ∑ U ∈ K,
          if ∀ j, p j ∈ U then ∏ i ∈ U, w i else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨U, hUK, hpU, hpWeight⟩ := hextend p (by simpa [P] using hp)
      calc
        (∏ j, w (p j)) ≤ ∏ i ∈ U, w i := hpWeight
        _ = if ∀ j, p j ∈ U then ∏ i ∈ U, w i else 0 := by
          simp [hpU]
        _ ≤ ∑ V ∈ K,
            if ∀ j, p j ∈ V then ∏ i ∈ V, w i else 0 := by
          exact Finset.single_le_sum
            (s := K)
            (f := fun V =>
              if ∀ j, p j ∈ V then (∏ i ∈ V, w i) else (0 : ℝ))
            (fun V _hV => by
              by_cases hpV : ∀ j, p j ∈ V
              · simp [hpV, Finset.prod_nonneg fun i _ => hw i]
              · simp [hpV])
            (by simpa [K] using hUK)
    _ = ∑ U ∈ K, ∑ p ∈ P,
          if ∀ j, p j ∈ U then ∏ i ∈ U, w i else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ U ∈ K, (k : ℝ) ^ k * ∏ i ∈ U, w i := by
      apply Finset.sum_le_sum
      intro U hUK
      have hUcard : U.card = k := by simpa [K] using hUK
      let good := P.filter fun p => ∀ j, p j ∈ U
      have hgoodSubset : good ⊆ Fintype.piFinset (fun _ : Fin k => U) := by
        intro p hp
        have hpU : ∀ j, p j ∈ U := (Finset.mem_filter.mp hp).2
        exact Fintype.mem_piFinset.mpr hpU
      have hgoodCard : good.card ≤ k ^ k := by
        calc
          good.card ≤ (Fintype.piFinset (fun _ : Fin k => U)).card :=
            Finset.card_le_card hgoodSubset
          _ = U.card ^ k := Fintype.card_piFinset_const U k
          _ = k ^ k := by rw [hUcard]
      calc
        (∑ p ∈ P,
            if ∀ j, p j ∈ U then ∏ i ∈ U, w i else 0) =
            (good.card : ℝ) * ∏ i ∈ U, w i := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
            Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((k ^ k : ℕ) : ℝ) * ∏ i ∈ U, w i := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hgoodCard)
            (Finset.prod_nonneg fun i _ => hw i)
        _ = (k : ℝ) ^ k * ∏ i ∈ U, w i := by
          norm_num
    _ = (k : ℝ) ^ k *
        ∑ U ∈ K, ∏ i ∈ U, w i := by
      rw [Finset.mul_sum]

/-- Tao's trimmed elementary-symmetric lower bound.  The finset `L`
contains `k` largest weights: every weight outside `L` is at most every
weight in `L`.  Removing `L`, taking the `k`th power of the remaining
mass, and dividing by `k^k` is bounded by the `k`th elementary symmetric
sum of all weights. -/
theorem trimmed_sum_div_pow_le_powersetCard_prod
    {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ℝ) (L : Finset I) (k : ℕ)
    (hk : 0 < k) (hLcard : L.card = k)
    (hw : ∀ i, 0 ≤ w i)
    (hlargest : ∀ i ∈ (Finset.univ : Finset I) \ L,
      ∀ l ∈ L, w i ≤ w l) :
    ((∑ i ∈ (Finset.univ : Finset I) \ L, w i) / k) ^ k ≤
      ∑ U ∈ (Finset.univ : Finset I).powersetCard k,
        ∏ i ∈ U, w i := by
  classical
  let J : Finset I := (Finset.univ : Finset I) \ L
  have hextend : ∀ p ∈ Fintype.piFinset (fun _ : Fin k => J),
      ∃ U ∈ (Finset.univ : Finset I).powersetCard k,
        (∀ j, p j ∈ U) ∧ (∏ j, w (p j)) ≤ ∏ i ∈ U, w i := by
    intro p hp
    have hpJ : ∀ j, p j ∈ J := Fintype.mem_piFinset.mp hp
    let R : Finset I := Finset.univ.image p
    have hRsubset : R ⊆ J := by
      intro i hi
      obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hi
      exact hpJ j
    have hRcard : R.card ≤ k := by
      calc
        R.card ≤ (Finset.univ : Finset (Fin k)).card :=
          Finset.card_image_le
        _ = k := by simp
    obtain ⟨F, hFsub, hFcard⟩ :=
      Finset.exists_subset_card_eq (s := L) (n := k - R.card) (by
        rw [hLcard]
        exact Nat.sub_le _ _)
    have hRF : Disjoint R F := by
      rw [Finset.disjoint_left]
      intro i hiR hiF
      have hiJ := hRsubset hiR
      have hiL := hFsub hiF
      have hiNotL : i ∉ L := by simpa [J] using hiJ
      exact hiNotL hiL
    let U : Finset I := R ∪ F
    have hUcard : U.card = k := by
      unfold U
      rw [Finset.card_union_of_disjoint hRF, hFcard,
        Nat.add_sub_of_le hRcard]
    have hUK : U ∈ (Finset.univ : Finset I).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hUcard⟩
    have hpU : ∀ j, p j ∈ U := by
      intro j
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    let rep : {i // i ∈ R} → Fin k := fun i =>
      Classical.choose (Finset.mem_image.mp i.2)
    have hrep (i : {i // i ∈ R}) : p (rep i) = i.1 := by
      exact (Classical.choose_spec (Finset.mem_image.mp i.2)).2
    have hrepInj : Function.Injective rep := by
      intro i j hij
      apply Subtype.ext
      rw [← hrep i, ← hrep j, hij]
    let A : Finset (Fin k) := Finset.univ.image rep
    have hAcard : A.card = R.card := by
      unfold A
      rw [Finset.card_image_of_injective _ hrepInj]
      simp
    let D : Finset (Fin k) := Finset.univ \ A
    have hDcard : D.card = k - R.card := by
      unfold D
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hAcard]
      simp
    have hDFcard : D.card = F.card := by rw [hDcard, hFcard]
    let e : D ≃ F := Finset.equivOfCardEq hDFcard
    have hprodD : (∏ j ∈ D, w (p j)) ≤ ∏ f ∈ F, w f := by
      rw [← Finset.prod_coe_sort D (fun j => w (p j)),
        ← Finset.prod_coe_sort F w]
      calc
        (∏ j : D, w (p j.1)) ≤ ∏ j : D, w (e j).1 := by
          apply Finset.prod_le_prod
          · intro j _hj
            exact hw (p j.1)
          · intro j _hj
            exact hlargest (p j.1) (by simpa [J] using hpJ j.1)
              (e j).1 (hFsub (e j).2)
        _ = ∏ f : F, w f.1 := e.prod_comp (fun f : F => w f.1)
    have hprodA : (∏ j ∈ A, w (p j)) = ∏ i ∈ R, w i := by
      unfold A
      rw [Finset.prod_image]
      · rw [← Finset.prod_coe_sort R w]
        apply Finset.prod_congr rfl
        intro i _hi
        rw [hrep]
      · intro i _hi j _hj hij
        exact hrepInj hij
    have htupleSplit : (∏ j, w (p j)) =
        (∏ j ∈ A, w (p j)) * ∏ j ∈ D, w (p j) := by
      unfold D
      calc
        (∏ j, w (p j)) =
            ∏ j ∈ A ∪ (Finset.univ \ A), w (p j) := by
          rw [Finset.union_sdiff_of_subset (Finset.subset_univ A)]
        _ = (∏ j ∈ A, w (p j)) *
            ∏ j ∈ Finset.univ \ A, w (p j) :=
          Finset.prod_union Finset.disjoint_sdiff
    have hUSplit : (∏ i ∈ U, w i) =
        (∏ i ∈ R, w i) * ∏ i ∈ F, w i := by
      unfold U
      exact Finset.prod_union hRF
    refine ⟨U, hUK, hpU, ?_⟩
    rw [htupleSplit, hprodA, hUSplit]
    exact mul_le_mul_of_nonneg_left hprodD
      (Finset.prod_nonneg fun i _ => hw i)
  have hcore := sum_pow_le_pow_mul_powersetCard_prod_of_tuple_extension
    w J k hw hextend
  have hkpow : 0 < (k : ℝ) ^ k := by positivity
  rw [div_pow, div_le_iff₀ hkpow]
  simpa only [J, mul_comm] using hcore

/-- The normalized proportion of residue classes removed modulo one
modulus. -/
noncomputable def residueRemovedFraction
    {I : Type*} (modulus : I → ℕ)
    (vanishing : ∀ i, Finset (ZMod (modulus i))) (i : I) : ℝ :=
  ((vanishing i).card : ℝ) / (modulus i : ℝ)

lemma residueRemovedFraction_le_residueRemovalRatio
    {I : Type*} (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (hproper : ∀ i, (vanishing i).card < modulus i) (i : I) :
    residueRemovedFraction modulus vanishing i ≤
      residueRemovalRatio modulus vanishing i := by
  unfold residueRemovedFraction residueRemovalRatio
  exact div_le_div_of_nonneg_left (by positivity)
    (by exact_mod_cast Nat.sub_pos_of_lt (hproper i))
    (by exact_mod_cast Nat.sub_le (modulus i) (vanishing i).card)

/-- Tao's simplified larger sieve (Corollary 2.9) for a consecutive
integer interval.  The finset `L` consists of the `k` largest normalized
removal proportions, so the displayed denominator is exactly the sum with
the `k` largest summands discarded. -/
theorem residueClassSurvivors_card_le_trimmed_largerSieve
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (k m0 N : ℕ) (hk : 0 < k)
    (hsubsets : Nonempty (fixedCardSubsets I k))
    (hproduct : ∀ T U : fixedCardSubsets I k,
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i)
    (L : Finset I) (hLcard : L.card = k)
    (htrimNonempty : ((Finset.univ : Finset I) \ L).Nonempty)
    (hlargest : ∀ i ∈ (Finset.univ : Finset I) \ L,
      ∀ l ∈ L,
        residueRemovedFraction modulus vanishing i ≤
          residueRemovedFraction modulus vanishing l) :
    ((residueClassSurvivors vanishing m0 N).card : ℝ) ≤
      ((N : ℝ) + N) /
        (((∑ i ∈ (Finset.univ : Finset I) \ L,
            residueRemovedFraction modulus vanishing i) / k) ^ k) := by
  classical
  let w : I → ℝ := residueRemovedFraction modulus vanishing
  let r : I → ℝ := residueRemovalRatio modulus vanishing
  let D : ℝ := ((∑ i ∈ (Finset.univ : Finset I) \ L, w i) / k) ^ k
  let E₀ : ℝ := ∑ U ∈ (Finset.univ : Finset I).powersetCard k,
    ∏ i ∈ U, w i
  let E₁ : ℝ := ∑ U ∈ (Finset.univ : Finset I).powersetCard k,
    ∏ i ∈ U, r i
  let R : ℝ := ∑ T : fixedCardSubsets I k, ∏ i ∈ T.1, r i
  have hwpos (i : I) : 0 < w i := by
    unfold w residueRemovedFraction
    exact div_pos
      (by exact_mod_cast Finset.card_pos.mpr (hnonempty i))
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (modulus i)))
  have hwr (i : I) : w i ≤ r i := by
    exact residueRemovedFraction_le_residueRemovalRatio
      modulus vanishing hproper i
  have hDleE₀ : D ≤ E₀ := by
    exact trimmed_sum_div_pow_le_powersetCard_prod w L k hk hLcard
      (fun i => (hwpos i).le) (by simpa [w] using hlargest)
  have hE₀leE₁ : E₀ ≤ E₁ := by
    unfold E₀ E₁
    apply Finset.sum_le_sum
    intro U _hU
    exact Finset.prod_le_prod (fun i _hi => (hwpos i).le)
      (fun i _hi => hwr i)
  have hE₁eqR : E₁ = R := by
    unfold E₁ R
    exact Finset.sum_subtype
      (p := fun U : Finset I => U.card = k)
      ((Finset.univ : Finset I).powersetCard k)
      (fun U => by simp) (fun U => ∏ i ∈ U, r i)
  have hDleR : D ≤ R := hDleE₀.trans (hE₀leE₁.trans_eq hE₁eqR)
  have hsumPos : 0 < ∑ i ∈ (Finset.univ : Finset I) \ L, w i :=
    Finset.sum_pos (fun i _hi => hwpos i) htrimNonempty
  have hDpos : 0 < D := by
    unfold D
    exact pow_pos (div_pos hsumPos (by exact_mod_cast hk)) _
  have hcard := residueClassSurvivors_card_le_powerset_ratio
    modulus hcoprime vanishing k m0 N hsubsets hproduct
      hnonempty hproper
  change ((residueClassSurvivors vanishing m0 N).card : ℝ) ≤
    ((N : ℝ) + N) / D
  exact hcard.trans (div_le_div_of_nonneg_left (by positivity) hDpos hDleR)

/-! ## Prime-divisor specialization -/

/-- Integers in a consecutive interval having no divisor in the prescribed
finite set of primes. -/
def primeDivisibilitySurvivors (Q : Finset ℕ) (m0 N : ℕ) : Finset ℕ :=
  (Finset.Ioc m0 (m0 + N)).filter fun n => ∀ q ∈ Q, ¬q ∣ n

lemma residueClassSurvivors_zero_eq_primeDivisibilitySurvivors
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime) (m0 N : ℕ) :
    letI : ∀ q : Q, NeZero q.1 := fun q => ⟨(hprime q.1 q.2).ne_zero⟩
    residueClassSurvivors (modulus := fun q : Q => q.1)
        (fun _q => {(0 : ZMod _ )}) m0 N =
      primeDivisibilitySurvivors Q m0 N := by
  classical
  letI : ∀ q : Q, NeZero q.1 := fun q => ⟨(hprime q.1 q.2).ne_zero⟩
  ext n
  simp only [residueClassSurvivors, primeDivisibilitySurvivors,
    Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨hn, havoid⟩
    refine ⟨hn, ?_⟩
    intro q hq hdiv
    exact havoid ⟨q, hq⟩ ((ZMod.natCast_eq_zero_iff n q).mpr hdiv)
  · rintro ⟨hn, havoid⟩
    refine ⟨hn, ?_⟩
    intro q hzero
    exact havoid q.1 q.2 ((ZMod.natCast_eq_zero_iff n q.1).mp hzero)

/-- Simplified larger sieve for integers avoiding divisibility by every
prime in `Q`.  Here the removal proportions are the reciprocals `1/q`, so
the denominator is ready for Mertens estimates in the smooth-run argument. -/
theorem primeDivisibilitySurvivors_card_le_trimmed_largerSieve
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (k m0 N : ℕ) (hk : 0 < k)
    (hsubsets : Nonempty (fixedCardSubsets Q k))
    (hproduct : ∀ T U : fixedCardSubsets Q k,
      (∏ q ∈ T.1, q.1) * (∏ q ∈ U.1, q.1) ≤ N)
    (L : Finset Q) (hLcard : L.card = k)
    (htrimNonempty : ((Finset.univ : Finset Q) \ L).Nonempty)
    (hlargest : ∀ q ∈ (Finset.univ : Finset Q) \ L,
      ∀ r ∈ L, (1 : ℝ) / q.1 ≤ (1 : ℝ) / r.1) :
    ((primeDivisibilitySurvivors Q m0 N).card : ℝ) ≤
      ((N : ℝ) + N) /
        (((∑ q ∈ (Finset.univ : Finset Q) \ L,
            (1 : ℝ) / q.1) / k) ^ k) := by
  classical
  letI : ∀ q : Q, NeZero q.1 := fun q => ⟨(hprime q.1 q.2).ne_zero⟩
  have hcoprime : Pairwise (Nat.Coprime on fun q : Q => q.1) := by
    intro q r hqr
    exact (Nat.coprime_primes (hprime q.1 q.2) (hprime r.1 r.2)).mpr
      (Subtype.coe_ne_coe.mpr hqr)
  have hbound := residueClassSurvivors_card_le_trimmed_largerSieve
    (fun q : Q => q.1) hcoprime (fun _q => {(0 : ZMod _)})
      k m0 N hk hsubsets hproduct
      (fun _q => by simp)
      (fun q => by simpa using (hprime q.1 q.2).one_lt)
      L hLcard htrimNonempty (by
        intro q hq r hr
        simpa [residueRemovedFraction] using hlargest q hq r hr)
  rw [residueClassSurvivors_zero_eq_primeDivisibilitySurvivors
    Q hprime m0 N] at hbound
  simpa [residueRemovedFraction] using hbound

/-- Montgomery's uncertainty principle for one modulus.  This is the
`k = 1` case of Tao's Lemma 2.7, stated for a function already collected
by residue class. -/
theorem montgomery_uncertainty_single
    {q : ℕ} [NeZero q] (vanishing : Finset (ZMod q))
    (f : ZMod q → ℂ)
    (hvanish : ∀ x ∈ vanishing, f x = 0)
    (hproper : vanishing.card < q) :
    ((vanishing.card : ℝ) / (q - vanishing.card : ℕ)) *
        ‖∑ x : ZMod q, f x‖ ^ 2 ≤
      ∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
        ‖ZMod.dft f a‖ ^ 2 := by
  classical
  let T := survivingResidues vanishing
  let A : ℝ := ∑ x : ZMod q, ‖f x‖ ^ 2
  let F : ℝ := ‖∑ x : ZMod q, f x‖ ^ 2
  have hcardT : T.card = q - vanishing.card :=
    card_survivingResidues vanishing
  have htposNat : 0 < q - vanishing.card := Nat.sub_pos_of_lt hproper
  have htpos : (0 : ℝ) < (q - vanishing.card : ℕ) := by
    exact_mod_cast htposNat
  have henergy : F ≤ (q - vanishing.card : ℕ) * A := by
    have hcs := norm_sum_sq_le_card_mul_sum_norm_sq T f
    rw [← sum_eq_sum_survivingResidues_of_eq_zero vanishing f hvanish,
      ← sum_norm_sq_eq_sum_survivingResidues_of_eq_zero vanishing f hvanish,
      hcardT] at hcs
    exact hcs
  have hparseval := BoundedGaps.Maynard.sum_norm_sq_dft f
  have hzero : ZMod.dft f 0 = ∑ x : ZMod q, f x := ZMod.dft_apply_zero f
  have hsplit :
      (∑ a : ZMod q, ‖ZMod.dft f a‖ ^ 2) =
        F + ∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
          ‖ZMod.dft f a‖ ^ 2 := by
    calc
      (∑ a : ZMod q, ‖ZMod.dft f a‖ ^ 2) =
          (∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
            ‖ZMod.dft f a‖ ^ 2) + ‖ZMod.dft f 0‖ ^ 2 :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q))).symm
      _ = F + ∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
          ‖ZMod.dft f a‖ ^ 2 := by rw [hzero]; ring
  have hqcard : (q : ℝ) =
      (vanishing.card : ℝ) + (q - vanishing.card : ℕ) := by
    norm_cast
    omega
  have hfrequency :
      (∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
        ‖ZMod.dft f a‖ ^ 2) = (q : ℝ) * A - F := by
    dsimp only [A, F]
    linarith [hparseval, hsplit]
  rw [hfrequency]
  dsimp only [A, F] at henergy ⊢
  rw [div_mul_eq_mul_div, div_le_iff₀ htpos]
  nlinarith

end Erdos380

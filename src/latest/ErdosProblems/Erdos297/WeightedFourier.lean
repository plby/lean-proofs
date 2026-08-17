/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Modular

/-!
# Weighted finite Fourier inversion for Erdős Problem 297

This file isolates the finite algebra behind the weighted Bernoulli model in
Liu--Sawhney's Proposition 3.2.  A finite family of increments in `ZMod n` is
selected independently, with a possibly different real weight at every
index.  The Fourier transform of the resulting subset-sum law is the product

`∏ i, ((1 - p i) + p i * χ (-(step i * h)))`.

The final lemmas are deliberately analytic interfaces: after the zero
frequency contributes one, a norm bound for the sum of the nonzero modes
gives a pointwise lower bound for the mass of every prescribed residue.
-/

open scoped BigOperators

namespace Erdos297.WeightedFourier

open Complex Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Product Bernoulli weight of a subset `B` of the finite index set `I`. -/
def subsetWeight {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p : ι → ℝ) (B : Finset ι) : ℝ :=
  (∏ i ∈ B, p i) * ∏ i ∈ I \ B, (1 - p i)

theorem subsetWeight_nonneg {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {B : Finset ι} (hB : B ∈ I.powerset) :
    0 ≤ subsetWeight I p B := by
  have hsub : B ⊆ I := Finset.mem_powerset.mp hB
  exact mul_nonneg
    (Finset.prod_nonneg fun i hi => hp0 i (hsub hi))
    (Finset.prod_nonneg fun i hi =>
      sub_nonneg.mpr (hp1 i (Finset.mem_sdiff.mp hi).1))

/-- The Bernoulli weights of all subsets of `I` add to one. -/
theorem sum_subsetWeight {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p : ι → ℝ) :
    ∑ B ∈ I.powerset, subsetWeight I p B = 1 := by
  unfold subsetWeight
  rw [← Finset.prod_add (fun i => p i) (fun i => 1 - p i) I]
  simp

/-- Mass assigned by the weighted subset-sum law to a residue `a`. -/
def residueMass {ι : Type*} [DecidableEq ι] (n : ℕ)
    (I : Finset ι) (step : ι → ZMod n) (p : ι → ℝ) (a : ZMod n) : ℝ :=
  ∑ B ∈ I.powerset,
    if B.sum step = a then subsetWeight I p B else 0

theorem residueMass_nonneg {ι : Type*} [DecidableEq ι] (n : ℕ)
    (I : Finset ι) (step : ι → ZMod n) (p : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    (a : ZMod n) :
    0 ≤ residueMass n I step p a := by
  apply Finset.sum_nonneg
  intro B hB
  split_ifs
  · exact subsetWeight_nonneg I p hp0 hp1 hB
  · exact le_rfl

/-- Weighted character product at frequency `h`. -/
def coefficient {ι : Type*} [DecidableEq ι] {n : ℕ} [NeZero n]
    (I : Finset ι) (step : ι → ZMod n) (p : ι → ℝ) (h : ZMod n) : ℂ :=
  I.prod fun i =>
    ((1 - p i : ℝ) : ℂ) + (p i : ℂ) * ZMod.stdAddChar (-(step i * h))

@[simp] theorem coefficient_zero {ι : Type*} [DecidableEq ι] {n : ℕ} [NeZero n]
    (I : Finset ι) (step : ι → ZMod n) (p : ι → ℝ) :
    coefficient I step p 0 = 1 := by
  simp [coefficient]

/-- Expanding the weighted product chooses either the selected or omitted
factor at every index. -/
theorem sum_weight_mul_characterProduct {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p : ι → ℝ) (χ : ι → ℂ) :
    (∑ B ∈ I.powerset,
      (subsetWeight I p B : ℂ) * ∏ i ∈ B, χ i) =
      ∏ i ∈ I, (((1 - p i : ℝ) : ℂ) + (p i : ℂ) * χ i) := by
  calc
    (∑ B ∈ I.powerset,
        (subsetWeight I p B : ℂ) * ∏ i ∈ B, χ i) =
        ∑ B ∈ I.powerset,
          (∏ i ∈ B, (p i : ℂ) * χ i) *
            ∏ i ∈ I \ B, ((1 - p i : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro B _
      simp only [subsetWeight, Complex.ofReal_mul, Complex.ofReal_prod,
        Finset.prod_mul_distrib]
      ring
    _ = ∏ i ∈ I,
        ((p i : ℂ) * χ i + ((1 - p i : ℝ) : ℂ)) := by
      exact (Finset.prod_add (fun i => (p i : ℂ) * χ i)
        (fun i => ((1 - p i : ℝ) : ℂ)) I).symm
    _ = ∏ i ∈ I,
        (((1 - p i : ℝ) : ℂ) + (p i : ℂ) * χ i) := by
      apply Finset.prod_congr rfl
      intro i _
      ring

/-- The DFT of the weighted subset-sum law is the product of its independent
one-index Fourier factors. -/
theorem dft_residueMass {ι : Type*} [DecidableEq ι] {n : ℕ} [NeZero n]
    (I : Finset ι) (step : ι → ZMod n) (p : ι → ℝ) (h : ZMod n) :
    ZMod.dft (fun a => (residueMass n I step p a : ℂ)) h =
      coefficient I step p h := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, residueMass]
  push_cast
  simp_rw [Finset.mul_sum]
  rw [sum_comm]
  have hinner (B : Finset ι) :
      (∑ a : ZMod n,
        ZMod.stdAddChar (-(a * h)) *
          ((if B.sum step = a then subsetWeight I p B else 0 : ℝ) : ℂ)) =
        (subsetWeight I p B : ℂ) *
          ZMod.stdAddChar (-(B.sum step * h)) := by
    let s : ZMod n := B.sum step
    change (∑ a : ZMod n,
      ZMod.stdAddChar (-(a * h)) *
        ((if s = a then subsetWeight I p B else 0 : ℝ) : ℂ)) = _
    rw [Finset.sum_eq_single s]
    · simp [s, mul_comm]
    · intro b _ hbs
      simp [Ne.symm hbs]
    · simp
  have hchar (B : Finset ι) :
      ZMod.stdAddChar (-(B.sum step * h)) =
        ∏ i ∈ B, ZMod.stdAddChar (-(step i * h)) := by
    induction B using Finset.induction with
    | empty => simp
    | @insert i B hi ih =>
        rw [sum_insert hi, prod_insert hi, ← ih, ← AddChar.map_add_eq_mul]
        congr 1
        ring
  simp_rw [hinner, hchar]
  exact sum_weight_mul_characterProduct I p
    (fun i => ZMod.stdAddChar (-(step i * h)))

/-- Exact finite Fourier inversion for a prescribed residue. -/
theorem residueMass_fourier {ι : Type*} [DecidableEq ι]
    {n : ℕ} [NeZero n] (I : Finset ι) (step : ι → ZMod n)
    (p : ι → ℝ) (a : ZMod n) :
    (residueMass n I step p a : ℂ) =
      (n : ℂ)⁻¹ * ∑ h : ZMod n,
        ZMod.stdAddChar (h * a) * coefficient I step p h := by
  have hinv := congr_fun
    (ZMod.dft.symm_apply_apply (fun b => (residueMass n I step p b : ℂ))) a
  rw [ZMod.invDFT_apply] at hinv
  simp only [smul_eq_mul, dft_residueMass] at hinv
  exact hinv.symm

/-- Contribution of all nonzero frequencies in weighted Fourier inversion. -/
def nonzeroError {ι : Type*} [DecidableEq ι] (n : ℕ) [NeZero n]
    (I : Finset ι) (step : ι → ZMod n) (p : ι → ℝ) (a : ZMod n) : ℂ :=
  ∑ h ∈ (Finset.univ.erase 0 : Finset (ZMod n)),
    ZMod.stdAddChar (h * a) * coefficient I step p h

/-- Fourier inversion split into its unit zero mode and the nonzero error. -/
theorem residueMass_eq_zeroMode_add_error {ι : Type*} [DecidableEq ι]
    {n : ℕ} [NeZero n] (I : Finset ι) (step : ι → ZMod n)
    (p : ι → ℝ) (a : ZMod n) :
    (residueMass n I step p a : ℂ) =
      (n : ℂ)⁻¹ * (1 + nonzeroError n I step p a) := by
  rw [residueMass_fourier]
  congr 1
  rw [← sum_erase_add _ _ (mem_univ (0 : ZMod n))]
  simp [nonzeroError]

/-- Real form of the zero-mode decomposition. -/
theorem modulus_mul_residueMass_eq {ι : Type*} [DecidableEq ι]
    {n : ℕ} [NeZero n] (I : Finset ι) (step : ι → ZMod n)
    (p : ι → ℝ) (a : ZMod n) :
    (n : ℝ) * residueMass n I step p a =
      1 + (nonzeroError n I step p a).re := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hcomplex :
      (n : ℂ) * (residueMass n I step p a : ℂ) =
        1 + nonzeroError n I step p a := by
    rw [residueMass_eq_zeroMode_add_error, ← mul_assoc,
      mul_inv_cancel₀ hn, one_mul]
  have hreal := congrArg Complex.re hcomplex
  simpa using hreal

/-- A bound on the norm of the complete nonzero-frequency contribution. -/
theorem norm_nonzeroError_le_sum {ι : Type*} [DecidableEq ι]
    {n : ℕ} [NeZero n] (I : Finset ι) (step : ι → ZMod n)
    (p : ι → ℝ) (a : ZMod n) :
    ‖nonzeroError n I step p a‖ ≤
      ∑ h ∈ (Finset.univ.erase 0 : Finset (ZMod n)),
        ‖coefficient I step p h‖ := by
  calc
    ‖nonzeroError n I step p a‖ ≤
        ∑ h ∈ (Finset.univ.erase 0 : Finset (ZMod n)),
          ‖ZMod.stdAddChar (h * a) * coefficient I step p h‖ := by
            simpa only [nonzeroError] using
              norm_sum_le (Finset.univ.erase 0 : Finset (ZMod n))
                (fun h => ZMod.stdAddChar (h * a) * coefficient I step p h)
    _ = ∑ h ∈ (Finset.univ.erase 0 : Finset (ZMod n)),
          ‖coefficient I step p h‖ := by
            apply Finset.sum_congr rfl
            intro h _
            rw [norm_mul, AddChar.norm_apply, one_mul]

/-- Zero-mode domination in its most direct form: total nonzero error at most
`ε` leaves scaled residue mass at least `1 - ε`. -/
theorem scaled_residueMass_lower_bound_of_error_norm
    {ι : Type*} [DecidableEq ι] {n : ℕ} [NeZero n]
    (I : Finset ι) (step : ι → ZMod n) (p : ι → ℝ) (a : ZMod n)
    {ε : ℝ} (herror : ‖nonzeroError n I step p a‖ ≤ ε) :
    1 - ε ≤ (n : ℝ) * residueMass n I step p a := by
  have habs : |(nonzeroError n I step p a).re| ≤ ε :=
    (Complex.abs_re_le_norm _).trans herror
  have hre : -ε ≤ (nonzeroError n I step p a).re := (abs_le.mp habs).1
  rw [modulus_mul_residueMass_eq]
  linarith

/-- Normalized local lower bound for a prescribed residue. -/
theorem residueMass_lower_bound_of_error_norm
    {ι : Type*} [DecidableEq ι] {n : ℕ} [NeZero n]
    (I : Finset ι) (step : ι → ZMod n) (p : ι → ℝ) (a : ZMod n)
    {ε : ℝ} (herror : ‖nonzeroError n I step p a‖ ≤ ε) :
    (1 - ε) / (n : ℝ) ≤ residueMass n I step p a := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [div_le_iff₀ hn]
  simpa [mul_comm] using
    scaled_residueMass_lower_bound_of_error_norm I step p a herror

/-- Uniform control of every nonzero product gives a completely explicit
local lower bound. -/
theorem residueMass_lower_bound_of_uniform_coefficient_bound
    {ι : Type*} [DecidableEq ι] {n : ℕ} [NeZero n]
    (I : Finset ι) (step : ι → ZMod n) (p : ι → ℝ) (a : ZMod n)
    (E : ℝ)
    (hcoeff : ∀ h : ZMod n, h ≠ 0 → ‖coefficient I step p h‖ ≤ E) :
    (1 - ((n - 1 : ℕ) : ℝ) * E) / (n : ℝ) ≤
      residueMass n I step p a := by
  apply residueMass_lower_bound_of_error_norm
  calc
    ‖nonzeroError n I step p a‖ ≤
        ∑ h ∈ (Finset.univ.erase 0 : Finset (ZMod n)),
          ‖coefficient I step p h‖ :=
      norm_nonzeroError_le_sum I step p a
    _ ≤ ∑ _h ∈ (Finset.univ.erase 0 : Finset (ZMod n)), E := by
      apply Finset.sum_le_sum
      intro h hh
      exact hcoeff h (ne_of_mem_erase hh)
    _ = ((n - 1 : ℕ) : ℝ) * E := by
      rw [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ (0 : ZMod n)),
        card_univ, ZMod.card]

end

end Erdos297.WeightedFourier

#print axioms Erdos297.WeightedFourier.residueMass_fourier
#print axioms Erdos297.WeightedFourier.residueMass_lower_bound_of_uniform_coefficient_bound

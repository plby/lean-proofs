import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Combinatorics.Additive.Dissociation
import Mathlib.Combinatorics.Additive.Randomisation

/-!
# Chang's large-spectrum lemma for a finite abelian group

This file supplies the part of Chang's lemma needed in the quantitative Roth
argument.  The Fourier coefficient of the indicator of `A` at `psi` is kept
unnormalized:

`sum x in A, psi x`.

Consequently `largeSpectrum A eta` consists of the characters for which the
norm of this sum is at least `eta * #A`.  The final theorem covers this
spectrum by the `{0, 1, -1}`-span of at most

`ceil (2 * log (|G| / |A|) / eta^2)`

characters.

The analytic input is proved here.  It is the exponential form of Rudin's
inequality for a polynomial whose character support is dissociated.  Jensen's
inequality on `A`, followed by Rudin's inequality on `G`, gives the stated
dimension bound directly.
-/

open Finset Function Real
open Complex (re)
open scoped BigOperators ComplexConjugate

namespace Erdos140
namespace Chang

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-! ## Exponential Rudin inequality -/

/-- Exponential Rudin inequality for a character polynomial with dissociated
support.  Both sides use the uniform probability measure on `G`.

This coefficient formulation is slightly more convenient than first defining
a Fourier transform: it is exactly what is needed in Chang's argument. -/
theorem rudin_exp_ineq (c : AddChar G ℂ → ℂ)
    (hc : AddDissociated {psi | c psi ≠ 0}) :
    Finset.expect Finset.univ (fun a ↦ exp ((∑ psi, c psi * psi a).re)) ≤
      exp ((∑ psi, ‖c psi‖ ^ 2) / 2) := by
  have hexp (z : ℂ) :
      exp z.re ≤ cosh ‖z‖ + (z / ‖z‖).re * sinh ‖z‖ := by
    calc
      _ = exp ((z / ‖z‖).re * ‖z‖) := by
        obtain rfl | hz := eq_or_ne z 0 <;> simp [*]
      _ ≤ _ := exp_mul_le_cosh_add_mul_sinh
        (by simpa using z.abs_re_div_norm_le_one) _
  choose u hu huc using fun psi ↦ Complex.exists_norm_mul_eq_self (c psi)
  have hu0 (psi : AddChar G ℂ) : u psi ≠ 0 := fun h ↦ by
    simpa [h] using hu psi
  have hpoint (a : G) :
      exp ((∑ psi, c psi * psi a).re) ≤
        ∏ psi, (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi a).re) := by
    calc
      exp ((∑ psi, c psi * psi a).re)
          = ∏ psi, exp ((c psi * psi a).re) := by
              simp_rw [← exp_sum, ← Complex.re_sum]
      _ ≤ ∏ psi,
          (cosh ‖c psi * psi a‖ +
            ((c psi * psi a) / ‖c psi * psi a‖).re * sinh ‖c psi * psi a‖) :=
            prod_le_prod (fun _ _ ↦ by positivity) fun _ _ ↦ hexp _
      _ = ∏ psi, (cosh ‖c psi‖ +
          (u psi * (c psi * psi a) / (u psi * ↑‖c psi‖)).re * sinh ‖c psi‖) := by
        simp_rw [norm_mul, AddChar.norm_apply, mul_one, mul_div_mul_left _ _ (hu0 _)]
      _ = ∏ psi, (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi a).re) := by
        congr with psi
        obtain hpsi | hpsi := eq_or_ne (c psi) 0
        · simp [hpsi]
        simp only [huc, mul_left_comm (u psi), mul_div_cancel_left₀ _ hpsi,
          ← Complex.re_mul_ofReal, mul_right_comm]
  calc
    Finset.expect Finset.univ (fun a ↦ exp ((∑ psi, c psi * psi a).re))
        ≤ Finset.expect Finset.univ (fun a ↦ ∏ psi,
            (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi a).re)) :=
          expect_le_expect fun a _ ↦ hpoint a
    _ = ∏ psi, cosh ‖c psi‖ :=
      AddDissociated.randomisation _ _ <| by
        simpa [-Complex.ofReal_sinh, hu0]
    _ ≤ ∏ psi, exp (‖c psi‖ ^ 2 / 2) :=
      prod_le_prod (fun _ _ ↦ by positivity) fun _ _ ↦ cosh_le_exp_half_sq _
    _ = exp ((∑ psi, ‖c psi‖ ^ 2) / 2) := by
      simp_rw [← exp_sum, ← sum_div]

/-- Jensen's inequality for the exponential function and a nonempty finite
uniform average. -/
theorem exp_expect_le_expect_exp {I : Type*} (s : Finset I) (hs : s.Nonempty)
    (f : I → ℝ) :
    exp (Finset.expect s f) ≤ Finset.expect s (fun i ↦ exp (f i)) := by
  let w : I → ℝ := fun _ ↦ (s.card : ℝ)⁻¹
  have hw0 : ∀ i ∈ s, 0 ≤ w i := by
    intro i hi
    exact inv_nonneg.mpr (by positivity)
  have hw1 : ∑ i ∈ s, w i = 1 := by
    simp [w, hs.card_ne_zero]
  have h := convexOn_exp.map_sum_le (p := f) hw0 hw1 (fun _ _ ↦ Set.mem_univ _)
  simpa [Finset.expect_eq_sum_div_card, w, div_eq_inv_mul,
    Finset.mul_sum] using h

/-! ## Large spectrum -/

/-- The unnormalized Fourier sum of `1_A` at a character. -/
noncomputable def spectrumSum (A : Finset G) (psi : AddChar G ℂ) : ℂ :=
  ∑ x ∈ A, psi x

/-- The characters on which the Fourier transform of `1_A` has magnitude at
least `eta * |A|`. -/
noncomputable def largeSpectrum (A : Finset G) (eta : ℝ) : Finset (AddChar G ℂ) :=
  Finset.univ.filter fun psi ↦ eta * A.card ≤ ‖spectrumSum A psi‖

@[simp]
theorem mem_largeSpectrum {A : Finset G} {eta : ℝ} {psi : AddChar G ℂ} :
    psi ∈ largeSpectrum A eta ↔ eta * A.card ≤ ‖spectrumSum A psi‖ := by
  simp [largeSpectrum]

/-! ## Chang's covering theorem -/

/-- A dissociated subset of the large spectrum has logarithmically bounded
cardinality.  This is the analytic heart of Chang's lemma. -/
theorem card_addDissociated_largeSpectrum_le {A : Finset G} {eta : ℝ}
    {Delta : Finset (AddChar G ℂ)} (hA : A.Nonempty) (heta : 0 < eta)
    (hsub : Delta ⊆ largeSpectrum A eta)
    (hdis : AddDissociated (Delta : Set (AddChar G ℂ))) :
    (Delta.card : ℝ) ≤
      2 * log ((Fintype.card G : ℝ) / A.card) / eta ^ 2 := by
  classical
  choose u hu husum using fun psi : AddChar G ℂ ↦
    Complex.exists_norm_eq_mul_self (spectrumSum A psi)
  have hu0 (psi : AddChar G ℂ) : u psi ≠ 0 := fun h ↦ by
    simpa [h] using hu psi
  let c : AddChar G ℂ → ℂ := fun psi ↦
    if psi ∈ Delta then (eta : ℂ) * u psi else 0
  let P : G → ℝ := fun x ↦ (∑ psi, c psi * psi x).re
  have hc_support : {psi | c psi ≠ 0} = (Delta : Set (AddChar G ℂ)) := by
    ext psi
    simp [c, heta.ne', hu0]
  have hc_dis : AddDissociated {psi | c psi ≠ 0} := by
    rw [hc_support]
    exact hdis
  have hc_norm_sq (psi : AddChar G ℂ) :
      ‖c psi‖ ^ 2 = if psi ∈ Delta then eta ^ 2 else 0 := by
    simp only [c]
    split_ifs
    · simp [hu, abs_of_pos heta]
    · simp
  have hc_sq : ∑ psi, ‖c psi‖ ^ 2 = eta ^ 2 * Delta.card := by
    simp_rw [hc_norm_sq]
    simp
    ring
  have hcomplex :
      ∑ x ∈ A, ∑ psi, c psi * psi x =
        (eta : ℂ) * ∑ psi ∈ Delta, (‖spectrumSum A psi‖ : ℂ) := by
    calc
      ∑ x ∈ A, ∑ psi, c psi * psi x =
          ∑ psi, ∑ x ∈ A, c psi * psi x := by rw [sum_comm]
      _ = ∑ psi, c psi * spectrumSum A psi := by
        apply sum_congr rfl
        intro psi hpsi
        simp [spectrumSum, mul_sum]
      _ = ∑ psi ∈ Delta, (eta : ℂ) * u psi * spectrumSum A psi := by
        simp [c]
      _ = ∑ psi ∈ Delta, (eta : ℂ) * (‖spectrumSum A psi‖ : ℂ) := by
        apply sum_congr rfl
        intro psi hpsi
        rw [mul_assoc, ← husum]
      _ = (eta : ℂ) * ∑ psi ∈ Delta, (‖spectrumSum A psi‖ : ℂ) := by
        rw [mul_sum]
  have hsumP :
      ∑ x ∈ A, P x = eta * ∑ psi ∈ Delta, ‖spectrumSum A psi‖ := by
    change ∑ x ∈ A, (∑ psi, c psi * psi x).re = _
    rw [← Complex.re_sum, hcomplex]
    simp
  have hsum_lower :
      eta ^ 2 * A.card * Delta.card ≤ ∑ x ∈ A, P x := by
    rw [hsumP]
    calc
      eta ^ 2 * (A.card : ℝ) * Delta.card =
          ∑ psi ∈ Delta, eta * (eta * A.card) := by
            simp
            ring
      _ ≤ ∑ psi ∈ Delta, eta * ‖spectrumSum A psi‖ := by
        gcongr with psi hpsi
        exact mem_largeSpectrum.1 (hsub hpsi)
      _ = eta * ∑ psi ∈ Delta, ‖spectrumSum A psi‖ := by
        rw [mul_sum]
  have hmean : eta ^ 2 * Delta.card ≤ Finset.expect A P := by
    rw [Finset.expect_eq_sum_div_card]
    have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    rw [le_div_iff₀ hcard]
    nlinarith [hsum_lower]
  have hsubset_expect :
      Finset.expect A (fun x ↦ exp (P x)) ≤
        ((Fintype.card G : ℝ) / A.card) *
          Finset.expect Finset.univ (fun x ↦ exp (P x)) := by
    rw [Finset.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
    have hsum : ∑ x ∈ A, exp (P x) ≤ ∑ x : G, exp (P x) := by
      exact sum_le_sum_of_subset_of_nonneg (by simp) fun _ _ _ ↦ (exp_pos _).le
    have hAcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
    have hGcard : (Fintype.card G : ℝ) ≠ 0 := by positivity
    calc
      (∑ x ∈ A, exp (P x)) / A.card ≤
          (∑ x : G, exp (P x)) / A.card := by
            gcongr
      _ = ((Fintype.card G : ℝ) / A.card) *
          ((∑ x : G, exp (P x)) / Fintype.card G) := by
            field_simp
  have hchain :
      exp (eta ^ 2 * Delta.card) ≤
        ((Fintype.card G : ℝ) / A.card) *
          exp (eta ^ 2 * Delta.card / 2) := by
    calc
      exp (eta ^ 2 * Delta.card) ≤ exp (Finset.expect A P) := by gcongr
      _ ≤ Finset.expect A (fun x ↦ exp (P x)) :=
        exp_expect_le_expect_exp A hA P
      _ ≤ ((Fintype.card G : ℝ) / A.card) *
          Finset.expect Finset.univ (fun x ↦ exp (P x)) := hsubset_expect
      _ ≤ ((Fintype.card G : ℝ) / A.card) *
          exp ((∑ psi, ‖c psi‖ ^ 2) / 2) := by
            gcongr
            exact rudin_exp_ineq c hc_dis
      _ = ((Fintype.card G : ℝ) / A.card) *
          exp (eta ^ 2 * Delta.card / 2) := by rw [hc_sq]
  have hratio_pos : (0 : ℝ) < (Fintype.card G : ℝ) / A.card := by
    positivity
  have hhalf :
      exp (eta ^ 2 * Delta.card / 2) ≤
        (Fintype.card G : ℝ) / A.card := by
    calc
      exp (eta ^ 2 * Delta.card / 2) =
          exp (eta ^ 2 * Delta.card) / exp (eta ^ 2 * Delta.card / 2) := by
            rw [← exp_sub]
            congr 1
            ring
      _ ≤ (((Fintype.card G : ℝ) / A.card) *
          exp (eta ^ 2 * Delta.card / 2)) /
            exp (eta ^ 2 * Delta.card / 2) := by
              gcongr
      _ = (Fintype.card G : ℝ) / A.card := by
        field_simp
  have hlog : eta ^ 2 * Delta.card / 2 ≤
      log ((Fintype.card G : ℝ) / A.card) :=
    (le_log_iff_exp_le hratio_pos).2 hhalf
  have heta_sq : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [le_div_iff₀ heta_sq]
  nlinarith

/-- **Chang's lemma.**  The large spectrum of a nonempty finite set is
contained in the `{0, 1, -1}`-span of a logarithmically small subset.

The constant is explicit and the Fourier transform is unnormalized, as in
`largeSpectrum`. -/
theorem exists_largeSpectrum_subset_addSpan (A : Finset G) (eta : ℝ)
    (hA : A.Nonempty) (heta : 0 < eta) :
    ∃ Delta, Delta ⊆ largeSpectrum A eta ∧
      Delta.card ≤
        ⌈2 * log ((Fintype.card G : ℝ) / A.card) / eta ^ 2⌉₊ ∧
      largeSpectrum A eta ⊆ Delta.addSpan := by
  apply exists_subset_addSpan_card_le_of_forall_addDissociated
  intro Delta hsub hdis
  have hreal := card_addDissociated_largeSpectrum_le hA heta hsub hdis
  exact_mod_cast hreal.trans (Nat.le_ceil _)

end Chang
end Erdos140

#print axioms Erdos140.Chang.exists_largeSpectrum_subset_addSpan

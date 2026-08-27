import ErdosProblems.Erdos4.ProductPrimeMeanSquare

/-! The two prime transforms with arbitrary source activation weights. -/

open scoped BigOperators

namespace Erdos4.ProductPrimeMeanSquare

open FiniteCharacterSupport ProductCharacterEncoding

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

noncomputable def weightedSourceError (R : ℕ) (c : smallCharacters ell R → ℂ)
    (sources : Finset ℕ) (a : sources → ℂ) (q : ℕ) : ℂ :=
  ∑ chi : smallCharacters ell R,
    (c chi * ∑ p : sources, a p * value ell chi.val p) * star (value ell chi.val q)

theorem weightedSourceError_add (R : ℕ) (c d : smallCharacters ell R → ℂ)
    (sources : Finset ℕ) (a : sources → ℂ) (q : ℕ) :
    weightedSourceError ell R (fun chi => c chi + d chi) sources a q =
      weightedSourceError ell R c sources a q + weightedSourceError ell R d sources a q := by
  simp only [weightedSourceError, add_mul, Finset.sum_add_distrib]

theorem weightedSourceError_one (R : ℕ) (c : smallCharacters ell R → ℂ)
    (sources : Finset ℕ) (q : ℕ) :
    weightedSourceError ell R c sources (fun _ => 1) q = sourceError ell R c sources q := by
  simp only [weightedSourceError, sourceError, one_mul]

theorem weighted_source_error_mean_square {t R : ℕ} (ht : 2 ≤ t)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective ell) (hRQ : R ^ 2 ≤ t ^ 10)
    (X Y : ℕ) (hX : t ^ 50 ≤ X) (hY : t ^ 50 ≤ Y)
    (sources targets : Finset ℕ)
    (hsources : ∀ n ∈ sources, n.Prime ∧ t ^ 2 < n ∧ n ≤ X)
    (htargets : ∀ n ∈ targets, n.Prime ∧ t ^ 2 < n ∧ n ≤ Y)
    (hscop : ∀ n ∈ sources, n.Coprime (modulus ell))
    (htcop : ∀ n ∈ targets, n.Coprime (modulus ell))
    (c : smallCharacters ell R → ℂ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hc : ∀ chi, ‖c chi‖ ≤ γ) (a : sources → ℂ) :
    (∑ q : targets, ‖weightedSourceError ell R c sources a q‖ ^ 2) ≤
      (2 * (Y : ℝ) / Real.log t) * γ ^ 2 *
        ((2 * (X : ℝ) / Real.log t) * ∑ p : sources, ‖a p‖ ^ 2) := by
  have hB : 0 ≤ 2 * (Y : ℝ) / Real.log t := by positivity
  have hh := DoubleMeanSquare.sum_norm_sq_composition_le
    (fun (chi : smallCharacters ell R) (p : sources) => star (value ell chi.val p))
    (fun (chi : smallCharacters ell R) (q : targets) => value ell chi.val q)
    (2 * (X : ℝ) / Real.log t) (2 * (Y : ℝ) / Real.log t) γ hB hγ
    (source_mean_square ell ht hH hinj hRQ X hX sources hsources hscop)
    (target_mean_square ell ht hH hinj hRQ Y hY targets htargets htcop)
    (fun chi => star (c chi)) (fun chi => by simpa only [norm_star] using hc chi)
    (fun p => star (a p))
  have heq : ∀ q : targets, weightedSourceError ell R c sources a q =
      star (∑ chi : smallCharacters ell R,
        (star (c chi) * ∑ p : sources, star (a p) * star (value ell chi.val p)) *
          value ell chi.val q) := by
    intro q
    simp only [weightedSourceError, star_sum, star_mul, star_star]
    apply Finset.sum_congr rfl
    intro chi _
    have hs : (∑ p : sources, value ell chi.val p * a p) =
        ∑ p : sources, a p * value ell chi.val p :=
      Finset.sum_congr rfl (fun p _ => mul_comm _ _)
    rw [hs]
    ring
  simpa only [heq, norm_star] using hh

theorem activation_energy_le_mass {I : Type*} [Fintype I]
    (a : I → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    (∑ i, ‖(a i : ℂ)‖ ^ 2) ≤ ∑ i, a i := by
  apply Finset.sum_le_sum
  intro i _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 i)]
  nlinarith [ha0 i, ha1 i]

theorem activation_source_error_mean_square {t R : ℕ} (ht : 2 ≤ t)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective ell) (hRQ : R ^ 2 ≤ t ^ 10)
    (X Y : ℕ) (hX : t ^ 50 ≤ X) (hY : t ^ 50 ≤ Y)
    (sources targets : Finset ℕ)
    (hsources : ∀ n ∈ sources, n.Prime ∧ t ^ 2 < n ∧ n ≤ X)
    (htargets : ∀ n ∈ targets, n.Prime ∧ t ^ 2 < n ∧ n ≤ Y)
    (hscop : ∀ n ∈ sources, n.Coprime (modulus ell))
    (htcop : ∀ n ∈ targets, n.Coprime (modulus ell))
    (c : smallCharacters ell R → ℂ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hc : ∀ chi, ‖c chi‖ ≤ γ)
    (a : sources → ℝ) (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1) :
    (∑ q : targets, ‖weightedSourceError ell R c sources (fun p => (a p : ℂ)) q‖ ^ 2) ≤
      (2 * (Y : ℝ) / Real.log t) * γ ^ 2 *
        ((2 * (X : ℝ) / Real.log t) * ∑ p : sources, a p) := by
  refine (weighted_source_error_mean_square ell ht hH hinj hRQ X Y hX hY
    sources targets hsources htargets hscop htcop c hγ hc (fun p => (a p : ℂ))).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul_of_nonneg_left (activation_energy_le_mass a ha0 ha1) (by positivity)
  · positivity

end Erdos4.ProductPrimeMeanSquare

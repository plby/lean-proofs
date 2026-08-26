import ErdosProblems.Erdos4.FiniteCharacterSupport
import ErdosProblems.Erdos4.PrimeMeanSquare
import ErdosProblems.Erdos4.DoubleMeanSquare

/-!
# Prime mean-square estimates for the actual product characters

The CRT encoding and conductor support discharge the family hypotheses of
the prime-supported large sieve. Both source and target estimates retain
the logarithmic saving. Their composition uses the supremum of the
actual Fourier coefficients, without multiplying by the family size.
-/

open scoped BigOperators

namespace Erdos4.ProductPrimeMeanSquare

open FiniteCharacterSupport ProductCharacterEncoding

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

noncomputable def value (chi : ∀ p, DirichletCharacter ℂ (ell p)) (n : ℕ) : ℂ :=
  ∏ p, chi p (n : ZMod (ell p))

theorem coprime_modulus_of_prime_gt {n : ℕ} (hn : n.Prime) (hgt : ∀ p, ell p < n) :
    n.Coprime (modulus ell) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p _hp
  exact (Nat.coprime_primes hn (Fact.out : (ell p).Prime)).mpr (ne_of_gt (hgt p))

theorem target_mean_square {t R : ℕ} (ht : 2 ≤ t)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective ell) (hRQ : R ^ 2 ≤ t ^ 10)
    (N : ℕ) (hN : t ^ 50 ≤ N) (primes : Finset ℕ)
    (hprimes : ∀ n ∈ primes, n.Prime ∧ t ^ 2 < n ∧ n ≤ N)
    (hcop : ∀ n ∈ primes, n.Coprime (modulus ell))
    (a : smallCharacters ell R → ℂ) :
    (∑ n : primes, ‖∑ chi : smallCharacters ell R, a chi * value ell chi.val n‖ ^ 2) ≤
      (2 * (N : ℝ) / Real.log t) * ∑ chi, ‖a chi‖ ^ 2 := by
  have hh := PrimeMeanSquare.prime_mean_square_at_good_cutoff ht hH
    (fun chi : smallCharacters ell R => entry ell chi.val)
    (family_valid ell) (family_injective ell hinj)
    (fun chi => (entry_conductor_le ell chi).trans hRQ) N hN primes hprimes a
  have hv : ∀ (chi : smallCharacters ell R) (n : primes),
      PrimitiveCharacterFamily.value (entry ell chi.val) n = value ell chi.val n := by
    intro chi n
    exact entry_value_eq_product ell chi.val n (hcop n n.property)
  rw [← Finset.sum_coe_sort primes
    (fun n => ‖∑ chi : smallCharacters ell R,
      a chi * PrimitiveCharacterFamily.value (entry ell chi.val) n‖ ^ 2)] at hh
  simpa only [hv] using hh

theorem source_mean_square {t R : ℕ} (ht : 2 ≤ t)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective ell) (hRQ : R ^ 2 ≤ t ^ 10)
    (N : ℕ) (hN : t ^ 50 ≤ N) (primes : Finset ℕ)
    (hprimes : ∀ n ∈ primes, n.Prime ∧ t ^ 2 < n ∧ n ≤ N)
    (hcop : ∀ n ∈ primes, n.Coprime (modulus ell))
    (a : primes → ℂ) :
    (∑ chi : smallCharacters ell R, ‖∑ n : primes, a n * star (value ell chi.val n)‖ ^ 2) ≤
      (2 * (N : ℝ) / Real.log t) * ∑ n : primes, ‖a n‖ ^ 2 := by
  have hh := PrimeMeanSquare.prime_mean_square_dual_at_good_cutoff ht hH
    (fun chi : smallCharacters ell R => entry ell chi.val)
    (family_valid ell) (family_injective ell hinj)
    (fun chi => (entry_conductor_le ell chi).trans hRQ) N hN primes hprimes
    (fun n => star (a n))
  have hv : ∀ (chi : smallCharacters ell R) (n : primes),
      PrimitiveCharacterFamily.value (entry ell chi.val) n = value ell chi.val n := by
    intro chi n
    exact entry_value_eq_product ell chi.val n (hcop n n.property)
  simp only [hv, norm_star] at hh
  have hsum : ∀ chi : smallCharacters ell R,
      (∑ n : primes, a n * star (value ell chi.val n)) =
        star (∑ n : primes, star (a n) * value ell chi.val n) := by
    intro chi
    simp only [star_sum, star_mul, star_star, mul_comm]
  simpa only [hsum, norm_star] using hh

noncomputable def sourceError (R : ℕ) (c : smallCharacters ell R → ℂ)
    (sources : Finset ℕ) (q : ℕ) : ℂ :=
  ∑ chi : smallCharacters ell R,
    (c chi * ∑ p : sources, value ell chi.val p) * star (value ell chi.val q)

theorem source_error_mean_square {t R : ℕ} (ht : 2 ≤ t)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective ell) (hRQ : R ^ 2 ≤ t ^ 10)
    (X Y : ℕ) (hX : t ^ 50 ≤ X) (hY : t ^ 50 ≤ Y)
    (sources targets : Finset ℕ)
    (hsources : ∀ n ∈ sources, n.Prime ∧ t ^ 2 < n ∧ n ≤ X)
    (htargets : ∀ n ∈ targets, n.Prime ∧ t ^ 2 < n ∧ n ≤ Y)
    (hscop : ∀ n ∈ sources, n.Coprime (modulus ell))
    (htcop : ∀ n ∈ targets, n.Coprime (modulus ell))
    (c : smallCharacters ell R → ℂ) {γ : ℝ} (hγ : 0 ≤ γ) (hc : ∀ chi, ‖c chi‖ ≤ γ) :
    (∑ q : targets, ‖sourceError ell R c sources q‖ ^ 2) ≤
      (2 * (Y : ℝ) / Real.log t) * γ ^ 2 *
        ((2 * (X : ℝ) / Real.log t) * sources.card) := by
  have hB : 0 ≤ 2 * (Y : ℝ) / Real.log t := by positivity
  have hh := DoubleMeanSquare.sum_norm_sq_source_average_le
    (fun (chi : smallCharacters ell R) (p : sources) => star (value ell chi.val p))
    (fun (chi : smallCharacters ell R) (q : targets) => value ell chi.val q)
    (2 * (X : ℝ) / Real.log t) (2 * (Y : ℝ) / Real.log t) γ hB hγ
    (source_mean_square ell ht hH hinj hRQ X hX sources hsources hscop)
    (target_mean_square ell ht hH hinj hRQ Y hY targets htargets htcop)
    (fun chi => star (c chi)) (fun chi => by simpa only [norm_star] using hc chi)
  have heq : ∀ q : targets, sourceError ell R c sources q =
      star (∑ chi : smallCharacters ell R,
        (star (c chi) * ∑ p : sources, star (value ell chi.val p)) * value ell chi.val q) := by
    intro q
    simp only [sourceError, star_sum, star_mul, star_star]
    apply Finset.sum_congr rfl
    intro chi _hchi
    ring
  simpa only [heq, norm_star, Fintype.card_coe] using hh

/-- The diagonal multiplier is now the actual anchored Fourier
coefficient, with its proved energy-normalized supremum bound. -/
theorem actual_source_error_mean_square {k t R : ℕ} {m : ℝ} (hm : 1 ≤ m)
    (ht : 2 ≤ t) (hR : 2 ≤ R)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective ell) (hRQ : R ^ 2 ≤ t ^ 10) (hell : ∀ p, k + 2 ≤ ell p)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlocal : ∀ p, 20 * (k : ℝ) ^ 3 ≤ δ * ell p)
    (X Y : ℕ) (hX : t ^ 50 ≤ X) (hY : t ^ 50 ≤ Y)
    (sources targets : Finset ℕ)
    (hsources : ∀ n ∈ sources, n.Prime ∧ t ^ 2 < n ∧ n ≤ X)
    (htargets : ∀ n ∈ targets, n.Prime ∧ t ^ 2 < n ∧ n ≤ Y)
    (hscop : ∀ n ∈ sources, n.Coprime (modulus ell))
    (htcop : ∀ n ∈ targets, n.Coprime (modulus ell)) :
    (∑ q : targets, ‖sourceError ell R
      (fun chi => UnitFourier.coefficient ell m R h j chi.val) sources q‖ ^ 2) ≤
      (2 * (Y : ℝ) / Real.log t) *
        ((RestrictedProductNorm.energy (DivisorCoefficients.coefficient (k := k) m R ell) /
          UnitFourier.unitDensity ell) * δ) ^ 2 *
        ((2 * (X : ℝ) / Real.log t) * sources.card) := by
  apply source_error_mean_square ell ht hH hinj hRQ X Y hX hY sources targets
    hsources htargets hscop htcop
  · exact mul_nonneg (div_nonneg (RestrictedProductNorm.energy_nonneg _)
      (UnitFourier.unitDensity_pos ell).le) hδ0
  · intro chi
    exact norm_nonprincipal_coefficient_le ell hm hR hell h hh j chi.val
      ((mem_smallCharacters ell R chi.val).mp chi.property).1 hδ1 hlocal

end Erdos4.ProductPrimeMeanSquare

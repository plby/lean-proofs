import ErdosProblems.Erdos4.ProductCharacterMatrix
import ErdosProblems.Erdos4.RestrictedTensor
import ErdosProblems.Erdos4.ConductorDecay

/-!
# Decay of the actual product-character coefficient

The nonprincipal prime coordinates use the twisted local matrix. The
principal prime coordinates form an exact deletion contraction. Splitting
the actual cutoff vector combines these facts without a coefficient-count
loss.
-/

open scoped BigOperators

namespace Erdos4.FourierDecay

open DivisorCoefficients DivisorSlices LocalCharacterMatrix RestrictedTensor
  RestrictedProductNorm ConductorDecay ProductCharacterMatrix

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

theorem fourierCoefficient_eq_contractedTwist (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P)
    (hchi : ∀ p ∈ J, chi p ≠ 1) (houtside : ∀ p, p ∉ J → chi p = 1) :
    fourierCoefficient ell m R h j chi =
      contractedTwist m R ell J j
        (fun p i => star (chi p (AnchorRoots.anchorRoot (h p) j i : ZMod (ell p))))
        (fun s => ∏ p : {p : P // p ∉ J}, deletionMask j (s p)) := by
  let M : J → Option (Fin k) → Option (Fin k) → ℂ := fun p =>
    LocalFourier.twistedMatrix (ell p : ℝ) j
      (fun i => star (chi p (AnchorRoots.anchorRoot (h p) j i : ZMod (ell p))))
  let N : {p : P // p ∉ J} → Option (Fin k) → Option (Fin k) → ℂ :=
    fun p a b => (localKernel (ell p : ℝ) (deletionMask j) a b : ℂ)
  have hM : (fun p => characterMatrix (chi p) (h p) j) = mixedMatrix J M N := by
    funext p a b
    by_cases hp : p ∈ J
    · rw [mixedMatrix, dif_pos hp, characterMatrix_eq_twisted (chi p) (hchi p hp) (h p) (hh p) j]
    · rw [mixedMatrix, dif_neg hp, houtside p hp, principal_characterMatrix_eq_mean (h p) (hh p) j]
      rfl
  rw [fourierCoefficient_eq_tensor, hM, tensorForm_mixed]
  unfold contractedTwist productMatrix
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  congr 1
  rw [restrictedForm_productMask_eq]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, slice, N]

/-- Product conductor decay for the genuine character average of the
actual divisor-cutoff amplitude. -/
theorem norm_fourierCoefficient_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (hell : ∀ p, k + 2 ≤ ell p)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P)
    (hchi : ∀ p ∈ J, chi p ≠ 1) (houtside : ∀ p, p ∉ J → chi p = 1) :
    ‖fourierCoefficient ell m R h j chi‖ ≤
      energy (coefficient (k := k) m R ell) * ∏ p : J, 20 * (k : ℝ) ^ 3 / ell p := by
  rw [fourierCoefficient_eq_contractedTwist ell m R h hh j chi J hchi houtside]
  apply norm_contractedTwist_le hm hR ell hell J j
  · intro p i
    rw [norm_star]
    exact (chi p).norm_le_one _
  · intro s
    exact Finset.prod_nonneg (fun p _hp => deletionMask_nonneg j (s p))
  · intro s
    exact Finset.prod_le_one (fun p _hp => deletionMask_nonneg j (s p))
      (fun p _hp => deletionMask_le_one j (s p))

/-- A fixed lower cutoff on conductor primes makes every nonprincipal
coefficient an arbitrarily small fixed multiple of the exact energy. -/
theorem norm_fourierCoefficient_le_small {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (hell : ∀ p, k + 2 ≤ ell p) {δ : ℝ} (hδ : δ ≤ 1)
    (hlocal : ∀ p, 20 * (k : ℝ) ^ 3 ≤ δ * ell p)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P) (hJ : J.Nonempty)
    (hchi : ∀ p ∈ J, chi p ≠ 1) (houtside : ∀ p, p ∉ J → chi p = 1) :
    ‖fourierCoefficient ell m R h j chi‖ ≤ energy (coefficient (k := k) m R ell) * δ := by
  exact (norm_fourierCoefficient_le ell hm hR hell h hh j chi J hchi houtside).trans
    (mul_le_mul_of_nonneg_left
      (product_decay_le hδ ell (fun p => (Fact.out : (ell p).Prime).pos) J hJ
        (fun p _hp => hlocal p)) (energy_nonneg _))

end Erdos4.FourierDecay

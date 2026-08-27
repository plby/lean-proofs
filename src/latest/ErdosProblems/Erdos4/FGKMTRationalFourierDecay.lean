import ErdosProblems.Erdos4.FGKMTRationalFourier
import ErdosProblems.Erdos4.FGKMTProjectionSlices
import ErdosProblems.Erdos4.ConductorDecay
import ErdosProblems.Erdos4.RestrictedTensor

/-! Energy-normalized conductor decay for the actual rational sieve transform. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients DivisorSlices LocalCharacterMatrix RestrictedTensor
  RestrictedProductNorm ConductorDecay

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def rationalContractedTwist (b : ℝ) (R : ℕ) (ell : P → ℕ) (J : Finset P)
    (j : Fin k) (phase : J → Fin k → ℂ)
    (mask : ({p : P // p ∉ J} → Option (Fin k)) → ℝ) : ℂ :=
  ∑ a : J → Option (Fin k), ∑ c : J → Option (Fin k),
    productMatrix ell J j phase a c *
      (restrictedForm (fun p : {p : P // p ∉ J} => (ell p : ℝ)) mask
        (rationalSlice b R ell J a) (rationalSlice b R ell J c) : ℂ)

theorem norm_rationalContractedTwist_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) (J : Finset P) (j : Fin k)
    (phase : J → Fin k → ℂ) (hphase : ∀ p i, ‖phase p i‖ ≤ 1)
    (mask : ({p : P // p ∉ J} → Option (Fin k)) → ℝ)
    (hmask0 : ∀ s, 0 ≤ mask s) (hmask1 : ∀ s, mask s ≤ 1) :
    ‖rationalContractedTwist b R ell J j phase mask‖ ≤
      energy (rationalCoefficient (k := k) b R ell) * ∏ p : J, 20 * (k : ℝ) ^ 3 / ell p := by
  have hell' : ∀ p, (k : ℝ) < (ell p : ℝ) := by
    intro p
    exact_mod_cast (show k < ell p by have := hell p; omega)
  have hslice := rationalSlice_energy_le (k := k) hb R ell (fun p => by have := hell p; omega) J
  have hh := SliceBounds.norm_matrix_slice_sum_le
    (fun p : {p : P // p ∉ J} => (ell p : ℝ)) (fun p => hell' p)
    mask hmask0 hmask1 (rationalSlice b R ell J) (sliceFactor ell J)
    (productMatrix ell J j phase) (energy_nonneg _) (sliceFactor_nonneg ell J) hslice
  exact hh.trans (mul_le_mul_of_nonneg_left (weighted_productMatrix_le ell hell J j phase hphase)
    (energy_nonneg _))

variable (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

theorem rationalRawFourier_eq_contractedTwist (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P)
    (hχ : ∀ p ∈ J, χ p ≠ 1) (houtside : ∀ p, p ∉ J → χ p = 1) :
    rationalRawFourier ell b R h j χ =
      rationalContractedTwist b R ell J j
        (fun p i => star (χ p (AnchorRoots.anchorRoot (h p) j i : ZMod (ell p))))
        (fun s => ∏ p : {p : P // p ∉ J}, deletionMask j (s p)) := by
  let M : J → Option (Fin k) → Option (Fin k) → ℂ := fun p =>
    LocalFourier.twistedMatrix (ell p : ℝ) j
      (fun i => star (χ p (AnchorRoots.anchorRoot (h p) j i : ZMod (ell p))))
  let N : {p : P // p ∉ J} → Option (Fin k) → Option (Fin k) → ℂ :=
    fun p a c => (localKernel (ell p : ℝ) (deletionMask j) a c : ℂ)
  have hM : (fun p => characterMatrix (χ p) (h p) j) = mixedMatrix J M N := by
    funext p a c
    by_cases hp : p ∈ J
    · rw [mixedMatrix, dif_pos hp, characterMatrix_eq_twisted (χ p) (hχ p hp) (h p) (hh p) j]
    · rw [mixedMatrix, dif_neg hp, houtside p hp, principal_characterMatrix_eq_mean (h p) (hh p) j]
      rfl
  rw [rationalRawFourier_eq_tensor, hM, tensorForm_mixed]
  unfold rationalContractedTwist productMatrix
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  rw [restrictedForm_productMask_eq]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, rationalSlice, N]

theorem norm_rationalRawFourier_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ p, k + 2 ≤ ell p)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P)
    (hχ : ∀ p ∈ J, χ p ≠ 1) (houtside : ∀ p, p ∉ J → χ p = 1) :
    ‖rationalRawFourier ell b R h j χ‖ ≤
      energy (rationalCoefficient (k := k) b R ell) * ∏ p : J, 20 * (k : ℝ) ^ 3 / ell p := by
  rw [rationalRawFourier_eq_contractedTwist ell b R h hh j χ J hχ houtside]
  apply norm_rationalContractedTwist_le hb R ell hell J j
  · intro p i
    rw [norm_star]
    exact (χ p).norm_le_one _
  · intro s
    exact Finset.prod_nonneg (fun p _ => deletionMask_nonneg j (s p))
  · intro s
    exact Finset.prod_le_one (fun p _ => deletionMask_nonneg j (s p))
      (fun p _ => deletionMask_le_one j (s p))

theorem norm_rationalRawFourier_le_small {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ p, k + 2 ≤ ell p) {δ : ℝ} (hδ : δ ≤ 1)
    (hlocal : ∀ p, 20 * (k : ℝ) ^ 3 ≤ δ * ell p)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P) (hJ : J.Nonempty)
    (hχ : ∀ p ∈ J, χ p ≠ 1) (houtside : ∀ p, p ∉ J → χ p = 1) :
    ‖rationalRawFourier ell b R h j χ‖ ≤ energy (rationalCoefficient (k := k) b R ell) * δ := by
  exact (norm_rationalRawFourier_le ell hb R hell h hh j χ J hχ houtside).trans
    (mul_le_mul_of_nonneg_left
      (product_decay_le hδ ell (fun p => (Fact.out : (ell p).Prime).pos) J hJ
        (fun p _ => hlocal p)) (energy_nonneg _))

end Erdos4.FGKMT

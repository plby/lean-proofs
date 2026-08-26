import ErdosProblems.Erdos4.DivisorSlices
import ErdosProblems.Erdos4.LocalFourier

/-!
# Product decay for conductor-coordinate contractions

This combines the actual divisor-coefficient slices with the local twisted
matrix estimate. The mask on the untouched prime coordinates may be any
function between zero and one, in particular the deletion of an anchored
occupied residue state at each untouched prime.
-/

open scoped BigOperators

namespace Erdos4.ConductorDecay

open DivisorCoefficients DivisorSlices LocalFourier RestrictedProductNorm

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def productMatrix (ell : P → ℕ) (J : Finset P) (j : Fin k)
    (phase : J → Fin k → ℂ) (a b : J → Option (Fin k)) : ℂ :=
  ∏ p : J, twistedMatrix (ell p : ℝ) j (phase p) (a p) (b p)

omit [Fintype P] in
theorem weighted_productMatrix_eq (ell : P → ℕ) (J : Finset P) (j : Fin k)
    (phase : J → Fin k → ℂ) :
    weightedMatrixNorm (sliceFactor ell J) (productMatrix ell J j phase) =
      ∏ p : J, weightedMatrixNorm (localWeight (ell p)) (twistedMatrix (ell p : ℝ) j (phase p)) := by
  unfold weightedMatrixNorm productMatrix sliceFactor
  simp_rw [norm_prod, ← Finset.prod_mul_distrib]
  exact SliceBounds.sum_sum_product (fun (p : J) a b =>
    ‖twistedMatrix (ell p : ℝ) j (phase p) a b‖ * localWeight (ell p) a * localWeight (ell p) b)

omit [Fintype P] in
theorem weighted_productMatrix_le (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p)
    (J : Finset P) (j : Fin k) (phase : J → Fin k → ℂ)
    (hphase : ∀ p i, ‖phase p i‖ ≤ 1) :
    weightedMatrixNorm (sliceFactor ell J) (productMatrix ell J j phase) ≤
      ∏ p : J, 20 * (k : ℝ) ^ 3 / ell p := by
  rw [weighted_productMatrix_eq]
  exact Finset.prod_le_prod
    (fun p _hp => weightedMatrixNorm_nonneg (localWeight (ell p)) (localWeight_nonneg (ell p)) _)
    (fun p _hp => weighted_twistedMatrix_le (hell p) j (phase p) (hphase p))

noncomputable def contractedTwist (m : ℝ) (R : ℕ) (ell : P → ℕ) (J : Finset P)
    (j : Fin k) (phase : J → Fin k → ℂ)
    (mask : ({p : P // p ∉ J} → Option (Fin k)) → ℝ) : ℂ :=
  ∑ a : J → Option (Fin k), ∑ b : J → Option (Fin k),
    productMatrix ell J j phase a b *
      (restrictedForm (fun p : {p : P // p ∉ J} => (ell p : ℝ)) mask
        (slice m R ell J a) (slice m R ell J b) : ℂ)

/-- The true cutoff coefficients retain their exact energy in the conductor bound. -/
theorem norm_contractedTwist_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) (J : Finset P) (j : Fin k)
    (phase : J → Fin k → ℂ) (hphase : ∀ p i, ‖phase p i‖ ≤ 1)
    (mask : ({p : P // p ∉ J} → Option (Fin k)) → ℝ)
    (hmask0 : ∀ s, 0 ≤ mask s) (hmask1 : ∀ s, mask s ≤ 1) :
    ‖contractedTwist m R ell J j phase mask‖ ≤
      energy (coefficient (k := k) m R ell) * ∏ p : J, 20 * (k : ℝ) ^ 3 / ell p := by
  have hell' : ∀ p, (k : ℝ) < (ell p : ℝ) := by
    intro p
    exact_mod_cast (show k < ell p by have := hell p; omega)
  have hslice := slice_energy_le (k := k) hm hR ell (fun p => by have := hell p; omega) J
  have hh := SliceBounds.norm_matrix_slice_sum_le
    (fun p : {p : P // p ∉ J} => (ell p : ℝ)) (fun p => hell' p)
    mask hmask0 hmask1 (slice m R ell J) (sliceFactor ell J)
    (productMatrix ell J j phase) (energy_nonneg _) (sliceFactor_nonneg ell J) hslice
  exact hh.trans (mul_le_mul_of_nonneg_left (weighted_productMatrix_le ell hell J j phase hphase)
    (energy_nonneg _))

omit [Fintype P] in
/-- One conductor prime supplies any prescribed fixed small factor; every
other conductor prime contributes at most one. No fractional-power bound is needed. -/
theorem product_decay_le {δ : ℝ} (hδ1 : δ ≤ 1)
    (ell : P → ℕ) (hell : ∀ p, 0 < ell p) (J : Finset P) (hJ : J.Nonempty)
    (hlocal : ∀ p ∈ J, 20 * (k : ℝ) ^ 3 ≤ δ * ell p) :
    (∏ p : J, 20 * (k : ℝ) ^ 3 / ell p) ≤ δ := by
  obtain ⟨p, hp⟩ := hJ
  have hfactor0 : ∀ q : J, 0 ≤ 20 * (k : ℝ) ^ 3 / ell q := by
    intro q
    positivity
  have hfactor : ∀ q : J, 20 * (k : ℝ) ^ 3 / ell q ≤ δ := by
    intro q
    exact (div_le_iff₀ (by exact_mod_cast hell q)).mpr (hlocal q q.property)
  have hrest : (∏ q ∈ (Finset.univ : Finset J).erase ⟨p, hp⟩,
      20 * (k : ℝ) ^ 3 / ell q) ≤ 1 :=
    Finset.prod_le_one (fun q _hq => hfactor0 q) (fun q _hq => (hfactor q).trans hδ1)
  rw [← Finset.mul_prod_erase (Finset.univ : Finset J)
    (fun q => 20 * (k : ℝ) ^ 3 / ell q) (Finset.mem_univ ⟨p, hp⟩)]
  exact (mul_le_mul_of_nonneg_left hrest (hfactor0 ⟨p, hp⟩)).trans (by simpa using hfactor ⟨p, hp⟩)

end Erdos4.ConductorDecay

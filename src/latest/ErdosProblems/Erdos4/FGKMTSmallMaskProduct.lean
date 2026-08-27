import ErdosProblems.Erdos4.FGKMTSmallMaskFourier
import ErdosProblems.Erdos4.FGKMTUnitFourier
import ErdosProblems.Erdos4.ProductFourierInversion

/-! Exact product masks and their ordinary unit-group Fourier coefficients. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical ProductFourierInversion

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

theorem transform_product (f : ∀ p, (ZMod (ell p))ˣ → ℂ)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) :
    transform ell (fun u => ∏ p, f p (u p)) χ =
      ∏ p, (Fintype.card ((ZMod (ell p))ˣ) : ℂ)⁻¹ *
        ∑ u : (ZMod (ell p))ˣ, star (χ p (u : ZMod (ell p))) * f p u := by
  unfold transform value
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun p (u : (ZMod (ell p))ˣ) =>
    star (χ p (u : ZMod (ell p))) * f p u),
    Fintype.card_pi, Nat.cast_prod, ← Finset.prod_inv_distrib, Finset.prod_mul_distrib]

noncomputable def smallProductDensity (h : ∀ p, Fin k → ZMod (ell p)) : ℝ :=
  ∏ p, smallPresieveDensity (h p)

noncomputable def smallProductMask (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (u : ∀ p, (ZMod (ell p))ˣ) : ℂ :=
  ∏ p, if SmallAnchorGood (h p) j (u p) then 1 else 0

noncomputable def smallProductFourier (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) : ℂ :=
  ∏ p, smallMaskFourier (h p) j (χ p)

theorem smallProductFourier_eq_transform (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) :
    smallProductFourier ell h j χ = transform ell (smallProductMask ell h j) χ := by
  unfold smallProductMask
  rw [transform_product ell
    (fun (p : P) (u : (ZMod (ell p))ˣ) => if SmallAnchorGood (h p) j u then (1 : ℂ) else 0) χ]
  apply Finset.prod_congr rfl
  intro p _
  unfold smallMaskFourier smallAnchorGoodStates
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [div_eq_mul_inv, mul_comm]

theorem smallProductMask_inversion (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (u : ∀ p, (ZMod (ell p))ˣ) :
    (∑ χ : ∀ p, DirichletCharacter ℂ (ell p),
      smallProductFourier ell h j χ * value ell χ u) = smallProductMask ell h j u := by
  simp_rw [smallProductFourier_eq_transform]
  exact inversion ell (smallProductMask ell h j) u

theorem smallProductDensity_nonneg (h : ∀ p, Fin k → ZMod (ell p)) :
    0 ≤ smallProductDensity ell h :=
  Finset.prod_nonneg (fun p _ => smallPresieveDensity_nonneg (h p))

theorem smallProductDensity_pos (h : ∀ p, Fin k → ZMod (ell p))
    (ha : ∀ p, ∃ x, SmallPrimeGood (h p) x) : 0 < smallProductDensity ell h :=
  Finset.prod_pos (fun p _ => smallPresieveDensity_pos (h p) (ha p))

theorem smallProductDensity_ge_inv (h : ∀ p, Fin k → ZMod (ell p))
    (ha : ∀ p, ∃ x, SmallPrimeGood (h p) x) :
    ((∏ p, ell p : ℕ) : ℝ)⁻¹ ≤ smallProductDensity ell h := by
  rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg (ell p)))
  intro p _
  exact smallPresieveDensity_ge_inv (h p) (ha p)

theorem smallProduct_anchored_density (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k) :
    (∏ p, smallAnchoredDensity (h p) j) = smallProductDensity ell h / sieveWindowDensity ell := by
  simp_rw [smallAnchoredDensity_eq]
  rw [Finset.prod_div_distrib]
  rfl

theorem smallProductFourier_principal (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k) :
    smallProductFourier ell h j (fun _ => 1) =
      ((smallProductDensity ell h / sieveWindowDensity ell : ℝ) : ℂ) := by
  unfold smallProductFourier
  simp_rw [smallMaskFourier_principal]
  rw [← Complex.ofReal_prod, smallProduct_anchored_density]

theorem smallProductFourier_norm_le (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) :
    ‖smallProductFourier ell h j χ‖ ≤ smallProductDensity ell h / sieveWindowDensity ell := by
  rw [smallProductFourier, norm_prod, ← smallProduct_anchored_density ell h j]
  exact Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p _ => smallMaskFourier_norm_le (h p) j (χ p))

end Erdos4.FGKMT

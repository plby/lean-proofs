import ErdosProblems.Erdos4.FGKMTFourierProduct
import ErdosProblems.Erdos4.FGKMTUnitInversion

/-! The small-prime mask times the rational sieve square, with exact Fourier coefficients. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical ProductFourierInversion

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ p, Fact (ell₀ p).Prime] [∀ q, Fact (ell₁ q).Prime]

noncomputable def smallProductRealMask (h : ∀ p, Fin k → ZMod (ell₀ p)) (j : Fin k)
    (u : ∀ p, (ZMod (ell₀ p))ˣ) : ℝ :=
  ∏ p, if SmallAnchorGood (h p) j (u p) then 1 else 0

theorem smallProductRealMask_nonneg (h : ∀ p, Fin k → ZMod (ell₀ p)) (j : Fin k)
    (u : ∀ p, (ZMod (ell₀ p))ˣ) : 0 ≤ smallProductRealMask ell₀ h j u := by
  apply Finset.prod_nonneg
  intro p _
  split_ifs <;> norm_num

theorem smallProductRealMask_cast (h : ∀ p, Fin k → ZMod (ell₀ p)) (j : Fin k)
    (u : ∀ p, (ZMod (ell₀ p))ˣ) :
    (smallProductRealMask ell₀ h j u : ℂ) = smallProductMask ell₀ h j u := by
  simp only [smallProductRealMask, smallProductMask, Complex.ofReal_prod, apply_ite,
    Complex.ofReal_one, Complex.ofReal_zero]

noncomputable def maskedUnitWeight (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q)) (j : Fin k)
    (u : ∀ s, (ZMod (Sum.elim ell₀ ell₁ s))ˣ) : ℝ :=
  smallProductRealMask ell₀ h₀ j (fun p => u (.inl p)) *
    rationalUnitSquare ell₁ b R h₁ j (fun q => u (.inr q))

noncomputable def maskedUnitFourier (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q)) (j : Fin k)
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s)) : ℂ :=
  smallProductFourier ell₀ h₀ j (fun p => χ (.inl p)) *
    rationalUnitFourier ell₁ b R h₁ j (fun q => χ (.inr q))

theorem maskedUnitWeight_nonneg (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q)) (j : Fin k)
    (u : ∀ s, (ZMod (Sum.elim ell₀ ell₁ s))ˣ) :
    0 ≤ maskedUnitWeight ell₀ ell₁ b R h₀ h₁ j u :=
  mul_nonneg (smallProductRealMask_nonneg ell₀ h₀ j _)
    (rationalUnitSquare_nonneg ell₁ b R h₁ j _)

theorem maskedUnitWeight_inversion (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q)) (j : Fin k)
    (u : ∀ s, (ZMod (Sum.elim ell₀ ell₁ s))ˣ) :
    (∑ χ, maskedUnitFourier ell₀ ell₁ b R h₀ h₁ j χ * value (Sum.elim ell₀ ell₁) χ u) =
      (maskedUnitWeight ell₀ ell₁ b R h₀ h₁ j u : ℂ) := by
  have hh := productFourier_inversion ell₀ ell₁ (smallProductMask ell₀ h₀ j)
    (fun u => (rationalUnitSquare ell₁ b R h₁ j u : ℂ))
    (smallProductFourier ell₀ h₀ j) (rationalUnitFourier ell₁ b R h₁ j)
    (smallProductMask_inversion ell₀ h₀ j) (rationalUnitSquare_inversion ell₁ b R h₁ j) u
  have hcast : (maskedUnitWeight ell₀ ell₁ b R h₀ h₁ j u : ℂ) =
      smallProductMask ell₀ h₀ j (fun p => u (.inl p)) *
        (rationalUnitSquare ell₁ b R h₁ j (fun q => u (.inr q)) : ℂ) := by
    exact (Complex.ofReal_mul _ _).trans
      (congrArg (fun z : ℂ => z * (rationalUnitSquare ell₁ b R h₁ j
        (fun q => u (.inr q)) : ℂ))
        (smallProductRealMask_cast ell₀ h₀ j (fun p => u (.inl p))))
  exact hh.trans hcast.symm

noncomputable def aggregateUnitFourier (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s)) : ℂ :=
  ∑ j : Fin k, maskedUnitFourier ell₀ ell₁ b R h₀ h₁ j χ

noncomputable def aggregateUnitWeight (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (u : ∀ s, (ZMod (Sum.elim ell₀ ell₁ s))ˣ) : ℝ :=
  ∑ j : Fin k, maskedUnitWeight ell₀ ell₁ b R h₀ h₁ j u

theorem aggregateUnitWeight_nonneg (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (u : ∀ s, (ZMod (Sum.elim ell₀ ell₁ s))ˣ) :
    0 ≤ aggregateUnitWeight ell₀ ell₁ b R h₀ h₁ u :=
  Finset.sum_nonneg (fun j _ => maskedUnitWeight_nonneg ell₀ ell₁ b R h₀ h₁ j u)

theorem aggregateUnitWeight_inversion (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (u : ∀ s, (ZMod (Sum.elim ell₀ ell₁ s))ˣ) :
    (∑ χ, aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ χ * value (Sum.elim ell₀ ell₁) χ u) =
      (aggregateUnitWeight ell₀ ell₁ b R h₀ h₁ u : ℂ) := by
  simp only [aggregateUnitFourier, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [maskedUnitWeight_inversion, aggregateUnitWeight, Complex.ofReal_sum]

theorem maskedUnitFourier_principal (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hinj : ∀ q, Function.Injective (h₁ q)) (j : Fin k) :
    maskedUnitFourier ell₀ ell₁ b R h₀ h₁ j (fun _ => 1) =
      ((smallProductDensity ell₀ h₀ / sieveWindowDensity ell₀ *
        rationalTrueForm b R ell₁ j / sieveWindowDensity ell₁ : ℝ) : ℂ) := by
  change smallProductFourier ell₀ h₀ j (fun _ : P => 1) *
    rationalUnitFourier ell₁ b R h₁ j (fun _ : Q => 1) = _
  rw [smallProductFourier_principal ell₀ h₀ j,
    rational_unit_principal_eq_trueForm ell₁ b R h₁ hinj j]
  push_cast
  ring

theorem aggregateUnitFourier_principal (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hinj : ∀ q, Function.Injective (h₁ q)) :
    aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ (fun _ => 1) =
      ((smallProductDensity ell₀ h₀ / sieveWindowDensity ell₀ *
        (∑ j : Fin k, rationalTrueForm b R ell₁ j) / sieveWindowDensity ell₁ : ℝ) : ℂ) := by
  unfold aggregateUnitFourier
  simp_rw [maskedUnitFourier_principal ell₀ ell₁ b R h₀ h₁ hinj]
  rw [← Complex.ofReal_sum, ← Finset.sum_div, ← Finset.mul_sum]

end Erdos4.FGKMT

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierRelativeComparison
import ErdosProblems.Erdos4b.GeneralFourierFullIntegral

/-!
# The exact rough-prime reference zeta product

Removing the finitely many pre-sieve prime factors divides the full
reference zeta product by their literal finite product. Nonvanishing is
proved for both factors, with no asymptotic approximation at this stage.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def doubledFourierReferenceZetaProduct {ι : Type*} [Fintype ι]
    (s : (ι ⊕ ι) → Bool → ℂ) : ℂ :=
  ∏ i, riemannZeta (1 + (s i false + s i true)) /
    (riemannZeta (1 + s i false) * riemannZeta (1 + s i true))

def smallDoubledFourierReferenceProduct {ι : Type*} [Fintype ι]
    (w : ℕ) (s : (ι ⊕ ι) → Bool → ℂ) : ℂ :=
  ∏ p ∈ boundedFourierPrimes w, doubledFourierReferenceFactor s p

def roughDoubledFourierReferenceFactor {ι : Type*} [Fintype ι]
    (w : ℕ) (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) : ℂ :=
  if w < p then doubledFourierReferenceFactor s p else 1

theorem hasProd_doubledFourierReferenceFactor {ι : Type*} [Fintype ι]
    (s : (ι ⊕ ι) → Bool → ℂ) (hRe : ∀ i b, 0 < (s i b).re) :
    HasProd (fun p : Nat.Primes ↦ doubledFourierReferenceFactor s p)
      (doubledFourierReferenceZetaProduct s) := by
  exact hasProd_finite_pairReferenceProduct Finset.univ
    (fun i ↦ s i false) (fun i ↦ s i true)
    (fun i hi ↦ hRe i false) (fun i hi ↦ hRe i true)

theorem smallDoubledFourierReferenceProduct_ne_zero {ι : Type*} [Fintype ι]
    (w : ℕ) (s : (ι ⊕ ι) → Bool → ℂ) (hRe : ∀ i b, 0 ≤ (s i b).re) :
    smallDoubledFourierReferenceProduct w s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact doubledFourierReferenceFactor_ne_zero s (by exact_mod_cast p.property.two_le) hRe

theorem doubledFourierReferenceZetaProduct_ne_zero {ι : Type*} [Fintype ι]
    (s : (ι ⊕ ι) → Bool → ℂ) (hRe : ∀ i b, 0 < (s i b).re) :
    doubledFourierReferenceZetaProduct s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hz (b : Bool) : riemannZeta (1 + s i b) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by
      simp only [Complex.add_re, Complex.one_re]
      linarith [hRe i b])
  apply div_ne_zero _ (mul_ne_zero (hz false) (hz true))
  exact riemannZeta_ne_zero_of_one_le_re (by
    simp only [Complex.add_re, Complex.one_re]
    linarith [hRe i false, hRe i true])

theorem hasProd_roughDoubledFourierReferenceFactor {ι : Type*} [Fintype ι]
    (w : ℕ) (s : (ι ⊕ ι) → Bool → ℂ) (hRe : ∀ i b, 0 < (s i b).re) :
    HasProd (fun p : Nat.Primes ↦ roughDoubledFourierReferenceFactor w s p)
      (doubledFourierReferenceZetaProduct s / smallDoubledFourierReferenceProduct w s) := by
  classical
  let g : Nat.Primes → ℂ := fun p ↦
    if p ∈ boundedFourierPrimes w then (doubledFourierReferenceFactor s p)⁻¹ else 1
  have hg : HasProd g (smallDoubledFourierReferenceProduct w s)⁻¹ := by
    have hfin : HasProd g (∏ p ∈ boundedFourierPrimes w, g p) :=
      hasProd_prod_of_ne_finset_one (s := boundedFourierPrimes w)
      (f := g) (fun p hp ↦ by simp [g, hp])
    have heq : (∏ p ∈ boundedFourierPrimes w, g p) =
        (smallDoubledFourierReferenceProduct w s)⁻¹ := by
      calc
        _ = ∏ p ∈ boundedFourierPrimes w, (doubledFourierReferenceFactor s p)⁻¹ :=
          Finset.prod_congr rfl fun p hp ↦ if_pos hp
        _ = _ := Finset.prod_inv_distrib (fun p : Nat.Primes ↦ doubledFourierReferenceFactor s p)
    exact heq ▸ hfin
  have h := (hasProd_doubledFourierReferenceFactor s hRe).mul hg
  convert! h using 1
  · ext p
    have hp0 := doubledFourierReferenceFactor_ne_zero s
      (by exact_mod_cast p.property.two_le) (fun i b ↦ (hRe i b).le)
    by_cases hwp : w < p.val
    · simp [roughDoubledFourierReferenceFactor, g, mem_boundedFourierPrimes,
        hwp, not_le.mpr hwp]
    · simp [roughDoubledFourierReferenceFactor, g, mem_boundedFourierPrimes,
        hwp, Nat.le_of_not_gt hwp, hp0]

theorem tprod_roughDoubledFourierReferenceFactor_ne_zero {ι : Type*} [Fintype ι]
    (w : ℕ) (s : (ι ⊕ ι) → Bool → ℂ) (hRe : ∀ i b, 0 < (s i b).re) :
    (∏' p : Nat.Primes, roughDoubledFourierReferenceFactor w s p) ≠ 0 := by
  rw [(hasProd_roughDoubledFourierReferenceFactor w s hRe).tprod_eq]
  exact div_ne_zero (doubledFourierReferenceZetaProduct_ne_zero s hRe)
    (smallDoubledFourierReferenceProduct_ne_zero w s (fun i b ↦ (hRe i b).le))

end

end Erdos4b

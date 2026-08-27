import ErdosProblems.Erdos4.FGKMTSmallMaskProduct

/-! The actual nonnegative rational sieve square and its exact unit Fourier inversion. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open LocalOrthogonality ProductFourierInversion

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

noncomputable def rationalUnitAmplitude (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (u : ∀ p, (ZMod (ell p))ˣ) : ℝ :=
  ∑ a : P → Option (Fin k), rationalCoefficient b R ell a *
    ∏ p, extendedBasis (ell p : ℝ) (a p)
      (RootStates.rootState (Finset.univ.erase j) (AnchorRoots.anchorRoot (h p) j) (u p))

noncomputable def rationalUnitSquare (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (u : ∀ p, (ZMod (ell p))ˣ) : ℝ := rationalUnitAmplitude ell b R h j u ^ 2

theorem rationalUnitSquare_nonneg (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (u : ∀ p, (ZMod (ell p))ˣ) : 0 ≤ rationalUnitSquare ell b R h j u := sq_nonneg _

theorem rationalUnitFourier_eq_transform (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) :
    rationalUnitFourier ell b R h j χ =
      transform ell (fun u => (rationalUnitSquare ell b R h j u : ℂ)) χ := by
  simp only [rationalUnitFourier, transform, value, star_prod,
    rationalUnitSquare, rationalUnitAmplitude, TensorMoments.amplitude,
    Complex.ofReal_pow, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod]

theorem rationalUnitSquare_inversion (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (u : ∀ p, (ZMod (ell p))ˣ) :
    (∑ χ : ∀ p, DirichletCharacter ℂ (ell p),
      rationalUnitFourier ell b R h j χ * value ell χ u) =
        (rationalUnitSquare ell b R h j u : ℂ) := by
  simp_rw [rationalUnitFourier_eq_transform]
  exact inversion ell (fun u => (rationalUnitSquare ell b R h j u : ℂ)) u

end Erdos4.FGKMT

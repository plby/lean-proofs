import ErdosProblems.Erdos4.FGKMTSieveCoefficients
import ErdosProblems.Erdos4.ProductCharacterMatrix

/-! The actual product-character transform of the rational-cutoff sieve amplitude. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients LocalOrthogonality AnchorRoots Classical

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem rationalCoefficient_ne_zero_cutoff (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (a : P → Option (Fin k)) (ha : rationalCoefficient b R ell a ≠ 0) : totalDivisor ell a ≤ R := by
  by_contra hh
  simp only [rationalCoefficient, if_neg hh, ne_eq, not_true_eq_false] at ha

theorem rational_tensorForm_eq_zero_of_large_conductor (b : ℝ) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P)
    (hlarge : R ^ 2 < ∏ p ∈ J, ell p)
    (M : P → Option (Fin k) → Option (Fin k) → ℂ)
    (hzero : ∀ p ∈ J, M p none none = 0) :
    ConductorSupport.tensorForm (rationalCoefficient b R ell) M = 0 := by
  unfold ConductorSupport.tensorForm
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro c _
  by_cases ha : rationalCoefficient b R ell a = 0
  · simp [ha]
  by_cases hc : rationalCoefficient b R ell c = 0
  · simp [hc]
  have hex : ∃ p ∈ J, a p = none ∧ c p = none := by
    by_contra hn
    push Not at hn
    have hcover : ∀ p ∈ J, a p ≠ none ∨ c p ≠ none := by
      intro p hp
      by_cases hpa : a p = none
      · exact Or.inr (hn p hp hpa)
      · exact Or.inl hpa
    have hh := (ConductorSupport.conductorProduct_le ell hell J a c hcover).trans
      (Nat.mul_le_mul (rationalCoefficient_ne_zero_cutoff b R ell a ha)
        (rationalCoefficient_ne_zero_cutoff b R ell c hc))
    nlinarith
  obtain ⟨p, hp, hpa, hpc⟩ := hex
  have hprod : (∏ q, M q (a q) (c q)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ p) (by simpa only [hpa, hpc] using hzero p hp)
  rw [hprod, mul_zero]

theorem rationalCoefficient_moment_factorization {U : P → Type*} [∀ p, Fintype (U p)]
    (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (state : ∀ p, U p → Option (Fin k)) (weight : ∀ p, U p → ℂ) :
    (∑ u : ∀ p, U p, (∏ p, weight p (u p)) *
      TensorMoments.amplitude (fun a => (rationalCoefficient b R ell a : ℂ))
        (fun p a t => (extendedBasis (ell p : ℝ) a (state p t) : ℂ)) u ^ 2) =
      ConductorSupport.tensorForm (rationalCoefficient b R ell)
        (fun p a c => ∑ t : U p, weight p t *
          ((extendedBasis (ell p : ℝ) a (state p t) : ℂ) *
            (extendedBasis (ell p : ℝ) c (state p t) : ℂ))) := by
  simpa only [pow_two, ConductorSupport.tensorForm] using
    TensorMoments.moment_factorization (fun a => (rationalCoefficient b R ell a : ℂ))
      (fun a => (rationalCoefficient b R ell a : ℂ))
      (fun p a t => (extendedBasis (ell p : ℝ) a (state p t) : ℂ)) weight

variable (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

noncomputable def rationalRawFourier (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) : ℂ :=
  ∑ u : ∀ p, (ZMod (ell p))ˣ,
    (∏ p, (ell p : ℂ)⁻¹ * star (χ p (u p : ZMod (ell p)))) *
      TensorMoments.amplitude (fun a => (rationalCoefficient b R ell a : ℂ))
        (fun p a t => (extendedBasis (ell p : ℝ) a
          (RootStates.rootState (Finset.univ.erase j) (anchorRoot (h p) j) t) : ℂ)) u ^ 2

theorem rationalRawFourier_eq_tensor (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) :
    rationalRawFourier ell b R h j χ = ConductorSupport.tensorForm (rationalCoefficient b R ell)
      (fun p => LocalCharacterMatrix.characterMatrix (χ p) (h p) j) := by
  have hh := rationalCoefficient_moment_factorization b R ell
    (fun p t => RootStates.rootState (Finset.univ.erase j) (anchorRoot (h p) j) t)
    (fun p t => (ell p : ℂ)⁻¹ * star (χ p (t : ZMod (ell p))))
  have hlocal : ∀ p a c,
      (∑ t : (ZMod (ell p))ˣ, ((ell p : ℂ)⁻¹ * star (χ p (t : ZMod (ell p)))) *
        ((extendedBasis (ell p : ℝ) a
          (RootStates.rootState (Finset.univ.erase j) (anchorRoot (h p) j) t) : ℂ) *
          (extendedBasis (ell p : ℝ) c
            (RootStates.rootState (Finset.univ.erase j) (anchorRoot (h p) j) t) : ℂ))) =
        LocalCharacterMatrix.characterMatrix (χ p) (h p) j a c := by
    intro p a c
    unfold LocalCharacterMatrix.characterMatrix
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp_rw [hlocal] at hh
  exact hh

theorem rationalRawFourier_eq_zero_of_large_conductor (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P)
    (hχ : ∀ p ∈ J, χ p ≠ 1) (hlarge : R ^ 2 < ∏ p ∈ J, ell p) :
    rationalRawFourier ell b R h j χ = 0 := by
  rw [rationalRawFourier_eq_tensor]
  apply rational_tensorForm_eq_zero_of_large_conductor b R ell
    (fun p => (Fact.out : (ell p).Prime).one_le) J hlarge
  intro p hp
  unfold LocalCharacterMatrix.characterMatrix
  simp only [extendedBasis, Complex.ofReal_one, one_mul, mul_one]
  rw [LocalCharacterMatrix.sum_star_units_eq_zero (χ p) (hχ p hp), mul_zero]

end Erdos4.FGKMT

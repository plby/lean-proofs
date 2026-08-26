import ErdosProblems.Erdos4.LocalCharacterMatrix
import ErdosProblems.Erdos4.TensorMoments

/-!
# Product-character coefficients of the actual cutoff amplitude

The average is normalized by the product of the primes, rather than by the
size of the unit group. Dividing by the later Euler factor gives the usual
unit-group Fourier coefficient. This module proves the exact tensor
identity and the `R^2` conductor support for this actual character average.
-/

open scoped BigOperators

namespace Erdos4.ProductCharacterMatrix

open LocalOrthogonality AnchorRoots DivisorCoefficients

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

noncomputable def fourierCoefficient (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) : ℂ :=
  ∑ u : ∀ p, (ZMod (ell p))ˣ,
    (∏ p, (ell p : ℂ)⁻¹ * star (chi p (u p : ZMod (ell p)))) *
      TensorMoments.amplitude (fun a => (coefficient m R ell a : ℂ))
        (fun p a t => (extendedBasis (ell p : ℝ) a
          (RootStates.rootState (Finset.univ.erase j) (anchorRoot (h p) j) t) : ℂ)) u ^ 2

theorem fourierCoefficient_eq_tensor (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) :
    fourierCoefficient ell m R h j chi =
      ConductorSupport.tensorForm (coefficient m R ell)
        (fun p => LocalCharacterMatrix.characterMatrix (chi p) (h p) j) := by
  have hh := TensorMoments.coefficient_moment_factorization m R ell
    (fun p t => RootStates.rootState (Finset.univ.erase j) (anchorRoot (h p) j) t)
    (fun p t => (ell p : ℂ)⁻¹ * star (chi p (t : ZMod (ell p))))
  have hlocal : ∀ p a b,
      (∑ t : (ZMod (ell p))ˣ, ((ell p : ℂ)⁻¹ * star (chi p (t : ZMod (ell p)))) *
        ((extendedBasis (ell p : ℝ) a
          (RootStates.rootState (Finset.univ.erase j) (anchorRoot (h p) j) t) : ℂ) *
          (extendedBasis (ell p : ℝ) b
            (RootStates.rootState (Finset.univ.erase j) (anchorRoot (h p) j) t) : ℂ))) =
        LocalCharacterMatrix.characterMatrix (chi p) (h p) j a b := by
    intro p a b
    unfold LocalCharacterMatrix.characterMatrix
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _ht
    ring
  simp_rw [hlocal] at hh
  exact hh

/-- An actual product character with conductor above `R^2` has coefficient zero. -/
theorem fourierCoefficient_eq_zero_of_large_conductor (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P)
    (hchi : ∀ p ∈ J, chi p ≠ 1) (hlarge : R ^ 2 < ∏ p ∈ J, ell p) :
    fourierCoefficient ell m R h j chi = 0 := by
  rw [fourierCoefficient_eq_tensor]
  apply ConductorSupport.tensorForm_eq_zero_of_large_conductor m R ell
    (fun p => (Fact.out : (ell p).Prime).one_le) J hlarge
  intro p hp
  rw [LocalCharacterMatrix.characterMatrix_eq_twisted (chi p) (hchi p hp) (h p) (hh p) j]
  exact ConductorSupport.twistedMatrix_none_none _ j _

end Erdos4.ProductCharacterMatrix

import ErdosProblems.Erdos4.UnitFourier
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Exact inversion over the product of local unit groups

Local Dirichlet-character orthogonality gives inversion for every
function on the finite product. Applying it to the actual anchored
amplitude square uses exactly the Fourier coefficients already estimated.
-/

open scoped BigOperators

namespace Erdos4.ProductFourierInversion

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

noncomputable def value (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (u : ∀ p, (ZMod (ell p))ˣ) : ℂ := ∏ p, chi p (u p : ZMod (ell p))

theorem local_orthogonality (p : P) (u v : (ZMod (ell p))ˣ) :
    (∑ chi : DirichletCharacter ℂ (ell p),
      star (chi (u : ZMod (ell p))) * chi (v : ZMod (ell p))) =
      if u = v then (Fintype.card (ZMod (ell p))ˣ : ℂ) else 0 := by
  classical
  simp only [MulChar.star_apply', MulChar.inv_apply']
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit (v : ZMod (ell p)),
    ZMod.card_units_eq_totient]
  have heq : (u : ZMod (ell p)) = (v : ZMod (ell p)) ↔ u = v := Units.val_inj
  simp only [heq]

theorem orthogonality (u v : ∀ p, (ZMod (ell p))ˣ) :
    (∑ chi : ∀ p, DirichletCharacter ℂ (ell p), star (value ell chi u) * value ell chi v) =
      if u = v then (Fintype.card (∀ p, (ZMod (ell p))ˣ) : ℂ) else 0 := by
  classical
  unfold value
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun p (chi : DirichletCharacter ℂ (ell p)) =>
    star (chi (u p : ZMod (ell p))) * chi (v p : ZMod (ell p)))]
  simp_rw [local_orthogonality ell]
  by_cases huv : u = v
  · subst v
    simp [Fintype.card_pi, Nat.cast_prod]
  · rw [if_neg huv]
    have hex : ∃ p, u p ≠ v p := by
      by_contra h
      apply huv
      funext p
      exact not_ne_iff.mp (fun hp => h ⟨p, hp⟩)
    obtain ⟨p, hp⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

noncomputable def transform (F : (∀ p, (ZMod (ell p))ˣ) → ℂ)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) : ℂ :=
  (Fintype.card (∀ p, (ZMod (ell p))ˣ) : ℂ)⁻¹ *
    ∑ u, star (value ell chi u) * F u

theorem inversion (F : (∀ p, (ZMod (ell p))ˣ) → ℂ)
    (v : ∀ p, (ZMod (ell p))ˣ) :
    (∑ chi : ∀ p, DirichletCharacter ℂ (ell p), transform ell F chi * value ell chi v) = F v := by
  classical
  have hc : (Fintype.card (∀ p, (ZMod (ell p))ˣ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (Fintype.card (∀ p, (ZMod (ell p))ˣ) : ℂ)⁻¹ *
        ∑ chi : ∀ p, DirichletCharacter ℂ (ell p),
          ∑ u : ∀ p, (ZMod (ell p))ˣ, (star (value ell chi u) * value ell chi v) * F u := by
      unfold transform
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _hchi
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro u _hu
      ring
    _ = (Fintype.card (∀ p, (ZMod (ell p))ˣ) : ℂ)⁻¹ *
        ∑ u : ∀ p, (ZMod (ell p))ˣ, F u *
          ∑ chi : ∀ p, DirichletCharacter ℂ (ell p), star (value ell chi u) * value ell chi v := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun chi _hchi => mul_comm _ _)
    _ = F v := by
      simp_rw [orthogonality ell]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp

theorem actual_coefficient_inversion {k : ℕ} (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k) (u : ∀ p, (ZMod (ell p))ˣ) :
    (∑ chi : ∀ p, DirichletCharacter ℂ (ell p),
      UnitFourier.coefficient ell m R h j chi * value ell chi u) =
      TensorMoments.amplitude (fun a => (DivisorCoefficients.coefficient m R ell a : ℂ))
        (fun p a t => (LocalOrthogonality.extendedBasis (ell p : ℝ) a
          (RootStates.rootState (Finset.univ.erase j) (AnchorRoots.anchorRoot (h p) j) t) : ℂ)) u ^ 2 := by
  simpa only [transform, value, star_prod, UnitFourier.coefficient] using
    inversion ell (fun u =>
      TensorMoments.amplitude (fun a => (DivisorCoefficients.coefficient m R ell a : ℂ))
        (fun p a t => (LocalOrthogonality.extendedBasis (ell p : ℝ) a
          (RootStates.rootState (Finset.univ.erase j) (AnchorRoots.anchorRoot (h p) j) t) : ℂ)) u ^ 2) u

end Erdos4.ProductFourierInversion

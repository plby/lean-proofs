import ErdosProblems.Erdos4.AnchorRoots
import ErdosProblems.Erdos4.CharacterCorrelations
import Mathlib.Data.Nat.Totient

/-!
# The actual local Dirichlet-character matrix

The phase is the conjugate of a Dirichlet character on the unit group of a
prime field. Nonprincipal cancellation identifies its matrix with the
twisted matrix already bounded in the divisor-weighted norm.
-/

open scoped BigOperators

namespace Erdos4.LocalCharacterMatrix

open LocalOrthogonality AnchorRoots

theorem sum_units_eq_zero {d : ℕ} [NeZero d]
    (chi : DirichletCharacter ℂ d) (hchi : chi ≠ 1) :
    (∑ t : (ZMod d)ˣ, chi (t : ZMod d)) = 0 := by
  obtain ⟨b, hb⟩ := MulChar.ne_one_iff.mp hchi
  apply eq_zero_of_mul_eq_self_left hb
  simpa only [Equiv.coe_mulLeft, Units.val_mul, map_mul, Finset.mul_sum] using
    Equiv.sum_comp (Equiv.mulLeft b) (fun t : (ZMod d)ˣ => chi (t : ZMod d))

theorem sum_star_units_eq_zero {d : ℕ} [NeZero d]
    (chi : DirichletCharacter ℂ d) (hchi : chi ≠ 1) :
    (∑ t : (ZMod d)ˣ, star (chi (t : ZMod d))) = 0 := by
  rw [← star_sum, sum_units_eq_zero chi hchi, star_zero]

variable {ell k : ℕ} [Fact ell.Prime]

noncomputable def characterMatrix (chi : DirichletCharacter ℂ ell)
    (h : Fin k → ZMod ell) (j : Fin k) (a b : Option (Fin k)) : ℂ :=
  (ell : ℂ)⁻¹ * ∑ t : (ZMod ell)ˣ, star (chi (t : ZMod ell)) *
    ((extendedBasis (ell : ℝ) a (RootStates.rootState (Finset.univ.erase j) (anchorRoot h j) t) : ℂ) *
      (extendedBasis (ell : ℝ) b (RootStates.rootState (Finset.univ.erase j) (anchorRoot h j) t) : ℂ))

theorem characterMatrix_eq_twisted (chi : DirichletCharacter ℂ ell) (hchi : chi ≠ 1)
    (h : Fin k → ZMod ell) (hh : Function.Injective h) (j : Fin k) :
    characterMatrix chi h j = LocalFourier.twistedMatrix (ell : ℝ) j
      (fun i => star (chi (anchorRoot h j i : ZMod ell))) := by
  funext a b
  exact RootStates.twisted_rootState_matrix (ell : ℝ) j (anchorRoot h j)
    (anchorRoot_injective h hh j) (fun t : (ZMod ell)ˣ => star (chi (t : ZMod ell)))
    (sum_star_units_eq_zero chi hchi) a b

/-- The local decay estimate now applies to actual nonprincipal characters. -/
theorem weighted_characterMatrix_le (hell : k + 2 ≤ ell)
    (chi : DirichletCharacter ℂ ell) (hchi : chi ≠ 1)
    (h : Fin k → ZMod ell) (hh : Function.Injective h) (j : Fin k) :
    LocalFourier.weightedMatrixNorm (DivisorCoefficients.localWeight ell)
      (characterMatrix chi h j) ≤ 20 * (k : ℝ) ^ 3 / ell := by
  rw [characterMatrix_eq_twisted chi hchi h hh j]
  apply LocalFourier.weighted_twistedMatrix_le hell j
  intro i
  rw [norm_star]
  exact chi.norm_le_one _

/-- The principal character has the exact anchored-state frequencies. -/
theorem principal_characterMatrix (h : Fin k → ZMod ell) (hh : Function.Injective h)
    (j : Fin k) (a b : Option (Fin k)) :
    characterMatrix 1 h j a b =
      (((ell : ℂ) - k) / ell) *
        ((extendedBasis (ell : ℝ) a none : ℂ) * (extendedBasis (ell : ℝ) b none : ℂ)) +
      (ell : ℂ)⁻¹ * ∑ i ∈ Finset.univ.erase j,
        (extendedBasis (ell : ℝ) a (some i) : ℂ) * (extendedBasis (ell : ℝ) b (some i) : ℂ) := by
  have hcard : (Fintype.card (ZMod ell)ˣ : ℂ) = (ell : ℂ) - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : ell.Prime),
      Nat.cast_sub (Fact.out : ell.Prime).one_le, Nat.cast_one]
  unfold characterMatrix
  simp only [MulChar.one_apply_coe, star_one, one_mul]
  exact RootStates.normalized_sum_rootState (ell : ℝ) j (anchorRoot h j)
    (anchorRoot_injective h hh j) hcard
    (fun s => (extendedBasis (ell : ℝ) a s : ℂ) * (extendedBasis (ell : ℝ) b s : ℂ))

def deletionMask (j : Fin k) (s : Option (Fin k)) : ℝ := if s = some j then 0 else 1

theorem deletionMask_nonneg (j : Fin k) (s : Option (Fin k)) : 0 ≤ deletionMask j s := by
  unfold deletionMask
  split_ifs <;> norm_num

theorem deletionMask_le_one (j : Fin k) (s : Option (Fin k)) : deletionMask j s ≤ 1 := by
  unfold deletionMask
  split_ifs <;> norm_num

theorem mean_deletionMask (ell : ℝ) (j : Fin k) (f : Option (Fin k) → ℝ) :
    mean ell (fun s => deletionMask j s * f s) =
      ((ell - k) / ell) * f none + (1 / ell) * ∑ i ∈ Finset.univ.erase j, f (some i) := by
  have hsum : (∑ i : Fin k, deletionMask j (some i) * f (some i)) =
      ∑ i ∈ Finset.univ.erase j, f (some i) := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin k))
      (fun i => deletionMask j (some i) * f (some i)) (Finset.mem_univ j)]
    simp only [deletionMask, ↓reduceIte, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Option.some.injEq, if_neg (Finset.ne_of_mem_erase hi), one_mul]
  unfold mean
  rw [hsum]
  simp only [deletionMask, reduceCtorEq, ↓reduceIte, one_mul]

/-- The principal local character matrix is exactly the deletion projection. -/
theorem principal_characterMatrix_eq_mean (h : Fin k → ZMod ell)
    (hh : Function.Injective h) (j : Fin k) (a b : Option (Fin k)) :
    characterMatrix 1 h j a b =
      (mean (ell : ℝ) (fun s => deletionMask j s *
        (extendedBasis (ell : ℝ) a s * extendedBasis (ell : ℝ) b s)) : ℂ) := by
  rw [principal_characterMatrix h hh j a b, mean_deletionMask]
  push_cast
  rw [one_div]

end Erdos4.LocalCharacterMatrix

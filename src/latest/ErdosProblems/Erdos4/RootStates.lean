import ErdosProblems.Erdos4.LocalFourier

/-!
# Local states and their twisted finite averages

Each occupied state occurs at its own root. All other residues have the
unoccupied state. A phase with sum zero leaves exactly the differences of
occupied and unoccupied evaluation matrices used in `LocalFourier`.
-/

open scoped BigOperators

namespace Erdos4.RootStates

variable {T : Type*} {k : ℕ}

noncomputable def rootState (S : Finset (Fin k)) (root : Fin k → T) (t : T) : Option (Fin k) := by
  classical
  exact if h : ∃ i : S, root i = t then some (Classical.choose h).val else none

theorem rootState_at_root (S : Finset (Fin k)) (root : Fin k → T)
    (hroot : Function.Injective (fun i : S => root i)) (i : S) :
    rootState S root (root i) = some i.val := by
  have hex : ∃ j : S, root j = root i := ⟨i, rfl⟩
  have hi : Classical.choose hex = i := hroot (Classical.choose_spec hex)
  simp only [rootState, dif_pos hex, hi]

theorem rootState_of_no_root (S : Finset (Fin k)) (root : Fin k → T) (t : T)
    (ht : ¬∃ i : S, root i = t) : rootState S root t = none := by
  simp only [rootState, dif_neg ht]

theorem rootState_eq_some_iff (S : Finset (Fin k)) (root : Fin k → T)
    (hroot : Function.Injective (fun i : S => root i)) (t : T) (i : Fin k) :
    rootState S root t = some i ↔ i ∈ S ∧ root i = t := by
  classical
  constructor
  · intro hi
    by_cases ht : ∃ a : S, root a = t
    · have hval : (Classical.choose ht).val = i := by
        simpa only [rootState, dif_pos ht, Option.some.injEq] using hi
      exact ⟨hval ▸ (Classical.choose ht).property, hval ▸ Classical.choose_spec ht⟩
    · simp only [rootState_of_no_root S root t ht, reduceCtorEq] at hi
  · rintro ⟨hi, ht⟩
    rw [← ht]
    exact rootState_at_root S root hroot ⟨i, hi⟩

theorem value_rootState [DecidableEq T] (S : Finset (Fin k)) (root : Fin k → T)
    (hroot : Function.Injective (fun i : S => root i)) (f : Option (Fin k) → ℂ) (t : T) :
    f (rootState S root t) = f none +
      ∑ i : S, if root i = t then f (some i.val) - f none else 0 := by
  classical
  by_cases ht : ∃ i : S, root i = t
  · obtain ⟨i, rfl⟩ := ht
    rw [rootState_at_root S root hroot i]
    have hsum : (∑ j : S, if root j = root i then f (some j.val) - f none else 0) =
        f (some i.val) - f none := by
      have heq : ∀ j : S, root j = root i ↔ j = i := fun j => hroot.eq_iff
      simp only [heq]
      simp
    rw [hsum]
    ring
  · rw [rootState_of_no_root S root t ht]
    have hi : ∀ i : S, root i ≠ t := by simpa only [not_exists] using ht
    simp only [hi, ↓reduceIte, Finset.sum_const_zero, add_zero]

theorem sum_weighted_rootState [Fintype T] (S : Finset (Fin k)) (root : Fin k → T)
    (hroot : Function.Injective (fun i : S => root i)) (f : Option (Fin k) → ℂ) (w : T → ℂ) :
    (∑ t : T, w t * f (rootState S root t)) =
      (∑ t : T, w t) * f none + ∑ i : S, w (root i) * (f (some i.val) - f none) := by
  classical
  simp_rw [value_rootState S root hroot f, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [mul_ite, mul_zero]
  simp

/-- The cancellation of the background state uses only the zero phase sum. -/
theorem sum_weighted_rootState_of_sum_zero [Fintype T]
    (S : Finset (Fin k)) (root : Fin k → T)
    (hroot : Function.Injective (fun i : S => root i)) (f : Option (Fin k) → ℂ)
    (w : T → ℂ) (hw : ∑ t : T, w t = 0) :
    (∑ t : T, w t * f (rootState S root t)) =
      ∑ i : S, w (root i) * (f (some i.val) - f none) := by
  rw [sum_weighted_rootState S root hroot f w, hw, zero_mul, zero_add]

/-- The principal phase gives precisely the anchored residue-state counts. -/
theorem normalized_sum_rootState [Fintype T] (ell : ℝ) (j : Fin k)
    (root : Fin k → T)
    (hroot : Function.Injective (fun i : (Finset.univ.erase j) => root i))
    (hcard : (Fintype.card T : ℂ) = (ell : ℂ) - 1) (f : Option (Fin k) → ℂ) :
    (ell : ℂ)⁻¹ * ∑ t : T, f (rootState (Finset.univ.erase j) root t) =
      (((ell : ℂ) - k) / ell) * f none +
        (ell : ℂ)⁻¹ * ∑ i ∈ Finset.univ.erase j, f (some i) := by
  have hk : 1 ≤ k := by have := j.isLt; omega
  have hcardS : (Fintype.card (Finset.univ.erase j) : ℂ) = (k : ℂ) - 1 := by
    simp only [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin, Nat.cast_sub hk, Nat.cast_one]
  have hh := sum_weighted_rootState (Finset.univ.erase j) root hroot f (fun _ => 1)
  simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Finset.sum_sub_distrib] at hh
  rw [hcard, hcardS, Finset.sum_coe_sort (Finset.univ.erase j) (fun i => f (some i))] at hh
  rw [hh]
  simp only [div_eq_mul_inv]
  ring

/-- Exact identification of the nonprincipal local Fourier matrix. -/
theorem twisted_rootState_matrix [Fintype T] (ell : ℝ) (j : Fin k) (root : Fin k → T)
    (hroot : Function.Injective (fun i : (Finset.univ.erase j) => root i))
    (w : T → ℂ) (hw : ∑ t : T, w t = 0) (a b : Option (Fin k)) :
    (ell : ℂ)⁻¹ * ∑ t : T, w t *
      ((LocalOrthogonality.extendedBasis ell a (rootState (Finset.univ.erase j) root t) : ℂ) *
        (LocalOrthogonality.extendedBasis ell b (rootState (Finset.univ.erase j) root t) : ℂ)) =
      LocalFourier.twistedMatrix ell j (fun i => w (root i)) a b := by
  have hh := sum_weighted_rootState_of_sum_zero (Finset.univ.erase j) root hroot
    (fun s => (LocalOrthogonality.extendedBasis ell a s : ℂ) *
      (LocalOrthogonality.extendedBasis ell b s : ℂ)) w hw
  rw [hh]
  unfold LocalFourier.twistedMatrix LocalFourier.evaluationDifference
  congr 1
  rw [Finset.sum_coe_sort (Finset.univ.erase j)
    (fun i => w (root i) *
      ((LocalOrthogonality.extendedBasis ell a (some i) : ℂ) *
        (LocalOrthogonality.extendedBasis ell b (some i) : ℂ) -
        (LocalOrthogonality.extendedBasis ell a none : ℂ) *
          (LocalOrthogonality.extendedBasis ell b none : ℂ)))]
  simp only [Complex.ofReal_mul]

end Erdos4.RootStates

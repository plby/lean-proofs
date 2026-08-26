import ErdosProblems.Erdos4.RootStates

/-!
# The roots of the anchored affine forms

For distinct shifts over a field, the non-anchor forms vanish at distinct
nonzero ratios. These are the exact roots used by the local Fourier matrix.
-/

open scoped BigOperators

namespace Erdos4.AnchorRoots

variable {F : Type*} [Field F] {k : ℕ}

noncomputable def anchorRoot (h : Fin k → F) (j i : Fin k) : Fˣ := by
  classical
  exact if hd : h i - h j ≠ 0 then -(Units.mk0 (h i - h j) hd)⁻¹ else 1

theorem anchorRoot_coe (h : Fin k → F) (hh : Function.Injective h)
    (j i : Fin k) (hij : i ≠ j) :
    (anchorRoot h j i : F) = -(h i - h j)⁻¹ := by
  have hd : h i - h j ≠ 0 := sub_ne_zero.mpr (fun heq => hij (hh heq))
  simp [anchorRoot, hd]

theorem anchorRoot_injective (h : Fin k → F) (hh : Function.Injective h) (j : Fin k) :
    Function.Injective (fun i : (Finset.univ.erase j) => anchorRoot h j i) := by
  intro a b hab
  have hac := anchorRoot_coe h hh j a (Finset.ne_of_mem_erase a.property)
  have hbc := anchorRoot_coe h hh j b (Finset.ne_of_mem_erase b.property)
  have heq := congrArg (fun u : Fˣ => (u : F)) hab
  rw [hac, hbc] at heq
  have hd : h a - h j = h b - h j := inv_injective (neg_injective heq)
  exact Subtype.ext (hh (sub_left_injective hd))

theorem anchorRoot_eq_iff (h : Fin k → F) (hh : Function.Injective h)
    (j i : Fin k) (hij : i ≠ j) (t : Fˣ) :
    anchorRoot h j i = t ↔ 1 + (h i - h j) * (t : F) = 0 := by
  have hd : h i - h j ≠ 0 := sub_ne_zero.mpr (fun heq => hij (hh heq))
  rw [← Units.val_inj, anchorRoot_coe h hh j i hij]
  constructor
  · intro ht
    rw [← ht]
    field_simp
    ring
  · intro ht
    field_simp
    linear_combination -ht

/-- The residue state records precisely which anchored form vanishes. -/
theorem rootState_eq_some_iff (h : Fin k → F) (hh : Function.Injective h)
    (j i : Fin k) (t : Fˣ) :
    RootStates.rootState (Finset.univ.erase j) (anchorRoot h j) t = some i ↔
      1 + (h i - h j) * (t : F) = 0 := by
  rw [RootStates.rootState_eq_some_iff _ _ (anchorRoot_injective h hh j)]
  constructor
  · rintro ⟨hi, ht⟩
    exact (anchorRoot_eq_iff h hh j i (Finset.ne_of_mem_erase hi) t).mp ht
  · intro ht
    have hij : i ≠ j := by
      intro heq
      subst i
      simp at ht
    exact ⟨Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩,
      (anchorRoot_eq_iff h hh j i hij t).mpr ht⟩

theorem anchored_form_zero_iff (h : Fin k → F) (j i : Fin k) (p q : F) (hq : q ≠ 0) :
    (q - h j * p) + h i * p = 0 ↔ 1 + (h i - h j) * (p / q) = 0 := by
  field_simp
  constructor <;> intro hh <;> linear_combination hh

end Erdos4.AnchorRoots

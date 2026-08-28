import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionBasic

/-!
# The inverse of an actual barycentric face map

Deleting the vanishing coordinate is a continuous inverse to Mathlib's
cosimplicial face map on its precise geometric range.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

/-- Delete the vanishing coordinate on the geometric `i`-th face. -/
def simplexFaceInverse (n : ℕ) (i : Fin (n + 2)) :
    C({s : Simplex (n + 1) // s i = 0}, Simplex n) where
  toFun s := ⟨fun k => s.val (i.succAbove k),
    ⟨fun k => stdSimplex.zero_le s.val (i.succAbove k), by
      have hs := stdSimplex.sum_eq_one s.val
      rw [Fin.sum_univ_succAbove _ i, s.property, zero_add] at hs
      exact hs⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    have hc : Continuous (fun s : Simplex (n + 1) => s (i.succAbove k)) :=
      (continuous_apply (i.succAbove k)).comp continuous_subtype_val
    exact hc.comp continuous_subtype_val

@[simp] theorem simplexFaceInverse_apply (n : ℕ) (i : Fin (n + 2))
    (s : {s : Simplex (n + 1) // s i = 0}) (k : Fin (n + 1)) :
    simplexFaceInverse n i s k = s.val (i.succAbove k) := rfl

/-- Restoring the deleted coordinate recovers the original face point. -/
@[simp] theorem simplexFace_inverse (n : ℕ) (i : Fin (n + 2))
    (s : {s : Simplex (n + 1) // s i = 0}) :
    simplexFace n i (simplexFaceInverse n i s) = s.val := by
  apply Subtype.ext
  funext k
  change simplexFace n i (simplexFaceInverse n i s) k = s.val k
  by_cases hk : k = i
  · subst k
    exact (simplexFace_apply_self n i _).trans s.property.symm
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
    exact simplexFace_apply_succAbove n i _ l

/-- Deleting the coordinate inserted by an actual face map is the identity. -/
@[simp] theorem simplexFaceInverse_face (n : ℕ) (i : Fin (n + 2))
    (s : Simplex n) :
    simplexFaceInverse n i ⟨simplexFace n i s, simplexFace_apply_self n i s⟩ = s := by
  apply Subtype.ext
  funext k
  change simplexFace n i s (i.succAbove k) = s k
  exact simplexFace_apply_succAbove n i s k

/-- The range of an actual face map is exactly its zero-coordinate face. -/
theorem simplexFace_range (n : ℕ) (i : Fin (n + 2)) :
    range (simplexFace n i) = {s : Simplex (n + 1) | s i = 0} := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact simplexFace_apply_self n i t
  · intro hs
    exact ⟨simplexFaceInverse n i ⟨s, hs⟩, simplexFace_inverse n i ⟨s, hs⟩⟩

@[simp] theorem simplexFace_mem_range_iff (n : ℕ) (i : Fin (n + 2))
    (s : Simplex (n + 1)) :
    s ∈ range (simplexFace n i) ↔ s i = 0 := by
  rw [simplexFace_range]
  rfl

theorem simplexFace_injective (n : ℕ) (i : Fin (n + 2)) :
    Function.Injective (simplexFace n i) := by
  intro s t h
  apply Subtype.ext
  funext k
  change s k = t k
  have hk := congrArg (fun u : Simplex (n + 1) => u (i.succAbove k)) h
  simpa only [simplexFace_apply_succAbove] using hk

/-- The actual simplex is homeomorphic to its geometric face. -/
def simplexFaceHomeomorph (n : ℕ) (i : Fin (n + 2)) :
    Simplex n ≃ₜ {s : Simplex (n + 1) // s i = 0} where
  toFun s := ⟨simplexFace n i s, simplexFace_apply_self n i s⟩
  invFun := simplexFaceInverse n i
  left_inv := simplexFaceInverse_face n i
  right_inv s := Subtype.ext (simplexFace_inverse n i s)
  continuous_toFun := (simplexFace n i).continuous.subtype_mk _
  continuous_invFun := (simplexFaceInverse n i).continuous

@[simp] theorem simplexFaceHomeomorph_val (n : ℕ) (i : Fin (n + 2))
    (s : Simplex n) :
    (simplexFaceHomeomorph n i s).val = simplexFace n i s := rfl

@[simp] theorem simplexFaceHomeomorph_symm_apply (n : ℕ) (i : Fin (n + 2))
    (s : {s : Simplex (n + 1) // s i = 0}) :
    (simplexFaceHomeomorph n i).symm s = simplexFaceInverse n i s := rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

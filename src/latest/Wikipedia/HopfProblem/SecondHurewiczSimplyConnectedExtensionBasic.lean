import Wikipedia.HopfProblem.FirstHurewiczSimplex

/-!
# The bottom and side of a standard simplex cylinder

These are literal subsets of Mathlib's barycentric simplex and its product
with the unit interval. No homotopy extension property is assumed.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

/-- The union of the actual barycentric faces. -/
def simplexBoundary (n : ℕ) : Set (Simplex n) :=
  {s | ∃ i : Fin (n + 1), s i = 0}

/-- The actual boundary as a subspace of the simplex. -/
abbrev SimplexBoundary (n : ℕ) := ↥(simplexBoundary n)

/-- The prescribed part of the simplex cylinder: its bottom and its side. -/
def bottomOrSide (n : ℕ) : Set (unitInterval × Simplex n) :=
  {u | u.1 = 0 ∨ u.2 ∈ simplexBoundary n}

theorem isClosed_simplexBoundary (n : ℕ) : IsClosed (simplexBoundary n) := by
  have h : IsClosed (⋃ i : Fin (n + 1), {s : Simplex n | s i = 0}) :=
    isClosed_iUnion_of_finite fun i =>
      isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const
  simpa only [simplexBoundary, ofPred_exists] using h

theorem isClosed_bottomOrSide (n : ℕ) : IsClosed (bottomOrSide n) := by
  exact (isClosed_eq continuous_fst continuous_const).union
    ((isClosed_simplexBoundary n).preimage continuous_snd)

theorem simplexFace_mem_boundary (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    simplexFace n i s ∈ simplexBoundary (n + 1) :=
  ⟨i, simplexFace_apply_self n i s⟩

/-- The inclusion of the bottom into the prescribed subspace. -/
def bottomInclusion (n : ℕ) : C(Simplex n, ↥(bottomOrSide n)) where
  toFun s := ⟨(0, s), Or.inl rfl⟩
  continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _

/-- The inclusion of the side into the prescribed subspace. -/
def sideInclusion (n : ℕ) : C(unitInterval × SimplexBoundary n, ↥(bottomOrSide n)) where
  toFun u := ⟨(u.1, u.2.val), Or.inr u.2.property⟩
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

@[simp] theorem bottomInclusion_val (n : ℕ) (s : Simplex n) :
    (bottomInclusion n s).val = (0, s) := rfl

@[simp] theorem sideInclusion_val (n : ℕ) (u : unitInterval × SimplexBoundary n) :
    (sideInclusion n u).val = (u.1, u.2.val) := rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

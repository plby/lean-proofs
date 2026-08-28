import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyBasic

/-!
# Flat coordinates on the actual barycentric simplex

Discarding coordinate zero identifies the standard `n`-simplex with the
full-dimensional simplex in `ℝⁿ`. The inverse restores that coordinate
as one minus the sum of the remaining coordinates.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz

/-- Discard the zeroth barycentric coordinate. -/
def simplexFlat (n : ℕ) (s : Simplex n) : ↥(flatSimplexSet n) :=
  ⟨fun i => s i.succ, by
    refine ⟨fun i => stdSimplex.zero_le s i.succ, ?_⟩
    have hs := stdSimplex.sum_eq_one s
    rw [Fin.sum_univ_succ] at hs
    have h0 := stdSimplex.zero_le s 0
    linarith⟩

/-- Restore the zeroth barycentric coordinate from the sum. -/
def flatSimplex (n : ℕ) (v : ↥(flatSimplexSet n)) : Simplex n :=
  ⟨Fin.cons (1 - ∑ i, v.val i) v.val, by
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr v.property.2
      · exact v.property.1 j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      exact sub_add_cancel 1 _⟩

@[simp] theorem simplexFlat_apply (n : ℕ) (s : Simplex n) (i : Fin n) :
    (simplexFlat n s).val i = s i.succ := rfl

@[simp] theorem flatSimplex_zero (n : ℕ) (v : ↥(flatSimplexSet n)) :
    flatSimplex n v 0 = 1 - ∑ i, v.val i := rfl

@[simp] theorem flatSimplex_succ (n : ℕ) (v : ↥(flatSimplexSet n)) (i : Fin n) :
    flatSimplex n v i.succ = v.val i := rfl

theorem continuous_simplexFlat (n : ℕ) : Continuous (simplexFlat n) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i =>
    (continuous_apply i.succ).comp continuous_subtype_val

theorem continuous_flatSimplex (n : ℕ) : Continuous (flatSimplex n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const.sub <| continuous_finsetSum _ fun j _ =>
      (continuous_apply j).comp continuous_subtype_val
  · exact (continuous_apply j).comp continuous_subtype_val

@[simp] theorem flatSimplex_simplexFlat (n : ℕ) (s : Simplex n) :
    flatSimplex n (simplexFlat n s) = s := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change 1 - ∑ j : Fin n, s j.succ = s 0
    have hs := stdSimplex.sum_eq_one s
    rw [Fin.sum_univ_succ] at hs
    linarith
  · rfl

@[simp] theorem simplexFlat_flatSimplex (n : ℕ) (v : ↥(flatSimplexSet n)) :
    simplexFlat n (flatSimplex n v) = v := by
  apply Subtype.ext
  rfl

/-- The actual simplex homeomorphism obtained by dropping coordinate zero. -/
def simplexFlatHomeomorph (n : ℕ) : Simplex n ≃ₜ ↥(flatSimplexSet n) where
  toFun := simplexFlat n
  invFun := flatSimplex n
  left_inv := flatSimplex_simplexFlat n
  right_inv := simplexFlat_flatSimplex n
  continuous_toFun := continuous_simplexFlat n
  continuous_invFun := continuous_flatSimplex n

@[simp] theorem simplexFlatHomeomorph_apply (n : ℕ) (s : Simplex n) (i : Fin n) :
    (simplexFlatHomeomorph n s).val i = s i.succ := rfl

@[simp] theorem simplexFlatHomeomorph_symm_zero (n : ℕ) (v : ↥(flatSimplexSet n)) :
    (simplexFlatHomeomorph n).symm v 0 = 1 - ∑ i, v.val i := rfl

@[simp] theorem simplexFlatHomeomorph_symm_succ (n : ℕ)
    (v : ↥(flatSimplexSet n)) (i : Fin n) :
    (simplexFlatHomeomorph n).symm v i.succ = v.val i := rfl

end Wikipedia.HopfProblem.HigherHurewicz

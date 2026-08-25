import StackExchange.Puzzling139335.Definitions
import Mathlib.Data.Fintype.Card

/-!
# At most four pairwise nonacute directions in the plane

Four half-open quadrants cover the nonzero vectors. Two vectors in the same
quadrant have strictly positive inner product, so a family of nonzero vectors
with pairwise nonpositive inner products injects into the four quadrants.
-/

namespace Puzzling139335.CornerSupport

private def InQuadrant (q : Fin 4) (v : Plane) : Prop :=
  if q = 0 then 0 < v 0 ∧ 0 ≤ v 1
  else if q = 1 then v 0 ≤ 0 ∧ 0 < v 1
  else if q = 2 then v 0 < 0 ∧ v 1 ≤ 0
  else 0 ≤ v 0 ∧ v 1 < 0

private theorem exists_quadrant {v : Plane} (hv : v ≠ 0) :
    ∃ q : Fin 4, InQuadrant q v := by
  by_cases hx : 0 < v 0
  · by_cases hy : 0 ≤ v 1
    · exact ⟨0, by simpa [InQuadrant] using And.intro hx hy⟩
    · exact ⟨3, by simpa [InQuadrant] using And.intro hx.le (lt_of_not_ge hy)⟩
  · have hx' : v 0 ≤ 0 := le_of_not_gt hx
    by_cases hy : 0 < v 1
    · exact ⟨1, by simpa [InQuadrant] using And.intro hx' hy⟩
    · have hy' : v 1 ≤ 0 := le_of_not_gt hy
      by_cases hxneg : v 0 < 0
      · exact ⟨2, by simpa [InQuadrant] using And.intro hxneg hy'⟩
      · have hxzero : v 0 = 0 := le_antisymm hx' (le_of_not_gt hxneg)
        have hyneg : v 1 < 0 := by
          by_contra h
          have hyzero : v 1 = 0 := le_antisymm hy' (le_of_not_gt h)
          apply hv
          ext i
          fin_cases i <;> simp [hxzero, hyzero]
        exact ⟨3, by simpa [InQuadrant, hxzero] using hyneg⟩

private theorem inner_pos_of_same_quadrant {q : Fin 4} {u v : Plane}
    (hu : InQuadrant q u) (hv : InQuadrant q v) :
    0 < inner ℝ u v := by
  rw [Schoenflies.Plane.inner_eq]
  fin_cases q <;> dsimp only [InQuadrant] at hu hv
  · exact add_pos_of_pos_of_nonneg (mul_pos hu.1 hv.1) (mul_nonneg hu.2 hv.2)
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg_of_nonpos_of_nonpos hu.1 hv.1) (mul_pos hu.2 hv.2)
  · exact add_pos_of_pos_of_nonneg
      (mul_pos_of_neg_of_neg hu.1 hv.1) (mul_nonneg_of_nonpos_of_nonpos hu.2 hv.2)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hu.1 hv.1)
      (mul_pos_of_neg_of_neg hu.2 hv.2)

/-- A finite family of nonzero planar vectors with pairwise nonpositive inner
products has at most four members. The indexing function need not be assumed
injective: the inner-product condition already excludes repetitions. -/
theorem card_le_four_of_pairwise_nonpos_inner {ι : Type*} (s : Finset ι)
    (f : ι → Plane) (hne : ∀ i ∈ s, f i ≠ 0)
    (hinner : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (f i) (f j) ≤ 0) :
    s.card ≤ 4 := by
  classical
  let q : {i // i ∈ s} → Fin 4 :=
    fun i => (exists_quadrant (hne i.1 i.2)).choose
  have hq : ∀ i : {i // i ∈ s}, InQuadrant (q i) (f i.1) :=
    fun i => (exists_quadrant (hne i.1 i.2)).choose_spec
  have hqinj : Function.Injective q := by
    intro i j hij
    apply Subtype.ext
    by_contra hneij
    have hpos : 0 < inner ℝ (f i.1) (f j.1) :=
      inner_pos_of_same_quadrant (hq i) (hij ▸ hq j)
    exact (not_lt_of_ge (hinner i.1 i.2 j.1 j.2 hneij)) hpos
  simpa using Fintype.card_le_of_injective q hqinj

/-- The special case of vectors with squared norm two, as used for the sums
of two perpendicular unit support normals. -/
theorem card_le_four_of_norm_sq_eq_two {ι : Type*} (s : Finset ι)
    (f : ι → Plane) (hnorm : ∀ i ∈ s, ‖f i‖ ^ 2 = (2 : ℝ))
    (hinner : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (f i) (f j) ≤ 0) :
    s.card ≤ 4 := by
  apply card_le_four_of_pairwise_nonpos_inner s f ?_ hinner
  intro i hi hzero
  have h := hnorm i hi
  simp [hzero] at h

end Puzzling139335.CornerSupport

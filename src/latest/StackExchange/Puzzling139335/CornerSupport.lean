import StackExchange.Puzzling139335.CornerSupport.Frames
import StackExchange.Puzzling139335.CornerSupport.Quadrants
import StackExchange.Puzzling139335.CornerSupport.Bisectors
import Mathlib.Data.Set.Card

/-!
# At most four supporting right corners

At distinct supporting corners, the outward bisectors have nonpositive inner
product.  The half-open quadrant bound therefore gives at most four distinct
corners, without a polygonality or boundary-length assumption.
-/

open Set

namespace Puzzling139335

namespace SupportCorner

/-- The outward bisectors at two distinct supporting right corners form a
nonacute angle. -/
theorem bisectors_inner_nonpos {P : Set Plane} {v w : Plane}
    (hv : SupportCorner P v) (hw : SupportCorner P w) (hvw : v ≠ w) :
    inner ℝ hv.bisector hw.bisector ≤ 0 := by
  have hdelta : w - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hvw)
  have hvproj := hv.bisector_projection hw.mem
  have hwproj := hw.bisector_projection hv.mem
  have hneg : v - w = -(w - v) := by abel
  rw [hneg, inner_neg_right, norm_neg] at hwproj
  have hwproj' : ‖w - v‖ ≤ inner ℝ hw.bisector (w - v) := by linarith
  exact CornerSupport.inner_le_zero_of_opposed_bisectors
    hv.bisector hw.bisector (w - v) hdelta
    hv.bisector_norm_sq hw.bisector_norm_sq hvproj hwproj'

end SupportCorner

namespace CornerSupport

/-- A planar set has at most four distinct supporting right corners. -/
theorem card_le_four {P : Set Plane} (s : Finset Plane)
    (hSupport : ∀ v ∈ s, IsSupportCorner P v) : s.card ≤ 4 := by
  classical
  let frame (v : {v // v ∈ s}) : SupportCorner P v :=
    Classical.choice (hSupport v v.property)
  have hcard : (Finset.univ : Finset {v // v ∈ s}).card ≤ 4 := by
    apply card_le_four_of_norm_sq_eq_two Finset.univ (fun v => (frame v).bisector)
    · intro v _
      exact (frame v).bisector_norm_sq
    · intro v _ w _ hvw
      exact (frame v).bisectors_inner_nonpos (frame w) (fun h => hvw (Subtype.ext h))
  simpa using hcard

/-- The collection of all supporting right corners is finite. -/
theorem supportingCorners_finite (P : Set Plane) : {v | IsSupportCorner P v}.Finite := by
  classical
  by_contra hInfinite
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hInfinite 5
  have hbound := card_le_four s (fun v hv => hs hv)
  omega

/-- The cardinality bound also holds for the entire set of supporting corners. -/
theorem supportingCorners_ncard_le_four (P : Set Plane) :
    {v | IsSupportCorner P v}.ncard ≤ 4 := by
  classical
  rw [Set.ncard_eq_toFinset_card _ (supportingCorners_finite P)]
  apply card_le_four (P := P)
  intro v hv
  simpa using hv

open scoped Classical in
/-- In any finite collection of isometric placements into the square, there
are at most four distinct preimages of occupied square corners. -/
theorem card_image_preimages_le_four {ι : Type*} (s : Finset ι) (P : Set Plane)
    (e : ι → Plane ≃ᵃⁱ[ℝ] Plane) (j : ι → Fin 4)
    (hSubset : ∀ i ∈ s, e i '' P ⊆ unitSquare)
    (hCorner : ∀ i ∈ s, corner (j i) ∈ e i '' P) :
    (s.image fun i => (e i).symm (corner (j i))).card ≤ 4 := by
  apply card_le_four (P := P)
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  exact isSupportCorner_preimage (e i) (hSubset i hi) (j i) (hCorner i hi)

end CornerSupport

end Puzzling139335

import StackExchange.Puzzling139335.N6.Incidence
import StackExchange.Puzzling139335.N7.FullPairNormalization.SquareAction
import StackExchange.Puzzling139335.N4Dispatch.FiniteRouting

/-!
# Common-frame transport for the two-double-corner branch

Only physical corner multiplicities are transported. Intrinsic corner
choices in the new dissection are not identified with old choices.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

noncomputable section

/-- Express an actual placement in a common new Euclidean frame. -/
def frameConjugate (q e : Plane ≃ᵃⁱ[ℝ] Plane) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (q.symm.trans e).trans q

theorem frameConjugate_apply_image (q e : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane) :
    frameConjugate q e (q p) = q (e p) := by
  change q (e (q.symm (q p))) = _
  rw [q.symm_apply_apply]

theorem frameConjugate_image (q e : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) :
    frameConjugate q e '' (q '' P) = q '' (e '' P) := by
  simp only [image_image, frameConjugate_apply_image]

theorem frameConjugate_preserves_square (q e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hq : q '' unitSquare = unitSquare) (he : e '' unitSquare = unitSquare) :
    frameConjugate q e '' unitSquare = unitSquare := by
  calc
    _ = frameConjugate q e '' (q '' unitSquare) := by rw [hq]
    _ = q '' (e '' unitSquare) := frameConjugate_image q e unitSquare
    _ = unitSquare := by rw [he, hq]

theorem hasTwoDoubleCorners_map (d : SquareDissection)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare = unitSquare)
    (hD : HasTwoDoubleCorners d) : HasTwoDoubleCorners (d.map e he) := by
  let π := SquareSymmetry.cornerPermutation e he.subset
  have hπ (a : Fin 4) : e (corner a) = corner (π a) :=
    SquareSymmetry.cornerPermutation_apply e he.subset a
  have hcount (a : Fin 4) : (d.map e he).cornerTileCount (π a) = d.cornerTileCount a :=
    N7.FullPairNormalization.cornerTileCount_map_of_corner_image d e he (hπ a)
  obtain ⟨s, t, hst, hs, ht, hrest⟩ := hD
  refine ⟨π s, π t, π.injective.ne hst, (hcount s).trans hs, (hcount t).trans ht, ?_⟩
  intro a has hat
  have hs' : π.symm a ≠ s := fun h => has (by rw [← h, π.apply_symm_apply])
  have ht' : π.symm a ≠ t := fun h => hat (by rw [← h, π.apply_symm_apply])
  have hc := hcount (π.symm a)
  rw [π.apply_symm_apply] at hc
  exact hc.trans (hrest _ hs' ht')

theorem hasTwoDoubleCorners_reindex (d : SquareDissection)
    (σ : Equiv.Perm (Fin 4)) (hD : HasTwoDoubleCorners d) :
    HasTwoDoubleCorners (d.reindex σ) := by
  simpa only [HasTwoDoubleCorners, SquareDissection.reindex_cornerTileCount] using hD

end

end Puzzling139335.N6.TwoDouble

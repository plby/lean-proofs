import StackExchange.Puzzling139335.N4TwoOneOne.AxisCase
import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Nonzero entries of the fourth placement's top-coordinate row

The first column is non-axis-aligned by the geometric axis exclusion.
Orthogonality of the two matrix rows then excludes a zero final entry.
-/

namespace Puzzling139335.N4TwoOneOne.SourceData

open PlaneIsometries

theorem fourth_top_row_nonzero {d : SquareDissection} {θ u v : ℝ}
    (h : SourceData d θ u v) (hcfg : Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3) :
    linearMatrix e 1 0 ≠ 0 ∧ linearMatrix e 1 1 ≠ 0 := by
  obtain ⟨h00, h10⟩ := fourth_image_column_nonzero hcfg h hc e he
  refine ⟨h10, ?_⟩
  intro h11
  have hprod : linearMatrix e 0 0 * linearMatrix e 1 0 = 0 := by
    simpa [h11] using linearMatrix_row_dot e 0 1
  exact mul_ne_zero h00 h10 hprod

end Puzzling139335.N4TwoOneOne.SourceData

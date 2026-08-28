import Wikipedia.HopfProblem.CuspCircleNormalTrivializationToricTopology

/-!
# The original middle curve is the actual zero section

In the established product homeomorphism, the zero normal vector gives
the unchanged middle axis in both original toric affine charts. This
curve is genuinely embedded, and the inverse normal coordinate vanishes
exactly on its image.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts ToricFan

/-- The unchanged toric curve, parametrized by the actual zero normal vector. -/
def toricZeroSection (p : RiemannSphere) : ToricSpace.Space := fromProduct (p, 0)

/-- The zero section is literally the middle axis in either original affine chart. -/
@[simp] theorem toricZeroSection_affineMap (b : Bool) (a : ℂ) :
    toricZeroSection (RiemannSphere.standardCharts.affineMap b a) =
      ToricSpace.inclusion (chartTriangle b) ![0, a, 0] := by
  change fromProduct (baseProductChart b (a, 0)) = _
  rw [fromProduct_baseProductChart, toricChartMap_apply, chartCoordinates_symm_zero]

/-- The zero section is embedded in the actual toric space. -/
theorem toricZeroSection_isEmbedding : IsEmbedding toricZeroSection :=
  fromProduct_isOpenEmbedding.isEmbedding.comp (isEmbedding_prodMkLeft (0 : Fibre))

theorem toricZeroSection_continuous : Continuous toricZeroSection :=
  toricZeroSection_isEmbedding.continuous

theorem toricZeroSection_injective : Function.Injective toricZeroSection :=
  toricZeroSection_isEmbedding.injective

theorem toricZeroSection_mem (p : RiemannSphere) : toricZeroSection p ∈ toricNeighborhood :=
  fromProduct_mem_toricNeighborhood (p, 0)

/-- The inverse homeomorphism has zero normal coordinate exactly on the original curve. -/
theorem toricNeighborhoodHomeomorph_inverse_fibre_zero_iff (y : toricNeighborhood) :
    (toricNeighborhoodHomeomorph.symm y).2 = 0 ↔
      (y : ToricSpace.Space) ∈ range toricZeroSection := by
  constructor
  · intro hy
    refine ⟨(toricNeighborhoodHomeomorph.symm y).1, ?_⟩
    have hp : ((toricNeighborhoodHomeomorph.symm y).1, (0 : Fibre)) =
        toricNeighborhoodHomeomorph.symm y := Prod.ext rfl hy.symm
    change fromProduct ((toricNeighborhoodHomeomorph.symm y).1, 0) = _
    rw [hp]
    change (toricNeighborhoodHomeomorph (toricNeighborhoodHomeomorph.symm y) :
      ToricSpace.Space) = (y : ToricSpace.Space)
    rw [toricNeighborhoodHomeomorph.apply_symm_apply]
  · rintro ⟨p, hp⟩
    have hy : y = toricNeighborhoodHomeomorph (p, 0) := Subtype.ext hp.symm
    rw [hy, toricNeighborhoodHomeomorph.symm_apply_apply]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization

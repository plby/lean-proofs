import Wikipedia.HopfProblem.CuspCircleNormalTrivializationToricZeroSection
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationGeometry

/-!
# The actual real-analytic normal-neighborhood diffeomorphism

The product homeomorphism is real analytic in the original toric and
Riemann-sphere atlases. The local diffeomorphisms are literal compositions
of their original affine parametrizations. The inverse of the established
homeomorphism is identified with these genuine smooth local inverses.
-/

noncomputable section

open Set Topology Filter
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts

local notation "I₃" => 𝓘(ℝ, CoordinateSpace 3)
local notation "IP" => 𝓘(ℝ, Model)

/-- The explicit toric product map is a native local real-analytic diffeomorphism. -/
theorem fromProduct_isLocalDiffeomorph : IsLocalDiffeomorph IP I₃ ω fromProduct := by
  intro p
  obtain ⟨b, q, rfl⟩ := baseProductChart_cover p
  let e := baseProductParametrization b
  let g := normalChartParametrization b
  have hq : q ∈ e.source := by
    rw [baseProductParametrization_source]
    exact mem_univ q
  refine ⟨e.symm.trans g, ⟨e.map_source hq, ?_⟩, ?_⟩
  · change e.symm (baseProductChart b q) ∈ (normalChartParametrization b).source
    rw [normalChartParametrization_source]
    exact mem_univ _
  · intro y hy
    have hr : baseProductChart b (e.symm y) = y := e.right_inv hy.1
    change fromProduct y = normalChartParametrization b (e.symm y)
    calc
      fromProduct y = fromProduct (baseProductChart b (e.symm y)) :=
        congrArg fromProduct hr.symm
      _ = normalChartParametrization b (e.symm y) := fromProduct_baseProductChart b _

/-- Real analyticity of the original product map in the original atlases. -/
theorem contMDiff_fromProduct : ContMDiff IP I₃ ω fromProduct :=
  fromProduct_isLocalDiffeomorph.contMDiff

/-- Real analyticity of the actual homeomorphism into the original open submanifold. -/
theorem toricNeighborhoodHomeomorph_contMDiff :
    ContMDiff IP I₃ ω toricNeighborhoodHomeomorph := by
  intro p
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
  exact contMDiff_fromProduct p

/-- The actual inverse homeomorphism is real analytic; no inverse regularity is assumed. -/
theorem toricNeighborhoodHomeomorph_symm_contMDiff :
    ContMDiff I₃ IP ω toricNeighborhoodHomeomorph.symm := by
  intro y
  let x := toricNeighborhoodHomeomorph.symm y
  have hx := fromProduct_isLocalDiffeomorph x
  have he : fromProduct x = (y : ToricSpace.Space) := by
    change (toricNeighborhoodHomeomorph (toricNeighborhoodHomeomorph.symm y) :
      ToricSpace.Space) = (y : ToricSpace.Space)
    rw [toricNeighborhoodHomeomorph.apply_symm_apply]
  have hlocal : ContMDiffAt I₃ IP ω hx.localInverse (y : ToricSpace.Space) := by
    rw [← he]
    exact hx.localInverse_contMDiffAt
  have hmem : (y : ToricSpace.Space) ∈ hx.localInverse.source := by
    rw [← he]
    exact hx.localInverse_mem_source
  have hopen : IsOpen {z : toricNeighborhood | (z : ToricSpace.Space) ∈ hx.localInverse.source} :=
    hx.localInverse.open_source.preimage continuous_subtype_val
  apply (hlocal.comp y contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hmem] with z hz
  apply fromProduct_injective
  change fromProduct (toricNeighborhoodHomeomorph.symm z) =
    fromProduct (hx.localInverse (z : ToricSpace.Space))
  rw [hx.localInverse_right_inv hz]
  change (toricNeighborhoodHomeomorph (toricNeighborhoodHomeomorph.symm z) :
    ToricSpace.Space) = (z : ToricSpace.Space)
  rw [toricNeighborhoodHomeomorph.apply_symm_apply]

/-- The actual real-analytic product diffeomorphism onto the two original toric charts. -/
def toricNeighborhoodDiffeomorph :
    Diffeomorph IP I₃ (RiemannSphere × Fibre) toricNeighborhood ω where
  toEquiv := toricNeighborhoodHomeomorph.toEquiv
  contMDiff_toFun := toricNeighborhoodHomeomorph_contMDiff
  contMDiff_invFun := toricNeighborhoodHomeomorph_symm_contMDiff

@[simp] theorem toricNeighborhoodDiffeomorph_coe (p : RiemannSphere × Fibre) :
    (toricNeighborhoodDiffeomorph p : ToricSpace.Space) = fromProduct p := rfl

@[simp] theorem toricNeighborhoodDiffeomorph_baseProductChart (b : Bool) (q : Model) :
    toricNeighborhoodDiffeomorph (baseProductChart b q) =
      toricInclusion b ((chartCoordinates b).symm q) :=
  toricNeighborhoodHomeomorph_baseProductChart b q

@[simp] theorem toricNeighborhoodDiffeomorph_symm_toricInclusion
    (b : Bool) (z : CoordinateSpace 3) :
    toricNeighborhoodDiffeomorph.symm (toricInclusion b z) =
      baseProductChart b (chartCoordinates b z) :=
  toricNeighborhoodHomeomorph_symm_toricInclusion b z

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization

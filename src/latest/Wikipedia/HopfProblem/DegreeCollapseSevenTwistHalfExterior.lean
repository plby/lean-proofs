import Wikipedia.HopfProblem.DegreeCollapseSevenTwistExteriorHomology
import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryHalfClosedPresentation

/-!
# The section-meridian relation in the actual compact filling half

The common time function and its positive tube margin transfer to the twisted
product. The point-preserving exterior comparison restricts to the actual
nonnegative exteriors used by the two half-boundary presentations. Their
literal corner maps give the same integral relation inside the filling half.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization OrthogonalPaths
open SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [T2Space M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2)
  (B : FramedAttachingProduct e a f) (hB : B.radius = 2)
  (ρ : C(Sphere 3, OrthogonalOperators 4))
  (ht : ∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = A.tube (s, (ρ s).1.1 w))
  (T : TimeData A)

/-- The original smooth time, regular zero set and positive margin are unchanged. -/
def twistTimeData : TimeData B where
  time := T.time
  smooth := T.smooth
  regular := T.regular
  margin := T.margin
  margin_pos := T.margin_pos
  tube_time s w hw := by
    rw [ht]
    apply T.tube_time
    rw [mem_closedBall, dist_zero_right, (ρ s).2, hA]
    simpa only [mem_closedBall, dist_zero_right, hB] using hw

abbrev HalfExterior := NonnegativeSurgeryPair.Exterior (closedBoundaryPair A hA) T.time

def halfExteriorHomeomorph :
    HalfExterior B hB (twistTimeData A hA B hB ρ ht T) ≃ₜ HalfExterior A hA T where
  toFun x := ⟨exteriorHomeomorph A hA B hB ρ ht x.val, x.property⟩
  invFun x := ⟨(exteriorHomeomorph A hA B hB ρ ht).symm x.val, x.property⟩
  left_inv x := Subtype.ext ((exteriorHomeomorph A hA B hB ρ ht).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((exteriorHomeomorph A hA B hB ρ ht).apply_symm_apply x.val)
  continuous_toFun :=
    ((exteriorHomeomorph A hA B hB ρ ht).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((exteriorHomeomorph A hA B hB ρ ht).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem halfExteriorHomeomorph_val
    (x : HalfExterior B hB (twistTimeData A hA B hB ρ ht T)) :
    (halfExteriorHomeomorph A hA B hB ρ ht T x).val.val = x.val.val := rfl

def halfCornerMap : C(Sphere 3 × Sphere 3, HalfExterior A hA T) :=
  ⟨(halfBoundaryPair A hA T).boundary, (cornerMap A hA).continuous.subtype_mk _⟩

theorem halfCornerMap_eq_boundary (p : Sphere 3 × Sphere 3) :
    halfCornerMap A hA T p = (halfBoundaryPair A hA T).boundary p := rfl

def halfSectionMap (v : Sphere 3) : C(Sphere 3, HalfExterior A hA T) :=
  (halfCornerMap A hA T).comp (ProductThirdHomology.leftSection v)

def halfMeridianMap (s : Sphere 3) : C(Sphere 3, HalfExterior A hA T) :=
  (halfCornerMap A hA T).comp (ProductThirdHomology.rightSection s)

theorem halfSection_twist (v : Sphere 3) :
    (halfExteriorHomeomorph A hA B hB ρ ht T : C(_, _)).comp
      (halfSectionMap B hB (twistTimeData A hA B hB ρ ht T) v) =
        (halfCornerMap A hA T).comp (columnGraph ρ v) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  apply Subtype.ext
  exact ht s v.val

/-- The relation belongs to the actual half-exterior homology, with integral torsion retained. -/
theorem halfSection_homology_twist (v s : Sphere 3) (c : SingularHomology (Sphere 3) 3) :
    singularHomologyMap (halfExteriorHomeomorph A hA B hB ρ ht T : C(_, _)) 3
      (singularHomologyMap (halfSectionMap B hB (twistTimeData A hA B hB ρ ht T) v) 3 c) =
        singularHomologyMap (halfSectionMap A hA T v) 3 c +
          singularHomologyMap (halfMeridianMap A hA T s) 3
            (singularHomologyMap (column v ρ) 3 c) := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, halfSection_twist]
  rw [singularHomologyMap_comp, LinearMap.comp_apply, columnGraph_homology ρ v s, map_add]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

theorem halfSection_homology_twist_of_multiplier (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3,
      singularHomologyMap (column v ρ) 3 c = j • c)
    (c : SingularHomology (Sphere 3) 3) :
    singularHomologyMap (halfExteriorHomeomorph A hA B hB ρ ht T : C(_, _)) 3
      (singularHomologyMap (halfSectionMap B hB (twistTimeData A hA B hB ρ ht T) v) 3 c) =
        singularHomologyMap (halfSectionMap A hA T v) 3 c +
          j • singularHomologyMap (halfMeridianMap A hA T s) 3 c := by
  rw [halfSection_homology_twist A hA B hB ρ ht T v s, hρ, map_zsmul]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist

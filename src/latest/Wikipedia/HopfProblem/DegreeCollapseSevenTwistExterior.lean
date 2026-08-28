import Wikipedia.HopfProblem.DegreeCollapseSevenCommonAttachingRadius
import Wikipedia.HopfProblem.DegreeCollapseSevenUnitSurgeryCoordinates
import Wikipedia.SmoothSixDPoincare.FramedSurgeryExterior
import Wikipedia.NoExoticSixSphere.ProductThirdHomologyFactors

/-!
# The actual common exterior and section maps of a normal-coordinate twist

Orthogonal twists preserve the removed open unit tube exactly. The exterior
homeomorphism is the identity on original manifold points. The new section
becomes the original corner map applied to the graph of the actual column
map; this retains the sphere parameters needed for integral homology.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization OrthogonalPaths
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [T2Space M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2)
  (B : FramedAttachingProduct e a f) (hB : B.radius = 2)
  (ρ : C(Sphere 3, OrthogonalOperators 4))
  (ht : ∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = A.tube (s, (ρ s).1.1 w))

include ht in
theorem faceInterior_eq :
    FramedSurgery.faceInterior (E := Vector 4) (face B hB) =
      FramedSurgery.faceInterior (E := Vector 4) (face A hA) := by
  ext p
  constructor
  · rintro ⟨⟨s, w⟩, ⟨_, hw⟩, hp⟩
    change B.tube (s, w) = p at hp
    refine ⟨(s, (ρ s).1.1 w), ⟨mem_univ _, ?_⟩, ?_⟩
    · simpa only [mem_ball, dist_zero_right, (ρ s).2] using hw
    · change A.tube (s, (ρ s).1.1 w) = p
      exact (ht s w).symm.trans hp
  · rintro ⟨⟨s, w⟩, ⟨_, hw⟩, hp⟩
    change A.tube (s, w) = p at hp
    let w' := (toEquiv (ρ s)).symm w
    have hnorm : ‖w'‖ = ‖w‖ := (toEquiv (ρ s)).symm.norm_map w
    have hinv : (ρ s).1.1 w' = w := (toEquiv (ρ s)).apply_symm_apply w
    refine ⟨(s, w'), ⟨mem_univ _, ?_⟩, ?_⟩
    · simpa only [mem_ball, dist_zero_right, hnorm] using hw
    · change B.tube (s, w') = p
      rw [ht, hinv]
      exact hp

/-- This homeomorphism retains every original point, including the corner. -/
def exteriorHomeomorph :
    FramedSurgery.Exterior (E := Vector 4) (face B hB) ≃ₜ
      FramedSurgery.Exterior (E := Vector 4) (face A hA) :=
  Homeomorph.setCongr (congrArg Set.compl (faceInterior_eq A hA B hB ρ ht))

theorem exteriorHomeomorph_val (x : FramedSurgery.Exterior (E := Vector 4) (face B hB)) :
    (exteriorHomeomorph A hA B hB ρ ht x).val = x.val := rfl

def cornerMap : C(Sphere 3 × Sphere 3, FramedSurgery.Exterior (E := Vector 4) (face A hA)) := by
  let q : C(Sphere 3 × Sphere 3, Sphere 3 × MorseHandle.UnitDisk (Vector 4)) :=
    ⟨fun p ↦ (p.1, ⟨p.2.val, sphere_subset_closedBall p.2.property⟩),
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩
  exact ⟨FramedSurgery.exteriorCorner (E := Vector 4) (face A hA),
    ((face A hA).map.continuous.comp q.continuous).subtype_mk _⟩

theorem cornerMap_val (p : Sphere 3 × Sphere 3) :
    (cornerMap A hA p).val = A.tube (p.1, p.2.val) := rfl

def sectionMap (v : Sphere 3) :
    C(Sphere 3, FramedSurgery.Exterior (E := Vector 4) (face A hA)) :=
  (cornerMap A hA).comp (ProductThirdHomology.leftSection v)

def meridianMap (s : Sphere 3) :
    C(Sphere 3, FramedSurgery.Exterior (E := Vector 4) (face A hA)) :=
  (cornerMap A hA).comp (ProductThirdHomology.rightSection s)

def columnGraph (v : Sphere 3) : C(Sphere 3, Sphere 3 × Sphere 3) :=
  (ContinuousMap.id (Sphere 3)).prodMk (column v ρ)

include ht in
theorem section_twist (v : Sphere 3) :
    (exteriorHomeomorph A hA B hB ρ ht :
      C(FramedSurgery.Exterior (E := Vector 4) (face B hB),
        FramedSurgery.Exterior (E := Vector 4) (face A hA))).comp
        (sectionMap B hB v) = (cornerMap A hA).comp (columnGraph ρ v) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  exact ht s v.val

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist

import Wikipedia.HopfProblem.DegreeCollapseSevenTwistExterior

/-!
# The exact integral section-meridian relation under an attaching twist

The genuine H3 product coordinates identify the graph class with its two
actual factor classes. The literal common-exterior homeomorphism therefore
carries the twisted section to the old section plus the meridian applied to
the actual column class. An even column multiplier gives precisely the
corresponding even meridian multiple, with no orientation sign discarded.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization OrthogonalPaths
open SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare

theorem columnGraph_homology (ρ : C(Sphere 3, OrthogonalOperators 4))
    (v s : Sphere 3) (c : SingularHomology (Sphere 3) 3) :
    singularHomologyMap (columnGraph ρ v) 3 c =
      singularHomologyMap (ProductThirdHomology.leftSection v) 3 c +
        singularHomologyMap (ProductThirdHomology.rightSection s) 3
          (singularHomologyMap (column v ρ) 3 c) := by
  let : SimplyConnectedSpace (Sphere 3) := EuclideanSphere.simplyConnectedSpace 1
  let : Subsingleton (HomotopyGroup (Fin 2) (Sphere 3) s) :=
    subsingleton_sphereHomotopyGroup (by decide) s
  let : Subsingleton (HomotopyGroup (Fin 2) (Sphere 3) v) :=
    subsingleton_sphereHomotopyGroup (by decide) v
  apply (ProductThirdHomology.equivalence s v).injective
  rw [map_add, ProductThirdHomology.equivalence_left, ProductThirdHomology.equivalence_right]
  apply Prod.ext
  · change (ProductThirdHomology.equivalence s v
      (singularHomologyMap (columnGraph ρ v) 3 c)).1 = c + 0
    rw [add_zero, ProductThirdHomology.equivalence_fst,
      ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    change singularHomologyMap (ContinuousMap.id (Sphere 3)) 3 c = c
    rw [singularHomologyMap_id]
    rfl
  · change (ProductThirdHomology.equivalence s v
      (singularHomologyMap (columnGraph ρ v) 3 c)).2 =
        0 + singularHomologyMap (column v ρ) 3 c
    rw [zero_add, ProductThirdHomology.equivalence_snd,
      ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    rfl

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [T2Space M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2)
  (B : FramedAttachingProduct e a f) (hB : B.radius = 2)
  (ρ : C(Sphere 3, OrthogonalOperators 4))
  (ht : ∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = A.tube (s, (ρ s).1.1 w))

theorem section_homology_twist (v s : Sphere 3) (c : SingularHomology (Sphere 3) 3) :
    singularHomologyMap (exteriorHomeomorph A hA B hB ρ ht : C(_, _)) 3
      (singularHomologyMap (sectionMap B hB v) 3 c) =
        singularHomologyMap (sectionMap A hA v) 3 c +
          singularHomologyMap (meridianMap A hA s) 3
            (singularHomologyMap (column v ρ) 3 c) := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, section_twist]
  rw [singularHomologyMap_comp, LinearMap.comp_apply, columnGraph_homology ρ v s, map_add]
  change singularHomologyMap (cornerMap A hA) 3
      (singularHomologyMap (ProductThirdHomology.leftSection v) 3 c) +
    singularHomologyMap (cornerMap A hA) 3
      (singularHomologyMap (ProductThirdHomology.rightSection s) 3
        (singularHomologyMap (column v ρ) 3 c)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

/-- This is an equality in the actual original exterior's integral homology, including torsion. -/
theorem section_homology_twist_of_multiplier (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3,
      singularHomologyMap (column v ρ) 3 c = j • c)
    (c : SingularHomology (Sphere 3) 3) :
    singularHomologyMap (exteriorHomeomorph A hA B hB ρ ht : C(_, _)) 3
      (singularHomologyMap (sectionMap B hB v) 3 c) =
        singularHomologyMap (sectionMap A hA v) 3 c +
          j • singularHomologyMap (meridianMap A hA s) 3 c := by
  rw [section_homology_twist A hA B hB ρ ht v s, hρ, map_zsmul]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist

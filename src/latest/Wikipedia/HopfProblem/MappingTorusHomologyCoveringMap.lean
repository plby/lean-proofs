import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusQuotient
import Wikipedia.HopfProblem.MappingTorusHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductMaps

/-!
# The actual finite cyclic map to a mapping torus

The proved homeomorphism from the finite twist quotient defines the map
from the original circle product to the inverse-monodromy mapping torus.
Its real representative multiplies time by the finite period.  On the
time-zero section it is exactly the original fibre inclusion, so its
induced singular homology map has zero Wang boundary on section classes.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.MappingTorusHomology.Covering

open MappingTorus MappingTorus.HomologyCover PeriodTorusHigherHomology SingularMayerVietoris
open PeriodTorusHigherHomology.CircleTopology

variable {X : Type} [TopologicalSpace X]

/-- An integral change of the real chart coordinate applies exactly the
corresponding positive monodromy power in the unchanged time chart. -/
theorem mk_add_int (f : X ≃ₜ X) (t : ℝ) (k : ℤ) (x : X) :
    mk f (t + (k : ℝ), x) = mk f (t, (f ^ k) x) := by
  apply (mk_eq_mk_iff f _ _).mpr
  exact ⟨-k, by simp, by simp⟩

theorem mk_symm_add_int (B : X ≃ₜ X) (t : ℝ) (k : ℤ) (x : X) :
    mk B.symm (t + (k : ℝ), x) = mk B.symm (t, (B.symm ^ k) x) :=
  mk_add_int B.symm t k x

variable [CompactSpace X] [T2Space X]
  (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)

/-- The literal finite-orbit projection followed by its proved
homeomorphism to the inverse-monodromy mapping torus. -/
def productCover : C(MappingTorus.Circle × X, Torus B.symm) where
  toFun := Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph m B hB ∘
    Elliptic.HigherHomology.MappingTorusQuotient.project m B hB
  continuous_toFun :=
    (Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph m B hB).continuous.comp
      (Elliptic.HigherHomology.MappingTorusQuotient.project_continuous m B hB)

theorem productCover_real_apply (t : ℝ) (x : X) :
    productCover m B hB ((t : MappingTorus.Circle), x) = mk B.symm (t * m, x) :=
  Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph_project m B hB t x

theorem productCover_surjective : Function.Surjective (productCover m B hB) :=
  (Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph m B hB).surjective.comp
    (Elliptic.HigherHomology.MappingTorusQuotient.project_surjective m B hB)

/-- On the actual circle origin the finite cyclic map is the unchanged
fibre inclusion; there is no monodromy factor at this section. -/
@[simp] theorem productCover_zero_apply (x : X) :
    productCover m B hB (0, x) = mk B.symm (0, x) := by
  simpa only [AddCircle.coe_zero, zero_mul] using productCover_real_apply m B hB 0 x

@[simp] theorem productCover_comp_productSection :
    (productCover m B hB).comp (productSection X) = fibreInclusion B.symm := by
  apply ContinuousMap.ext
  intro x
  exact productCover_zero_apply m B hB x

/-- The genuine induced map on integral singular homology in every degree. -/
abbrev productCoverHomology (n : ℕ) :
    SingularHomology (MappingTorus.Circle × X) n →ₗ[ℤ] SingularHomology (Torus B.symm) n :=
  singularHomologyMap (productCover m B hB) n

/-- Functoriality identifies the fixed-section contribution with the
actual fibre homology map of the inverse-monodromy mapping torus. -/
theorem productCoverHomology_comp_circleSection (n : ℕ) :
    (productCoverHomology m B hB n).comp (circleSectionHomology X n) =
      fibreHomologyMap B.symm n := by
  change (singularHomologyMap (productCover m B hB) n).comp
    (singularHomologyMap (productSection X) n) = _
  rw [← singularHomologyMap_comp, productCover_comp_productSection]

@[simp] theorem productCoverHomology_circleSection_apply (n : ℕ)
    (a : SingularHomology X n) :
    productCoverHomology m B hB n (circleSectionHomology X n a) =
      fibreHomologyMap B.symm n a :=
  LinearMap.congr_fun (productCoverHomology_comp_circleSection m B hB n) a

/-- Exactness of the actual Wang sequence annihilates every fixed-section
class after applying the finite cyclic map. -/
theorem wangBoundary_productCover_circleSection (n : ℕ) :
    ((wangBoundary B.symm n).comp (productCoverHomology m B hB (n + 1))).comp
      (circleSectionHomology X (n + 1)) = 0 := by
  ext a
  change wangBoundary B.symm n
    (productCoverHomology m B hB (n + 1) (circleSectionHomology X (n + 1) a)) = 0
  rw [productCoverHomology_circleSection_apply]
  have ha : fibreHomologyMap B.symm (n + 1) a ∈
      LinearMap.range (fibreHomologyMap B.symm (n + 1)) := ⟨a, rfl⟩
  rw [wang_exact_at_mappingTorus] at ha
  exact ha

@[simp] theorem wangBoundary_productCover_circleSection_apply (n : ℕ)
    (a : SingularHomology X (n + 1)) :
    wangBoundary B.symm n
      (productCoverHomology m B hB (n + 1) (circleSectionHomology X (n + 1) a)) = 0 :=
  LinearMap.congr_fun (wangBoundary_productCover_circleSection m B hB n) a

end Wikipedia.HopfProblem.MappingTorusHomology.Covering

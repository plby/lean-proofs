import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroRetraction
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroTorusHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySourceSequence
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyProducts

/-!
# Actual fourth-homology detection for the zero-γ regular subfamily

The literal zero-γ parts of the upper and lower slit family members have
the homotopy type of the actual three-torus, hence have zero fourth
homology.  The whole overlap inclusion has the proved continuous
retraction.  Naturality of the actual singular Mayer--Vietoris boundary
therefore makes that boundary injective on the fourth homology of the
subfamily.

The original source-kernel projection has exactly the same kernel as
that boundary.  Consequently it is injective on the actual image of
this subfamily.  No choice of a splitting or attachment matrix is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomology.CircleTopology
open scoped ContinuousMap

variable (D : Data ℂ TriangleRegularPoint)

/-- The actual upper zero-γ family member contracts to its unchanged fibre. -/
def upperHomotopyEquiv : upperFamily D ≃ₕ Fibre :=
  (sectionChart D Homology.upperBase
    (Homology.upperLift Homology.normalizedSlitBaseLift)
    (Homology.upperLift_project Homology.normalizedSlitBaseLift)).toHomotopyEquiv.trans
      (contractibleProdHomotopyEquiv Homology.upperBase Fibre)

/-- The actual lower member has the same native three-torus homotopy type. -/
def lowerHomotopyEquiv : lowerFamily D ≃ₕ Fibre :=
  (sectionChart D Homology.lowerBase
    (Homology.lowerLift Homology.normalizedSlitBaseLift)
    (Homology.lowerLift_project Homology.normalizedSlitBaseLift)).toHomotopyEquiv.trans
      (contractibleProdHomotopyEquiv Homology.lowerBase Fibre)

def upperHomologyEquiv (n : ℕ) :
    SingularHomology (upperFamily D) n ≃ₗ[ℤ] SingularHomology Fibre n :=
  homotopyEquivHomologyEquiv (upperHomotopyEquiv D) n

def lowerHomologyEquiv (n : ℕ) :
    SingularHomology (lowerFamily D) n ≃ₗ[ℤ] SingularHomology Fibre n :=
  homotopyEquivHomologyEquiv (lowerHomotopyEquiv D) n

/-- Fourth homology vanishes on the literal upper cover member. -/
theorem upperH4_subsingleton : Subsingleton (SingularHomology (upperFamily D) 4) := by
  let := fibreH4_subsingleton
  exact (upperHomologyEquiv D 4).injective.subsingleton

/-- Fourth homology vanishes on the literal lower cover member. -/
theorem lowerH4_subsingleton : Subsingleton (SingularHomology (lowerFamily D) 4) := by
  let := fibreH4_subsingleton
  exact (lowerHomologyEquiv D 4).injective.subsingleton

/-- The singular-homology map of the actual inclusion in every degree. -/
def homologyInclusion (n : ℕ) :
    SingularHomology (Space D) n →ₗ[ℤ] SingularHomology D.Space n :=
  singularHomologyMap (inclusion D) n

/-- The original regular-family Mayer--Vietoris boundary detects all subfamily `H₄` classes. -/
theorem connecting_comp_homologyInclusion_injective :
    Function.Injective
      ((Homology.familyConnectingHomomorphism D 3).comp (homologyInclusion D 4)) := by
  let := upperH4_subsingleton D
  let := lowerH4_subsingleton D
  exact connecting_comp_homologyMap_injective (inclusion D)
    (upperFamily D) (lowerFamily D) (Homology.upperFamily D) (Homology.lowerFamily D)
    (inclusion_mapsTo_upper D) (inclusion_mapsTo_lower D)
    (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D)
    (Homology.upperFamily D).isOpen (Homology.lowerFamily D).isOpen
    (Homology.upperFamily_union_lowerFamily D) 3
    (intersectionHomologyInclusion_injective D 3)

/-- In particular, the actual subfamily inclusion is injective on fourth singular homology. -/
theorem homologyInclusion_four_injective : Function.Injective (homologyInclusion D 4) := by
  intro a b hab
  apply connecting_comp_homologyInclusion_injective D
  exact congrArg (Homology.familyConnectingHomomorphism D 3) hab

/-- The proved source-oriented projection and the literal boundary have the same zero set. -/
theorem sourceKernelProjection_eq_zero_iff_connecting (n : ℕ)
    (a : SingularHomology D.Space (n + 1)) :
    Homology.sourceKernelProjection D n a = 0 ↔
      Homology.familyConnectingHomomorphism D n a = 0 := by
  change a ∈ LinearMap.ker (Homology.sourceKernelProjection D n) ↔
    a ∈ LinearMap.ker (Homology.familyConnectingHomomorphism D n)
  rw [Homology.sourceKernelProjection_kernel,
    Homology.familyConnectingHomomorphism_ker_eq_fibre D Homology.normalizedSlitBaseLift]

/-- Equality detection agrees for the two actual versions of the boundary. -/
theorem sourceKernelProjection_eq_iff_connecting (n : ℕ)
    (a b : SingularHomology D.Space (n + 1)) :
    Homology.sourceKernelProjection D n a = Homology.sourceKernelProjection D n b ↔
      Homology.familyConnectingHomomorphism D n a =
        Homology.familyConnectingHomomorphism D n b := by
  simpa only [map_sub, sub_eq_zero] using
    sourceKernelProjection_eq_zero_iff_connecting D n (a - b)

/-- The original source-kernel projection is injective after the actual subfamily inclusion. -/
theorem sourceKernelProjection_comp_homologyInclusion_injective :
    Function.Injective
      ((Homology.sourceKernelProjection D 3).comp (homologyInclusion D 4)) := by
  intro a b hab
  apply connecting_comp_homologyInclusion_injective D
  exact (sourceKernelProjection_eq_iff_connecting D 3
    (homologyInclusion D 4 a) (homologyInclusion D 4 b)).mp hab

/-- An actual subfamily class with zero source-kernel coordinate is itself zero. -/
theorem sourceKernelProjection_homologyInclusion_eq_zero_iff
    (a : SingularHomology (Space D) 4) :
    Homology.sourceKernelProjection D 3 (homologyInclusion D 4 a) = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply sourceKernelProjection_comp_homologyInclusion_injective D
    exact h.trans (map_zero ((Homology.sourceKernelProjection D 3).comp
      (homologyInclusion D 4))).symm
  · rintro rfl
    rw [map_zero, map_zero]

/-- Residual-fibre-coordinate control for every actual class in the subfamily image. -/
theorem eq_zero_of_mem_range_of_sourceKernelProjection_eq_zero
    (a : SingularHomology D.Space 4) (ha : a ∈ LinearMap.range (homologyInclusion D 4))
    (h : Homology.sourceKernelProjection D 3 a = 0) : a = 0 := by
  obtain ⟨b, rfl⟩ := ha
  rw [(sourceKernelProjection_homologyInclusion_eq_zero_iff D b).mp h, map_zero]

/-- The actual subfamily image has no nonzero residual fibre class. -/
theorem range_inf_sourceKernelProjection_ker :
    LinearMap.range (homologyInclusion D 4) ⊓
      LinearMap.ker (Homology.sourceKernelProjection D 3) = ⊥ := by
  apply le_antisymm
  · intro a ha
    exact (Submodule.mem_bot ℤ).mpr
      (eq_zero_of_mem_range_of_sourceKernelProjection_eq_zero D a ha.1 ha.2)
  · exact bot_le

/-- This controls equality only on the proved subfamily image,
not on arbitrary family classes. -/
theorem sourceKernelProjection_injOn_range :
    Set.InjOn (Homology.sourceKernelProjection D 3)
      (LinearMap.range (homologyInclusion D 4)) := by
  rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩ h
  exact congrArg (homologyInclusion D 4)
    (sourceKernelProjection_comp_homologyInclusion_injective D h)

/-- A genuine continuous factorization into the subfamily gives the actual homology factorization. -/
theorem homologyMap_lift {X : Type} [TopologicalSpace X] (f : C(X, D.Space))
    (hf : ∀ x, familyGamma D (f x) = 0) (n : ℕ) :
    (homologyInclusion D n).comp (singularHomologyMap (lift D f hf) n) =
      singularHomologyMap f n := by
  change (singularHomologyMap (inclusion D) n).comp
    (singularHomologyMap (lift D f hf) n) = _
  rw [← singularHomologyMap_comp, inclusion_comp_lift]

end Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

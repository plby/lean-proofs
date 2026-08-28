import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyMayerVietoris
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyIntersectionMaps
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyGeneratorActions
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraExtension

/-!
# The actual regular-family exact sequence in torus coordinates

The previously proved actual slit-cover charts normalize its genuine
Mayer--Vietoris intersection map to the signed three-overlap map. Its
identity block can then be removed by the explicit integral coordinate
changes. This constructs a short exact sequence whose middle object is
the actual singular homology of the regular family and whose endpoints
are the actual kernel and cokernel of the two monodromy differences.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris TrianglePeriodFamilyHomologyAlgebra
open CategoryTheory

/-- The signed three-component map with the actual overlap homeomorphisms as coefficients. -/
abbrev slitOverlapMap (b : SlitBaseLift) (n : ℕ) :=
  overlapMap (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n)

variable (D : Data ℂ TriangleRegularPoint) (b : SlitBaseLift)

/-- The actual incoming map expressed in the two cover-member torus markings. -/
def familyMarkedRight (n : ℕ) :
    (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) →ₗ[ℤ]
      SingularHomology D.Space n :=
  (familyRightHomologyMap D n).comp (pairHomologyEquiv D b n).symm.toLinearMap

/-- The actual connecting map in the middle--left--right intersection marking. -/
def familyMarkedConnecting (n : ℕ) :
    SingularHomology D.Space (n + 1) →ₗ[ℤ]
      (SingularHomology RealTorus₄ n ×
        (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n)) :=
  (intersectionHomologyEquiv D b n).toLinearMap.comp (familyConnectingHomomorphism D n)

@[simp] theorem familyMarkedRight_apply (n : ℕ)
    (a : SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) :
    familyMarkedRight D b n a =
      familyRightHomologyMap D n ((pairHomologyEquiv D b n).symm a) := rfl

@[simp] theorem familyMarkedConnecting_apply (n : ℕ)
    (a : SingularHomology D.Space (n + 1)) :
    familyMarkedConnecting D b n a =
      intersectionHomologyEquiv D b n (familyConnectingHomomorphism D n a) := rfl

/-- The actual marked first map, in the direction convenient for exactness transport. -/
theorem slitOverlapMap_intersection (n : ℕ)
    (a : SingularHomology (familyIntersection D) n) :
    slitOverlapMap b n (intersectionHomologyEquiv D b n a) =
      pairHomologyEquiv D b n (familyLeftHomologyMap D n a) :=
  (pairHomologyEquiv_leftHomologyMap D b n a).symm

/-- Exactness at the two marked cover homology groups follows from actual Mayer--Vietoris. -/
theorem familyMarked_exact_at_pair (n : ℕ) :
    Function.Exact (slitOverlapMap b n) (familyMarkedRight D b n) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (family_exact_at_pair D n ((pairHomologyEquiv D b n).symm x)).mp hx
    refine ⟨intersectionHomologyEquiv D b n a, ?_⟩
    exact (slitOverlapMap_intersection D b n a).trans
      ((congrArg (pairHomologyEquiv D b n) ha).trans
        ((pairHomologyEquiv D b n).apply_symm_apply x))
  · rintro ⟨v, rfl⟩
    obtain ⟨a, rfl⟩ := (intersectionHomologyEquiv D b n).surjective v
    rw [familyMarkedRight_apply, slitOverlapMap_intersection, LinearEquiv.symm_apply_apply]
    exact (family_exact_at_pair D n).apply_apply_eq_zero a

/-- The marked incoming and connecting maps are exact at actual family homology. -/
theorem familyMarked_exact_at_ambient (n : ℕ) :
    Function.Exact (familyMarkedRight D b (n + 1)) (familyMarkedConnecting D b n) := by
  intro x
  constructor
  · intro hx
    have hzero : familyConnectingHomomorphism D n x = 0 := by
      apply (intersectionHomologyEquiv D b n).injective
      exact hx.trans (intersectionHomologyEquiv D b n).map_zero.symm
    obtain ⟨a, ha⟩ := (family_exact_at_ambient D n x).mp hzero
    refine ⟨pairHomologyEquiv D b (n + 1) a, ?_⟩
    rw [familyMarkedRight_apply, LinearEquiv.symm_apply_apply]
    exact ha
  · rintro ⟨a, rfl⟩
    rw [familyMarkedConnecting_apply, familyMarkedRight_apply,
      (family_exact_at_ambient D n).apply_apply_eq_zero]
    exact (intersectionHomologyEquiv D b n).map_zero

/-- The actual marked connecting map surjects onto the kernel of the marked overlap map. -/
theorem familyMarked_exact_at_intersection (n : ℕ) :
    Function.Exact (familyMarkedConnecting D b n) (slitOverlapMap b n) := by
  intro x
  constructor
  · intro hx
    have hzero : familyLeftHomologyMap D n ((intersectionHomologyEquiv D b n).symm x) = 0 := by
      apply (pairHomologyEquiv D b n).injective
      rw [← slitOverlapMap_intersection, LinearEquiv.apply_symm_apply, hx, map_zero]
    obtain ⟨a, ha⟩ :=
      (family_exact_at_intersection D n ((intersectionHomologyEquiv D b n).symm x)).mp hzero
    refine ⟨a, ?_⟩
    rw [familyMarkedConnecting_apply, ha, LinearEquiv.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    exact (slitOverlapMap_intersection D b n (familyConnectingHomomorphism D n a)).trans
      ((congrArg (pairHomologyEquiv D b n)
        ((family_exact_at_intersection D n).apply_apply_eq_zero a)).trans
          (pairHomologyEquiv D b n).map_zero)

/-- The degree-zero marked incoming map is genuinely surjective. -/
theorem familyMarkedRight_zero_surjective : Function.Surjective (familyMarkedRight D b 0) :=
  (familyRightHomologyMap_zero_surjective D).comp (pairHomologyEquiv D b 0).symm.surjective

/-- The actual incoming map on the quotient by the two slit monodromy differences. -/
def slitCoinvariantInclusion (n : ℕ) :
    (SingularHomology RealTorus₄ n ⧸ LinearMap.range (slitDifference b n)) →ₗ[ℤ]
      SingularHomology D.Space n :=
  reducedCokernelToMiddle (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n)
    (familyMarkedRight D b n) (familyMarked_exact_at_pair D b n)

@[simp] theorem slitCoinvariantInclusion_mk (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    slitCoinvariantInclusion D b n (Submodule.Quotient.mk a) = familyMarkedRight D b n (0, -a) :=
  reducedCokernelToMiddle_mk (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n)
    (familyMarkedRight D b n) (familyMarked_exact_at_pair D b n) a

theorem slitCoinvariantInclusion_injective (n : ℕ) :
    Function.Injective (slitCoinvariantInclusion D b n) :=
  reducedCokernelToMiddle_injective (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n)
    (familyMarkedRight D b n) (familyMarked_exact_at_pair D b n)

/-- The actual connecting homomorphism with its two non-common coordinates retained. -/
def slitKernelProjection (n : ℕ) :
    SingularHomology D.Space (n + 1) →ₗ[ℤ] LinearMap.ker (slitDifference b n) :=
  middleToReducedKernel (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n)
    (familyMarkedConnecting D b n) (familyMarked_exact_at_intersection D b n)

@[simp] theorem slitKernelProjection_val (n : ℕ) (a : SingularHomology D.Space (n + 1)) :
    (slitKernelProjection D b n a :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      (familyMarkedConnecting D b n a).2 := rfl

theorem slitKernelProjection_surjective (n : ℕ) :
    Function.Surjective (slitKernelProjection D b n) :=
  middleToReducedKernel_surjective (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n)
    (familyMarkedConnecting D b n) (familyMarked_exact_at_intersection D b n)

/-- The actual regular-family homology is an extension of the actual difference kernel
by the actual difference cokernel. -/
theorem slitCoinvariantInclusion_kernelProjection_exact (n : ℕ) :
    Function.Exact (slitCoinvariantInclusion D b (n + 1)) (slitKernelProjection D b n) :=
  reducedExtension_exact
    (overlapHomologyAction b 0 (n + 1)) (overlapHomologyAction b 2 (n + 1))
    (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n)
    (familyMarkedRight D b (n + 1)) (familyMarkedConnecting D b n)
    (familyMarked_exact_at_pair D b (n + 1)) (familyMarked_exact_at_ambient D b n)
    (familyMarked_exact_at_intersection D b n)

/-- The reduced actual singular-homology sequence, before orienting the two meridians. -/
def familySlitExtension (n : ℕ) : ShortComplex (ModuleCat.{0} ℤ) :=
  reducedExtension
    (overlapHomologyAction b 0 (n + 1)) (overlapHomologyAction b 2 (n + 1))
    (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n)
    (familyMarkedRight D b (n + 1)) (familyMarkedConnecting D b n)
    (familyMarked_exact_at_pair D b (n + 1)) (familyMarked_exact_at_ambient D b n)
    (familyMarked_exact_at_intersection D b n)

@[simp] theorem familySlitExtension_middle (n : ℕ) :
    (familySlitExtension D b n).X₂ = SingularHomology D.Space (n + 1) := rfl

/-- The reduced sequence is proved short exact for the constructed regular family
in every degree. -/
theorem familySlitExtension_shortExact (n : ℕ) : (familySlitExtension D b n).ShortExact :=
  reducedExtension_shortExact
    (overlapHomologyAction b 0 (n + 1)) (overlapHomologyAction b 2 (n + 1))
    (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n)
    (familyMarkedRight D b (n + 1)) (familyMarkedConnecting D b n)
    (familyMarked_exact_at_pair D b (n + 1)) (familyMarked_exact_at_ambient D b n)
    (familyMarked_exact_at_intersection D b n)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

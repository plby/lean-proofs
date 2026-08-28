import Wikipedia.HopfProblem.ThreefoldHomologyStarSequence
import Wikipedia.HopfProblem.ThreefoldHomologyStarDegreeZero
import Wikipedia.HopfProblem.ThreefoldHomologyLowDegrees
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraExact

/-!
# Actual global homology through the threefold star cover

The middle object of the following short exact sequence is the native
integral singular homology of the constructed threefold.  Its end terms
are the cokernel and kernel of the single signed map of actual overlaps
into the actual regular family and filling pieces.  All maps retain
their literal geometric definitions, without assumptions about matrices
or splittings in the higher degrees.

In degree one the signed overlap map is proved surjective using the
already established actual simple connectedness and Hurewicz theorem.
The degree-zero map is the checked augmentation matrix `(sum, -id)`.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris TrianglePeriodFamilyHomologyAlgebra

/-- The actual global positive-degree homology, expressed between the
cokernel and kernel of the genuine signed star-cover maps. -/
def starExtension (n : ℕ) : ShortComplex (ModuleCat.{0} ℤ) :=
  cokernelKernelShortComplex
    (starLeftHomologyMap (n + 1)) (starRightHomologyMap (n + 1))
    (starConnectingHomomorphism n) (starLeftHomologyMap n)
    (star_exact_at_pair (n + 1)) (star_exact_at_ambient n) (star_exact_at_intersection n)

@[simp] theorem starExtension_middle (n : ℕ) :
    (starExtension n).X₂ = SingularHomology Space (n + 1) := rfl

/-- Short exactness comes from the actual singular Mayer–Vietoris sequence. -/
theorem starExtension_shortExact (n : ℕ) : (starExtension n).ShortExact :=
  cokernelKernelShortComplex_shortExact
    (starLeftHomologyMap (n + 1)) (starRightHomologyMap (n + 1))
    (starConnectingHomomorphism n) (starLeftHomologyMap n)
    (star_exact_at_pair (n + 1)) (star_exact_at_ambient n) (star_exact_at_intersection n)

/-- On representatives the first map is the sum of the four actual inclusions. -/
@[simp] theorem starExtension_left_mk (n : ℕ) (a : StarPairHomology (n + 1)) :
    (starExtension n).f.hom ((LinearMap.range (starLeftHomologyMap (n + 1))).mkQ a) =
      starRightHomologyMap (n + 1) a := rfl

/-- After forgetting the kernel subtype the second map is the genuine
singular connecting homomorphism of the full star cover. -/
@[simp] theorem starExtension_right_apply (n : ℕ)
    (a : SingularHomology Space (n + 1)) :
    (LinearMap.ker (starLeftHomologyMap n)).subtype ((starExtension n).g.hom a) =
      starConnectingHomomorphism n a := rfl

/-- Every actual piece inclusion has zero image in the genuine first homology. -/
theorem starRightHomologyMap_one_eq_zero : starRightHomologyMap 1 = 0 := by
  apply LinearMap.ext
  intro a
  exact LowDegrees.singularH1_eq_zero _

/-- The full degree-one signed boundary map is genuinely onto. -/
theorem starLeftHomologyMap_one_surjective : Function.Surjective (starLeftHomologyMap 1) := by
  intro a
  apply (star_exact_at_pair 1 a).mp
  exact LowDegrees.singularH1_eq_zero _

/-- The actual degree-zero connecting homomorphism vanishes. -/
theorem starConnectingHomomorphism_zero_eq_zero : starConnectingHomomorphism 0 = 0 := by
  apply LinearMap.ext
  intro a
  change starConnectingHomomorphism 0 a = 0
  rw [LowDegrees.singularH1_eq_zero a, map_zero]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

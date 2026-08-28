import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyMarkedSequence
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyFibreInclusionMaps

/-!
# The actual regular-family sequence in the prescribed meridian basis

The explicit slit-to-meridian change of coordinates identifies the two
monodromy differences with the source generators. The sign of the reduced
cokernel map is corrected, so its value on every representative is exactly
the positive, literal fibre-inclusion map on singular homology.

The connecting projection is the actual Mayer--Vietoris homomorphism,
followed by the three-component marking, deletion of the common component,
and the already proved orientation change. No abstract bundle homology or
spectral-sequence identification is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris CategoryTheory

variable (D : Data ℂ TriangleRegularPoint)

/-- The inverse cokernel normalization also preserves every actual representative. -/
@[simp] theorem normalizedSlitCokernelEquiv_symm_mk (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    (normalizedSlitCokernelEquiv n).symm (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk a := by
  apply (normalizedSlitCokernelEquiv n).injective
  rw [LinearEquiv.apply_symm_apply, normalizedSlitCokernelEquiv_mk]

/-- The actual marked cover map is the literal fibre map applied to the sum. -/
theorem familyMarkedRight_eq_fibre (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) :
    familyMarkedRight D b n a =
      singularHomologyMap (familyFibreInclusion D b) n (a.1 + a.2) :=
  familyRightHomologyMap_pair_symm D b n a

/-- The incoming source-coinvariant map, with positive fibre-inclusion sign. -/
def sourceCoinvariantInclusion (n : ℕ) :
    (SingularHomology RealTorus₄ n ⧸ LinearMap.range (sourceDifference n)) →ₗ[ℤ]
      SingularHomology D.Space n :=
  -((slitCoinvariantInclusion D normalizedSlitBaseLift n).comp
    (normalizedSlitCokernelEquiv n).symm.toLinearMap)

@[simp] theorem sourceCoinvariantInclusion_apply (n : ℕ)
    (a : SingularHomology RealTorus₄ n ⧸ LinearMap.range (sourceDifference n)) :
    sourceCoinvariantInclusion D n a =
      -slitCoinvariantInclusion D normalizedSlitBaseLift n
        ((normalizedSlitCokernelEquiv n).symm a) := rfl

/-- On every quotient representative the incoming map is the actual fibre inclusion. -/
@[simp] theorem sourceCoinvariantInclusion_mk (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    sourceCoinvariantInclusion D n (Submodule.Quotient.mk a) =
      singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) n a := by
  rw [sourceCoinvariantInclusion_apply, normalizedSlitCokernelEquiv_symm_mk,
    slitCoinvariantInclusion_mk, familyMarkedRight_eq_fibre]
  simp only [zero_add, map_neg, neg_neg]

/-- The actual fibre inclusion is injective after quotienting by the monodromy differences. -/
theorem sourceCoinvariantInclusion_injective (n : ℕ) :
    Function.Injective (sourceCoinvariantInclusion D n) := by
  intro a b hab
  have hneg :
      -slitCoinvariantInclusion D normalizedSlitBaseLift n
        ((normalizedSlitCokernelEquiv n).symm a) =
      -slitCoinvariantInclusion D normalizedSlitBaseLift n
        ((normalizedSlitCokernelEquiv n).symm b) := hab
  exact (normalizedSlitCokernelEquiv n).symm.injective
    (slitCoinvariantInclusion_injective D normalizedSlitBaseLift n (neg_injective hneg))

/-- The actual connecting map with the two meridian coordinates and their source orientations. -/
def sourceKernelProjection (n : ℕ) :
    SingularHomology D.Space (n + 1) →ₗ[ℤ] LinearMap.ker (sourceDifference n) :=
  (normalizedSlitKernelEquiv n).toLinearMap.comp
    (slitKernelProjection D normalizedSlitBaseLift n)

@[simp] theorem sourceKernelProjection_apply (n : ℕ)
    (a : SingularHomology D.Space (n + 1)) :
    sourceKernelProjection D n a =
      normalizedSlitKernelEquiv n (slitKernelProjection D normalizedSlitBaseLift n a) := rfl

/-- The underlying coordinates are obtained from the literal Mayer--Vietoris boundary. -/
@[simp] theorem sourceKernelProjection_val (n : ℕ)
    (a : SingularHomology D.Space (n + 1)) :
    (sourceKernelProjection D n a :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      normalizedSourceDomainEquiv n
        (intersectionHomologyEquiv D normalizedSlitBaseLift n
          (familyConnectingHomomorphism D n a)).2 := rfl

/-- Every actual source-difference kernel class is the boundary of an actual family class. -/
theorem sourceKernelProjection_surjective (n : ℕ) :
    Function.Surjective (sourceKernelProjection D n) :=
  (normalizedSlitKernelEquiv n).surjective.comp
    (slitKernelProjection_surjective D normalizedSlitBaseLift n)

/-- The positive actual fibre map and the source-oriented actual boundary form an exact pair. -/
theorem sourceCoinvariantInclusion_kernelProjection_exact (n : ℕ) :
    Function.Exact (sourceCoinvariantInclusion D (n + 1)) (sourceKernelProjection D n) := by
  intro a
  constructor
  · intro ha
    have hzero : slitKernelProjection D normalizedSlitBaseLift n a = 0 := by
      apply (normalizedSlitKernelEquiv n).injective
      exact ha.trans (normalizedSlitKernelEquiv n).map_zero.symm
    obtain ⟨q, hq⟩ :=
      (slitCoinvariantInclusion_kernelProjection_exact D normalizedSlitBaseLift n a).mp hzero
    refine ⟨-normalizedSlitCokernelEquiv (n + 1) q, ?_⟩
    rw [sourceCoinvariantInclusion_apply, map_neg, LinearEquiv.symm_apply_apply,
      map_neg, neg_neg]
    exact hq
  · rintro ⟨q, rfl⟩
    have hex := slitCoinvariantInclusion_kernelProjection_exact D normalizedSlitBaseLift n
    rw [sourceKernelProjection_apply, sourceCoinvariantInclusion_apply, map_neg,
      hex.apply_apply_eq_zero, neg_zero, map_zero]

/-- The actual regular-family integral homology extension in the source marking. -/
def familySourceExtension (n : ℕ) : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.moduleCatMk (sourceCoinvariantInclusion D (n + 1))
    (sourceKernelProjection D n)
    (sourceCoinvariantInclusion_kernelProjection_exact D n).linearMap_comp_eq_zero

@[simp] theorem familySourceExtension_middle (n : ℕ) :
    (familySourceExtension D n).X₂ = SingularHomology D.Space (n + 1) := rfl

/-- This is a proved short exact sequence of the actual singular-homology groups. -/
theorem familySourceExtension_shortExact (n : ℕ) :
    (familySourceExtension D n).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact sourceCoinvariantInclusion_kernelProjection_exact D n
  · exact sourceCoinvariantInclusion_injective D (n + 1)
  · exact sourceKernelProjection_surjective D n

/-- The literal fibre map kills exactly the integral source-monodromy differences. -/
theorem familyFibreInclusion_kernel (n : ℕ) :
    LinearMap.ker (singularHomologyMap
      (familyFibreInclusion D normalizedSlitBaseLift) n) =
      LinearMap.range (sourceDifference n) := by
  ext a
  change singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) n a = 0 ↔ _
  rw [← sourceCoinvariantInclusion_mk]
  constructor
  · intro ha
    have hq : (Submodule.Quotient.mk a :
        SingularHomology RealTorus₄ n ⧸ LinearMap.range (sourceDifference n)) = 0 :=
      sourceCoinvariantInclusion_injective D n (ha.trans (map_zero _).symm)
    exact (Submodule.Quotient.mk_eq_zero
      (p := LinearMap.range (sourceDifference n)) (x := a)).mp hq
  · intro ha
    rw [(Submodule.Quotient.mk_eq_zero
      (p := LinearMap.range (sourceDifference n)) (x := a)).mpr ha, map_zero]

/-- The coinvariant inclusion has precisely the image of the literal fibre map. -/
theorem sourceCoinvariantInclusion_range (n : ℕ) :
    LinearMap.range (sourceCoinvariantInclusion D n) =
      LinearMap.range (singularHomologyMap
        (familyFibreInclusion D normalizedSlitBaseLift) n) := by
  apply le_antisymm
  · rintro a ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨x, (sourceCoinvariantInclusion_mk D n x).symm⟩
  · rintro a ⟨x, rfl⟩
    exact ⟨Submodule.Quotient.mk x, sourceCoinvariantInclusion_mk D n x⟩

/-- The source-oriented boundary has exactly the actual fibre image as kernel. -/
theorem sourceKernelProjection_kernel (n : ℕ) :
    LinearMap.ker (sourceKernelProjection D n) =
      LinearMap.range (singularHomologyMap
        (familyFibreInclusion D normalizedSlitBaseLift) (n + 1)) :=
  (LinearMap.exact_iff.mp (sourceCoinvariantInclusion_kernelProjection_exact D n)).trans
    (sourceCoinvariantInclusion_range D (n + 1))

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

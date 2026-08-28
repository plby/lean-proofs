import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorLocal
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorAffineHomogeneous
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorDescent

/-!
# Actual descended differences of the constructed local μ sections

The numerator is the difference of the already constructed affine local
sections and the denominator is the homogeneous generator.  Distinct
patch overlaps avoid both elliptic orbits, so the denominator is nonzero
there.  The diagonal quotient is identically zero.  Consequently every
overlap quotient is genuinely holomorphic, and its all-word invariance
gives actual holomorphic descent through the quotient and the supplied
sphere coordinate.

No overlap function, holomorphic extension, or cocycle equation is
supplied as an additional input.
-/

noncomputable section

open Set Topology UpperHalfPlane TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

/-- The literal intersection of two full upstairs patch saturations. -/
def overlap (i j : Cover.Index) : Opens ℍ :=
  ⟨(Cover.patch i).saturation ∩ (Cover.patch j).saturation,
    (Cover.patch i).saturation_isOpen.inter (Cover.patch j).saturation_isOpen⟩

theorem overlap_invariant (i j : Cover.Index) (g : TriangleGroup) (z : ℍ) :
    triangleGeometricRepresentation g z ∈ overlap i j ↔ z ∈ overlap i j := by
  change (_ ∈ (Cover.patch i).saturation ∧ _ ∈ (Cover.patch j).saturation) ↔ _
  rw [(Cover.patch i).saturation_invariant, (Cover.patch j).saturation_invariant]
  rfl

variable {τ : ℍ → ℍ} (hτ : TauCovariant τ)
  (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)

def overlapQuotient (i j : Cover.Index) (z : ℍ) : ℂ :=
  (localSection hτ hτa i z - localSection hτ hτa j z) / F z

theorem overlapQuotient_invariant (hFc : MuGenerator.Homogeneous τ F)
    (i j : Cover.Index) (g : TriangleGroup) (z : ℍ) (hz : z ∈ overlap i j) :
    overlapQuotient hτ hτa F i j (triangleGeometricRepresentation g z) =
      overlapQuotient hτ hτa F i j z := by
  unfold overlapQuotient
  rw [localSection_equivariant hτ hτa i g z hz.1,
    localSection_equivariant hτ hτa j g z hz.2,
    AffineCocycle.fibreMap_sub, homogeneous_scale_law hτ hτa hFc]
  exact mul_div_mul_left _ _ (cocycle hτ hτa |>.scale g z).ne_zero

variable (hFzero : ∀ z, F z = 0 ↔
  triangleOrbitProjection z = triangleOrbitCenterOne ∨
    triangleOrbitProjection z = triangleOrbitCenterTwo)

include hFzero in
theorem overlap_generator_ne_zero {i j : Cover.Index} (hij : i ≠ j)
    {z : ℍ} (hz : z ∈ overlap i j) : F z ≠ 0 := by
  have hr := Cover.distinct_saturation_overlap_subset_regularLocus hij hz
  have hq := (triangleOrbitRegularDomain_mem_iff _).mp
    ((triangleOrbitProjection_mem_regularDomain_iff z).mpr hr)
  intro hf
  rcases (hFzero z).mp hf with h | h
  · exact hq.1 h
  · exact hq.2 h

include hFzero in
theorem overlapQuotient_holomorphic (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (i j : Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (overlapQuotient hτ hτa F i j) (overlap i j) := by
  by_cases hij : i = j
  · subst j
    have he : overlapQuotient hτ hτa F i i = fun _ => 0 := by
      funext z
      simp only [overlapQuotient, sub_self, zero_div]
    rw [he]
    exact contMDiffOn_const
  · have h₁ := (localSection_holomorphic hτ hτa i).mono
      (show (overlap i j : Set ℍ) ⊆ (Cover.patch i).saturation from inter_subset_left)
    have h₂ := (localSection_holomorphic hτ hτa j).mono
      (show (overlap i j : Set ℍ) ⊆ (Cover.patch j).saturation from inter_subset_right)
    exact (h₁.sub h₂).div₀ hF.contMDiffOn
      (fun z hz => overlap_generator_ne_zero F hFzero hij hz)

include hFzero in
/-- At a zero of `F`, the cover has only one admissible local section. -/
theorem localSection_eq_at_generator_zero (i j : Cover.Index) (z : ℍ)
    (hi : z ∈ (Cover.patch i).saturation) (hj : z ∈ (Cover.patch j).saturation)
    (hz : F z = 0) : localSection hτ hτa i z = localSection hτ hτa j z := by
  have hij : i = j := by
    by_contra h
    exact overlap_generator_ne_zero F hFzero h ⟨hi, hj⟩ hz
  rw [hij]

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ in
theorem finiteProjection_mem_patch (i : Cover.Index) (z : ℍ) :
    BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i ↔
      z ∈ (Cover.patch i).saturation :=
  (BetaTorsor.finiteProjection_mem_pullback π hπ (Cover.compactPatch i) z).trans
    (Cover.compactifiedProjection_mem_compactPatch i z)

include hπ in
theorem finiteProjection_preimage_patch (i : Cover.Index) :
    BetaTorsor.finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ) =
      (Cover.patch i).saturation := by
  ext z
  exact finiteProjection_mem_patch π hπ i z

theorem finiteDescentDomain_overlap (i j : Cover.Index) :
    (BetaTorsor.finiteDescentDomain π hπ (overlap i j) : Set ℂ) =
      (Cover.finitePatch π i : Set ℂ) ∩ Cover.finitePatch π j := by
  ext w
  obtain ⟨z, rfl⟩ := BetaTorsor.finiteProjection_surjective π hπ w
  change BetaTorsor.finiteProjection π z ∈ BetaTorsor.finiteDescentDomain π hπ (overlap i j) ↔
    BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i ∧
      BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π j
  rw [BetaTorsor.finiteDescentDomain_projection π hπ (overlap i j) (overlap_invariant i j)]
  rw [finiteProjection_mem_patch π hπ, finiteProjection_mem_patch π hπ]
  rfl

/-- The overlap coefficient is obtained by actual quotient descent, not
selected from a postulated Cousin cocycle. -/
def descendedOverlap (i j : Cover.Index) : ℂ → ℂ :=
  BetaTorsor.finiteDescent π hπ (overlap i j) (overlapQuotient hτ hτa F i j)

theorem descendedOverlap_projection (hFc : MuGenerator.Homogeneous τ F)
    (i j : Cover.Index) (z : ℍ)
    (hi : BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i)
    (hj : BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π j) :
    descendedOverlap hτ hτa F π hπ i j (BetaTorsor.finiteProjection π z) =
      (localSection hτ hτa i z - localSection hτ hτa j z) / F z := by
  exact BetaTorsor.finiteDescent_projection π hπ (overlap i j)
    (overlapQuotient hτ hτa F i j) (overlap_invariant i j)
    (overlapQuotient_invariant hτ hτa F hFc i j)
    ⟨(finiteProjection_mem_patch π hπ i z).mp hi,
      (finiteProjection_mem_patch π hπ j z).mp hj⟩

include hFzero in
theorem descendedOverlap_analytic (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hFc : MuGenerator.Homogeneous τ F) (i j : Cover.Index) :
    AnalyticOnNhd ℂ (descendedOverlap hτ hτa F π hπ i j)
      ((Cover.finitePatch π i : Set ℂ) ∩ Cover.finitePatch π j) := by
  rw [← finiteDescentDomain_overlap π hπ]
  exact BetaTorsor.finiteDescent_analytic π hπ (overlap i j)
    (overlapQuotient hτ hτa F i j) (overlap_invariant i j)
    (overlapQuotient_invariant hτ hτa F hFc i j)
    (overlapQuotient_holomorphic hτ hτa F hFzero hF i j)

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

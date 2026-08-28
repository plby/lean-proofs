import Wikipedia.HopfProblem.SpecialPeriodsTriangleCompactifiedOrdersCenters
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientOrdersTranslated
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientRamification

/-!
# Actual elliptic coordinates on the compactified triangle curve

The existing quotient charts are transported through the proved
biholomorphism with the actual cusp complement.  The compact curve keeps
its previously constructed atlas.  The transported pullbacks are exactly
the original normalized Cayley powers, so their orders are three and four
at every actual translate of the elliptic centers.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

private theorem triangleCuspComplement_nonempty_for_coordinates : Nonempty triangleCuspComplement :=
  ⟨triangleOpenInclusionToComplement triangleOrbitCenterOne⟩

/-- The literal original-quotient inclusion as an analytic partial
biholomorphism onto the actual cusp complement. -/
def triangleOpenInclusionPartial :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace TriangleCompactifiedOrbitSpace ω :=
  triangleOpenComplementBiholomorph.toPartialDiffeomorph.trans
    (opensInclusionPartialDiffeomorph 𝓘(ℂ) triangleCuspComplement
      triangleCuspComplement_nonempty_for_coordinates)

@[simp] theorem triangleOpenInclusionPartial_source :
    triangleOpenInclusionPartial.source = univ := by
  simp [triangleOpenInclusionPartial, PartialDiffeomorph.trans,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp] theorem triangleOpenInclusionPartial_target :
    triangleOpenInclusionPartial.target =
      (triangleCuspComplement : Set TriangleCompactifiedOrbitSpace) := by
  simp [triangleOpenInclusionPartial, PartialDiffeomorph.trans,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp] theorem triangleOpenInclusionPartial_apply (q : TriangleOrbitSpace) :
    triangleOpenInclusionPartial q = triangleOpenInclusion q := rfl

@[simp] theorem triangleOpenInclusionPartial_symm_apply (q : TriangleOrbitSpace) :
    triangleOpenInclusionPartial.symm (triangleOpenInclusion q) = q := by
  change triangleOpenInclusionPartial.toPartialEquiv.invFun
    (triangleOpenInclusionPartial.toPartialEquiv.toFun q) = q
  exact triangleOpenInclusionPartial.toPartialEquiv.left_inv (by simp)

namespace Triangle

/-- The actual old elliptic partial coordinate, transported through the
proved analytic inclusion.  Both maps are analytic for the existing atlas. -/
def ellipticCompactifiedPartial (j : Elliptic.Kind) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace ℂ ω :=
  triangleOpenInclusionPartial.symm.trans (triangleOrbitCoordinatePartial (.inr j))

def ellipticCompactifiedChart (j : Elliptic.Kind) :
    OpenPartialHomeomorph TriangleCompactifiedOrbitSpace ℂ :=
  (ellipticCompactifiedPartial j).toOpenPartialHomeomorph

@[simp] theorem ellipticCompactifiedChart_openInclusion (j : Elliptic.Kind)
    (q : TriangleOrbitSpace) :
    ellipticCompactifiedChart j (triangleOpenInclusion q) = ellipticFullChart j q := by
  change ellipticFullChart j (triangleOpenInclusionPartial.symm (triangleOpenInclusion q)) = _
  rw [triangleOpenInclusionPartial_symm_apply]

@[simp] theorem openInclusion_mem_ellipticCompactifiedChart_source (j : Elliptic.Kind)
    (q : TriangleOrbitSpace) :
    triangleOpenInclusion q ∈ (ellipticCompactifiedChart j).source ↔
      q ∈ (ellipticFullChart j).source := by
  change (triangleOpenInclusion q ∈ triangleOpenInclusionPartial.target ∧
    triangleOpenInclusionPartial.symm (triangleOpenInclusion q) ∈
      (ellipticFullChart j).source) ↔ _
  rw [triangleOpenInclusionPartial_target, triangleOpenInclusionPartial_symm_apply]
  exact and_iff_right (triangleOpenInclusion_ne_cusp q)

theorem ellipticCompactifiedChart_source (j : Elliptic.Kind) :
    (ellipticCompactifiedChart j).source =
      triangleOpenInclusion '' (ellipticFullChart j).source := by
  ext x
  constructor
  · intro hx
    have hc : x ∈ triangleCuspComplement := by
      have h := hx.1
      change x ∈ triangleOpenInclusionPartial.target at h
      rwa [triangleOpenInclusionPartial_target] at h
    obtain ⟨q, hq⟩ := OnePoint.ne_infty_iff_exists.mp hc
    have hq' : triangleOpenInclusion q = x := hq
    refine ⟨q, ?_, hq'⟩
    apply (openInclusion_mem_ellipticCompactifiedChart_source j q).mp
    rw [hq']
    exact hx
  · rintro ⟨q, hq, rfl⟩
    exact (openInclusion_mem_ellipticCompactifiedChart_source j q).mpr hq

@[simp] theorem ellipticCompactifiedChart_target (j : Elliptic.Kind) :
    (ellipticCompactifiedChart j).target = (unitDisc : Set ℂ) := by
  change (ellipticFullChart j).target ∩
    (ellipticFullChart j).symm ⁻¹' triangleOpenInclusionPartial.source = _
  rw [triangleOpenInclusionPartial_source, preimage_univ, inter_univ,
    ellipticFullChart_target]

theorem cusp_not_mem_ellipticCompactifiedChart_source (j : Elliptic.Kind) :
    triangleCuspPoint ∉ (ellipticCompactifiedChart j).source := by
  rw [ellipticCompactifiedChart_source]
  rintro ⟨q, _, hq⟩
  exact triangleOpenInclusion_ne_cusp q hq

theorem ellipticCompactifiedChart_center_mem_source (j : Elliptic.Kind) :
    ellipticCompactifiedCenter j ∈ (ellipticCompactifiedChart j).source :=
  (openInclusion_mem_ellipticCompactifiedChart_source j (ellipticOrbitCenter j)).mpr
    (ellipticFullChart_center_mem_source j)

@[simp] theorem ellipticCompactifiedChart_center (j : Elliptic.Kind) :
    ellipticCompactifiedChart j (ellipticCompactifiedCenter j) = 0 := by
  change ellipticCompactifiedChart j (triangleOpenInclusion (ellipticOrbitCenter j)) = 0
  rw [ellipticCompactifiedChart_openInclusion, ellipticFullChart_center]

theorem ellipticCompactifiedChart_holomorphic (j : Elliptic.Kind) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (ellipticCompactifiedChart j)
      (ellipticCompactifiedChart j).source :=
  (ellipticCompactifiedPartial j).contMDiffOn

theorem ellipticCompactifiedChart_symm_holomorphic (j : Elliptic.Kind) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (ellipticCompactifiedChart j).symm
      (ellipticCompactifiedChart j).target :=
  (ellipticCompactifiedPartial j).symm.contMDiffOn

theorem ellipticCompactifiedChart_isLocalDiffeomorphAt (j : Elliptic.Kind)
    {x : TriangleCompactifiedOrbitSpace} (hx : x ∈ (ellipticCompactifiedChart j).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (ellipticCompactifiedChart j) x :=
  (ellipticCompactifiedPartial j).isLocalDiffeomorphAt _ _ _ hx

/-- Exact equality of the native pulled-back coordinates on the entire
upper half-plane, not just equality of their orders. -/
theorem ellipticCompactifiedChart_pullback_eq (j : Elliptic.Kind) :
    ellipticCompactifiedChart j ∘ triangleCompactifiedProjection =
      ellipticFullChart j ∘ triangleOrbitProjection := by
  funext z
  exact ellipticCompactifiedChart_openInclusion j (triangleOrbitProjection z)

theorem ellipticCompactifiedChart_complexGerm_eq (j : Elliptic.Kind) :
    ellipticCompactifiedChart j ∘ triangleCompactifiedProjection ∘ ofComplex =
      ellipticFullChart j ∘ triangleOrbitProjection ∘ ofComplex := by
  funext z
  exact ellipticCompactifiedChart_openInclusion j (triangleOrbitProjection (ofComplex z))

/-- The actual compact projection is the normalized Cayley third or
fourth power on the corresponding uniformizing neighborhood. -/
theorem ellipticCompactifiedChart_projection (j : Elliptic.Kind) (z : ellipticNeighborhood j) :
    ellipticCompactifiedChart j (triangleCompactifiedProjection z) =
      normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order z := by
  change (ellipticCompactifiedChart j ∘ triangleCompactifiedProjection) z = _
  rw [ellipticCompactifiedChart_pullback_eq]
  exact ellipticFullChart_projection j z

/-- The same exact local branch equation on every actual translated
uniformizing neighborhood. -/
theorem ellipticCompactifiedChart_projection_translated (j : Elliptic.Kind)
    (g : TriangleGroup) (z : ellipticNeighborhood j) :
    ellipticCompactifiedChart j
      (triangleCompactifiedProjection (triangleGeometricRepresentation g z)) =
      normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order z := by
  simp only [triangleCompactifiedProjection, Function.comp_apply,
    triangleOrbitProjection_smul, ellipticCompactifiedChart_openInclusion]
  exact ellipticFullChart_projection j z

theorem ellipticCompactifiedChart_complexGerm_analyticAt_translated_center
    (j : Elliptic.Kind) (g : TriangleGroup) :
    AnalyticAt ℂ (ellipticCompactifiedChart j ∘ triangleCompactifiedProjection ∘ ofComplex)
      (triangleGeometricRepresentation g (ellipticCenter j) : ℂ) := by
  rw [ellipticCompactifiedChart_complexGerm_eq]
  exact ellipticFullChart_complexGerm_analyticAt_translated_center j g

/-- Exact analytic ramification order at every point of either full
elliptic orbit in the actual compact quotient curve. -/
theorem ellipticCompactifiedChart_order_translated_center (j : Elliptic.Kind) (g : TriangleGroup) :
    analyticOrderAt (ellipticCompactifiedChart j ∘ triangleCompactifiedProjection ∘ ofComplex)
      (triangleGeometricRepresentation g (ellipticCenter j) : ℂ) = (j.order : ℕ∞) := by
  rw [ellipticCompactifiedChart_complexGerm_eq]
  exact ellipticFullChart_order_translated_center j g

theorem ellipticCompactifiedChart_order_center (j : Elliptic.Kind) :
    analyticOrderAt (ellipticCompactifiedChart j ∘ triangleCompactifiedProjection ∘ ofComplex)
      (ellipticCenter j : ℂ) = (j.order : ℕ∞) := by
  rw [ellipticCompactifiedChart_complexGerm_eq]
  exact ellipticFullChart_order_center j

theorem ellipticCompactifiedChart_order_translated_centerOne (g : TriangleGroup) :
    analyticOrderAt (ellipticCompactifiedChart .three ∘ triangleCompactifiedProjection ∘ ofComplex)
      (triangleGeometricRepresentation g centerOne : ℂ) = 3 :=
  ellipticCompactifiedChart_order_translated_center .three g

theorem ellipticCompactifiedChart_order_translated_centerTwo (g : TriangleGroup) :
    analyticOrderAt (ellipticCompactifiedChart .four ∘ triangleCompactifiedProjection ∘ ofComplex)
      (triangleGeometricRepresentation g centerTwo : ℂ) = 4 :=
  ellipticCompactifiedChart_order_translated_center .four g

end Triangle

/-- Compactification adds no ramification on the original upper half-plane. -/
theorem triangleCompactifiedProjection_isLocalDiffeomorphAt_iff (z : ℍ) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleCompactifiedProjection z ↔
      z ∈ triangleRegularLocus := by
  constructor
  · intro hz
    have hsource : triangleCompactifiedProjection z ∈ triangleOpenInclusionPartial.target := by
      rw [triangleOpenInclusionPartial_target]
      exact triangleCompactifiedProjection_ne_cusp z
    have hi := triangleOpenInclusionPartial.symm.isLocalDiffeomorphAt _ _ _ hsource
    have hc := hz.comp (K := 𝓘(ℂ)) (P := TriangleOrbitSpace) hi
    have he : triangleOpenInclusionPartial.symm ∘ triangleCompactifiedProjection =
        triangleOrbitProjection := by
      funext w
      exact triangleOpenInclusionPartial_symm_apply (triangleOrbitProjection w)
    rw [he] at hc
    exact (triangleOrbitProjection_isLocalDiffeomorphAt_iff z).mp hc
  · exact triangleCompactifiedProjection_isLocalDiffeomorphAt_of_regular

theorem triangleCompactifiedProjection_not_isLocalDiffeomorphAt_iff (z : ℍ) :
    ¬ IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleCompactifiedProjection z ↔
      z ∈ triangleEllipticSet := by
  simp only [triangleCompactifiedProjection_isLocalDiffeomorphAt_iff,
    triangleRegularLocus_eq_compl_ellipticSet, mem_compl_iff, not_not]

end Wikipedia.HopfProblem.SpecialPeriods

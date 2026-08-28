import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticCharts
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientRegularChartsTopology
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCompactifiedOrders
import Wikipedia.HopfProblem.EllipticLogGaugeBasic
import Wikipedia.HopfProblem.EllipticLogGaugeRotation
import Wikipedia.HopfProblem.CuspPuncturedCovering

/-!
# The actual punctured elliptic chart in the regular triangle covering

The inverse normalized Cayley chart maps the full punctured unit disc
into the actual regular triangle locus. Its image is precisely the
regular points of the chosen no-return elliptic neighborhood. The
stabilizer rotation and the full quotient power coordinate are the
ones already used in the corresponding elliptic filling.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic.LogGauge

attribute [local instance] triangleGeometricAction

/-- The actual neighborhood point supplied by the inverse disc chart. -/
def neighborhoodPoint (j : Elliptic.Kind) (z : BaseStar) : Triangle.ellipticNeighborhood j :=
  (Triangle.ellipticNeighborhoodChart j).symm z.val

theorem neighborhoodPoint_ne_center (j : Elliptic.Kind) (z : BaseStar) :
    neighborhoodPoint j z ≠ Triangle.ellipticNeighborhoodCenter j := by
  intro he
  have hc := congrArg (Triangle.ellipticNeighborhoodChart j) he
  have hz : z.val = discZero := by
    simpa only [neighborhoodPoint, Diffeomorph.apply_symm_apply,
      Triangle.ellipticNeighborhoodChart_center] using hc
  exact z.property (congrArg (fun u : Disc => (u : ℂ)) hz)

/-- Removing the chart center excludes both exceptional elliptic orbits. -/
theorem localBase_regular (j : Elliptic.Kind) (z : BaseStar) :
    (neighborhoodPoint j z : ℍ) ∈ triangleRegularLocus := by
  have hself : triangleOrbitProjection (neighborhoodPoint j z) ≠
      Triangle.ellipticOrbitCenter j := fun he => neighborhoodPoint_ne_center j z
    ((Triangle.ellipticNeighborhood_projection_eq_center_iff j (neighborhoodPoint j z)).mp he)
  have hother := Triangle.ellipticNeighborhood_avoids_other j
    (neighborhoodPoint j z) (neighborhoodPoint j z).property
  apply (triangleOrbitProjection_mem_regularDomain_iff _).mp
  apply (triangleOrbitRegularDomain_mem_iff _).mpr
  cases j
  · exact ⟨hself, hother⟩
  · exact ⟨hother, hself⟩

/-- The full punctured disc maps to the literal regular triangle domain. -/
def localBase (j : Elliptic.Kind) (z : BaseStar) : TriangleRegularPoint :=
  ⟨neighborhoodPoint j z, localBase_regular j z⟩

@[simp] theorem localBase_val (j : Elliptic.Kind) (z : BaseStar) :
    (localBase j z : ℍ) = ((Triangle.ellipticNeighborhoodChart j).symm z.val : ℍ) := rfl

theorem localBase_mem_neighborhood (j : Elliptic.Kind) (z : BaseStar) :
    (localBase j z : ℍ) ∈ Triangle.ellipticNeighborhood j :=
  (neighborhoodPoint j z).property

@[simp] theorem localBase_chart (j : Elliptic.Kind) (z : BaseStar) :
    Triangle.ellipticNeighborhoodChart j
      ⟨(localBase j z : ℍ), localBase_mem_neighborhood j z⟩ = z.val :=
  (Triangle.ellipticNeighborhoodChart j).apply_symm_apply z.val

theorem localBase_injective (j : Elliptic.Kind) : Function.Injective (localBase j) := by
  intro z w he
  have hv : (localBase j z : ℍ) = (localBase j w : ℍ) :=
    congrArg (fun u : TriangleRegularPoint => (u : ℍ)) he
  have hn : (Triangle.ellipticNeighborhoodChart j).symm z.val =
      (Triangle.ellipticNeighborhoodChart j).symm w.val := Subtype.ext hv
  exact Subtype.ext ((Triangle.ellipticNeighborhoodChart j).symm.injective hn)

/-- The inverse chart and the two open inclusions are actual local
holomorphic diffeomorphisms for the inherited manifold structures. -/
theorem localBase_isLocalDiffeomorph (j : Elliptic.Kind) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (localBase j) := by
  have hn : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (neighborhoodPoint j) := by
    intro z
    exact (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) baseOpen z).comp
      (K := 𝓘(ℂ)) (P := Triangle.ellipticNeighborhood j)
      ((Triangle.ellipticNeighborhoodChart j).symm.isLocalDiffeomorph z.val)
  have hv : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : BaseStar => (neighborhoodPoint j z : ℍ)) := by
    intro z
    exact (hn z).comp (K := 𝓘(ℂ)) (P := ℍ)
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) (Triangle.ellipticNeighborhood j)
        (neighborhoodPoint j z))
  exact isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ) hv triangleRegularDomain
    (localBase_regular j)

theorem localBase_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (localBase j) :=
  (localBase_isLocalDiffeomorph j).contMDiff

theorem localBase_continuous (j : Elliptic.Kind) : Continuous (localBase j) :=
  (localBase_holomorphic j).continuous

theorem localBase_isOpenEmbedding (j : Elliptic.Kind) : IsOpenEmbedding (localBase j) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (localBase_continuous j)
    (localBase_injective j) (localBase_isLocalDiffeomorph j).isLocalHomeomorph.isOpenMap

theorem ellipticCenter_not_regular (j : Elliptic.Kind) :
    Triangle.ellipticCenter j ∉ triangleRegularLocus := by
  cases j
  · exact triangle_centerOne_not_regular
  · exact triangle_centerTwo_not_regular

theorem neighborhoodChart_ne_zero_of_regular (j : Elliptic.Kind)
    (u : Triangle.ellipticNeighborhood j) (hu : (u : ℍ) ∈ triangleRegularLocus) :
    (Triangle.ellipticNeighborhoodChart j u : ℂ) ≠ 0 := by
  intro he
  have hchart : Triangle.ellipticNeighborhoodChart j u = discZero := Subtype.ext he
  have huc : u = Triangle.ellipticNeighborhoodCenter j :=
    (Triangle.ellipticNeighborhoodChart j).injective
      (hchart.trans (Triangle.ellipticNeighborhoodChart_center j).symm)
  have hc : (u : ℍ) = Triangle.ellipticCenter j := congrArg Subtype.val huc
  exact ellipticCenter_not_regular j (hc ▸ hu)

/-- The local chart has the full punctured neighborhood as its image,
not an unmentioned smaller germ. -/
theorem localBase_range (j : Elliptic.Kind) :
    range (localBase j) =
      {u : TriangleRegularPoint | (u : ℍ) ∈ Triangle.ellipticNeighborhood j} := by
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    exact localBase_mem_neighborhood j z
  · intro hu
    let v : Triangle.ellipticNeighborhood j := ⟨u.val, hu⟩
    let z : BaseStar := ⟨Triangle.ellipticNeighborhoodChart j v,
      neighborhoodChart_ne_zero_of_regular j v u.property⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change ((Triangle.ellipticNeighborhoodChart j).symm
      (Triangle.ellipticNeighborhoodChart j v) : ℍ) = (u : ℍ)
    exact congrArg (fun q : Triangle.ellipticNeighborhood j => (q : ℍ))
      ((Triangle.ellipticNeighborhoodChart j).symm_apply_apply v)

/-- The actual negative primitive rotation restricted to the punctured disc. -/
def puncturedRotation (j : Elliptic.Kind) (z : BaseStar) : BaseStar :=
  ⟨Elliptic.familyRotation j z.val, familyRotation_ne_zero j z.val z.property⟩

@[simp] theorem puncturedRotation_val (j : Elliptic.Kind) (z : BaseStar) :
    (puncturedRotation j z).val = Elliptic.familyRotation j z.val := rfl

/-- The actual neighborhood generator acts by exactly the filling's rotation. -/
theorem localBase_rotation (j : Elliptic.Kind) (z : BaseStar) :
    localBase j (puncturedRotation j z) = Triangle.ellipticGenerator j • localBase j z := by
  let := Triangle.ellipticNeighborhoodAction j
  have he : (Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z.val) =
      Triangle.ellipticStabilizerGenerator j •
        (Triangle.ellipticNeighborhoodChart j).symm z.val := by
    apply (Triangle.ellipticNeighborhoodChart j).injective
    change Triangle.ellipticNeighborhoodChart j
      ((Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z.val)) =
      Triangle.ellipticNeighborhoodChart j (Triangle.ellipticStabilizerGenerator j •
        (Triangle.ellipticNeighborhoodChart j).symm z.val)
    rw [Diffeomorph.apply_symm_apply, Triangle.ellipticNeighborhoodChart_generator,
      Diffeomorph.apply_symm_apply]
  apply Subtype.ext
  exact congrArg (fun u : Triangle.ellipticNeighborhood j => (u : ℍ)) he

theorem localBase_rotation_iterate (j : Elliptic.Kind) (n : ℕ) (z : BaseStar) :
    localBase j ((puncturedRotation j)^[n] z) =
      Triangle.ellipticGenerator j ^ n • localBase j z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', localBase_rotation, ih, pow_succ', mul_smul]

/-- The actual projection of the local punctured chart to the regular
triangle quotient, before taking its cyclic rotation quotient. -/
def baseQuotient (j : Elliptic.Kind) : BaseStar → TriangleRegularQuotient :=
  triangleRegularProject ∘ localBase j

@[simp] theorem baseQuotient_apply (j : Elliptic.Kind) (z : BaseStar) :
    baseQuotient j z = triangleRegularProject (localBase j z) := rfl

@[simp] theorem baseQuotient_toOrbit (j : Elliptic.Kind) (z : BaseStar) :
    triangleRegularToOrbit (baseQuotient j z) =
      triangleOrbitProjection (localBase j z : ℍ) := rfl

theorem baseQuotient_continuous (j : Elliptic.Kind) : Continuous (baseQuotient j) :=
  triangleRegularProject_covering.continuous.comp (localBase_continuous j)

/-- The projected punctured chart is locally biholomorphic for the actual
regular quotient atlas obtained from its covering. -/
theorem baseQuotient_isLocalDiffeomorph (j : Elliptic.Kind) :
    letI := triangleRegularQuotientChartedSpace
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (baseQuotient j) := by
  let := triangleRegularQuotientChartedSpace
  intro z
  exact (localBase_isLocalDiffeomorph j z).comp (K := 𝓘(ℂ)) (P := TriangleRegularQuotient)
    (triangleRegularProject_isLocalDiffeomorph (localBase j z))

theorem baseQuotient_holomorphic (j : Elliptic.Kind) :
    letI := triangleRegularQuotientChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (baseQuotient j) := by
  let := triangleRegularQuotientChartedSpace
  exact (baseQuotient_isLocalDiffeomorph j).contMDiff

theorem baseQuotient_isOpenMap (j : Elliptic.Kind) : IsOpenMap (baseQuotient j) := by
  let := triangleRegularQuotientChartedSpace
  exact (baseQuotient_isLocalDiffeomorph j).isLocalHomeomorph.isOpenMap

@[simp] theorem baseQuotient_rotation (j : Elliptic.Kind) (z : BaseStar) :
    baseQuotient j (puncturedRotation j z) = baseQuotient j z := by
  change triangleRegularProject (localBase j (puncturedRotation j z)) = _
  rw [localBase_rotation]
  exact triangleRegularProject_covering.map_smul (Triangle.ellipticGenerator j)

theorem baseQuotient_rotation_iterate (j : Elliptic.Kind) (n : ℕ) (z : BaseStar) :
    baseQuotient j ((puncturedRotation j)^[n] z) = baseQuotient j z := by
  change triangleRegularProject (localBase j ((puncturedRotation j)^[n] z)) = _
  rw [localBase_rotation_iterate]
  exact triangleRegularProject_covering.map_smul (Triangle.ellipticGenerator j ^ n)

/-- No element outside the actual finite stabilizer identifies two
points in this punctured neighborhood. The bounded exponent also
specifies their exact disc rotation. -/
theorem localBase_orbit_classification (j : Elliptic.Kind) (g : TriangleGroup)
    (z w : BaseStar) (h : g • localBase j z = localBase j w) :
    ∃ n : ℕ, n < j.order ∧ g = Triangle.ellipticGenerator j ^ n ∧
      w = (puncturedRotation j)^[n] z := by
  have hambient : g • (localBase j z : ℍ) = (localBase j w : ℍ) :=
    congrArg Subtype.val h
  have hg : g ∈ Triangle.ellipticStabilizer j :=
    Triangle.ellipticNeighborhood_return j g
      ⟨(localBase j w : ℍ),
        ⟨(localBase j z : ℍ), localBase_mem_neighborhood j z, hambient⟩,
        localBase_mem_neighborhood j w⟩
  obtain ⟨n, hn, rfl⟩ := (Triangle.mem_ellipticStabilizer_iff j g).mp hg
  refine ⟨n, hn, rfl, ?_⟩
  apply localBase_injective j
  exact ((localBase_rotation_iterate j n z).trans h).symm

theorem localBase_smul_eq_iff (j : Elliptic.Kind) (g : TriangleGroup)
    (z w : BaseStar) :
    g • localBase j z = localBase j w ↔
      ∃ n : ℕ, n < j.order ∧ g = Triangle.ellipticGenerator j ^ n ∧
        w = (puncturedRotation j)^[n] z := by
  constructor
  · exact localBase_orbit_classification j g z w
  · rintro ⟨n, hn, rfl, rfl⟩
    exact (localBase_rotation_iterate j n z).symm

theorem localBase_projection_eq_iff (j : Elliptic.Kind) (z w : BaseStar) :
    triangleOrbitProjection (localBase j z : ℍ) =
        triangleOrbitProjection (localBase j w : ℍ) ↔
      ∃ n : ℕ, n < j.order ∧ w = (puncturedRotation j)^[n] z := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff _ _).mp h.symm
    have he : g • localBase j z = localBase j w := Subtype.ext hg
    obtain ⟨n, hn, hgn, hw⟩ := localBase_orbit_classification j g z w he
    exact ⟨n, hn, hw⟩
  · rintro ⟨n, hn, rfl⟩
    apply Eq.symm
    apply (triangleOrbitProjection_eq_iff _ _).mpr
    refine ⟨Triangle.ellipticGenerator j ^ n, ?_⟩
    exact congrArg Subtype.val (localBase_rotation_iterate j n z).symm

/-- The fibres of the projected punctured chart are exactly the finite
rotation orbits; this is derived from the actual triangle orbit relation. -/
theorem baseQuotient_eq_iff (j : Elliptic.Kind) (z w : BaseStar) :
    baseQuotient j z = baseQuotient j w ↔
      ∃ n : ℕ, n < j.order ∧ w = (puncturedRotation j)^[n] z := by
  rw [← triangleRegularToOrbit_injective.eq_iff]
  exact localBase_projection_eq_iff j z w

/-- The full elliptic quotient coordinate is the actual power coordinate
on the entire punctured unit disc. -/
theorem ellipticFullChart_localBase (j : Elliptic.Kind) (z : BaseStar) :
    Triangle.ellipticFullChart j (triangleOrbitProjection (localBase j z : ℍ)) =
      (z.val : ℂ) ^ j.order := by
  rw [localBase_val, Triangle.ellipticFullChart_projection]
  change ((Triangle.ellipticNeighborhoodChart j
    ((Triangle.ellipticNeighborhoodChart j).symm z.val) : Disc) : ℂ) ^ j.order = _
  rw [Diffeomorph.apply_symm_apply]

theorem ellipticFullChart_baseQuotient (j : Elliptic.Kind) (z : BaseStar) :
    Triangle.ellipticFullChart j (triangleRegularToOrbit (baseQuotient j z)) =
      (z.val : ℂ) ^ j.order :=
  ellipticFullChart_localBase j z

/-- The same exact coordinate after the actual inclusion into the
compactified triangle quotient. -/
theorem compactifiedBaseQuotient_chart (j : Elliptic.Kind) (z : BaseStar) :
    Triangle.ellipticCompactifiedChart j
        (triangleOpenInclusion (triangleRegularToOrbit (baseQuotient j z))) =
      (z.val : ℂ) ^ j.order := by
  rw [Triangle.ellipticCompactifiedChart_openInclusion, ellipticFullChart_baseQuotient]

/-- In the full orbit space the exact image is the chosen elliptic
neighborhood with its single elliptic point removed. -/
theorem localBase_projection_range (j : Elliptic.Kind) :
    range (triangleOrbitProjection ∘ Subtype.val ∘ localBase j) =
      (Triangle.ellipticNeighborhoodImage j : Set TriangleOrbitSpace) \
        {Triangle.ellipticOrbitCenter j} := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    change triangleOrbitProjection (localBase j z).val ∈
      (Triangle.ellipticNeighborhoodImage j : Set TriangleOrbitSpace) \
        {Triangle.ellipticOrbitCenter j}
    constructor
    · exact ⟨(localBase j z).val, localBase_mem_neighborhood j z, rfl⟩
    · change triangleOrbitProjection (neighborhoodPoint j z) ≠
        Triangle.ellipticOrbitCenter j
      intro he
      exact neighborhoodPoint_ne_center j z
        ((Triangle.ellipticNeighborhood_projection_eq_center_iff j
          (neighborhoodPoint j z)).mp he)
  · rintro ⟨⟨u, hu, rfl⟩, hne⟩
    change triangleOrbitProjection u ≠ Triangle.ellipticOrbitCenter j at hne
    have hu0 : (Triangle.ellipticNeighborhoodChart j ⟨u, hu⟩ : ℂ) ≠ 0 := by
      intro he
      apply hne
      apply (Triangle.ellipticNeighborhood_projection_eq_center_iff j ⟨u, hu⟩).mpr
      apply (Triangle.ellipticNeighborhoodChart j).injective
      exact (Subtype.ext he).trans (Triangle.ellipticNeighborhoodChart_center j).symm
    let z : BaseStar := ⟨Triangle.ellipticNeighborhoodChart j ⟨u, hu⟩, hu0⟩
    refine ⟨z, ?_⟩
    change triangleOrbitProjection (localBase j z).val = triangleOrbitProjection u
    rw [localBase_val]
    exact congrArg triangleOrbitProjection
      (congrArg Subtype.val ((Triangle.ellipticNeighborhoodChart j).symm_apply_apply ⟨u, hu⟩))

/-- The actual open patch of the regular quotient overlapping the
elliptic filling. Its definition uses the already chosen full elliptic
neighborhood, rather than a new smaller neighborhood. -/
def regularBasePatch (j : Elliptic.Kind) : TopologicalSpace.Opens TriangleRegularQuotient :=
  ⟨triangleRegularToOrbit ⁻¹' (Triangle.ellipticNeighborhoodImage j : Set TriangleOrbitSpace),
    (Triangle.ellipticNeighborhoodImage j).isOpen.preimage triangleRegularToOrbit_continuous⟩

@[simp] theorem regularBasePatch_mem (j : Elliptic.Kind) (q : TriangleRegularQuotient) :
    q ∈ regularBasePatch j ↔ triangleRegularToOrbit q ∈ Triangle.ellipticNeighborhoodImage j :=
  Iff.rfl

theorem baseQuotient_mem_regularBasePatch (j : Elliptic.Kind) (z : BaseStar) :
    baseQuotient j z ∈ regularBasePatch j :=
  ⟨(localBase j z : ℍ), localBase_mem_neighborhood j z, rfl⟩

/-- Every point of the full regular overlap is represented by the
punctured disc, and no other regular quotient point is represented. -/
theorem baseQuotient_range (j : Elliptic.Kind) :
    range (baseQuotient j) = (regularBasePatch j : Set TriangleRegularQuotient) := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact baseQuotient_mem_regularBasePatch j z
  · rintro ⟨u, hu, he⟩
    change triangleOrbitProjection u = triangleRegularToOrbit q at he
    have hreg : u ∈ triangleRegularLocus := by
      apply (triangleOrbitProjection_mem_regularDomain_iff u).mp
      rw [he]
      exact ⟨q, rfl⟩
    have hin : (⟨u, hreg⟩ : TriangleRegularPoint) ∈ range (localBase j) := by
      rw [localBase_range]
      exact hu
    obtain ⟨z, hz⟩ := hin
    refine ⟨z, triangleRegularToOrbit_injective ?_⟩
    rw [baseQuotient_toOrbit, hz]
    exact he

/-- Membership in the literal compactified chart source is exactly
membership in the regular overlap patch. -/
theorem regularBasePatch_mem_iff_compactifiedChart (j : Elliptic.Kind)
    (q : TriangleRegularQuotient) :
    q ∈ regularBasePatch j ↔
      triangleOpenInclusion (triangleRegularToOrbit q) ∈
        (Triangle.ellipticCompactifiedChart j).source := by
  rw [Triangle.openInclusion_mem_ellipticCompactifiedChart_source,
    Triangle.ellipticFullChart_source]
  rfl

theorem compactifiedBaseQuotient_mem_chart (j : Elliptic.Kind) (z : BaseStar) :
    triangleOpenInclusion (triangleRegularToOrbit (baseQuotient j z)) ∈
      (Triangle.ellipticCompactifiedChart j).source :=
  (regularBasePatch_mem_iff_compactifiedChart j _).mp
    (baseQuotient_mem_regularBasePatch j z)

/-- The actual compactified base point is recovered by the inverse
compactified chart from the filling's power coordinate. -/
theorem compactifiedBaseQuotient_eq_chart_symm (j : Elliptic.Kind) (z : BaseStar) :
    triangleOpenInclusion (triangleRegularToOrbit (baseQuotient j z)) =
      (Triangle.ellipticCompactifiedChart j).symm ((z.val : ℂ) ^ j.order) := by
  have he := (Triangle.ellipticCompactifiedChart j).left_inv
    (compactifiedBaseQuotient_mem_chart j z)
  rw [compactifiedBaseQuotient_chart] at he
  exact he.symm

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

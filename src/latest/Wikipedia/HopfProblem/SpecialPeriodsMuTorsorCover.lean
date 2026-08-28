import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCore
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCoverRegular
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCoverSphere
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticCharts
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspRegular

/-!
# The actual common quotient cover for the period torsors

The regular covering sheets, the two precisely invariant elliptic discs,
and the primitive cusp horodisc define actual subgroup patches upstairs.
Their orbit images, with the actual cusp added to the cusp image, cover the
compact quotient. A supplied normalized sphere identification transports
this cover to the complex plane. Distinct patch overlaps contain neither
elliptic point, and the cusp patch contains an exterior complex region.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Cover

open Triangle

attribute [local instance] triangleGeometricAction triangleCompactifiedChartedSpace

/-- One actual cusp patch, all actual regular sheets, and the two elliptic
neighbourhoods. -/
abbrev Index := Option (TriangleRegularQuotient ⊕ Elliptic.Kind)

def cuspIndex : Index := none
def regularIndex (x : TriangleRegularQuotient) : Index := some (.inl x)
def ellipticIndex (j : Elliptic.Kind) : Index := some (.inr j)

/-- The high horodisc and its proved primitive cusp returning subgroup. -/
def cuspPatch : PreciselyInvariantPatch where
  sheet := horodisc width
  stabilizer := Subgroup.zpowers triangleCuspGenerator
  mapsTo := cusp_horodisc_invariant width
  returning := triangle_horodisc_overlap_mem_cusp width le_rfl

/-- A genuine regular covering sheet has trivial returning subgroup. -/
def regularPatch (x : TriangleRegularQuotient) : PreciselyInvariantPatch where
  sheet := regularSheet x
  stabilizer := ⊥
  mapsTo := by
    intro g z hz
    have hg : (g : TriangleGroup) = 1 := Subgroup.mem_bot.mp g.property
    simpa only [hg, map_one, Equiv.Perm.one_apply] using hz
  returning := fun g hg => Subgroup.mem_bot.mpr (regularSheet_no_return x g hg)

/-- The actual stabilizer and the chosen precisely invariant Cayley disc. -/
def ellipticPatch (j : Elliptic.Kind) : PreciselyInvariantPatch where
  sheet := ellipticNeighborhood j
  stabilizer := ellipticStabilizer j
  mapsTo := ellipticNeighborhood_mapsTo j
  returning := ellipticNeighborhood_return j

def patch : Index → PreciselyInvariantPatch
  | none => cuspPatch
  | some (.inl x) => regularPatch x
  | some (.inr j) => ellipticPatch j

@[simp] theorem patch_cusp : patch cuspIndex = cuspPatch := rfl
@[simp] theorem patch_regular (x : TriangleRegularQuotient) :
    patch (regularIndex x) = regularPatch x := rfl
@[simp] theorem patch_elliptic (j : Elliptic.Kind) :
    patch (ellipticIndex j) = ellipticPatch j := rfl

theorem patch_sheet_nonempty (i : Index) : ((patch i).sheet : Set ℍ).Nonempty := by
  cases i with
  | none => exact horodisc_nonempty width
  | some i =>
    cases i with
    | inl x => exact regularSheet_nonempty x
    | inr j => exact ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j⟩

/-- An actual open image in the original orbit quotient, included in its
one-point compactification. -/
def compactImage (V : TopologicalSpace.Opens TriangleOrbitSpace) :
    TopologicalSpace.Opens TriangleCompactifiedOrbitSpace :=
  ⟨triangleOpenInclusion '' (V : Set TriangleOrbitSpace),
    triangleOpenInclusion_isOpenEmbedding.isOpenMap _ V.isOpen⟩

@[simp] theorem openInclusion_mem_compactImage
    (V : TopologicalSpace.Opens TriangleOrbitSpace) (q : TriangleOrbitSpace) :
    triangleOpenInclusion q ∈ compactImage V ↔ q ∈ V :=
  triangleOpenInclusion_isOpenEmbedding.injective.mem_set_image

theorem cusp_not_mem_compactImage (V : TopologicalSpace.Opens TriangleOrbitSpace) :
    triangleCuspPoint ∉ compactImage V := by
  rintro ⟨q, _, hq⟩
  exact triangleOpenInclusion_ne_cusp q hq

/-- The original quotient images, with the genuine added cusp only in the
horodisc patch. -/
def compactPatch : Index → TopologicalSpace.Opens TriangleCompactifiedOrbitSpace
  | none => cuspNeighborhood width
  | some (.inl x) => compactImage (regularImage x)
  | some (.inr j) => compactImage (ellipticNeighborhoodImage j)

@[simp] theorem compactPatch_cusp : compactPatch cuspIndex = cuspNeighborhood width := rfl
@[simp] theorem compactPatch_regular (x : TriangleRegularQuotient) :
    compactPatch (regularIndex x) = compactImage (regularImage x) := rfl
@[simp] theorem compactPatch_elliptic (j : Elliptic.Kind) :
    compactPatch (ellipticIndex j) = compactImage (ellipticNeighborhoodImage j) := rfl

/-- Each open compactified patch restricts to exactly the actual orbit image
of its specified upper-half-plane sheet. -/
theorem compactPatch_preimage_openInclusion (i : Index) :
    triangleOpenInclusion ⁻¹' (compactPatch i : Set TriangleCompactifiedOrbitSpace) =
      triangleOrbitProjection '' ((patch i).sheet : Set ℍ) := by
  cases i with
  | none => exact cuspNeighborhood_preimage width
  | some i =>
    cases i with
    | inl x =>
      ext q
      exact openInclusion_mem_compactImage (regularImage x) q
    | inr j =>
      ext q
      exact openInclusion_mem_compactImage (ellipticNeighborhoodImage j) q

/-- Pulling a quotient patch all the way upstairs gives the literal union
of translates of its actual precisely invariant sheet. -/
theorem compactPatch_preimage_projection (i : Index) :
    triangleCompactifiedProjection ⁻¹'
      (compactPatch i : Set TriangleCompactifiedOrbitSpace) = (patch i).saturation := by
  change triangleOrbitProjection ⁻¹' (triangleOpenInclusion ⁻¹'
    (compactPatch i : Set TriangleCompactifiedOrbitSpace)) = _
  rw [compactPatch_preimage_openInclusion, (patch i).saturation_eq_preimage_image]

@[simp] theorem compactifiedProjection_mem_compactPatch (i : Index) (z : ℍ) :
    triangleCompactifiedProjection z ∈ compactPatch i ↔ z ∈ (patch i).saturation := by
  change z ∈ triangleCompactifiedProjection ⁻¹'
    (compactPatch i : Set TriangleCompactifiedOrbitSpace) ↔ _
  rw [compactPatch_preimage_projection]

theorem exists_compactPatch (q : TriangleCompactifiedOrbitSpace) :
    ∃ i : Index, q ∈ compactPatch i := by
  induction q using OnePoint.rec with
  | infty => exact ⟨cuspIndex, cuspPoint_mem_cuspNeighborhood width⟩
  | coe q =>
    by_cases h₁ : q = triangleOrbitCenterOne
    · subst q
      exact ⟨ellipticIndex .three, triangleOrbitCenterOne,
        ellipticOrbitCenter_mem_neighborhoodImage .three, rfl⟩
    by_cases h₂ : q = triangleOrbitCenterTwo
    · subst q
      exact ⟨ellipticIndex .four, triangleOrbitCenterTwo,
        ellipticOrbitCenter_mem_neighborhoodImage .four, rfl⟩
    obtain ⟨x, hx⟩ := exists_regularImage q ((triangleOrbitRegularDomain_mem_iff q).mpr ⟨h₁, h₂⟩)
    exact ⟨regularIndex x, q, hx, rfl⟩

/-- This is a proved cover of the actual compact quotient. -/
theorem compactPatch_iUnion :
    (⋃ i : Index, (compactPatch i : Set TriangleCompactifiedOrbitSpace)) = univ := by
  ext q
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_compactPatch q

theorem cusp_mem_compactPatch_iff (i : Index) :
    triangleCuspPoint ∈ compactPatch i ↔ i = cuspIndex := by
  cases i with
  | none => exact iff_of_true (cuspPoint_mem_cuspNeighborhood width) rfl
  | some i =>
    cases i with
    | inl x =>
      exact iff_of_false (cusp_not_mem_compactImage (regularImage x)) (by intro h; cases h)
    | inr j =>
      exact iff_of_false (cusp_not_mem_compactImage (ellipticNeighborhoodImage j))
        (by intro h; cases h)

theorem ellipticOrbitCenter_not_mem_regularDomain (j : Elliptic.Kind) :
    ellipticOrbitCenter j ∉ triangleOrbitRegularDomain := by
  cases j with
  | three => exact fun h => ((triangleOrbitRegularDomain_mem_iff _).mp h).1 rfl
  | four => exact fun h => ((triangleOrbitRegularDomain_mem_iff _).mp h).2 rfl

theorem ellipticOrbitCenter_mem_neighborhoodImage_iff (j k : Elliptic.Kind) :
    ellipticOrbitCenter j ∈ ellipticNeighborhoodImage k ↔ j = k := by
  by_cases h : j = k
  · subst j
    exact iff_of_true (ellipticOrbitCenter_mem_neighborhoodImage k) rfl
  · have hj : j = ellipticOtherKind k := by
      cases j <;> cases k <;> simp_all [ellipticOtherKind]
    exact iff_of_false (by rw [hj]; exact ellipticOtherOrbitCenter_not_mem_neighborhoodImage k) h

/-- Each actual elliptic quotient point is contained in its own elliptic
patch and in no regular, cusp, or other elliptic patch. -/
theorem compactPatch_center_unique (j : Elliptic.Kind) (i : Index) :
    triangleOpenInclusion (ellipticOrbitCenter j) ∈ compactPatch i ↔ i = ellipticIndex j := by
  cases i with
  | none =>
    apply iff_of_false
    · intro h
      exact ellipticOrbitCenter_not_mem_regularDomain j
        (cuspImage_subset_regularDomain width le_rfl
          ((openInclusion_mem_cuspNeighborhood width _).mp h))
    · intro h
      cases h
  | some i =>
    cases i with
    | inl x =>
      apply iff_of_false
      · intro h
        exact ellipticOrbitCenter_not_mem_regularDomain j
          (regularImage_subset_regularDomain x
            ((openInclusion_mem_compactImage (regularImage x) _).mp h))
      · intro h
        cases h
    | inr k =>
      change triangleOpenInclusion (ellipticOrbitCenter j) ∈
        compactImage (ellipticNeighborhoodImage k) ↔ some (Sum.inr k) = some (Sum.inr j)
      rw [openInclusion_mem_compactImage, ellipticOrbitCenter_mem_neighborhoodImage_iff]
      simp only [Option.some.injEq, Sum.inr.injEq, eq_comm]

theorem distinct_compactPatch_overlap_avoids_center {i k : Index} (hik : i ≠ k)
    (j : Elliptic.Kind) :
    triangleOpenInclusion (ellipticOrbitCenter j) ∉
      (compactPatch i : Set TriangleCompactifiedOrbitSpace) ∩ compactPatch k := by
  intro h
  exact hik (((compactPatch_center_unique j i).mp h.1).trans
    ((compactPatch_center_unique j k).mp h.2).symm)

/-- Distinct patch saturations can meet only in the actual free locus
upstairs. Thus no elliptic stabilizer occurs on such an overlap. -/
theorem distinct_saturation_overlap_subset_regularLocus {i k : Index} (hik : i ≠ k) :
    (patch i).saturation ∩ (patch k).saturation ⊆ triangleRegularLocus := by
  intro z hz
  have hq : triangleCompactifiedProjection z ∈
      (compactPatch i : Set TriangleCompactifiedOrbitSpace) ∩ compactPatch k :=
    ⟨(compactifiedProjection_mem_compactPatch i z).mpr hz.1,
      (compactifiedProjection_mem_compactPatch k z).mpr hz.2⟩
  apply (triangleOrbitProjection_mem_regularDomain_iff z).mp
  apply (triangleOrbitRegularDomain_mem_iff _).mpr
  constructor
  · intro h
    have he : triangleCompactifiedProjection z =
        triangleOpenInclusion (ellipticOrbitCenter .three) :=
      congrArg triangleOpenInclusion h
    exact distinct_compactPatch_overlap_avoids_center hik .three (he ▸ hq)
  · intro h
    have he : triangleCompactifiedProjection z =
        triangleOpenInclusion (ellipticOrbitCenter .four) :=
      congrArg triangleOpenInclusion h
    exact distinct_compactPatch_overlap_avoids_center hik .four (he ▸ hq)

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)

/-- The actual finite-coordinate open cover transported through the
supplied sphere identification. -/
def finitePatch (i : Index) : TopologicalSpace.Opens ℂ := finitePullback π (compactPatch i)

@[simp] theorem mem_finitePatch (i : Index) (z : ℂ) :
    z ∈ finitePatch π i ↔ finiteInverse π z ∈ compactPatch i := Iff.rfl

theorem exists_finitePatch (z : ℂ) : ∃ i : Index, z ∈ finitePatch π i :=
  exists_compactPatch (finiteInverse π z)

theorem finitePatch_iUnion : (⋃ i : Index, (finitePatch π i : Set ℂ)) = univ := by
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_finitePatch π z

/-- The exterior region is obtained from the actual cusp neighbourhood
and the supplied normalization, rather than assumed as cover data. -/
theorem finitePatch_cusp_contains_exterior
    (hπ : π triangleCuspPoint = (∞ : RiemannSphere)) :
    ∃ R : ℝ, 0 < R ∧ (Metric.ball (0 : ℂ) R)ᶜ ⊆ finitePatch π cuspIndex :=
  finitePullback_contains_exterior π hπ (cuspNeighborhood width)
    (cuspPoint_mem_cuspNeighborhood width)

theorem finitePatch_center_unique (j : Elliptic.Kind) (i : Index) (z : ℂ)
    (hz : finiteInverse π z = triangleOpenInclusion (ellipticOrbitCenter j)) :
    z ∈ finitePatch π i ↔ i = ellipticIndex j := by
  rw [mem_finitePatch, hz]
  exact compactPatch_center_unique j i

theorem distinct_finitePatch_overlap_avoids_center {i k : Index} (hik : i ≠ k)
    (j : Elliptic.Kind) (z : ℂ) (hz : z ∈ (finitePatch π i : Set ℂ) ∩ finitePatch π k) :
    finiteInverse π z ≠ triangleOpenInclusion (ellipticOrbitCenter j) := by
  intro h
  exact hik (((finitePatch_center_unique π j i z h).mp hz.1).trans
    ((finitePatch_center_unique π j k z h).mp hz.2).symm)

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Cover

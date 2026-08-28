import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticGeometry

/-!
# The genuine elliptic central surfaces inside the global threefold

Each actual special central surface lies in the selected positive-radius
elliptic piece.  Its original inclusion into the full filling therefore
restricts to that piece, retaining the native quotient and subspace
topologies.  The resulting global inclusion identifies the surface
with the whole literal elliptic fibre of the sphere projection.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open EllipticFilling Triangle

attribute [local instance] space_t2Space

@[simp] theorem fullProjection_specialCentralInclusion (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    specialFullFillingProjection j (specialCentralInclusion j x) = Elliptic.discZero := by
  have hx := mem_range_self (f := specialCentralInclusion j) x
  rw [specialCentralInclusion_range] at hx
  exact hx

/-- The actual central surface lies inside every chosen positive-radius
elliptic piece, through its unchanged inclusion in the full filling. -/
def pieceCentralInclusion (j : Elliptic.Kind) :
    SpecialCentralSurface j → LocalSpace j := fun x =>
  ⟨specialCentralInclusion j x, by
    change ‖(specialFullFillingProjection j (specialCentralInclusion j x) : ℂ)‖ <
      specialBaseCover.radius (some j)
    rw [fullProjection_specialCentralInclusion]
    change ‖(0 : ℂ)‖ < specialBaseCover.radius (some j)
    simpa only [norm_zero] using specialBaseCover.radius_pos (some j)⟩

@[simp] theorem pieceCentralInclusion_coe (j : Elliptic.Kind) (x : SpecialCentralSurface j) :
    (pieceCentralInclusion j x : SpecialFullFilling j) = specialCentralInclusion j x := rfl

@[simp] theorem parameter_pieceCentralInclusion (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) : parameter j (pieceCentralInclusion j x) = 0 := by
  change (specialFullFillingProjection j (specialCentralInclusion j x) : ℂ) = 0
  rw [fullProjection_specialCentralInclusion]
  rfl

theorem pieceCentralInclusion_continuous (j : Elliptic.Kind) :
    Continuous (pieceCentralInclusion j) :=
  (specialCentralInclusion_isClosedEmbedding j).continuous.subtype_mk _

theorem pieceCentralInclusion_injective (j : Elliptic.Kind) :
    Function.Injective (pieceCentralInclusion j) := by
  intro x y hxy
  exact (specialCentralInclusion_isClosedEmbedding j).injective (congrArg Subtype.val hxy)

theorem pieceCentralInclusion_isClosedEmbedding (j : Elliptic.Kind) :
    IsClosedEmbedding (pieceCentralInclusion j) :=
  (pieceCentralInclusion_continuous j).isClosedEmbedding (pieceCentralInclusion_injective j)

/-- The restricted inclusion still reaches the entire actual central fibre. -/
theorem pieceCentralInclusion_range (j : Elliptic.Kind) :
    range (pieceCentralInclusion j) = parameter j ⁻¹' {0} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change (specialFullFillingProjection j (specialCentralInclusion j a) : ℂ) = 0
    rw [fullProjection_specialCentralInclusion]
    rfl
  · intro hx
    have hm : x.val ∈ range (specialCentralInclusion j) := by
      rw [specialCentralInclusion_range]
      exact Subtype.ext hx
    obtain ⟨a, ha⟩ := hm
    exact ⟨a, Subtype.ext ha⟩

/-- The genuine central-surface inclusion into the actual glued threefold. -/
def centralSurfaceInclusion (j : Elliptic.Kind) :
    SpecialCentralSurface j → Threefold.Space := inclusion j ∘ pieceCentralInclusion j

@[simp] theorem centralSurfaceInclusion_apply (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    centralSurfaceInclusion j x = inclusion j (pieceCentralInclusion j x) := rfl

theorem centralSurfaceInclusion_continuous (j : Elliptic.Kind) :
    Continuous (centralSurfaceInclusion j) :=
  (inclusion_continuous j).comp (pieceCentralInclusion_continuous j)

theorem centralSurfaceInclusion_injective (j : Elliptic.Kind) :
    Function.Injective (centralSurfaceInclusion j) :=
  (inclusion_injective j).comp (pieceCentralInclusion_injective j)

/-- Compactness of the original quotient surface makes its genuine
global embedding closed in the Hausdorff threefold. -/
theorem centralSurfaceInclusion_isClosedEmbedding (j : Elliptic.Kind) :
    IsClosedEmbedding (centralSurfaceInclusion j) :=
  (centralSurfaceInclusion_continuous j).isClosedEmbedding
    (centralSurfaceInclusion_injective j)

theorem centralSurfaceInclusion_isEmbedding (j : Elliptic.Kind) :
    IsEmbedding (centralSurfaceInclusion j) :=
  (centralSurfaceInclusion_isClosedEmbedding j).isEmbedding

@[simp] theorem projection_centralSurfaceInclusion (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    Threefold.projection (centralSurfaceInclusion j x) = puncturePoint (some j) :=
  (projection_inclusion_eq_point_iff j (pieceCentralInclusion j x)).mpr
    (parameter_pieceCentralInclusion j x)

@[simp] theorem projectionSphere_centralSurfaceInclusion (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    Threefold.projectionSphere (centralSurfaceInclusion j x) = sphereValue j :=
  (projectionSphere_inclusion_eq_value_iff j (pieceCentralInclusion j x)).mpr
    (parameter_pieceCentralInclusion j x)

/-- The original central surface reaches the entire literal global
elliptic fibre; the other glued pieces contribute no extra points. -/
theorem centralSurfaceInclusion_range (j : Elliptic.Kind) :
    range (centralSurfaceInclusion j) = Threefold.projectionSphere ⁻¹' {sphereValue j} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact projectionSphere_centralSurfaceInclusion j x
  · intro hy
    have hyproj : Threefold.projection y = puncturePoint (some j) :=
      triangleSphereUniformization.injective hy
    have hm : y ∈ range (inclusion j) := by
      rw [inclusion_range]
      change Threefold.projection y ∈ specialBaseCover.fillingPatch (some j)
      rw [hyproj]
      exact specialBaseCover.point_mem_fillingPatch (some j)
    obtain ⟨x, rfl⟩ := hm
    have hx : x ∈ range (pieceCentralInclusion j) := by
      rw [pieceCentralInclusion_range]
      exact (projectionSphere_inclusion_eq_value_iff j x).mp hy
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, rfl⟩

/-- The native central quotient surface is homeomorphic to the whole
literal elliptic sphere fibre with its inherited subspace topology. -/
def centralSurfaceFibreHomeomorph (j : Elliptic.Kind) :
    SpecialCentralSurface j ≃ₜ (Threefold.projectionSphere ⁻¹' {sphereValue j}) :=
  (centralSurfaceInclusion_isEmbedding j).toHomeomorph.trans
    (Homeomorph.setCongr (centralSurfaceInclusion_range j))

@[simp] theorem centralSurfaceFibreHomeomorph_coe (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    (centralSurfaceFibreHomeomorph j x : Threefold.Space) = centralSurfaceInclusion j x := rfl

theorem centralSurfaceFibreHomeomorph_symm_inclusion (j : Elliptic.Kind)
    (x : Threefold.projectionSphere ⁻¹' {sphereValue j}) :
    centralSurfaceInclusion j ((centralSurfaceFibreHomeomorph j).symm x) =
      (x : Threefold.Space) :=
  congrArg Subtype.val ((centralSurfaceFibreHomeomorph j).apply_symm_apply x)

theorem centralSurfaceInclusion_range_three :
    range (centralSurfaceInclusion .three) =
      Threefold.projectionSphere ⁻¹' {((0 : ℂ) : RiemannSphere)} := by
  simpa only [sphereValue_three] using centralSurfaceInclusion_range .three

theorem centralSurfaceInclusion_range_four :
    range (centralSurfaceInclusion .four) =
      Threefold.projectionSphere ⁻¹' {((1 : ℂ) : RiemannSphere)} := by
  simpa only [sphereValue_four] using centralSurfaceInclusion_range .four

/-- The order-three central surface is the literal global fibre over zero. -/
def centralSurfaceZeroFibreHomeomorph :
    SpecialCentralSurface .three ≃ₜ
      (Threefold.projectionSphere ⁻¹' {((0 : ℂ) : RiemannSphere)}) :=
  (centralSurfaceInclusion_isEmbedding .three).toHomeomorph.trans
    (Homeomorph.setCongr centralSurfaceInclusion_range_three)

/-- The order-four central surface is the literal global fibre over one. -/
def centralSurfaceOneFibreHomeomorph :
    SpecialCentralSurface .four ≃ₜ
      (Threefold.projectionSphere ⁻¹' {((1 : ℂ) : RiemannSphere)}) :=
  (centralSurfaceInclusion_isEmbedding .four).toHomeomorph.trans
    (Homeomorph.setCongr centralSurfaceInclusion_range_four)

@[simp] theorem centralSurfaceZeroFibreHomeomorph_coe (x : SpecialCentralSurface .three) :
    (centralSurfaceZeroFibreHomeomorph x : Threefold.Space) = centralSurfaceInclusion .three x :=
  rfl

@[simp] theorem centralSurfaceOneFibreHomeomorph_coe (x : SpecialCentralSurface .four) :
    (centralSurfaceOneFibreHomeomorph x : Threefold.Space) = centralSurfaceInclusion .four x :=
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

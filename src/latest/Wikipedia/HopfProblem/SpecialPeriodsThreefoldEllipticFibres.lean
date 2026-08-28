import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticFibreTopology
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticParametrization
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularImmersion

/-!
# The native complex surfaces in the two elliptic sphere fibres

The original affine quotient surfaces immerse in the actual glued
threefold through its proved full-filling parametrizations. The literal
fibres carry the atlas obtained from these ambient immersion charts.
Every chosen fibre chart has its full source and both coordinate
directions identified with an actual ambient slice. The resulting
biholomorphisms therefore compare genuine complex structures, not
arbitrary transported atlases.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open EllipticFilling

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] specialFullFillingChartedSpace Threefold.chartedSpace

local instance : IsManifold IF ω Threefold.Space := Threefold.space_isManifold

/-- The global inclusion is the original central inclusion followed by
the actual native full-filling parametrization at every surface point. -/
theorem centralSurfaceInclusion_eq_fullParametrization (j : Elliptic.Kind) :
    centralSurfaceInclusion j = fullParametrization j ∘ specialCentralInclusion j := by
  funext x
  exact (fullParametrization_apply j (pieceCentralInclusion j x)).symm

/-- The genuine global inclusion has a complex one-dimensional normal
complement in the actual glued-manifold atlas. -/
theorem centralSurfaceInclusion_isImmersionOfComplement (j : Elliptic.Kind) :
    Manifold.IsImmersionOfComplement ℂ I₂ IF ω (centralSurfaceInclusion j) := by
  rw [centralSurfaceInclusion_eq_fullParametrization]
  intro x
  exact immersionAt_postcomp_localDiffeomorph
    (specialCentralInclusion_isImmersionOfComplement j x)
    (fullParametrization_isLocalDiffeomorphAt j
      (specialCentralInclusion_mem_fullParametrization_source j x))

theorem centralSurfaceInclusion_isImmersion (j : Elliptic.Kind) :
    Manifold.IsImmersion I₂ IF ω (centralSurfaceInclusion j) :=
  (centralSurfaceInclusion_isImmersionOfComplement j).isImmersion

theorem centralSurfaceInclusion_holomorphic (j : Elliptic.Kind) :
    ContMDiff I₂ IF ω (centralSurfaceInclusion j) :=
  (centralSurfaceInclusion_isImmersionOfComplement j).contMDiff

/-- The literal inverse image of a sphere point, with its unchanged
subspace topology. -/
abbrev SphereFibre (b : RiemannSphere) := Threefold.projectionSphere ⁻¹' {b}

section Fibre

variable (j : Elliptic.Kind) (b : RiemannSphere) (hb : sphereValue j = b)

/-- Relabel only the target point of the proved full-fibre homeomorphism.
The actual inclusion into the threefold is unchanged. -/
def centralSurfaceSphereFibreHomeomorph : SpecialCentralSurface j ≃ₜ SphereFibre b :=
  (centralSurfaceFibreHomeomorph j).trans
    (Homeomorph.setCongr
      (congrArg (fun c : RiemannSphere => Threefold.projectionSphere ⁻¹' {c}) hb))

@[simp] theorem centralSurfaceSphereFibreHomeomorph_coe (x : SpecialCentralSurface j) :
    (centralSurfaceSphereFibreHomeomorph j b hb x : Threefold.Space) =
      centralSurfaceInclusion j x := rfl

theorem centralSurfaceSphereFibreHomeomorph_isImmersionOfComplement :
    Manifold.IsImmersionOfComplement ℂ I₂ IF ω
      (Subtype.val ∘ centralSurfaceSphereFibreHomeomorph j b hb) :=
  centralSurfaceInclusion_isImmersionOfComplement j

/-- Restrict the actual global ambient immersion charts to their zero
normal slices, keeping the literal fibre's original subspace topology. -/
@[instance_reducible] def centralSphereFibreChartedSpace :
    ChartedSpace ComplexPlane₂ (SphereFibre b) :=
  EmbeddedFibre.chartedSpace (centralSurfaceSphereFibreHomeomorph j b hb)
    (centralSurfaceSphereFibreHomeomorph_isImmersionOfComplement j b hb)

theorem centralSphereFibre_isManifold :
    letI := centralSphereFibreChartedSpace j b hb
    IsManifold I₂ ω (SphereFibre b) :=
  EmbeddedFibre.isManifold (centralSurfaceSphereFibreHomeomorph j b hb)
    (centralSurfaceSphereFibreHomeomorph_isImmersionOfComplement j b hb)

theorem centralSphereFibre_inclusion_isImmersionOfComplement :
    letI := centralSphereFibreChartedSpace j b hb
    Manifold.IsImmersionOfComplement ℂ I₂ IF ω
      (Subtype.val : SphereFibre b → Threefold.Space) :=
  EmbeddedFibre.inclusion_isImmersionOfComplement
    (centralSurfaceSphereFibreHomeomorph j b hb)
    (centralSurfaceSphereFibreHomeomorph_isImmersionOfComplement j b hb)

theorem centralSphereFibre_inclusion_holomorphic :
    letI := centralSphereFibreChartedSpace j b hb
    ContMDiff I₂ IF ω (Subtype.val : SphereFibre b → Threefold.Space) := by
  let := centralSphereFibreChartedSpace j b hb
  exact (centralSphereFibre_inclusion_isImmersionOfComplement j b hb).contMDiff

/-- Full agreement with the actual glued atlas: complete chart-source
intersection, and literal zero-normal restriction in both directions. -/
theorem centralSphereFibre_charts_are_ambient_slices (x : SphereFibre b) :
    letI := centralSphereFibreChartedSpace j b hb
    ∃ c : OpenPartialHomeomorph Threefold.Space (ℂ × ComplexPlane₂),
      ∃ L : (ComplexPlane₂ × ℂ) ≃L[ℂ] (ℂ × ComplexPlane₂),
        c ∈ IsManifold.maximalAtlas IF ω Threefold.Space ∧
        (chartAt ComplexPlane₂ x).source = Subtype.val ⁻¹' c.source ∧
        (∀ y ∈ (chartAt ComplexPlane₂ x).source,
          c (y : Threefold.Space) = L (chartAt ComplexPlane₂ x y, 0)) ∧
        (∀ u ∈ (chartAt ComplexPlane₂ x).target,
          ((chartAt ComplexPlane₂ x).symm u : Threefold.Space) = c.symm (L (u, 0))) := by
  let := centralSphereFibreChartedSpace j b hb
  let e := centralSurfaceSphereFibreHomeomorph j b hb
  let hι := centralSurfaceSphereFibreHomeomorph_isImmersionOfComplement j b hb
  obtain ⟨c, hc, hs, hf, hi⟩ := EmbeddedFibre.exists_ambient_restriction e hι x
  exact ⟨c, EmbeddedFibre.coordinateEquiv e hι x, hc, hs, hf, hi⟩

/-- The original finite affine quotient of the actual special central
period torus is biholomorphic to the whole literal global sphere fibre,
with the checked ambient-slice complex structure. -/
def centralSphereFibreBiholomorph :
    letI := centralSphereFibreChartedSpace j b hb
    Diffeomorph I₂ I₂ (SpecialCentralSurface j) (SphereFibre b) ω := by
  let := centralSphereFibreChartedSpace j b hb
  exact EmbeddedFibre.biholomorphOfHomeomorph
    (centralSurfaceSphereFibreHomeomorph j b hb)
    (centralSurfaceInclusion_isImmersion j)
    (centralSphereFibre_inclusion_isImmersionOfComplement j b hb).isImmersion
    (fun _ => rfl)

@[simp] theorem centralSphereFibreBiholomorph_coe (x : SpecialCentralSurface j) :
    letI := centralSphereFibreChartedSpace j b hb
    (centralSphereFibreBiholomorph j b hb x : Threefold.Space) =
      centralSurfaceInclusion j x := rfl

end Fibre

/-- The actual ambient-slice atlas on the literal fibre over zero. -/
@[instance_reducible] def zeroFibreChartedSpace :
    ChartedSpace ComplexPlane₂ (SphereFibre ((0 : ℂ) : RiemannSphere)) :=
  centralSphereFibreChartedSpace .three _ sphereValue_three

/-- The actual ambient-slice atlas on the literal fibre over one. -/
@[instance_reducible] def oneFibreChartedSpace :
    ChartedSpace ComplexPlane₂ (SphereFibre ((1 : ℂ) : RiemannSphere)) :=
  centralSphereFibreChartedSpace .four _ sphereValue_four

/-- No uniformization or fibre identification is assumed: the actual
order-three surface is biholomorphic to the literal sphere fibre at zero. -/
def zeroFibreBiholomorph :
    letI := zeroFibreChartedSpace
    Diffeomorph I₂ I₂ (SpecialCentralSurface .three)
      (SphereFibre ((0 : ℂ) : RiemannSphere)) ω :=
  centralSphereFibreBiholomorph .three _ sphereValue_three

/-- The actual order-four surface is biholomorphic to the literal
sphere fibre at one, using the genuine ambient-slice atlas. -/
def oneFibreBiholomorph :
    letI := oneFibreChartedSpace
    Diffeomorph I₂ I₂ (SpecialCentralSurface .four)
      (SphereFibre ((1 : ℂ) : RiemannSphere)) ω :=
  centralSphereFibreBiholomorph .four _ sphereValue_four

@[simp] theorem zeroFibreBiholomorph_coe (x : SpecialCentralSurface .three) :
    letI := zeroFibreChartedSpace
    (zeroFibreBiholomorph x : Threefold.Space) = centralSurfaceInclusion .three x := rfl

@[simp] theorem oneFibreBiholomorph_coe (x : SpecialCentralSurface .four) :
    letI := oneFibreChartedSpace
    (oneFibreBiholomorph x : Threefold.Space) = centralSurfaceInclusion .four x := rfl

theorem zeroFibre_isManifold :
    letI := zeroFibreChartedSpace
    IsManifold I₂ ω (SphereFibre ((0 : ℂ) : RiemannSphere)) :=
  centralSphereFibre_isManifold .three _ sphereValue_three

theorem oneFibre_isManifold :
    letI := oneFibreChartedSpace
    IsManifold I₂ ω (SphereFibre ((1 : ℂ) : RiemannSphere)) :=
  centralSphereFibre_isManifold .four _ sphereValue_four

/-- Both elliptic fibres of the actual compact threefold are the
specified native finite affine quotient surfaces. -/
theorem ellipticFibres_are_actual_surfaces :
    letI := zeroFibreChartedSpace
    letI := oneFibreChartedSpace
    IsManifold I₂ ω (SphereFibre ((0 : ℂ) : RiemannSphere)) ∧
      IsManifold I₂ ω (SphereFibre ((1 : ℂ) : RiemannSphere)) ∧
      Nonempty (Diffeomorph I₂ I₂ (SpecialCentralSurface .three)
        (SphereFibre ((0 : ℂ) : RiemannSphere)) ω) ∧
      Nonempty (Diffeomorph I₂ I₂ (SpecialCentralSurface .four)
        (SphereFibre ((1 : ℂ) : RiemannSphere)) ω) := by
  let := zeroFibreChartedSpace
  let := oneFibreChartedSpace
  exact ⟨zeroFibre_isManifold, oneFibre_isManifold,
    ⟨zeroFibreBiholomorph⟩, ⟨oneFibreBiholomorph⟩⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

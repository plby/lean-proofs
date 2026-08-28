import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularFibreTopology
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularImmersion
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularParameters
import Wikipedia.HopfProblem.EllipticFibreManifoldCore
import Wikipedia.HopfProblem.EllipticFibreBiholomorphCore

/-!
# Native complex structures on the actual regular fibres of the threefold

The original period torus embeds in the actual glued manifold through
the regular piece.  Its immersion normal forms give charts on the
literal global sphere fibre.  Each chosen chart is proved to be exactly
an ambient-chart slice, with its full source and both coordinate
directions identified.  The resulting fibre biholomorphism uses these
ambient-induced charts, not an arbitrary transported complex atlas.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle TrianglePeriodFamily

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] chartedSpace specialRegularFamilyChartedSpace localPieceChartedSpace

local instance : IsManifold IF ω Space := space_isManifold

/-- The actual period-torus inclusion remains an immersion after the
native regular-piece inclusion in the constructed threefold. -/
theorem regularTorusInclusion_isImmersionOfComplement (z : TriangleRegularPoint) :
    Manifold.IsImmersionOfComplement ℂ I₂ IF ω (regularTorusInclusion z) := by
  change Manifold.IsImmersionOfComplement ℂ I₂ IF ω
    (regularFamilyInclusion ∘ (regularFamilyData specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂).fibreInclusion z)
  exact immersion_postcomp_localDiffeomorph (M := SpecialRegularFamily) (N := Space)
    ((regularFamilyData specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂).fibreInclusion_isImmersionOfComplement
        (regularCovering specialPeriodMap specialPeriodMap_generator₁
          specialPeriodMap_generator₂) z)
    regularFamilyInclusion_isLocalDiffeomorph

/-- The fibre is the literal inverse image of the specified sphere point,
with its existing subspace topology. -/
abbrev RegularSphereFibre (b : RiemannSphere) := projectionSphere ⁻¹' {b}

/-- The actual torus homeomorphism with its literal target point relabelled
by a proved equality of sphere values.  Its ambient map is unchanged. -/
def regularTorusSphereFibreHomeomorph (z : TriangleRegularPoint) (b : RiemannSphere)
    (hz : regularSphereValue z = b) : RegularTorus z ≃ₜ RegularSphereFibre b :=
  (regularTorusFibreHomeomorph z).trans
    (Homeomorph.setCongr (congrArg (fun c : RiemannSphere => projectionSphere ⁻¹' {c}) hz))

@[simp] theorem regularTorusSphereFibreHomeomorph_coe (z : TriangleRegularPoint)
    (b : RiemannSphere) (hz : regularSphereValue z = b) (x : RegularTorus z) :
    (regularTorusSphereFibreHomeomorph z b hz x : Space) = regularTorusInclusion z x := rfl

theorem regularTorusSphereFibreHomeomorph_isImmersionOfComplement
    (z : TriangleRegularPoint) (b : RiemannSphere) (hz : regularSphereValue z = b) :
    Manifold.IsImmersionOfComplement ℂ I₂ IF ω
      (Subtype.val ∘ regularTorusSphereFibreHomeomorph z b hz) :=
  regularTorusInclusion_isImmersionOfComplement z

section SphereValue

variable (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere))
    (h₀ : b ≠ ((0 : ℂ) : RiemannSphere))
    (h₁ : b ≠ ((1 : ℂ) : RiemannSphere))

/-- The chosen period parameter really lies above the specified point. -/
theorem regularPointOver_sphereValue :
    regularSphereValue (regularPointOver b h_inf h₀ h₁) = b :=
  regularPointOver_value b h_inf h₀ h₁

/-- This is the actual inclusion of a genuine period torus onto the
literal global fibre, selected using proved covering surjectivity. -/
def regularSphereFibreHomeomorph :
    RegularTorus (regularPointOver b h_inf h₀ h₁) ≃ₜ RegularSphereFibre b :=
  regularTorusSphereFibreHomeomorph (regularPointOver b h_inf h₀ h₁) b
    (regularPointOver_sphereValue b h_inf h₀ h₁)

theorem regularSphereFibreHomeomorph_isImmersionOfComplement :
    Manifold.IsImmersionOfComplement ℂ I₂ IF ω
      (Subtype.val ∘ regularSphereFibreHomeomorph b h_inf h₀ h₁) :=
  regularTorusInclusion_isImmersionOfComplement (regularPointOver b h_inf h₀ h₁)

/-- Restrict the actual ambient immersion charts to their zero
transverse coordinate, retaining the literal fibre topology. -/
@[instance_reducible] def regularSphereFibreChartedSpace :
    ChartedSpace ComplexPlane₂ (RegularSphereFibre b) :=
  EmbeddedFibre.chartedSpace (regularSphereFibreHomeomorph b h_inf h₀ h₁)
    (regularSphereFibreHomeomorph_isImmersionOfComplement b h_inf h₀ h₁)

theorem regularSphereFibre_isManifold :
    letI := regularSphereFibreChartedSpace b h_inf h₀ h₁
    IsManifold I₂ ω (RegularSphereFibre b) :=
  EmbeddedFibre.isManifold (regularSphereFibreHomeomorph b h_inf h₀ h₁)
    (regularSphereFibreHomeomorph_isImmersionOfComplement b h_inf h₀ h₁)

theorem regularSphereFibre_inclusion_isImmersionOfComplement :
    letI := regularSphereFibreChartedSpace b h_inf h₀ h₁
    Manifold.IsImmersionOfComplement ℂ I₂ IF ω
      (Subtype.val : RegularSphereFibre b → Space) :=
  EmbeddedFibre.inclusion_isImmersionOfComplement
    (regularSphereFibreHomeomorph b h_inf h₀ h₁)
    (regularSphereFibreHomeomorph_isImmersionOfComplement b h_inf h₀ h₁)

theorem regularSphereFibre_inclusion_holomorphic :
    letI := regularSphereFibreChartedSpace b h_inf h₀ h₁
    ContMDiff I₂ IF ω (Subtype.val : RegularSphereFibre b → Space) := by
  let := regularSphereFibreChartedSpace b h_inf h₀ h₁
  exact (regularSphereFibre_inclusion_isImmersionOfComplement b h_inf h₀ h₁).contMDiff

/-- Full chart agreement with the native glued atlas: the selected fibre
chart source is the complete intersection with an ambient chart source,
and its forward and inverse coordinates are the actual zero-normal slices. -/
theorem regularSphereFibre_charts_are_ambient_slices (x : RegularSphereFibre b) :
    letI := regularSphereFibreChartedSpace b h_inf h₀ h₁
    ∃ c : OpenPartialHomeomorph Space (ℂ × ComplexPlane₂),
      ∃ L : (ComplexPlane₂ × ℂ) ≃L[ℂ] (ℂ × ComplexPlane₂),
        c ∈ IsManifold.maximalAtlas IF ω Space ∧
        (chartAt ComplexPlane₂ x).source = Subtype.val ⁻¹' c.source ∧
        (∀ y ∈ (chartAt ComplexPlane₂ x).source,
          c (y : Space) = L (chartAt ComplexPlane₂ x y, 0)) ∧
        (∀ u ∈ (chartAt ComplexPlane₂ x).target,
          ((chartAt ComplexPlane₂ x).symm u : Space) = c.symm (L (u, 0))) := by
  let := regularSphereFibreChartedSpace b h_inf h₀ h₁
  let e := regularSphereFibreHomeomorph b h_inf h₀ h₁
  let hι := regularSphereFibreHomeomorph_isImmersionOfComplement b h_inf h₀ h₁
  obtain ⟨c, hc, hs, hf, hi⟩ := EmbeddedFibre.exists_ambient_restriction e hι x
  exact ⟨c, EmbeddedFibre.coordinateEquiv e hι x, hc, hs, hf, hi⟩

/-- Every original period torus at a lift of the same unmarked sphere
point is biholomorphic to its literal global fibre with the one selected
ambient-induced atlas.  No comparison of transported atlases is assumed. -/
def regularTorusSphereFibreBiholomorph (z : TriangleRegularPoint)
    (hz : regularSphereValue z = b) :
    letI := regularSphereFibreChartedSpace b h_inf h₀ h₁
    Diffeomorph I₂ I₂ (RegularTorus z) (RegularSphereFibre b) ω := by
  let := regularSphereFibreChartedSpace b h_inf h₀ h₁
  exact EmbeddedFibre.biholomorphOfHomeomorph (regularTorusSphereFibreHomeomorph z b hz)
    (regularTorusInclusion_isImmersionOfComplement z).isImmersion
    (regularSphereFibre_inclusion_isImmersionOfComplement b h_inf h₀ h₁).isImmersion
    (fun _ => rfl)

@[simp] theorem regularTorusSphereFibreBiholomorph_coe (z : TriangleRegularPoint)
    (hz : regularSphereValue z = b) (x : RegularTorus z) :
    letI := regularSphereFibreChartedSpace b h_inf h₀ h₁
    (regularTorusSphereFibreBiholomorph b h_inf h₀ h₁ z hz x : Space) =
      regularTorusInclusion z x := rfl

/-- A fully constructed period-torus parametrization for every
unmarked sphere value, with no supplied upper-half-plane lift. -/
def regularSphereFibreBiholomorph :
    letI := regularSphereFibreChartedSpace b h_inf h₀ h₁
    Diffeomorph I₂ I₂ (RegularTorus (regularPointOver b h_inf h₀ h₁))
      (RegularSphereFibre b) ω :=
  regularTorusSphereFibreBiholomorph b h_inf h₀ h₁
    (regularPointOver b h_inf h₀ h₁) (regularPointOver_sphereValue b h_inf h₀ h₁)

@[simp] theorem regularSphereFibreBiholomorph_coe
    (x : RegularTorus (regularPointOver b h_inf h₀ h₁)) :
    letI := regularSphereFibreChartedSpace b h_inf h₀ h₁
    (regularSphereFibreBiholomorph b h_inf h₀ h₁ x : Space) =
      regularTorusInclusion (regularPointOver b h_inf h₀ h₁) x := rfl

/-- The regular fibre is an actual complex two-torus, with the original
period lattice and with its checked ambient-induced complex structure. -/
theorem regularSphereFibre_is_period_torus :
    letI := regularSphereFibreChartedSpace b h_inf h₀ h₁
    IsManifold I₂ ω (RegularSphereFibre b) ∧
      ∃ z : TriangleRegularPoint, regularSphereValue z = b ∧
        Nonempty (Diffeomorph I₂ I₂ (specialPeriodMap.point z.val).Torus
          (RegularSphereFibre b) ω) := by
  let := regularSphereFibreChartedSpace b h_inf h₀ h₁
  exact ⟨regularSphereFibre_isManifold b h_inf h₀ h₁,
    regularPointOver b h_inf h₀ h₁, regularPointOver_sphereValue b h_inf h₀ h₁,
    ⟨regularSphereFibreBiholomorph b h_inf h₀ h₁⟩⟩

end SphereValue

end Wikipedia.HopfProblem.SpecialPeriods.Threefold

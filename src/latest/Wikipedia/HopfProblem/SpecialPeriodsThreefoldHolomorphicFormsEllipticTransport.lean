import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticExtensionGluing
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularElliptic
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientDensity
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingBase

/-!
# Transport and gluing over the actual elliptic orbits

The missing points of the original regular upper half-plane are exactly
the two proved elliptic-center orbits. A genuine holomorphic covariance
map transports a local extension at a center to a local extension at
every point in its orbit. Density then glues the local extensions into a
global holomorphic function in the original upper-half-plane atlas.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticExtension

attribute [local instance] triangleGeometricAction

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IF" => modelWithCornersSelf ℂ F

/-- An actual holomorphic extension on an original open neighborhood,
with exact agreement on its entire overlap with the regular source. -/
def HasExtensionAt (f : TriangleRegularPoint → F) (x : ℍ) : Prop :=
  ∃ V : TopologicalSpace.Opens ℍ, x ∈ V ∧ ∃ h : V → F,
    ContMDiff I₁ IF ω h ∧
      ∀ y : V, ∀ hy : (y : ℍ) ∈ triangleRegularDomain, h y = f ⟨y, hy⟩

/-- The existing regular function is already its own local extension. -/
theorem hasExtensionAt_regular (f : TriangleRegularPoint → F)
    (hf : ContMDiff I₁ IF ω f) (x : ℍ) (hx : x ∈ triangleRegularDomain) :
    HasExtensionAt f x :=
  ⟨triangleRegularDomain, hx, f, hf, fun _ _ => rfl⟩

/-- Transport an actual germ by the genuine triangle action and an
actual jointly holomorphic coefficient transformation. -/
theorem hasExtensionAt_translate (f : TriangleRegularPoint → F) (g : TriangleGroup)
    (T : ℍ × F → F) (hT : ContMDiff ((I₁).prod IF) IF ω T)
    (hcov : ∀ z : TriangleRegularPoint, f (g • z) = T (z.val, f z))
    (x : ℍ) (hx : HasExtensionAt f x) :
    HasExtensionAt f (triangleGeometricRepresentation g x) := by
  obtain ⟨V, hxV, h, hh, hagree⟩ := hx
  let W : TopologicalSpace.Opens ℍ :=
    ⟨(fun y : ℍ => g⁻¹ • y) ⁻¹' V,
      V.isOpen.preimage (triangleGeometricRepresentation_holomorphic g⁻¹).continuous⟩
  have hxW : triangleGeometricRepresentation g x ∈ W := by
    change g⁻¹ • (g • x) ∈ V
    simpa only [inv_smul_smul] using hxV
  let back : W → V := fun y => ⟨g⁻¹ • y.val, y.property⟩
  have hpre : ContMDiff I₁ I₁ ω (fun y : W => g⁻¹ • y.val) :=
    (triangleGeometricRepresentation_holomorphic g⁻¹).comp contMDiff_subtype_val
  have hback : ContMDiff I₁ I₁ ω back := by
    intro y
    have he : ContMDiffAt I₁ I₁ ω (Subtype.val ∘ back) y ↔
        ContMDiffAt I₁ I₁ ω back y :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact he.mp (hpre y)
  let k : W → F := fun y => T (g⁻¹ • y.val, h (back y))
  have hk : ContMDiff I₁ IF ω k := hT.comp (hpre.prodMk (hh.comp hback))
  refine ⟨W, hxW, k, hk, ?_⟩
  intro y hy
  have hz : g⁻¹ • y.val ∈ triangleRegularDomain :=
    (triangleRegularLocus_invariant g⁻¹ y.val).mpr hy
  let z : TriangleRegularPoint := ⟨g⁻¹ • y.val, hz⟩
  have hzmap : g • z = (⟨y.val, hy⟩ : TriangleRegularPoint) := by
    apply Subtype.ext
    change g • (g⁻¹ • y.val) = y.val
    exact smul_inv_smul g y.val
  have he : h (back y) = f z := hagree (back y) hz
  change T (g⁻¹ • y.val, h (back y)) = f ⟨y.val, hy⟩
  rw [he]
  exact (hcov z).symm.trans (congrArg f hzmap)

/-- Every point omitted by the actual regular domain is a translate
of one of the two original elliptic centers. -/
theorem exists_elliptic_translate_of_not_regular (x : ℍ)
    (hx : x ∉ triangleRegularDomain) :
    ∃ j : Elliptic.Kind, ∃ g : TriangleGroup,
      x = triangleGeometricRepresentation g (Triangle.ellipticCenter j) := by
  classical
  have he : x ∈ triangleEllipticSet := by
    by_contra h
    apply hx
    change x ∈ triangleRegularLocus
    rw [triangleRegularLocus_eq_compl_ellipticSet]
    exact h
  rcases he with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact ⟨.three, g, hg.symm⟩
  · exact ⟨.four, g, hg.symm⟩

/-- Two actual center germs and the genuine holomorphic covariance
construct a global extension. All omitted points and overlap
compatibilities are discharged by the proved orbit classification and density. -/
theorem exists_extension_of_center_germs (f : TriangleRegularPoint → F)
    (hf : ContMDiff I₁ IF ω f) (T : TriangleGroup → ℍ × F → F)
    (hT : ∀ g, ContMDiff ((I₁).prod IF) IF ω (T g))
    (hcov : ∀ g (z : TriangleRegularPoint), f (g • z) = T g (z.val, f z))
    (hcenters : ∀ j : Elliptic.Kind, HasExtensionAt f (Triangle.ellipticCenter j)) :
    ∃ G : ℍ → F, ContMDiff I₁ IF ω G ∧ ∀ z : TriangleRegularPoint, G z.val = f z := by
  apply HolomorphicExtensionGluing.exists_holomorphic_extension_of_local_outside
    triangleRegularDomain f hf triangleRegularLocus_dense
  intro x hx
  obtain ⟨j, g, rfl⟩ := exists_elliptic_translate_of_not_regular x hx
  exact hasExtensionAt_translate f g (T g) (hT g) (hcov g)
    (Triangle.ellipticCenter j) (hcenters j)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticExtension

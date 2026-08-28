import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticGerms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticTransport
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticTransportFactors

/-!
# Lemma 9.16(i): genuine coefficient extensions to the whole upper half-plane

The actual elliptic filling gives the two center germs. The original
triangle action, with its actual holomorphic period cocycle, gives the
germs at every translated center. These cover every missing point of
the regular source, and density glues them uniquely. Thus all functions
below extend coefficients of arbitrary genuine global holomorphic forms;
there is no coefficient normal-form, local-extension, or period-map
existence hypothesis in these constructions.

As in the source, the base coefficient of a one-form is extended only
after its vertical coefficient vanishes.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticExtension

open Elliptic HolomorphicDifferentialForms

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The genuine vertical one-form coefficient extends over both complete
elliptic orbits to the original whole upper half-plane. -/
theorem exists_fibreOne_extension (θ : Form FamilyModel Threefold.Space 1) :
    ∃ C : ℍ → ComplexPlane₂, ContMDiff I₁ I₂ ω C ∧
      ∀ z : TriangleRegularPoint, C z.val = RegularCover.fibreOne θ z :=
  exists_extension_of_center_germs (RegularCover.fibreOne θ)
    (RegularCover.fibreOne_holomorphic θ) oneFibreTransform oneFibreTransform_holomorphic
    (fibreOne_group_transform θ) (fun j => EllipticCover.oneFibre_elliptic_germ j θ)

/-- The genuine mixed two-form coefficient has an unconditional extension. -/
theorem exists_mixedTwo_extension (θ : Form FamilyModel Threefold.Space 2) :
    ∃ B : ℍ → ComplexPlane₂, ContMDiff I₁ I₂ ω B ∧
      ∀ z : TriangleRegularPoint, B z.val = RegularCover.mixedTwo θ z :=
  exists_extension_of_center_germs (RegularCover.mixedTwo θ)
    (RegularCover.mixedTwo_holomorphic θ) twoMixedTransform twoMixedTransform_holomorphic
    (mixedTwo_group_transform θ) (fun j => EllipticCover.twoMixed_elliptic_germ j θ)

/-- The genuine top-form coefficient has an unconditional extension. -/
theorem exists_baseTop_extension (θ : Form FamilyModel Threefold.Space 3) :
    ∃ C : ℍ → ℂ, ContMDiff I₁ I₁ ω C ∧
      ∀ z : TriangleRegularPoint, C z.val = RegularCover.baseTop θ z :=
  exists_extension_of_center_germs (RegularCover.baseTop θ)
    (RegularCover.baseTop_holomorphic θ) topTransform topTransform_holomorphic
    (baseTop_group_transform θ) (fun j => EllipticCover.top_elliptic_germ j θ)

/-- After the actual vertical coefficient vanishes, the base one-form
coefficient also extends across every elliptic point. -/
theorem exists_baseOne_extension (θ : Form FamilyModel Threefold.Space 1)
    (hc : ∀ z : TriangleRegularPoint, RegularCover.fibreOne θ z = 0) :
    ∃ A : ℍ → ℂ, ContMDiff I₁ I₁ ω A ∧
      ∀ z : TriangleRegularPoint, A z.val = RegularCover.baseOne θ z :=
  exists_extension_of_center_germs (RegularCover.baseOne θ)
    (RegularCover.baseOne_holomorphic θ) oneBaseTransform oneBaseTransform_holomorphic
    (baseOne_group_transform θ)
    (fun j => EllipticCover.oneBase_elliptic_germ_of_fibre_zero j θ hc)

/-- The extension of the actual vertical one-form coefficient. -/
def fibreOne (θ : Form FamilyModel Threefold.Space 1) : ℍ → ComplexPlane₂ :=
  Classical.choose (exists_fibreOne_extension θ)

theorem fibreOne_holomorphic (θ : Form FamilyModel Threefold.Space 1) :
    ContMDiff I₁ I₂ ω (fibreOne θ) :=
  (Classical.choose_spec (exists_fibreOne_extension θ)).1

@[simp] theorem fibreOne_restrict (θ : Form FamilyModel Threefold.Space 1)
    (z : TriangleRegularPoint) : fibreOne θ z.val = RegularCover.fibreOne θ z :=
  (Classical.choose_spec (exists_fibreOne_extension θ)).2 z

/-- The extension of the actual mixed two-form coefficient. -/
def mixedTwo (θ : Form FamilyModel Threefold.Space 2) : ℍ → ComplexPlane₂ :=
  Classical.choose (exists_mixedTwo_extension θ)

theorem mixedTwo_holomorphic (θ : Form FamilyModel Threefold.Space 2) :
    ContMDiff I₁ I₂ ω (mixedTwo θ) :=
  (Classical.choose_spec (exists_mixedTwo_extension θ)).1

@[simp] theorem mixedTwo_restrict (θ : Form FamilyModel Threefold.Space 2)
    (z : TriangleRegularPoint) : mixedTwo θ z.val = RegularCover.mixedTwo θ z :=
  (Classical.choose_spec (exists_mixedTwo_extension θ)).2 z

/-- The extension of the actual top-form coefficient. -/
def baseTop (θ : Form FamilyModel Threefold.Space 3) : ℍ → ℂ :=
  Classical.choose (exists_baseTop_extension θ)

theorem baseTop_holomorphic (θ : Form FamilyModel Threefold.Space 3) :
    ContMDiff I₁ I₁ ω (baseTop θ) :=
  (Classical.choose_spec (exists_baseTop_extension θ)).1

@[simp] theorem baseTop_restrict (θ : Form FamilyModel Threefold.Space 3)
    (z : TriangleRegularPoint) : baseTop θ z.val = RegularCover.baseTop θ z :=
  (Classical.choose_spec (exists_baseTop_extension θ)).2 z

/-- The one-form base coefficient, with the source's prior
vanishing argument kept explicit in the construction. -/
def baseOne (θ : Form FamilyModel Threefold.Space 1)
    (hc : ∀ z : TriangleRegularPoint, RegularCover.fibreOne θ z = 0) : ℍ → ℂ :=
  Classical.choose (exists_baseOne_extension θ hc)

theorem baseOne_holomorphic (θ : Form FamilyModel Threefold.Space 1)
    (hc : ∀ z : TriangleRegularPoint, RegularCover.fibreOne θ z = 0) :
    ContMDiff I₁ I₁ ω (baseOne θ hc) :=
  (Classical.choose_spec (exists_baseOne_extension θ hc)).1

@[simp] theorem baseOne_restrict (θ : Form FamilyModel Threefold.Space 1)
    (hc : ∀ z : TriangleRegularPoint, RegularCover.fibreOne θ z = 0)
    (z : TriangleRegularPoint) : baseOne θ hc z.val = RegularCover.baseOne θ z :=
  (Classical.choose_spec (exists_baseOne_extension θ hc)).2 z

/-- Density makes the extension unique, independently of the local
neighborhoods or representatives used in its construction. -/
theorem fibreOne_unique (θ : Form FamilyModel Threefold.Space 1) {C : ℍ → ComplexPlane₂}
    (hC : ContMDiff I₁ I₂ ω C)
    (hagree : ∀ z : TriangleRegularPoint, C z.val = RegularCover.fibreOne θ z) :
    C = fibreOne θ :=
  HolomorphicExtensionGluing.holomorphic_extension_unique triangleRegularDomain
    (RegularCover.fibreOne θ) triangleRegularLocus_dense hC (fibreOne_holomorphic θ)
    hagree (fibreOne_restrict θ)

theorem mixedTwo_unique (θ : Form FamilyModel Threefold.Space 2) {B : ℍ → ComplexPlane₂}
    (hB : ContMDiff I₁ I₂ ω B)
    (hagree : ∀ z : TriangleRegularPoint, B z.val = RegularCover.mixedTwo θ z) :
    B = mixedTwo θ :=
  HolomorphicExtensionGluing.holomorphic_extension_unique triangleRegularDomain
    (RegularCover.mixedTwo θ) triangleRegularLocus_dense hB (mixedTwo_holomorphic θ)
    hagree (mixedTwo_restrict θ)

theorem baseTop_unique (θ : Form FamilyModel Threefold.Space 3) {C : ℍ → ℂ}
    (hC : ContMDiff I₁ I₁ ω C)
    (hagree : ∀ z : TriangleRegularPoint, C z.val = RegularCover.baseTop θ z) :
    C = baseTop θ :=
  HolomorphicExtensionGluing.holomorphic_extension_unique triangleRegularDomain
    (RegularCover.baseTop θ) triangleRegularLocus_dense hC (baseTop_holomorphic θ)
    hagree (baseTop_restrict θ)

theorem baseOne_unique (θ : Form FamilyModel Threefold.Space 1)
    (hc : ∀ z : TriangleRegularPoint, RegularCover.fibreOne θ z = 0) {A : ℍ → ℂ}
    (hA : ContMDiff I₁ I₁ ω A)
    (hagree : ∀ z : TriangleRegularPoint, A z.val = RegularCover.baseOne θ z) :
    A = baseOne θ hc :=
  HolomorphicExtensionGluing.holomorphic_extension_unique triangleRegularDomain
    (RegularCover.baseOne θ) triangleRegularLocus_dense hA (baseOne_holomorphic θ hc)
    hagree (baseOne_restrict θ hc)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticExtension

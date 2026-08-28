import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticJacobianChart
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticExtensions

/-!
# Genuine coefficient germs at the two elliptic centers

The actual full-source root parametrization has an open target in the
original upper half-plane. Its holomorphic inverse transports the proved
root-coordinate extensions to that target. Every regular point there has
nonzero inverse root coordinate: root zero maps to the elliptic center,
which is not regular. Thus the actual punctured-root coefficient formulas
give agreement on the entire regular overlap of the germ neighborhood.
-/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic HolomorphicDifferentialForms

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The actual open image of the whole small root domain. -/
def ellipticGermDomain (j : Kind) : Opens ℍ :=
  ⟨(baseParametrization j).target, baseParametrization_target_isOpen j⟩

theorem ellipticCenter_mem_ellipticGermDomain (j : Kind) :
    Triangle.ellipticCenter j ∈ ellipticGermDomain j :=
  ellipticCenter_mem_baseParametrization_target j

/-- The genuine inverse chart, restricted to its actual target. -/
def ellipticGermRoot (j : Kind) (y : ellipticGermDomain j) : Root j :=
  (baseParametrization j).symm y

theorem ellipticGermRoot_holomorphic (j : Kind) :
    ContMDiff I₁ I₁ ω (ellipticGermRoot j) := by
  intro y
  exact contMDiffAt_subtype_iff.mpr
    (baseParametrization_symm_holomorphicAt j y y.property)

@[simp] theorem baseLift_ellipticGermRoot (j : Kind) (y : ellipticGermDomain j) :
    baseLift j (ellipticGermRoot j y) = (y : ℍ) :=
  baseLift_baseParametrization_symm j y y.property

@[simp] theorem ellipticGermRoot_center (j : Kind) :
    ellipticGermRoot j
      ⟨Triangle.ellipticCenter j, ellipticCenter_mem_ellipticGermDomain j⟩ = rootZero j :=
  baseParametrization_symm_center j

/-- A regular point cannot have inverse root coordinate zero, since the
actual image of root zero is the nonregular elliptic center. -/
theorem ellipticGermRoot_ne_zero_of_regular (j : Kind) (y : ellipticGermDomain j)
    (hy : (y : ℍ) ∈ triangleRegularDomain) :
    rootCoordinate j (ellipticGermRoot j y) ≠ 0 := by
  intro hz
  have hroot : ellipticGermRoot j y = rootZero j := by
    apply Subtype.ext
    apply Subtype.ext
    exact hz
  have hcenter : (y : ℍ) = Triangle.ellipticCenter j := by
    rw [← baseLift_ellipticGermRoot j y, hroot, baseLift_rootZero]
  exact EllipticFilling.ellipticCenter_not_regular j (hcenter ▸ hy)

section Generic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- An actual holomorphic root extension gives a holomorphic germ in the
original upper half-plane with agreement on its whole regular overlap.
The neighborhood, inverse chart, and nonzero root property are constructed,
not assumed as extra extension data. -/
theorem exists_elliptic_germ_of_rootExtension (j : Kind)
    (f : TriangleRegularPoint → F) (h : Root j → F)
    (hh : ContMDiff I₁ (modelWithCornersSelf ℂ F) ω h)
    (heq : ∀ z : RootStar j, h z.val = f (regularBase j z)) :
    ∃ V : Opens ℍ, Triangle.ellipticCenter j ∈ V ∧ ∃ k : V → F,
      ContMDiff I₁ (modelWithCornersSelf ℂ F) ω k ∧
        ∀ y : V, ∀ hy : (y : ℍ) ∈ triangleRegularDomain, k y = f ⟨y, hy⟩ := by
  refine ⟨ellipticGermDomain j, ellipticCenter_mem_ellipticGermDomain j,
    h ∘ ellipticGermRoot j, hh.comp (ellipticGermRoot_holomorphic j), ?_⟩
  intro y hy
  let z : RootStar j :=
    ⟨ellipticGermRoot j y, ellipticGermRoot_ne_zero_of_regular j y hy⟩
  have hbase : regularBase j z = ⟨y, hy⟩ := by
    apply Subtype.ext
    exact baseLift_ellipticGermRoot j y
  exact (heq z).trans (congrArg f hbase)

end Generic

section ActualForms

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The genuine vertical coefficient of every global one-form extends
across each actual elliptic center. -/
theorem oneFibre_elliptic_germ (j : Kind) (θ : Form FamilyModel Threefold.Space 1) :
    ∃ V : Opens ℍ, Triangle.ellipticCenter j ∈ V ∧ ∃ h : V → ComplexPlane₂,
      ContMDiff I₁ I₂ ω h ∧ ∀ y : V, ∀ hy : (y : ℍ) ∈ triangleRegularDomain,
        h y = RegularCover.fibreOne θ ⟨y, hy⟩ :=
  exists_elliptic_germ_of_rootExtension j (RegularCover.fibreOne θ)
    (oneFibreExtension j θ) (oneFibreExtension_holomorphic j θ) (oneFibreExtension_eq j θ)

/-- The genuine mixed coefficient of every global two-form extends
across each actual elliptic center. -/
theorem twoMixed_elliptic_germ (j : Kind) (θ : Form FamilyModel Threefold.Space 2) :
    ∃ V : Opens ℍ, Triangle.ellipticCenter j ∈ V ∧ ∃ h : V → ComplexPlane₂,
      ContMDiff I₁ I₂ ω h ∧ ∀ y : V, ∀ hy : (y : ℍ) ∈ triangleRegularDomain,
        h y = RegularCover.mixedTwo θ ⟨y, hy⟩ :=
  exists_elliptic_germ_of_rootExtension j (RegularCover.mixedTwo θ)
    (twoMixedExtension j θ) (twoMixedExtension_holomorphic j θ) (twoMixedExtension_eq j θ)

/-- The genuine top-form coefficient extends across each actual elliptic center. -/
theorem top_elliptic_germ (j : Kind) (θ : Form FamilyModel Threefold.Space 3) :
    ∃ V : Opens ℍ, Triangle.ellipticCenter j ∈ V ∧ ∃ h : V → ℂ,
      ContMDiff I₁ I₁ ω h ∧ ∀ y : V, ∀ hy : (y : ℍ) ∈ triangleRegularDomain,
        h y = RegularCover.baseTop θ ⟨y, hy⟩ :=
  exists_elliptic_germ_of_rootExtension j (RegularCover.baseTop θ)
    (topExtension j θ) (topExtension_holomorphic j θ) (topExtension_eq j θ)

/-- Once its genuine fibre coefficient vanishes, the one-form base
coefficient extends, as required in source Lemma 9.16(i). -/
theorem oneBase_elliptic_germ_of_fibre_zero (j : Kind)
    (θ : Form FamilyModel Threefold.Space 1)
    (hc : ∀ z : TriangleRegularPoint, RegularCover.fibreOne θ z = 0) :
    ∃ V : Opens ℍ, Triangle.ellipticCenter j ∈ V ∧ ∃ h : V → ℂ,
      ContMDiff I₁ I₁ ω h ∧ ∀ y : V, ∀ hy : (y : ℍ) ∈ triangleRegularDomain,
        h y = RegularCover.baseOne θ ⟨y, hy⟩ :=
  exists_elliptic_germ_of_rootExtension j (RegularCover.baseOne θ)
    (oneBaseExtension j θ) (oneBaseExtension_holomorphic j θ)
    (oneBaseExtension_eq_of_fibre_zero j θ hc)

end ActualForms

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

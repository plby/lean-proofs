import Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialFormsNormalForms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupExtensionDerivative

/-!
# Original triangle maps on an invariant open period-vector cover

Every map below is the restriction of the already constructed full
triangle action and its original period right block. Preservation of
the open base only ensures that the actual restricted maps take values
in that base. The manifold structures remain the inherited native ones.
-/

noncomputable section

open Set Matrix UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms.Covariance

open SpecialPeriods
open SpecialPeriods.Threefold.HolomorphicForms.RegularCover
  (groupRightBlockExtension groupRightBlockExtension_entry_holomorphic)

attribute [local instance] coverChartedSpace cover_isManifold

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

variable (U : TopologicalSpace.Opens ℍ)

/-- The source's preservation condition for an actual triangle-group element. -/
def Preserves (g : TriangleGroup) : Prop :=
  MapsTo (triangleGeometricRepresentation g : ℍ → ℍ) (U : Set ℍ) (U : Set ℍ)

/-- Restriction of the original geometric triangle map to the invariant open base. -/
def baseMap (g : TriangleGroup) (hg : Preserves U g) (z : U) : U :=
  ⟨triangleGeometricRepresentation g z.val, hg z.property⟩

@[simp] theorem baseMap_coe (g : TriangleGroup) (hg : Preserves U g) (z : U) :
    (baseMap U g hg z).val = triangleGeometricRepresentation g z.val := rfl

/-- This is holomorphic in the inherited open-submanifold charts. -/
theorem baseMap_holomorphic (g : TriangleGroup) (hg : Preserves U g) :
    ContMDiff I₁ I₁ ω (baseMap U g hg) := by
  intro z
  have he : ContMDiffAt I₁ I₁ ω (fun y : U => (baseMap U g hg y).val) z ↔
      ContMDiffAt I₁ I₁ ω (baseMap U g hg) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := U)
      (baseMap U g hg) univ z
  exact he.mp (((triangleGeometricRepresentation_holomorphic g).comp
    (contMDiff_subtype_val (U := U))) z)

/-- The same original period right block, including at elliptic orbit points. -/
def rightBlock (g : TriangleGroup) (z : U) : Matrix (Fin 2) (Fin 2) ℂ :=
  groupRightBlockExtension g z.val

@[simp] theorem rightBlock_apply (g : TriangleGroup) (z : U) :
    rightBlock U g z = groupRightBlockExtension g z.val := rfl

theorem rightBlock_entry_holomorphic (g : TriangleGroup) (i k : Fin 2) :
    ContMDiff I₁ I₁ ω (fun z : U => rightBlock U g z i k) :=
  (groupRightBlockExtension_entry_holomorphic g i k).comp contMDiff_subtype_val

/-- The original complex-linear triangle lift restricted to the open vector cover. -/
def complexLift (g : TriangleGroup) (hg : Preserves U g) (x : Cover U) : Cover U :=
  (baseMap U g hg x.1, rightBlock U g x.1 *ᵥ x.2)

@[simp] theorem complexLift_apply (g : TriangleGroup) (hg : Preserves U g) (x : Cover U) :
    complexLift U g hg x = (baseMap U g hg x.1, rightBlock U g x.1 *ᵥ x.2) := rfl

/-- The actual restricted vector lift is holomorphic in the original product charts. -/
theorem complexLift_holomorphic (g : TriangleGroup) (hg : Preserves U g) :
    ContMDiff IF IF ω (complexLift U g hg) := by
  have hf : ContMDiff IF I₁ ω (Prod.fst : Cover U → U) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hs : ContMDiff IF I₂ ω (Prod.snd : Cover U → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hbase := (baseMap_holomorphic U g hg).comp hf
  have hvec : ContMDiff IF I₂ ω
      (fun x : Cover U => rightBlock U g x.1 *ᵥ x.2) := by
    apply contMDiff_pi_space.mpr
    intro i
    have h₀ := ((rightBlock_entry_holomorphic U g i 0).comp hf).mul
      ((contMDiff_pi_space.mp hs) 0)
    have h₁ := ((rightBlock_entry_holomorphic U g i 1).comp hf).mul
      ((contMDiff_pi_space.mp hs) 1)
    convert h₀.add h₁ using 1
    funext x
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Function.comp_def]
  rw [modelWithCornersSelf_prod] at hbase hvec ⊢
  exact hbase.prodMk hvec

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms.Covariance

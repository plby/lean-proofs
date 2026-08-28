import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleCover
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocyclePrimitiveBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroDerived

/-!
# Genuine holomorphic overlap sections of additive period cocycles

The primitive upstairs need not be holomorphic. Its difference between
two actual local lifts is nevertheless locally a fixed lattice character
of the holomorphic base coefficients. That exact local identity proves
holomorphicity in the original varying-period quotient atlas.

The sign convention is always first lift minus second lift.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- Literal first-lift minus second-lift difference of the actual primitive. -/
def difference (P : HolomorphicPeriodMap V B) (a : Coefficients V B)
    (i j : B × ComplexPlane₂) (x : P.TotalSpace) : ℂ :=
  primitive P a (lift P i x) - primitive P a (lift P j x)

@[simp] theorem difference_zero (P : HolomorphicPeriodMap V B)
    (i j : B × ComplexPlane₂) (x : P.TotalSpace) :
    difference P (0 : Coefficients V B) i j x = 0 := by
  simp only [difference, primitive_zero, sub_self]

theorem difference_add (P : HolomorphicPeriodMap V B) (a a' : Coefficients V B)
    (i j : B × ComplexPlane₂) (x : P.TotalSpace) :
    difference P (a + a') i j x = difference P a i j x + difference P a' i j x := by
  simp only [difference, primitive_add]
  abel

theorem difference_smul (P : HolomorphicPeriodMap V B) (c : ℂ) (a : Coefficients V B)
    (i j : B × ComplexPlane₂) (x : P.TotalSpace) :
    difference P (c • a) i j x = c * difference P a i j x := by
  simp only [difference, primitive_smul, mul_sub]

/-- A fixed actual lattice vector gives the difference on a whole neighborhood
of each overlap point, with the positive character sign for `L_i - L_j`. -/
theorem difference_eventually_character (P : HolomorphicPeriodMap V B)
    (a : Coefficients V B) (i j : B × ComplexPlane₂) {x : P.TotalSpace}
    (hx : x ∈ coverOpen P i ⊓ coverOpen P j) :
    ∃ g : standardLattice, difference P a i j =ᶠ[𝓝 x]
      fun y => character a (P.projection y) g := by
  obtain ⟨g, hg⟩ := lift_period_eventuallyEq P i j hx
  have hJ : ∀ᶠ y in 𝓝 x, y ∈ coverOpen P j := (coverOpen P j).isOpen.mem_nhds hx.2
  refine ⟨g, ?_⟩
  filter_upwards [hg, hJ] with y hgy hy
  rw [difference, hgy, primitive_add_period, add_sub_cancel_left, lift_base P j hy]

/-- Actual native sections on arbitrary total-space opens, with the original quotient atlas. -/
abbrev NativeSection (P : HolomorphicPeriodMap V B) (U : Opens P.TotalSpace) : Type :=
  letI := P.totalChartedSpace
  HolomorphicFunctionSheaf.Section IT P.TotalSpace U

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual overlap difference is holomorphic at every original overlap point. -/
theorem difference_holomorphicAt (P : HolomorphicPeriodMap V B) (a : Coefficients V B)
    (i j : B × ComplexPlane₂) {x : P.TotalSpace}
    (hx : x ∈ coverOpen P i ⊓ coverOpen P j) :
    letI := P.totalChartedSpace
    ContMDiffAt IT 𝓘(ℂ) ω (difference P a i j) x := by
  let := P.totalChartedSpace
  obtain ⟨g, hg⟩ := difference_eventually_character P a i j hx
  have h := (character_holomorphic a g).comp P.projection_holomorphic
  exact h.contMDiffAt.congr_of_eventuallyEq hg

/-- The genuine holomorphic section on the actual pairwise intersection. -/
def overlapSection (P : HolomorphicPeriodMap V B) (a : Coefficients V B)
    (i j : B × ComplexPlane₂) : NativeSection P (coverOpen P i ⊓ coverOpen P j) := by
  letI := P.totalChartedSpace
  refine ⟨fun x => difference P a i j x, ?_⟩
  intro x
  exact (difference_holomorphicAt P a i j x.property).comp x (contMDiff_subtype_val x)

@[simp] theorem overlapSection_apply (P : HolomorphicPeriodMap V B) (a : Coefficients V B)
    (i j : B × ComplexPlane₂) (x : ↥(coverOpen P i ⊓ coverOpen P j)) :
    overlapSection P a i j x =
      primitive P a (lift P i x) - primitive P a (lift P j x) := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle

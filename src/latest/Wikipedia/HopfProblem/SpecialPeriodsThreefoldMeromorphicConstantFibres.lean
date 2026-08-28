import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicFibresConstant
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularParameters
import Wikipedia.HopfProblem.SpecialPeriodsExceptionalRelations
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarSpecialTorus
import Mathlib.Analysis.Complex.Cardinality

/-!
# Uncountably many actual constant regular fibres

The native finite period-base coordinate is the finite coordinate of the
original normalized sphere base. The countable exceptional period values
and the countable restriction exceptions therefore define actual countable
subsets of that same sphere, together with its three marked values.
Every remaining fibre has a genuine restriction, and the full native
meromorphic field of its special period torus consists of constants.
Consequently every global meromorphic function has uncountably many
actual constant regular sphere fibres.
-/

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicFibres

open Triangle HolomorphicForms.RegularCover HolomorphicMeromorphic

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The actual period coordinate and the actual sphere value use the
same normalized uniformization, with no coordinate renormalization. -/
theorem regularSphereValue_eq_specialSourceCoordinate (z : TriangleRegularPoint) :
    regularSphereValue z = (specialSourceCoordinate z.val : RiemannSphere) :=
  (BetaTorsor.finiteOrbitCoordinate_coe triangleSphereUniformization
    triangleSphereUniformization_cusp (triangleOrbitProjection z.val)).symm

/-- The proved exceptional period-base values, placed in the original sphere. -/
def periodExceptionalSphereValues : Set RiemannSphere :=
  ((↑) : ℂ → RiemannSphere) '' exceptionalPeriodBaseValues

theorem periodExceptionalSphereValues_countable : periodExceptionalSphereValues.Countable :=
  exceptionalPeriodBaseValues_countable.image ((↑) : ℂ → RiemannSphere)

/-- Every actual regular lift over a nonexceptional sphere value has a
nonexceptional original finite period coordinate. -/
theorem sourceCoordinate_not_exceptional_of_sphere_not_exceptional
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ periodExceptionalSphereValues) :
    specialSourceCoordinate z.val ∉ exceptionalPeriodBaseValues := by
  intro hbad
  exact hz ⟨specialSourceCoordinate z.val, hbad,
    (regularSphereValue_eq_specialSourceCoordinate z).symm⟩

/-- A regular sphere value has an actual regular period parameter,
and avoidance of the period obstruction is preserved by that genuine lift. -/
theorem exists_regularPoint_over_not_exceptional (b : RiemannSphere)
    (hb : b ∈ sphereRegularPatch) (hbad : b ∉ periodExceptionalSphereValues) :
    ∃ z : TriangleRegularPoint, regularSphereValue z = b ∧
      specialSourceCoordinate z.val ∉ exceptionalPeriodBaseValues := by
  obtain ⟨hinf, hzero, hone⟩ := (mem_sphereRegularPatch b).mp hb
  obtain ⟨z, hz⟩ := exists_regularPoint_over b hinf hzero hone
  refine ⟨z, hz, sourceCoordinate_not_exceptional_of_sphere_not_exceptional z ?_⟩
  change regularSphereValue z = b at hz
  rwa [hz]

/-- The only nonregular sphere values are the three actual normalized
marked values, hence form a countable set. -/
theorem sphereRegularPatch_compl_countable :
    (sphereRegularPatch : Set RiemannSphere)ᶜ.Countable := by
  change (({(∞ : RiemannSphere), ((0 : ℂ) : RiemannSphere),
    ((1 : ℂ) : RiemannSphere)} : Set RiemannSphere)ᶜ)ᶜ.Countable
  rw [compl_compl]
  exact (((finite_singleton ((1 : ℂ) : RiemannSphere)).insert
    ((0 : ℂ) : RiemannSphere)).insert (∞ : RiemannSphere)).countable

/-- The actual countable sphere obstruction for one global meromorphic
function: its restriction exceptions, period exceptions, and marked values. -/
def constantFibreExceptions (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    Set RiemannSphere :=
  exceptionalValues g ∪ periodExceptionalSphereValues ∪ (sphereRegularPatch : Set RiemannSphere)ᶜ

theorem constantFibreExceptions_countable
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    (constantFibreExceptions g).Countable :=
  ((exceptionalValues_countable g).union periodExceptionalSphereValues_countable).union
    sphereRegularPatch_compl_countable

/-- Outside the constructed countable sphere obstruction, the actual
native torus restriction is constant by the proved special-torus theorem. -/
theorem mem_constantRegularFibres_of_not_exceptional
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) (b : RiemannSphere)
    (hb : b ∉ constantFibreExceptions g) : b ∈ MeromorphicRegularCover.constantRegularFibres g := by
  have hrestriction : b ∉ exceptionalValues g := fun h => hb (Or.inl (Or.inl h))
  have hperiod : b ∉ periodExceptionalSphereValues := fun h => hb (Or.inl (Or.inr h))
  have hregular : b ∈ sphereRegularPatch := by
    by_contra h
    exact hb (Or.inr h)
  obtain ⟨z, hzb, hzperiod⟩ := exists_regularPoint_over_not_exceptional b hregular hperiod
  have hzrestriction : regularSphereValue z ∉ exceptionalValues g := by
    rwa [hzb]
  obtain ⟨c, hc⟩ := PolarSpecialTorus.exists_eq_constant_of_base_not_exceptional z.val hzperiod
    (regularTorusRestriction g z hzrestriction)
  exact hzb ▸ mem_constantRegularFibres_of_regularTorusRestriction_eq
    g z hzrestriction c hc

/-- Every genuine global meromorphic function on the actual threefold
has uncountably many constant regular fibres. Both exceptional sets and
the existence of regular fibre points have been proved, not assumed. -/
theorem constantRegularFibres_uncountable
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    ¬ (MeromorphicRegularCover.constantRegularFibres g).Countable := by
  intro hcount
  have hsphere : (univ : Set RiemannSphere).Countable := by
    apply ((constantFibreExceptions_countable g).union hcount).mono
    intro b _
    by_cases hb : b ∈ constantFibreExceptions g
    · exact Or.inl hb
    · exact Or.inr (mem_constantRegularFibres_of_not_exceptional g b hb)
  apply not_countable_complex
  simpa only [preimage_univ] using hsphere.preimage
    (show _root_.Function.Injective ((↑) : ℂ → RiemannSphere) from OnePoint.coe_injective)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicFibres

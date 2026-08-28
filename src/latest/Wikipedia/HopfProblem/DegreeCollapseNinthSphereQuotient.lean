import Wikipedia.HopfProblem.DegreeCollapseQuaternionicPiNine
import Wikipedia.NoExoticSixSphere.StableThirdCyclicGroup
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSequence

/-!
# The original pi9(S3) is an explicit quotient of the third stable stem

The proved vanishing of pi9(Sp(2)) makes the actual quaternionic
connecting homomorphism surjective. Its source is the genuine
pi10(S7), already identified with Z/24 through the original suspensions.
Thus every ninth sphere class is a power of one specified connecting
class and has order dividing twenty-four.

The precise order and the stabilization of this connecting class are
not asserted. In particular this is not the completed sixth-stem
calculation.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.NinthSphereQuotient

open NoExoticSixSphere Wikipedia.HomotopyGroupsOfSpheres QuaternionicFibration

theorem baseSphereHomeomorph_north : baseSphereHomeomorph north = spherePole 7 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

abbrev Target := π_ 9 (NoExoticSixSphere.Sphere 3) (fiberSphereHomeomorph 1)

def sourceProjection : StableThirdAttaching.Stage 2 →* Target :=
  (sphereConnectingHom 9).comp
    (basepointEqMulEquiv (N := Fin 10) baseSphereHomeomorph_north).symm.toMonoidHom

theorem sourceProjection_surjective : Function.Surjective sourceProjection := by
  have h : Function.Surjective (sphereConnectingHom 9) :=
    (homeomorphMulEquiv (N := Fin 9) fiberSphereHomeomorph 1).surjective.comp
      (QuaternionicPiNine.connecting_nine_surjective.comp
        (homeomorphMulEquiv (N := Fin 10) baseSphereHomeomorph north).symm.surjective)
  exact h.comp (basepointEqMulEquiv (N := Fin 10) baseSphereHomeomorph_north).symm.surjective

def projection : Multiplicative (ZMod 24) →* Target :=
  sourceProjection.comp (StableThirdAttaching.groupEquiv 2).symm.toMonoidHom

theorem projection_surjective : Function.Surjective projection :=
  sourceProjection_surjective.comp (StableThirdAttaching.groupEquiv 2).symm.surjective

def quotientEquiv : (Multiplicative (ZMod 24) ⧸ projection.ker) ≃* Target :=
  QuotientGroup.quotientKerEquivOfSurjective projection projection_surjective

theorem quotientEquiv_mk (z : Multiplicative (ZMod 24)) :
    quotientEquiv (QuotientGroup.mk z) = projection z := rfl

def generator : Target := projection (Multiplicative.ofAdd (1 : ZMod 24))

theorem generator_pow (z : ZMod 24) :
    generator ^ z.val = projection (Multiplicative.ofAdd z) := by
  rw [generator, ← map_pow]
  congr 1
  change Multiplicative.ofAdd (z.val • (1 : ZMod 24)) = Multiplicative.ofAdd z
  simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem exists_generator_pow (x : Target) :
    ∃ k : Fin 24, generator ^ k.val = x := by
  obtain ⟨z, rfl⟩ := projection_surjective x
  exact ⟨⟨z.toAdd.val, ZMod.val_lt z.toAdd⟩, generator_pow z.toAdd⟩

theorem pow_twentyFour (x : Target) : x ^ 24 = 1 := by
  obtain ⟨c, rfl⟩ := sourceProjection_surjective x
  rw [← map_pow, StableThirdAttaching.pow_twentyFour 2, map_one]

instance finiteTarget : Finite Target :=
  Finite.of_surjective projection projection_surjective

end Wikipedia.HopfProblem.DegreeCollapse.NinthSphereQuotient

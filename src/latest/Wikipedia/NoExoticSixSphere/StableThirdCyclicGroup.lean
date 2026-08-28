import Wikipedia.NoExoticSixSphere.JamesAttachingTorsionParity
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The actual third-stem stable groups are cyclic of order twenty-four

The original suspended torsion subgroup contains an element of order
twelve, while the original Hopf-coordinate lift has nontrivial twelfth
power. Since the whole group has order twenty-four, the least common
multiple of these two element orders is twenty-four. Commutativity
supplies an element of that order, proving cyclicity. The chosen marking
is transported through the ORIGINAL suspension equivalences.

No assertion is made that the noncanonical Hopf-coordinate lift itself
has order twenty-four: its order can instead be eight.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.SphereFiveEighth

def torsionGenerator : π_ 8 (Sphere 5) (spherePole 5) :=
  torsionInclusion (Multiplicative.ofAdd (1 : ZMod 12))

theorem orderOf_torsionGenerator : orderOf torsionGenerator = 12 := by
  rw [torsionGenerator, orderOf_injective torsionInclusion torsionInclusion_injective]
  exact ZMod.addOrderOf_one 12

theorem lcm_twelve_eq_twentyFour (n : ℕ) (hd : n ∣ 24) (hn : ¬n ∣ 12) :
    Nat.lcm n 12 = 24 := by
  have hle : n ≤ 24 := Nat.le_of_dvd (by decide) hd
  interval_cases n <;> norm_num at hd
  all_goals norm_num at hn
  all_goals decide

theorem exists_orderOf_twentyFour : ∃ g : π_ 8 (Sphere 5) (spherePole 5), orderOf g = 24 := by
  obtain ⟨g, _, hg⟩ := (Commute.all integerLift torsionGenerator).exists_orderOf_eq_lcm
  refine ⟨g, hg.trans ?_⟩
  rw [orderOf_torsionGenerator]
  apply lcm_twelve_eq_twentyFour
  · exact cardinality ▸ orderOf_dvd_natCard integerLift
  · intro h
    exact integerLift_twelfth_power_ne_one (orderOf_dvd_iff_pow_eq_one.mp h)

theorem isCyclic : IsCyclic (π_ 8 (Sphere 5) (spherePole 5)) := by
  obtain ⟨g, hg⟩ := exists_orderOf_twentyFour
  exact isCyclic_of_orderOf_eq_card g (hg.trans cardinality.symm)

def groupEquiv : π_ 8 (Sphere 5) (spherePole 5) ≃* Multiplicative (ZMod 24) := by
  let := isCyclic
  exact (zmodMulEquivOfGenerator
    (IsCyclic.exists_generator (α := π_ 8 (Sphere 5) (spherePole 5))).choose_spec cardinality).symm

end NoExoticSixSphere.SphereFiveEighth

namespace NoExoticSixSphere.StableThirdAttaching

def groupEquiv (k : ℕ) : Stage k ≃* Multiplicative (ZMod 24) :=
  (fromFirst k).symm.trans SphereFiveEighth.groupEquiv

theorem groupEquiv_fromFirst (k : ℕ) (x : Stage 0) :
    groupEquiv k (fromFirst k x) = SphereFiveEighth.groupEquiv x := by
  change SphereFiveEighth.groupEquiv ((fromFirst k).symm (fromFirst k x)) = _
  rw [MulEquiv.symm_apply_apply]

theorem groupEquiv_stepHom (k : ℕ) (x : Stage k) :
    groupEquiv (k + 1) (stepHom k x) = groupEquiv k x := by
  obtain ⟨a, rfl⟩ := (fromFirst k).surjective x
  rw [← fromFirst_succ, groupEquiv_fromFirst, groupEquiv_fromFirst]

end NoExoticSixSphere.StableThirdAttaching

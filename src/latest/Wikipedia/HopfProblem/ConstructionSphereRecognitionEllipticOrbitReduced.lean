import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitAction
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitQuotient
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitFlatDeck

/-!
# The full elliptic cap after taking its original delta-circle quotient

The map forgets exactly the fourth real period coordinate before taking
the native finite action.  Its remaining finite generator is the literal
projected affine map, including the gamma couplings and the original twist.
Comparison of the two actual quotient topologies gives a homeomorphism.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

open Elliptic SpecialPeriods EllipticModel EllipticNative EllipticOrbitFlat
open SpecialPeriods.Threefold.Homology.DeltaSweep

local notation "Circle" => AddCircle (1 : ℝ)

/-- The residual finite affine quotient of the actual marked three-torus.
The finite elliptic deck action has not been discarded. -/
abbrev FibreModel (j : Kind) :=
  FibreQuotient j.order (deck j) (deck_pow_order j)

/-- The clockwise root disc with the actual projected affine finite action. -/
abbrev ReducedCap (j : Kind) :=
  CapQuotient j.order (deck j) (deck_pow_order j)

def fibreModelProjection (j : Kind) : DeltaBase → FibreModel j :=
  fibreProject j.order (deck j) (deck_pow_order j)

theorem fibreModelProjection_isOpenQuotientMap (j : Kind) :
    IsOpenQuotientMap (fibreModelProjection j) :=
  fibreProject_isOpenQuotientMap j.order (deck j) (deck_pow_order j)

def reducedCapProjection (j : Kind) : Disc × DeltaBase → ReducedCap j :=
  capProject j.order (deck j) (deck_pow_order j)

theorem reducedCapProjection_isOpenQuotientMap (j : Kind) :
    IsOpenQuotientMap (reducedCapProjection j) :=
  capProject_isOpenQuotientMap j.order (deck j) (deck_pow_order j)

variable {j : Kind} (D : Equivariant.Data j)

/-- Forget only delta on the original covering family, leaving the original root unchanged. -/
def coverDrop (x : D.TotalSpace) : Disc × DeltaBase := (x.1, dropDelta x.2)

@[simp] theorem coverDrop_apply (s : Disc) (x : RealTorus₄) :
    coverDrop D (s, x) = (s, dropDelta x) := rfl

theorem coverDrop_isOpenQuotientMap : IsOpenQuotientMap (coverDrop D) :=
  IsOpenQuotientMap.id.prodMap dropDelta_isOpenQuotientMap

/-- The native generator descends without deleting any of its affine terms. -/
theorem coverDrop_permutation (x : D.TotalSpace) :
    coverDrop D (D.permutation j.twist x) =
      capPermutation j.order (deck j) (coverDrop D x) := by
  change (familyRotation j x.1, dropDelta (flatTorusAffine j j.twist x.2)) =
    (rotate (-sector j.order) x.1, deck j (dropDelta x.2))
  rw [rotate_neg_sector, dropDelta_deck]

theorem coverDrop_action (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action j.twist (mainTwist_admissible j).1
    letI := capAction j.order (deck j) (deck_pow_order j)
    coverDrop D (g • x) = g • coverDrop D x := by
  let := D.action j.twist (mainTwist_admissible j).1
  let := capAction j.order (deck j) (deck_pow_order j)
  have h : Function.Semiconj (coverDrop D) (D.permutation j.twist)
      (capPermutation j.order (deck j)) := coverDrop_permutation D
  change coverDrop D ((D.permutation j.twist ^ g.toAdd.val) x) =
    (capPermutation j.order (deck j) ^ g.toAdd.val) (coverDrop D x)
  simp only [Equiv.Perm.coe_pow]
  exact h.iterate_right g.toAdd.val x

/-- The fibres upstairs are precisely the original fourth-column circle translations. -/
theorem coverDrop_eq_iff (x y : D.TotalSpace) :
    coverDrop D x = coverDrop D y ↔ ∃ d : Circle, upstairsCircleFlow D d y = x := by
  constructor
  · intro h
    have hs : x.1 = y.1 := congrArg (fun z : Disc × DeltaBase => z.1) h
    have hx : dropDelta x.2 = dropDelta y.2 :=
      congrArg (fun z : Disc × DeltaBase => z.2) h
    obtain ⟨d, hd⟩ := (dropDelta_eq_iff x.2 y.2).mp hx
    refine ⟨d, ?_⟩
    exact Prod.ext hs.symm hd.symm
  · rintro ⟨d, hd⟩
    rw [← hd]
    change (y.1, dropDelta (y.2 + deltaCircle d)) = (y.1, dropDelta y.2)
    rw [dropDelta_add_deltaCircle]

/-- The genuine map from the original cap into its reduced finite quotient. -/
def reducedCapMap :
    D.Space j.twist (mainTwist_admissible j) → ReducedCap j := by
  let := D.action j.twist (mainTwist_admissible j).1
  let := capAction j.order (deck j) (deck_pow_order j)
  exact QuotientModel.orbitMap (coverDrop D) (coverDrop_action D)

@[simp] theorem reducedCapMap_quotient (x : D.TotalSpace) :
    reducedCapMap D (D.quotient j.twist (mainTwist_admissible j) x) =
      reducedCapProjection j (coverDrop D x) := rfl

theorem reducedCapMap_isOpenQuotientMap : IsOpenQuotientMap (reducedCapMap D) := by
  let := D.action j.twist (mainTwist_admissible j).1
  let := capAction j.order (deck j) (deck_pow_order j)
  let := capAction_continuous j.order (deck j) (deck_pow_order j)
  exact QuotientModel.orbitMap_isOpenQuotientMap
    (coverDrop D) (coverDrop_action D) (coverDrop_isOpenQuotientMap D)

/-- No new equivalence relation is introduced downstairs: these are exactly
the orbits of the original native cap circle. -/
theorem reducedCapMap_eq_iff (x y : D.Space j.twist (mainTwist_admissible j)) :
    reducedCapMap D x = reducedCapMap D y ↔ ∃ d : Circle, fullCircleFlow D d y = x := by
  let := D.action j.twist (mainTwist_admissible j).1
  let := capAction j.order (deck j) (deck_pow_order j)
  exact QuotientModel.orbitMap_eq_iff_shift (coverDrop D) (coverDrop_action D)
    (upstairsCircleFlow D) (fullCircleFlow D) (fullCircleFlow_quotient D)
    (coverDrop_eq_iff D) x y

/-- The two orbit quotients carry their actual original quotient topologies. -/
def fullOrbitReducedHomeomorph : FullOrbit D ≃ₜ ReducedCap j :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph
    (fullOrbitProjection D) (reducedCapMap D)
    (fullOrbitProjection_isOpenQuotientMap D).isQuotientMap
    (reducedCapMap_isOpenQuotientMap D).isQuotientMap
    (fun x y => (fullOrbitProjection_eq_iff D x y).trans (reducedCapMap_eq_iff D x y).symm)

@[simp] theorem fullOrbitReducedHomeomorph_projection
    (x : D.Space j.twist (mainTwist_admissible j)) :
    fullOrbitReducedHomeomorph D (fullOrbitProjection D x) = reducedCapMap D x :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph_apply _ _ _ _ _ x

/-- Every original root-and-period representative is preserved by the comparison. -/
@[simp] theorem fullOrbitReducedHomeomorph_quotient (s : Disc) (x : RealTorus₄) :
    fullOrbitReducedHomeomorph D
      (fullOrbitProjection D (D.quotient j.twist (mainTwist_admissible j) (s, x))) =
        reducedCapProjection j (s, dropDelta x) := by
  rw [fullOrbitReducedHomeomorph_projection, reducedCapMap_quotient, coverDrop_apply]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

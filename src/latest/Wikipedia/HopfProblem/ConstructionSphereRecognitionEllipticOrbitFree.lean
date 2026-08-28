import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitReduced
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitSmallAction

/-!
# The exact period of the original elliptic-cap circle

The retained gamma coordinate proves that no nonidentity finite projected
deck element fixes a point.  Consequently the original delta circle has
no additional isotropy on either the full or small cap, including their
central fibres.  The native real flow has precisely the integral periods.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

open Elliptic SpecialPeriods EllipticModel EllipticOrbitFlat
open SpecialPeriods.Threefold.Homology.DeltaSweep

local notation "Circle" => AddCircle (1 : ℝ)

/-- Freeness is derived from the exact native signed gamma shift. -/
theorem fibreModelAction_free (j : Kind) :
    letI := fibreAction j.order (deck j) (deck_pow_order j)
    IsCancelSMul (CyclicGroup j) DeltaBase :=
  CyclicAction.isCancelSMul (deck j).toEquiv
    (fibrePermutation_pow_order j.order (deck j) (deck_pow_order j))
    (fun r hr hrm z => deck_iterate_ne j r hr hrm z)

/-- The projected finite action on the full root-disc cover is also free. -/
theorem reducedCapAction_free (j : Kind) :
    letI := capAction j.order (deck j) (deck_pow_order j)
    IsCancelSMul (CyclicGroup j) (Disc × DeltaBase) := by
  let := capAction j.order (deck j) (deck_pow_order j)
  let := fibreAction j.order (deck j) (deck_pow_order j)
  let := fibreModelAction_free j
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g p hp
  change (capPermutation j.order (deck j) ^ g.toAdd.val) p = p at hp
  rw [capPermutation_pow_apply] at hp
  have he : g • p.2 = p.2 := congrArg (fun z : Disc × DeltaBase => z.2) hp
  exact IsCancelSMul.eq_one_of_smul he

/-- The remaining finite quotient is a genuine covering, with its finite action retained. -/
theorem fibreModelProjection_isCoveringMap (j : Kind) :
    IsCoveringMap (fibreModelProjection j) := by
  let := fibreAction j.order (deck j) (deck_pow_order j)
  let := fibreAction_continuous j.order (deck j) (deck_pow_order j)
  let := fibreModelAction_free j
  exact FiniteQuotient.project_isCoveringMap (CyclicGroup j) DeltaBase

/-- The finite covering degree is the original elliptic order. -/
theorem fibreModelProjection_fibre_card (j : Kind) (z : FibreModel j) :
    Nat.card (fibreModelProjection j ⁻¹' {z}) = j.order := by
  let := fibreAction j.order (deck j) (deck_pow_order j)
  let := fibreAction_continuous j.order (deck j) (deck_pow_order j)
  let := fibreModelAction_free j
  have h := FiniteQuotient.fibre_card (CyclicGroup j) DeltaBase z
  exact h.trans (by simp [CyclicGroup])

variable {j : Kind} (D : Equivariant.Data j)

/-- No nonzero original circle parameter fixes any point of the full cap. -/
theorem fullCircleFlow_eq_self_iff (d : Circle)
    (x : D.Space j.twist (mainTwist_admissible j)) :
    fullCircleFlow D d x = x ↔ d = 0 := by
  constructor
  · intro h
    let := D.action j.twist (mainTwist_admissible j).1
    let := capAction j.order (deck j) (deck_pow_order j)
    let := reducedCapAction_free j
    obtain ⟨p, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) x
    rw [fullCircleFlow_quotient] at h
    obtain ⟨g, hg⟩ := (D.quotient_eq_iff_mem_orbit j.twist (mainTwist_admissible j)
      (upstairsCircleFlow D d p) p).mp h
    have he : g • coverDrop D p = coverDrop D p := by
      rw [← coverDrop_action, hg]
      change (p.1, dropDelta (p.2 + deltaCircle d)) = (p.1, dropDelta p.2)
      rw [dropDelta_add_deltaCircle]
    have hg1 : g = 1 := IsCancelSMul.eq_one_of_smul he
    have hp : p = upstairsCircleFlow D d p := by simpa only [hg1, one_smul] using hg
    have hp2 : p.2 + deltaCircle d = p.2 :=
      (congrArg (fun z : D.TotalSpace => z.2) hp).symm
    exact (add_deltaCircle_eq_self_iff p.2 d).mp hp2
  · rintro rfl
    exact fullCircleFlow_zero D x

/-- Exactly the integers, not a rescaled subgroup, are periods of the native real flow. -/
theorem fullRealFlow_eq_self_iff (t : ℝ)
    (x : D.Space j.twist (mainTwist_admissible j)) :
    SpecialPeriods.Threefold.VerticalAction.Elliptic.flow D j.twist
      (mainTwist_admissible j) (t : ℂ) x = x ↔ ∃ n : ℤ, (n : ℝ) = t := by
  rw [← fullCircleFlow_real, fullCircleFlow_eq_self_iff]
  simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ) (x := t))

/-- Restriction to the original small piece does not introduce any circle isotropy. -/
theorem smallCircleFlow_eq_self_iff (j : Kind) (d : Circle)
    (x : Threefold.SpecialEllipticPiece j) :
    smallCircleFlow j d x = x ↔ d = 0 := by
  constructor
  · intro h
    exact (fullCircleFlow_eq_self_iff (EllipticFilling.specialLocalData j) d
      (x.val : EllipticFilling.SpecialFullFilling j)).mp (congrArg Subtype.val h)
  · rintro rfl
    exact smallCircleFlow_zero j x

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit


import Wikipedia.HopfProblem.CuspRetractionPolar
import Wikipedia.HopfProblem.CuspRetractionBasic

/-!
# The actual punctured polar homeomorphism

Off the central fibre, the existing proper polar map has unique positive
and compact-torus factors. Restricting that map to nonzero time gives a
homeomorphism for the inherited subspace topologies, with no radius assumptions.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspRetraction

/-- The actual positive closed tube with the central fibre removed. -/
abbrev PuncturedPositiveTube (η : ℝ) :=
  {q : ClosedPositiveTube η // time (q.1 : Space) ≠ 0}

/-- The actual closed tube with the central fibre removed. -/
abbrev PuncturedClosedTube (η : ℝ) :=
  {x : ClosedTube η // time (x : Space) ≠ 0}

theorem puncturedPolarMap_mem_iff (η : ℝ) (p : CompactTorus × ClosedPositiveTube η) :
    closedPolarMap η p ∈ {x : ClosedTube η | time (x : Space) ≠ 0} ↔
      p.2 ∈ {q : ClosedPositiveTube η | time (q.1 : Space) ≠ 0} := by
  change time (compactTorusAction p.1 (p.2.1 : Space)) ≠ 0 ↔ time (p.2.1 : Space) ≠ 0
  rw [← norm_ne_zero_iff, norm_time_compactTorusAction, norm_ne_zero_iff]

/-- The invariant restriction of the existing closed polar map to nonzero time. -/
def puncturedPolarMap (η : ℝ) :
    CompactTorus × PuncturedPositiveTube η → PuncturedClosedTube η :=
  ProductRestriction.productRestriction (closedPolarMap η)
    {q : ClosedPositiveTube η | time (q.1 : Space) ≠ 0}
    {x : ClosedTube η | time (x : Space) ≠ 0} (puncturedPolarMap_mem_iff η)

@[simp] theorem puncturedPolarMap_closed_coe (η : ℝ)
    (p : CompactTorus × PuncturedPositiveTube η) :
    (puncturedPolarMap η p : ClosedTube η) = closedPolarMap η (p.1, p.2.1) := rfl

@[simp] theorem puncturedPolarMap_coe (η : ℝ)
    (p : CompactTorus × PuncturedPositiveTube η) :
    ((puncturedPolarMap η p : ClosedTube η) : Space) =
      compactTorusAction p.1 (p.2.1.1 : Space) := rfl

@[simp] theorem norm_time_puncturedPolarMap (η : ℝ)
    (p : CompactTorus × PuncturedPositiveTube η) :
    ‖time ((puncturedPolarMap η p).1 : Space)‖ = ‖time (p.2.1.1 : Space)‖ :=
  norm_time_compactTorusAction p.1 (p.2.1.1 : Space)

@[simp] theorem time_puncturedPolarMap (η : ℝ)
    (p : CompactTorus × PuncturedPositiveTube η) :
    time ((puncturedPolarMap η p).1 : Space) =
      (p.1 2 : ℂ) * time (p.2.1.1 : Space) :=
  time_torusAction (compactTorusUnits p.1) (p.2.1.1 : Space)

theorem puncturedPolarMap_continuous (η : ℝ) : Continuous (puncturedPolarMap η) :=
  ProductRestriction.productRestriction_continuous _ _ _ _ (closedPolarMap_continuous η)

theorem puncturedPolarMap_isProperMap (η : ℝ) : IsProperMap (puncturedPolarMap η) :=
  ProductRestriction.productRestriction_isProperMap _ _ _ _ (closedPolarMap_isProperMap η)

theorem puncturedPolarMap_isClosedMap (η : ℝ) : IsClosedMap (puncturedPolarMap η) :=
  ProductRestriction.productRestriction_isClosedMap _ _ _ _ (closedPolarMap_isClosedMap η)

theorem puncturedPolarMap_surjective (η : ℝ) : Function.Surjective (puncturedPolarMap η) :=
  ProductRestriction.productRestriction_surjective _ _ _ _ (closedPolarMap_surjective η)

theorem puncturedPolarMap_injective (η : ℝ) : Function.Injective (puncturedPolarMap η) := by
  rintro ⟨u, q⟩ ⟨v, r⟩ h
  have hclosed : closedPolarMap η (u, q.1) = closedPolarMap η (v, r.1) :=
    congrArg Subtype.val h
  have hqr : q = r := by
    apply Subtype.ext
    simpa only [closedModulusRetraction_closedPolarMap] using
      congrArg (closedModulusRetraction η) hclosed
  subst r
  have huv : u = v := compactTorusAction_injective_of_time_ne_zero q.property
    (congrArg (fun x : ClosedTube η => (x : Space)) hclosed)
  exact Prod.ext huv rfl

theorem puncturedPolarMap_bijective (η : ℝ) : Function.Bijective (puncturedPolarMap η) :=
  ⟨puncturedPolarMap_injective η, puncturedPolarMap_surjective η⟩

/-- Polar factors are unique off the central fibre, with the actual punctured topology. -/
def puncturedPolarHomeomorph (η : ℝ) :
    (CompactTorus × PuncturedPositiveTube η) ≃ₜ PuncturedClosedTube η :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (puncturedPolarMap η) (puncturedPolarMap_bijective η))
    (puncturedPolarMap_continuous η) (puncturedPolarMap_isClosedMap η)

@[simp] theorem puncturedPolarHomeomorph_apply (η : ℝ)
    (p : CompactTorus × PuncturedPositiveTube η) :
    puncturedPolarHomeomorph η p = puncturedPolarMap η p := rfl

@[simp] theorem puncturedPolarHomeomorph_closed_coe (η : ℝ)
    (p : CompactTorus × PuncturedPositiveTube η) :
    (puncturedPolarHomeomorph η p : ClosedTube η) = closedPolarMap η (p.1, p.2.1) := rfl

@[simp] theorem puncturedPolarHomeomorph_coe (η : ℝ)
    (p : CompactTorus × PuncturedPositiveTube η) :
    ((puncturedPolarHomeomorph η p : ClosedTube η) : Space) =
      compactTorusAction p.1 (p.2.1.1 : Space) := rfl

@[simp] theorem puncturedPolarHomeomorph_symm_map (η : ℝ)
    (p : CompactTorus × PuncturedPositiveTube η) :
    (puncturedPolarHomeomorph η).symm (puncturedPolarMap η p) = p :=
  (puncturedPolarHomeomorph η).symm_apply_apply p

@[simp] theorem puncturedPolarMap_symm (η : ℝ) (x : PuncturedClosedTube η) :
    puncturedPolarMap η ((puncturedPolarHomeomorph η).symm x) = x :=
  (puncturedPolarHomeomorph η).apply_symm_apply x

/-- The inverse's positive factor is precisely the existing closed modulus retraction. -/
@[simp] theorem puncturedPolarHomeomorph_symm_positive_coe (η : ℝ)
    (x : PuncturedClosedTube η) :
    ((puncturedPolarHomeomorph η).symm x).2.1 = closedModulusRetraction η x.1 := by
  have h := congrArg (fun y : PuncturedClosedTube η => closedModulusRetraction η y.1)
    (puncturedPolarMap_symm η x)
  simpa only [puncturedPolarMap_closed_coe, closedModulusRetraction_closedPolarMap] using h

end Wikipedia.HopfProblem.CuspControlledRetraction

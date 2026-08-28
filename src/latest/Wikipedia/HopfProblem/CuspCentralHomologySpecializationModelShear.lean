import Wikipedia.HopfProblem.CuspHoneycombCollapse
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelBasic
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelQuotient
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology

/-!
# Removing the frozen phase from the positive-level source action

The phase character below extends the actual frozen deck multiplier from
the integral lattice to the real honeycomb plane.  Dividing by this
character gives a continuous shear which turns the displayed deck action
into pure integral translation.  This is the phase action appropriate to
a positive real level; it does not assert the same formula at a level
with nontrivial complex phase.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspCollapse CuspHoneycomb CuspHoneycombTiling PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The real linear argument of the frozen phase character.  The inverse
quarter-turn converts honeycomb displacement to the deck parameter. -/
def sourcePhaseArgument (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (y : Plane) : Plane :=
  (fun i j => (C₀ i j).re) *ᵥ (-realCuspVector y)

theorem sourcePhaseArgument_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (y z : Plane) :
    sourcePhaseArgument C₀ (y + z) = sourcePhaseArgument C₀ y + sourcePhaseArgument C₀ z := by
  funext i
  simp [sourcePhaseArgument, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    realCuspVector, mul_add, add_comm, add_left_comm, add_assoc]

@[simp] theorem sourcePhaseArgument_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    sourcePhaseArgument C₀ 0 = 0 := by
  funext i
  simp [sourcePhaseArgument, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    realCuspVector]

theorem sourcePhaseArgument_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (sourcePhaseArgument C₀) := by
  unfold sourcePhaseArgument
  simp only [realCuspVector]
  fun_prop

theorem sourcePhaseArgument_lattice_cuspVector
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (i : Fin 2) :
    sourcePhaseArgument C₀ (latticePoint (cuspVector v)) i =
      ((C₀ *ᵥ (fun j => (v j : ℂ))) i).re := by
  simp [sourcePhaseArgument, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    realCuspVector, latticePoint, cuspVector, Complex.mul_re, add_comm]

/-- The actual circle-valued extension of the frozen deck phase. -/
def sourcePhaseCharacter (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (y : Plane) : CompactFibreTorus :=
  fun i => Circle.exp (2 * Real.pi * sourcePhaseArgument C₀ y i)

theorem sourcePhaseCharacter_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (sourcePhaseCharacter C₀) := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp
    (continuous_const.mul ((continuous_apply i).comp (sourcePhaseArgument_continuous C₀)))

@[simp] theorem sourcePhaseCharacter_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    sourcePhaseCharacter C₀ 0 = 1 := by
  funext i
  simp [sourcePhaseCharacter]

theorem sourcePhaseCharacter_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (y z : Plane) :
    sourcePhaseCharacter C₀ (y + z) = sourcePhaseCharacter C₀ y * sourcePhaseCharacter C₀ z := by
  funext i
  simp only [sourcePhaseCharacter, sourcePhaseArgument_add, Pi.add_apply,
    mul_add, Circle.exp_add, Pi.mul_apply]

@[simp] theorem sourcePhaseCharacter_lattice_cuspVector
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    sourcePhaseCharacter C₀ (latticePoint (cuspVector v)) = deckFibrePhase C₀ v := by
  funext i
  rw [sourcePhaseCharacter, sourcePhaseArgument_lattice_cuspVector,
    deckFibrePhase, CuspPositive.frozenPhaseCoordinate_eq_exp]

/-- Exact compatibility with the frozen multiplier, including its phase. -/
theorem sourcePhaseCharacter_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (y : Plane) :
    sourcePhaseCharacter C₀ (y + latticePoint (cuspVector v)) =
      deckFibrePhase C₀ v * sourcePhaseCharacter C₀ y := by
  rw [sourcePhaseCharacter_add, sourcePhaseCharacter_lattice_cuspVector, mul_comm]

/-- The phase shear and its explicit continuous inverse. -/
def sourcePhaseShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : PhasePlane ≃ₜ PhasePlane where
  toFun p := (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹, p.2)
  invFun p := (p.1 * sourcePhaseCharacter C₀ p.2, p.2)
  left_inv p := by simp only [mul_assoc, inv_mul_cancel, mul_one, Prod.eta]
  right_inv p := by simp only [mul_inv_cancel_right, Prod.eta]
  continuous_toFun :=
    (continuous_fst.mul ((sourcePhaseCharacter_continuous C₀).comp continuous_snd).inv).prodMk
      continuous_snd
  continuous_invFun :=
    (continuous_fst.mul ((sourcePhaseCharacter_continuous C₀).comp continuous_snd)).prodMk
      continuous_snd

@[simp] theorem sourcePhaseShear_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p : PhasePlane) :
    sourcePhaseShear C₀ p = (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹, p.2) := rfl

@[simp] theorem sourcePhaseShear_symm_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : PhasePlane) :
    (sourcePhaseShear C₀).symm p = (p.1 * sourcePhaseCharacter C₀ p.2, p.2) := rfl

/-- The actual diagonal deck transformation becomes pure planar
translation after applying the shear. -/
theorem sourcePhaseShear_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (p : PhasePlane) :
    sourcePhaseShear C₀ (honeycombDeckMap C₀ v p) =
      ((sourcePhaseShear C₀ p).1, p.2 + latticePoint (cuspVector v)) := by
  simp only [sourcePhaseShear_apply, honeycombDeckMap, sourcePhaseCharacter_deck]
  apply Prod.ext
  · simp only [mul_inv_rev]
    calc
      (deckFibrePhase C₀ v * p.1) *
          ((sourcePhaseCharacter C₀ p.2)⁻¹ * (deckFibrePhase C₀ v)⁻¹) =
          (deckFibrePhase C₀ v * (deckFibrePhase C₀ v)⁻¹) *
            (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹) := by ac_rfl
      _ = p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹ := by rw [mul_inv_cancel, one_mul]
  · rfl

/-- The inverse quarter-turn fixes the base marking: a deck parameter `v`
is sent to the standard integral vector `v`, not to its quarter-turn. -/
def sourceBaseMarking : Plane ≃ₜ Plane where
  toFun y := -realCuspVector y
  invFun y := realCuspVector y
  left_inv y := by
    funext i
    fin_cases i <;> simp [realCuspVector]
  right_inv y := by
    funext i
    fin_cases i <;> simp [realCuspVector]
  continuous_toFun := by simp only [realCuspVector]; fun_prop
  continuous_invFun := by simp only [realCuspVector]; fun_prop

@[simp] theorem sourceBaseMarking_apply (y : Plane) :
    sourceBaseMarking y = -realCuspVector y := rfl

@[simp] theorem sourceBaseMarking_symm_apply (y : Plane) :
    sourceBaseMarking.symm y = realCuspVector y := rfl

theorem sourceBaseMarking_add (y z : Plane) :
    sourceBaseMarking (y + z) = sourceBaseMarking y + sourceBaseMarking z := by
  simp only [sourceBaseMarking_apply, map_add, neg_add]

@[simp] theorem sourceBaseMarking_lattice_cuspVector (v : Fin 2 → ℤ) :
    sourceBaseMarking (latticePoint (cuspVector v)) = latticePoint v := by
  funext i
  fin_cases i <;> simp [sourceBaseMarking_apply, realCuspVector, latticePoint, cuspVector]

theorem sourceBaseMarking_deck (v : Fin 2 → ℤ) (y : Plane) :
    sourceBaseMarking (y + latticePoint (cuspVector v)) =
      sourceBaseMarking y + latticePoint v := by
  rw [sourceBaseMarking_add, sourceBaseMarking_lattice_cuspVector]

/-- The phase shear followed by the ordered source lattice marking. -/
def sourceMarkedShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : PhasePlane ≃ₜ PhasePlane :=
  (sourcePhaseShear C₀).trans ((Homeomorph.refl CompactFibreTorus).prodCongr sourceBaseMarking)

@[simp] theorem sourceMarkedShear_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p : PhasePlane) :
    sourceMarkedShear C₀ p =
      (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹, sourceBaseMarking p.2) := rfl

@[simp] theorem sourceMarkedShear_symm_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : PhasePlane) :
    (sourceMarkedShear C₀).symm p =
      (p.1 * sourcePhaseCharacter C₀ (realCuspVector p.2), realCuspVector p.2) := rfl

theorem sourceMarkedShear_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (p : PhasePlane) :
    sourceMarkedShear C₀ (honeycombDeckMap C₀ v p) =
      ((sourceMarkedShear C₀ p).1, (sourceMarkedShear C₀ p).2 + latticePoint v) := by
  change ((sourcePhaseShear C₀ (honeycombDeckMap C₀ v p)).1,
      sourceBaseMarking (honeycombDeckMap C₀ v p).2) = _
  rw [sourcePhaseShear_deck]
  change ((sourceMarkedShear C₀ p).1,
      sourceBaseMarking (p.2 + latticePoint (cuspVector v))) = _
  rw [sourceBaseMarking_deck]
  rfl

theorem sourceCoordinateProjection_isOpenQuotientMap :
    IsOpenQuotientMap (coordinateProjection 2) := by
  exact IsOpenQuotientMap.piMap
    (fun _ : Fin 2 => (QuotientAddGroup.isOpenQuotientMap_mk :
      IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ))))

theorem sourceCoordinateProjection_eq_iff (y z : Plane) :
    coordinateProjection 2 y = coordinateProjection 2 z ↔
      ∃ v : Fin 2 → ℤ, y = z + latticePoint v := by
  constructor
  · intro h
    have hz : coordinateProjection 2 (y - z) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨v, hv⟩ := (coordinateProjection_eq_zero_iff 2 _).mp hz
    refine ⟨v, ?_⟩
    change y - z = latticePoint v at hv
    calc
      y = (y - z) + z := (sub_add_cancel y z).symm
      _ = z + latticePoint v := by rw [hv, add_comm]
  · rintro ⟨v, rfl⟩
    have hz : coordinateProjection 2 (latticePoint v) = 0 :=
      (coordinateProjection_eq_zero_iff 2 (latticePoint v)).mpr ⟨v, rfl⟩
    rw [map_add, hz, add_zero]

/-- The source's two compact phase coordinates and its two marked base circles. -/
def sourceProductCoordinates (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    PhasePlane → CompactFibreTorus × ProductTorus 2 :=
  Prod.map id (coordinateProjection 2) ∘ sourceMarkedShear C₀

@[simp] theorem sourceProductCoordinates_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : PhasePlane) :
    sourceProductCoordinates C₀ p =
      (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹,
        coordinateProjection 2 (-realCuspVector p.2)) := rfl

theorem sourceProductCoordinates_isOpenQuotientMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    IsOpenQuotientMap (sourceProductCoordinates C₀) :=
  (IsOpenQuotientMap.id.prodMap sourceCoordinateProjection_isOpenQuotientMap).comp
    (sourceMarkedShear C₀).isOpenQuotientMap

theorem sourceProductCoordinates_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (sourceProductCoordinates C₀) :=
  (sourceProductCoordinates_isOpenQuotientMap C₀).continuous

theorem sourceProductCoordinates_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (sourceProductCoordinates C₀) :=
  (sourceProductCoordinates_isOpenQuotientMap C₀).surjective

theorem sourceProductCoordinates_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (p : PhasePlane) :
    sourceProductCoordinates C₀ (honeycombDeckMap C₀ v p) = sourceProductCoordinates C₀ p := by
  change Prod.map id (coordinateProjection 2) (sourceMarkedShear C₀ (honeycombDeckMap C₀ v p)) = _
  rw [sourceMarkedShear_deck]
  apply Prod.ext
  · rfl
  · change coordinateProjection 2 ((sourceMarkedShear C₀ p).2 + latticePoint v) =
      coordinateProjection 2 (sourceMarkedShear C₀ p).2
    exact (sourceCoordinateProjection_eq_iff _ _).mpr ⟨v, rfl⟩

/-- Equal marked product coordinates are exactly actual deck-equivalent
points; no phase stabilizers are collapsed in the source model. -/
theorem sourceProductCoordinates_eq_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : PhasePlane) :
    sourceProductCoordinates C₀ p = sourceProductCoordinates C₀ q ↔
      ∃ v : Fin 2 → ℤ, honeycombDeckMap C₀ v q = p := by
  constructor
  · intro h
    have hphase : (sourceMarkedShear C₀ p).1 = (sourceMarkedShear C₀ q).1 :=
      congrArg (fun x : CompactFibreTorus × ProductTorus 2 => x.1) h
    have hbase : coordinateProjection 2 (sourceMarkedShear C₀ p).2 =
        coordinateProjection 2 (sourceMarkedShear C₀ q).2 :=
      congrArg (fun x : CompactFibreTorus × ProductTorus 2 => x.2) h
    obtain ⟨v, hv⟩ := (sourceCoordinateProjection_eq_iff _ _).mp hbase
    refine ⟨v, (sourceMarkedShear C₀).injective ?_⟩
    rw [sourceMarkedShear_deck]
    apply Prod.ext
    · exact hphase.symm
    · exact hv.symm
  · rintro ⟨v, hv⟩
    rw [← hv, sourceProductCoordinates_deck]

/-- The marked product coordinates descend to the genuine free deck quotient. -/
def sourceProductMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    SourceModel C₀ → CompactFibreTorus × ProductTorus 2 :=
  Quotient.lift (sourceProductCoordinates C₀) (by
    rintro p q ⟨v, hv⟩
    rw [← hv]
    exact sourceProductCoordinates_deck C₀ v q)

@[simp] theorem sourceProductMap_projection (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : PhasePlane) :
    sourceProductMap C₀ (sourceProjection C₀ p) = sourceProductCoordinates C₀ p := rfl

theorem sourceProductMap_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (sourceProductMap C₀) :=
  (sourceProductCoordinates_continuous C₀).quotient_lift _

theorem sourceProductMap_injective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Injective (sourceProductMap C₀) := by
  intro x y h
  obtain ⟨p, rfl⟩ := sourceProjection_surjective C₀ x
  obtain ⟨q, rfl⟩ := sourceProjection_surjective C₀ y
  exact (sourceProjection_eq_iff C₀ p q).mpr
    ((sourceProductCoordinates_eq_iff C₀ p q).mp h)

theorem sourceProductMap_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (sourceProductMap C₀) := by
  intro x
  obtain ⟨p, hp⟩ := sourceProductCoordinates_surjective C₀ x
  exact ⟨sourceProjection C₀ p, hp⟩

theorem sourceProductMap_isQuotientMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    IsQuotientMap (sourceProductMap C₀) :=
  (sourceProjection_isQuotientMap C₀).of_comp_isQuotientMap
    (sourceProductCoordinates_isOpenQuotientMap C₀).isQuotientMap

/-- The actual source deck quotient is the product of its two compact
phase circles and its two marked additive base circles, with the given
quotient and product topologies. -/
def sourceProductHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    SourceModel C₀ ≃ₜ CompactFibreTorus × ProductTorus 2 :=
  (Equiv.ofBijective (sourceProductMap C₀)
    ⟨sourceProductMap_injective C₀, sourceProductMap_surjective C₀⟩).toHomeomorph
      (fun _ => (sourceProductMap_isQuotientMap C₀).isOpen_preimage)

@[simp] theorem sourceProductHomeomorph_projection
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p : PhasePlane) :
    sourceProductHomeomorph C₀ (sourceProjection C₀ p) =
      (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹,
        coordinateProjection 2 (-realCuspVector p.2)) := rfl

/-- A concrete representative of the inverse coordinate map; its base is
the quarter-turn of the marked real coordinates. -/
theorem sourceProductHomeomorph_symm_coordinateProjection
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (u : CompactFibreTorus) (y : Plane) :
    (sourceProductHomeomorph C₀).symm (u, coordinateProjection 2 y) =
      sourceProjection C₀
        (u * sourcePhaseCharacter C₀ (realCuspVector y), realCuspVector y) := by
  apply (sourceProductHomeomorph C₀).injective
  rw [Homeomorph.apply_symm_apply]
  change (u, coordinateProjection 2 y) =
    sourceProductCoordinates C₀ ((sourceMarkedShear C₀).symm (u, y))
  unfold sourceProductCoordinates
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  rfl

/-- The genuine source quotient is compact because its marked product
coordinates are actual circles. -/
theorem sourceModel_compactSpace (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CompactSpace (SourceModel C₀) := (sourceProductHomeomorph C₀).symm.compactSpace

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitReduced

/-!
# Product coordinates on the actual full-cap circle orbit space

The primitive signed gamma coordinate untwists the genuine projected
finite action.  The resulting factor is still its finite affine quotient,
not an unmarked torus.  The disc coordinate is exactly that of the already
proved original full-cap product homeomorphism.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

open Elliptic SpecialPeriods EllipticModel EllipticOrbitFlat
open EllipticGamma EllipticFullProduct

local notation "Circle" => AddCircle (1 : ℝ)

/-- The original normalized gamma coordinate, now on its actual three-circle quotient. -/
def modelGamma (j : Kind) : C(DeltaBase, Circle) :=
  ⟨fun z => j.twist 0 • z 0, (continuous_apply (0 : Fin 3)).const_smul (j.twist 0)⟩

@[simp] theorem modelGamma_dropDelta (j : Kind) (x : RealTorus₄) :
    modelGamma j (dropDelta x) = normalizedGamma j x := rfl

/-- The surviving affine generator shifts normalized gamma by precisely one sector. -/
theorem modelGamma_deck (j : Kind) (z : DeltaBase) :
    modelGamma j (deck j z) = modelGamma j z + sector j.order := by
  obtain ⟨x, rfl⟩ := dropDelta_surjective z
  rw [← dropDelta_deck, modelGamma_dropDelta, modelGamma_dropDelta]
  exact normalizedGamma_sector j x

variable {j : Kind} (D : Equivariant.Data j)

/-- The original circle-orbit cap is a disc times its genuine residual finite quotient. -/
def fullOrbitHomeomorph : FullOrbit D ≃ₜ Disc × FibreModel j :=
  (fullOrbitReducedHomeomorph D).trans
    (capProductHomeomorph j.order (deck j) (deck_pow_order j)
      (modelGamma j) (modelGamma_deck j))

/-- The exact root-and-original-period representative formula. -/
@[simp] theorem fullOrbitHomeomorph_quotient (s : Disc) (x : RealTorus₄) :
    fullOrbitHomeomorph D
      (fullOrbitProjection D (D.quotient j.twist (mainTwist_admissible j) (s, x))) =
        (rotate (normalizedGamma j x) s, fibreModelProjection j (dropDelta x)) := by
  change capProductHomeomorph j.order (deck j) (deck_pow_order j)
    (modelGamma j) (modelGamma_deck j)
    (fullOrbitReducedHomeomorph D
      (fullOrbitProjection D (D.quotient j.twist (mainTwist_admissible j) (s, x)))) = _
  rw [fullOrbitReducedHomeomorph_quotient]
  exact capProductHomeomorph_project j.order (deck j) (deck_pow_order j)
    (modelGamma j) (modelGamma_deck j) (s, dropDelta x)

/-- The inverse returns a literal original cap representative, with its original phase. -/
theorem fullOrbitHomeomorph_symm_project (s : Disc) (x : RealTorus₄) :
    (fullOrbitHomeomorph D).symm (s, fibreModelProjection j (dropDelta x)) =
      fullOrbitProjection D (D.quotient j.twist (mainTwist_admissible j)
        (rotate (-normalizedGamma j x) s, x)) := by
  apply (fullOrbitHomeomorph D).injective
  rw [Homeomorph.apply_symm_apply, fullOrbitHomeomorph_quotient, rotate_rotate_neg]

/-- The original full-cap quotient map, expressed in the proved product coordinates. -/
def fullOrbitMap : C(D.Space j.twist (mainTwist_admissible j), Disc × FibreModel j) :=
  ⟨fun x => fullOrbitHomeomorph D (fullOrbitProjection D x),
    (fullOrbitHomeomorph D).continuous.comp
      (fullOrbitProjection_isOpenQuotientMap D).continuous⟩

@[simp] theorem fullOrbitMap_apply (x : D.Space j.twist (mainTwist_admissible j)) :
    fullOrbitMap D x = fullOrbitHomeomorph D (fullOrbitProjection D x) := rfl

@[simp] theorem fullOrbitMap_quotient (s : Disc) (x : RealTorus₄) :
    fullOrbitMap D (D.quotient j.twist (mainTwist_admissible j) (s, x)) =
      (rotate (normalizedGamma j x) s, fibreModelProjection j (dropDelta x)) :=
  fullOrbitHomeomorph_quotient D s x

theorem fullOrbitMap_isOpenQuotientMap : IsOpenQuotientMap (fullOrbitMap D) :=
  (fullOrbitHomeomorph D).isOpenQuotientMap.comp (fullOrbitProjection_isOpenQuotientMap D)

theorem fullOrbitMap_eq_iff (x y : D.Space j.twist (mainTwist_admissible j)) :
    fullOrbitMap D x = fullOrbitMap D y ↔ ∃ d : Circle, fullCircleFlow D d y = x :=
  (fullOrbitHomeomorph D).injective.eq_iff.trans (fullOrbitProjection_eq_iff D x y)

/-- The quotient disc coordinate is the unchanged original full-product coordinate. -/
theorem fullOrbitMap_fst (x : D.Space j.twist (mainTwist_admissible j)) :
    (fullOrbitMap D x).1 = (fillingProductHomeomorph D x).1 := by
  obtain ⟨⟨s, y⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) x
  rw [fullOrbitMap_quotient, fillingProductHomeomorph_quotient]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit


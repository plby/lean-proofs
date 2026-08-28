import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticCapMap
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticFullProduct

/-!
# Unconditional Seifert maps on the actual special elliptic pieces

The original globally constructed periods and the two actual main twists
instantiate the finite quotient and its disc-circle coordinates.  The
small-piece map is a literal restriction to the exact radius used in the
threefold gluing.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSpecial

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling SpecialPeriods.Threefold
open EllipticModel EllipticCapMap EllipticGamma

abbrev SpecialSolidQuotient (j : Kind) := SolidQuotient j.order (j.twist 0)

/-- The genuine Seifert finite quotient of the actual full special-period cap. -/
def specialCapCoinvariantMap (j : Kind) : C(SpecialFullFilling j, SpecialSolidQuotient j) :=
  capCoinvariantMap (specialLocalData j) j.twist (mainTwist_admissible j)

/-- The actual full cap mapped to the native solid-torus product coordinates. -/
def specialCapSolidTorusMap (j : Kind) : C(SpecialFullFilling j, Disc × EllipticModel.Circle) :=
  capSolidTorusMap (specialLocalData j) j.twist (mainTwist_admissible j)
    (twist_gamma_eq_one_or_neg_one j)

theorem specialCapSolidTorusMap_isOpenQuotientMap (j : Kind) :
    IsOpenQuotientMap (specialCapSolidTorusMap j) :=
  capSolidTorusMap_isOpenQuotientMap (specialLocalData j) j.twist
    (mainTwist_admissible j) (twist_gamma_eq_one_or_neg_one j)

@[simp] theorem specialCapSolidTorusMap_quotient (j : Kind) (s : Disc) (x : RealTorus₄) :
    specialCapSolidTorusMap j
      ((specialLocalData j).quotient j.twist (mainTwist_admissible j) (s, x)) =
      (rotate (normalizedGamma j x) s,
        j.order • TrianglePeriodFamily.GammaZero.fibreGamma x) :=
  capSolidTorusMap_quotient (specialLocalData j) j.twist
    (mainTwist_admissible j) (twist_gamma_eq_one_or_neg_one j) s x

theorem specialCapSolidTorusMap_projection (j : Kind) (q : SpecialFullFilling j) :
    solidBase j.order (j.twist 0) (specialCapSolidTorusMap j q) =
      specialFullFillingProjection j q :=
  capSolidTorusMap_projection (specialLocalData j) j.twist
    (mainTwist_admissible j) (twist_gamma_eq_one_or_neg_one j) q

/-- The original delta flow is invisible to the complete Seifert quotient, not only to its base. -/
theorem specialCapSolidTorusMap_flow_real (j : Kind) (t : ℝ) (q : SpecialFullFilling j) :
    specialCapSolidTorusMap j
      (VerticalAction.Elliptic.flow (specialLocalData j) j.twist (mainTwist_admissible j)
        (t : ℂ) q) = specialCapSolidTorusMap j q :=
  capSolidTorusMap_flow_real (specialLocalData j) j.twist
    (mainTwist_admissible j) (twist_gamma_eq_one_or_neg_one j) t q

theorem specialCapSolidTorusMap_norm (j : Kind) (q : SpecialFullFilling j) :
    ‖((specialCapSolidTorusMap j q).1 : ℂ)‖ ^ j.order =
      ‖(specialFullFillingProjection j q : ℂ)‖ :=
  capSolidTorusMap_norm (specialLocalData j) j.twist
    (mainTwist_admissible j) (twist_gamma_eq_one_or_neg_one j) q

/-- The exact radius restriction in the product solid torus. -/
abbrev SmallSolidTorus (j : Kind) :=
  {p : Disc × EllipticModel.Circle //
    ‖(p.1 : ℂ)‖ ^ j.order < specialBaseCover.radius (some j)}

/-- The Seifert map on the literal small piece used in the global threefold. -/
def specialPieceSolidTorusMap (j : Kind) : C(SpecialEllipticPiece j, SmallSolidTorus j) :=
  ⟨fun q => ⟨specialCapSolidTorusMap j q.val, by
    rw [specialCapSolidTorusMap_norm]
    exact q.property⟩,
    ((specialCapSolidTorusMap j).continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem specialPieceSolidTorusMap_val (j : Kind) (q : SpecialEllipticPiece j) :
    (specialPieceSolidTorusMap j q).val = specialCapSolidTorusMap j q.val := rfl

theorem specialPieceSolidTorusMap_surjective (j : Kind) :
    Function.Surjective (specialPieceSolidTorusMap j) := by
  intro p
  obtain ⟨q, hq⟩ := (specialCapSolidTorusMap_isOpenQuotientMap j).surjective p.val
  have hmem : ‖(specialFullFillingProjection j q : ℂ)‖ < specialBaseCover.radius (some j) := by
    rw [← specialCapSolidTorusMap_norm, hq]
    exact p.property
  exact ⟨⟨q, hmem⟩, Subtype.ext hq⟩

private def piecePreimageHomeomorph (j : Kind) :
    SpecialEllipticPiece j ≃ₜ
      (specialCapSolidTorusMap j ⁻¹' {p : Disc × EllipticModel.Circle |
        ‖(p.1 : ℂ)‖ ^ j.order < specialBaseCover.radius (some j)}) :=
  Homeomorph.setCongr (by
    ext q
    change (‖(specialFullFillingProjection j q : ℂ)‖ < specialBaseCover.radius (some j)) ↔
      ‖((specialCapSolidTorusMap j q).1 : ℂ)‖ ^ j.order < specialBaseCover.radius (some j)
    rw [specialCapSolidTorusMap_norm])

/-- Restriction to the actual small cap still gives an open quotient onto its exact solid torus. -/
theorem specialPieceSolidTorusMap_isOpenQuotientMap (j : Kind) :
    IsOpenQuotientMap (specialPieceSolidTorusMap j) := by
  let S : Set (Disc × EllipticModel.Circle) :=
    {p | ‖(p.1 : ℂ)‖ ^ j.order < specialBaseCover.radius (some j)}
  have h := (specialCapSolidTorusMap_isOpenQuotientMap j).restrictPreimage S
  let e := piecePreimageHomeomorph j
  exact ⟨h.surjective.comp e.surjective, h.continuous.comp e.continuous,
    h.isOpenMap.comp e.isOpenMap⟩

/-- The actual small-piece projection retains the same original power-phase formula. -/
theorem specialPieceSolidTorusMap_projection (j : Kind) (q : SpecialEllipticPiece j) :
    solidBase j.order (j.twist 0) (specialPieceSolidTorusMap j q).val =
      specialFullFillingProjection j q.val :=
  specialCapSolidTorusMap_projection j q.val

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSpecial

import Wikipedia.HopfProblem.EllipticFundamentalGroupPresentation
import Wikipedia.HopfProblem.EllipticFundamentalGroupExtension

/-!
# The exact cyclic extensions of the actual surface and filling loop groups

The lattice injection, affine residue map, and exactness are transported
along the proved universal-cover isomorphisms. Thus the sequence used in
the proof of Theorem 5.4(iii) is a sequence of the actual fundamental
groups, with the marked generators from the presentation theorem.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

/-- The affine residue character of the actual surface fundamental group. -/
def surfaceFundamentalGroupResidue (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y) →*
      CyclicGroup j :=
  (deckResidue j v hv).comp (surfaceFundamentalGroupDeckEquiv j p v hv y).toMonoidHom

@[simp] theorem surfaceFundamentalGroupResidue_translation
    (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) (w : Multiplicative Lattice) :
    surfaceFundamentalGroupResidue j p v hv y (surfaceTranslationHom j p v hv y w) = 1 := by
  change deckResidue j v hv (surfaceFundamentalGroupDeckEquiv j p v hv y
    (surfaceTranslationHom j p v hv y w)) = 1
  rw [surfaceFundamentalGroupDeckEquiv_translation, deckResidue_translation]

@[simp] theorem surfaceFundamentalGroupResidue_generator
    (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :
    surfaceFundamentalGroupResidue j p v hv y (surfaceAffineGenerator j p v hv y) =
      Multiplicative.ofAdd (1 : ZMod j.order) := by
  change deckResidue j v hv (surfaceFundamentalGroupDeckEquiv j p v hv y
    (surfaceAffineGenerator j p v hv y)) = _
  rw [surfaceFundamentalGroupDeckEquiv_generator, deckResidue_generator]

theorem surfaceFundamentalGroupResidue_ker (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    (surfaceFundamentalGroupResidue j p v hv y).ker =
      (surfaceTranslationHom j p v hv y).range := by
  ext γ
  change deckResidue j v hv (surfaceFundamentalGroupDeckEquiv j p v hv y γ) = 1 ↔ _
  rw [deckResidue_eq_one_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, (surfaceFundamentalGroupDeckEquiv j p v hv y).injective ?_⟩
    exact (surfaceFundamentalGroupDeckEquiv_translation j p v hv y w).trans hw
  · rintro ⟨w, rfl⟩
    exact ⟨w, (surfaceFundamentalGroupDeckEquiv_translation j p v hv y w).symm⟩

/-- The actual surface group fits into `1 → Λ → π₁(S) → ℤ/m → 1`. -/
theorem surfaceFundamentalGroup_exactSequence (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Function.Injective (surfaceTranslationHom j p v hv y) ∧
      (surfaceFundamentalGroupResidue j p v hv y).ker =
        (surfaceTranslationHom j p v hv y).range ∧
      Function.Surjective (surfaceFundamentalGroupResidue j p v hv y) :=
  ⟨surfaceTranslationHom_injective j p v hv y, surfaceFundamentalGroupResidue_ker j p v hv y,
    (deckResidue_surjective j v hv).comp
      (surfaceFundamentalGroupDeckEquiv j p v hv y).surjective⟩

/-- The affine residue character of the actual filling fundamental group. -/
def fillingFundamentalGroupResidue (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FundamentalGroup (Filling j v hv)
        (centralFibreInclusion j v hv (affineCoverProjection j (centralPeriod j) v hv y)) →*
      CyclicGroup j :=
  (deckResidue j v hv).comp (fillingFundamentalGroupDeckEquiv j v hv y).toMonoidHom

@[simp] theorem fillingFundamentalGroupResidue_translation (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) (w : Multiplicative Lattice) :
    fillingFundamentalGroupResidue j v hv y (fillingTranslationHom j v hv y w) = 1 := by
  change deckResidue j v hv (fillingFundamentalGroupDeckEquiv j v hv y
    (fillingTranslationHom j v hv y w)) = 1
  rw [fillingFundamentalGroupDeckEquiv_translation, deckResidue_translation]

@[simp] theorem fillingFundamentalGroupResidue_generator (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    fillingFundamentalGroupResidue j v hv y (fillingAffineGenerator j v hv y) =
      Multiplicative.ofAdd (1 : ZMod j.order) := by
  change deckResidue j v hv (fillingFundamentalGroupDeckEquiv j v hv y
    (fillingAffineGenerator j v hv y)) = _
  rw [fillingFundamentalGroupDeckEquiv_generator, deckResidue_generator]

theorem fillingFundamentalGroupResidue_ker (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    (fillingFundamentalGroupResidue j v hv y).ker =
      (fillingTranslationHom j v hv y).range := by
  ext γ
  change deckResidue j v hv (fillingFundamentalGroupDeckEquiv j v hv y γ) = 1 ↔ _
  rw [deckResidue_eq_one_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, (fillingFundamentalGroupDeckEquiv j v hv y).injective ?_⟩
    exact (fillingFundamentalGroupDeckEquiv_translation j v hv y w).trans hw
  · rintro ⟨w, rfl⟩
    exact ⟨w, (fillingFundamentalGroupDeckEquiv_translation j v hv y w).symm⟩

/-- The actual filling group fits into `1 → Λ → π₁(U) → ℤ/m → 1`. -/
theorem fillingFundamentalGroup_exactSequence (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Function.Injective (fillingTranslationHom j v hv y) ∧
      (fillingFundamentalGroupResidue j v hv y).ker =
        (fillingTranslationHom j v hv y).range ∧
      Function.Surjective (fillingFundamentalGroupResidue j v hv y) :=
  ⟨fillingTranslationHom_injective j v hv y, fillingFundamentalGroupResidue_ker j v hv y,
    (deckResidue_surjective j v hv).comp (fillingFundamentalGroupDeckEquiv j v hv y).surjective⟩

end Wikipedia.HopfProblem.Elliptic

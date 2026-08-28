import Wikipedia.HopfProblem.EllipticFundamentalGroupPresentation

/-!
# Deck markings of actual paths in the elliptic affine cover

Projection of a path from `y` to `g • y` gives an actual surface loop.
Its value under the constructed fundamental-group equivalence is `g⁻¹`:
this sign is forced by the left deck action and the monodromy convention.
The proof uses uniqueness of path lifting, rather than an assumed marking.
We specialize this calculation to the affine generator and to straight
lattice-translation paths, as needed by the logarithmic attaching map.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.Elliptic

variable (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)

/-- Every actual affine deck transformation preserves the surface projection. -/
theorem affineCoverProjection_deck (y : RealCoordinates) (g : AffineDeckGroup j v) :
    affineCoverProjection j p v hv (g • y) = affineCoverProjection j p v hv y :=
  (affineCoverProjection_orbit_iff j p v hv _ _).mpr ⟨g, rfl⟩

/-- The projection of a path to a deck translate, with its endpoint cast
using the actual equality of projections. -/
def affineDeckPathLoop (y : RealCoordinates) (g : AffineDeckGroup j v)
    (q : Path y (g • y)) :
    Path (affineCoverProjection j p v hv y) (affineCoverProjection j p v hv y) :=
  (q.map (affineCoverProjection_continuous j p v hv)).cast rfl
    (affineCoverProjection_deck j p v hv y g).symm

@[simp] theorem affineDeckPathLoop_apply (y : RealCoordinates) (g : AffineDeckGroup j v)
    (q : Path y (g • y)) (t : unitInterval) :
    affineDeckPathLoop j p v hv y g q t = affineCoverProjection j p v hv (q t) := rfl

/-- The endpoint of the lifted projected loop is the specified deck translate. -/
theorem affineDeckPathLoop_monodromy (y : RealCoordinates) (g : AffineDeckGroup j v)
    (q : Path y (g • y)) :
    (affineCoverProjection_isQuotientCoveringMap j p v hv).isCoveringMap.monodromy
      (FundamentalGroup.fromPath ⟦affineDeckPathLoop j p v hv y g q⟧) ⟨y, rfl⟩ =
        ⟨g • y, affineCoverProjection_deck j p v hv y g⟩ := by
  let hq := affineCoverProjection_isQuotientCoveringMap j p v hv
  apply hq.isCoveringMap.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk q)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- The native fundamental-group marking of an actual lifted path.
Inversion is not a choice: it comes from the left-acting deck group. -/
theorem surfaceFundamentalGroupDeckEquiv_affineDeckPathLoop (y : RealCoordinates)
    (g : AffineDeckGroup j v) (q : Path y (g • y)) :
    surfaceFundamentalGroupDeckEquiv j p v hv y
      (FundamentalGroup.fromPath ⟦affineDeckPathLoop j p v hv y g q⟧) = g⁻¹ := by
  apply inv_injective
  rw [inv_inv]
  apply affineDeckGroup_eval_injective j v hv y
  exact (surfaceFundamentalGroupDeckEquiv_monodromy j p v hv y _).trans
    (congrArg Subtype.val (affineDeckPathLoop_monodromy j p v hv y g q))

/-- A pointwise projection equation suffices to compute the marking of
an independently constructed loop. No chosen representative is assumed. -/
theorem surfaceFundamentalGroupDeckEquiv_of_path_lift (y : RealCoordinates)
    (g : AffineDeckGroup j v)
    (γ : Path (affineCoverProjection j p v hv y) (affineCoverProjection j p v hv y))
    (q : Path y (g • y))
    (hγ : ∀ t, affineCoverProjection j p v hv (q t) = γ t) :
    surfaceFundamentalGroupDeckEquiv j p v hv y (FundamentalGroup.fromPath ⟦γ⟧) =
      g⁻¹ := by
  have heq : γ = affineDeckPathLoop j p v hv y g q := by
    ext t
    exact (hγ t).symm
  rw [heq]
  exact surfaceFundamentalGroupDeckEquiv_affineDeckPathLoop j p v hv y g q

/-- Endpoint-equality version for a path whose target has another expression. -/
theorem surfaceFundamentalGroupDeckEquiv_of_path_endpoint (y z : RealCoordinates)
    (g : AffineDeckGroup j v) (hz : z = g • y)
    (γ : Path (affineCoverProjection j p v hv y) (affineCoverProjection j p v hv y))
    (q : Path y z)
    (hγ : ∀ t, affineCoverProjection j p v hv (q t) = γ t) :
    surfaceFundamentalGroupDeckEquiv j p v hv y (FundamentalGroup.fromPath ⟦γ⟧) =
      g⁻¹ :=
  surfaceFundamentalGroupDeckEquiv_of_path_lift j p v hv y g γ
    (q.cast rfl hz.symm) hγ

/-- The affine lift of the elliptic generator has the expected actual
projected loop, independently of the path used to reach it. -/
def affineGeneratorPathLoop (y : RealCoordinates) (q : Path y (flatAffine j v y)) :
    Path (affineCoverProjection j p v hv y) (affineCoverProjection j p v hv y) :=
  affineDeckPathLoop j p v hv y (deckGenerator j v) q

@[simp] theorem affineGeneratorPathLoop_apply (y : RealCoordinates)
    (q : Path y (flatAffine j v y)) (t : unitInterval) :
    affineGeneratorPathLoop j p v hv y q t = affineCoverProjection j p v hv (q t) := rfl

theorem surfaceFundamentalGroupDeckEquiv_affineGeneratorPathLoop (y : RealCoordinates)
    (q : Path y (flatAffine j v y)) :
    surfaceFundamentalGroupDeckEquiv j p v hv y
      (FundamentalGroup.fromPath ⟦affineGeneratorPathLoop j p v hv y q⟧) =
        (deckGenerator j v)⁻¹ :=
  surfaceFundamentalGroupDeckEquiv_affineDeckPathLoop j p v hv y (deckGenerator j v) q

theorem affineGeneratorPathLoop_eq_marked_inverse (y : RealCoordinates)
    (q : Path y (flatAffine j v y)) :
    FundamentalGroup.fromPath ⟦affineGeneratorPathLoop j p v hv y q⟧ =
      (surfaceAffineGenerator j p v hv y)⁻¹ := by
  apply (surfaceFundamentalGroupDeckEquiv j p v hv y).injective
  rw [surfaceFundamentalGroupDeckEquiv_affineGeneratorPathLoop, map_inv,
    surfaceFundamentalGroupDeckEquiv_generator]

/-- The straight segment realizes positive translation by `w` on the real cover. -/
def affineTranslationPath (y : RealCoordinates) (w : Lattice) :
    Path y (y + realCast w) := Path.segment y (y + realCast w)

theorem affineTranslationPath_apply (y : RealCoordinates) (w : Lattice)
    (t : unitInterval) :
    affineTranslationPath y w t = y + (t : ℝ) • realCast w := by
  change AffineMap.lineMap y (y + realCast w) (t : ℝ) = _
  rw [AffineMap.lineMap_apply_module]
  module

theorem deckTranslationHom_smul (y : RealCoordinates) (w : Lattice) :
    deckTranslationHom j v (Multiplicative.ofAdd w) • y = y + realCast w :=
  add_comm _ _

/-- The actual loop projecting the straight positive lattice translation. -/
def affineTranslationLoop (y : RealCoordinates) (w : Lattice) :
    Path (affineCoverProjection j p v hv y) (affineCoverProjection j p v hv y) :=
  affineDeckPathLoop j p v hv y (deckTranslationHom j v (Multiplicative.ofAdd w))
    ((affineTranslationPath y w).cast rfl (deckTranslationHom_smul j v y w))

@[simp] theorem affineTranslationLoop_apply (y : RealCoordinates) (w : Lattice)
    (t : unitInterval) :
    affineTranslationLoop j p v hv y w t =
      affineCoverProjection j p v hv (y + (t : ℝ) • realCast w) := by
  change affineCoverProjection j p v hv (affineTranslationPath y w t) = _
  rw [affineTranslationPath_apply]

/-- Positive translation of the lifted path has negative marked translation. -/
theorem surfaceFundamentalGroupDeckEquiv_affineTranslationLoop (y : RealCoordinates)
    (w : Lattice) :
    surfaceFundamentalGroupDeckEquiv j p v hv y
      (FundamentalGroup.fromPath ⟦affineTranslationLoop j p v hv y w⟧) =
        deckTranslationHom j v (Multiplicative.ofAdd (-w)) := by
  change surfaceFundamentalGroupDeckEquiv j p v hv y
    (FundamentalGroup.fromPath ⟦affineDeckPathLoop j p v hv y _ _⟧) = _
  rw [surfaceFundamentalGroupDeckEquiv_affineDeckPathLoop]
  exact (map_inv (deckTranslationHom j v) (Multiplicative.ofAdd w)).symm

theorem affineTranslationLoop_eq_marked (y : RealCoordinates) (w : Lattice) :
    FundamentalGroup.fromPath ⟦affineTranslationLoop j p v hv y w⟧ =
      surfaceTranslationHom j p v hv y (Multiplicative.ofAdd (-w)) := by
  apply (surfaceFundamentalGroupDeckEquiv j p v hv y).injective
  rw [surfaceFundamentalGroupDeckEquiv_affineTranslationLoop,
    surfaceFundamentalGroupDeckEquiv_translation]

end Wikipedia.HopfProblem.Elliptic

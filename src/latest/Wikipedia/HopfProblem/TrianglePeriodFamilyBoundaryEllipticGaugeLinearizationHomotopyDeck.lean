import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationHomotopyCore

/-!
# Exact real gauge recurrence implies full mapping-torus deck equivariance

The forward recurrence gives the one-period identity for the actual
torus fibre map.  Integer induction, including negative deck shifts,
then gives the complete equivariance required by the original quotient.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

open Elliptic MappingTorus SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

/-- The complete torus fibre coordinate of a continuous real gauge. -/
def gaugeFibreCylinder (a : C(ℝ, RealCoordinates)) : C(ℝ × RealTorus₄, RealTorus₄) :=
  ⟨fun p => p.2 + standardLattice.mkQ (a p.1),
    continuous_snd.add (standardLattice.continuous_mkQ.comp
      (a.continuous.comp continuous_fst))⟩

@[simp] theorem gaugeFibreCylinder_apply (a : C(ℝ, RealCoordinates))
    (t : ℝ) (x : RealTorus₄) :
    gaugeFibreCylinder a (t, x) = x + standardLattice.mkQ (a t) := rfl

/-- The actual affine elliptic map is the triangle action plus its specified translation. -/
theorem flatTorusAffine_apply_eq_triangle_add (j : Kind) (v : Lattice) (x : RealTorus₄) :
    flatTorusAffine j v x =
      ellipticGenerator j • x + standardLattice.mkQ ((1 / (j.order : ℝ)) • realCast v) :=
  congrArg (fun f : C(RealTorus₄, RealTorus₄) => f x)
    (flatTorusAffine_eq_translation_triangle j v)

/-- The real recurrence is exactly the required one-period fibre identity. -/
theorem gaugeFibreCylinder_forward (j : Kind) (v : Lattice)
    (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (t : ℝ) (x : RealTorus₄) :
    ellipticGenerator j • gaugeFibreCylinder a (t + 1, x) =
      gaugeFibreCylinder a (t, flatTorusAffine j v x) := by
  change triangleTorusHomeomorph (ellipticGenerator j)
    (x + standardLattice.mkQ (a (t + 1))) =
      flatTorusAffine j v x + standardLattice.mkQ (a t)
  rw [triangleTorusHomeomorph_add, ellipticTriangle_mkQ, ha, map_add,
    flatTorusAffine_apply_eq_triangle_add]
  change triangleTorusHomeomorph (ellipticGenerator j) x +
    (standardLattice.mkQ (a t) + standardLattice.mkQ ((1 / (j.order : ℝ)) • realCast v)) =
      (triangleTorusHomeomorph (ellipticGenerator j) x +
        standardLattice.mkQ ((1 / (j.order : ℝ)) • realCast v)) +
          standardLattice.mkQ (a t)
  abel

/-- Equivariance for the actual unit deck transformation, with its inverse affine fibre map. -/
theorem gaugeFibreCylinder_deck_one (j : Kind) (v : Lattice)
    (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (p : ℝ × RealTorus₄) :
    gaugeFibreCylinder a (deck (flatTorusAffine j v) 1 p) =
      (ellipticGenerator j)⁻¹ • gaugeFibreCylinder a p := by
  apply (triangleTorusHomeomorph (ellipticGenerator j)).injective
  change ellipticGenerator j • gaugeFibreCylinder a (deck (flatTorusAffine j v) 1 p) =
    ellipticGenerator j • ((ellipticGenerator j)⁻¹ • gaugeFibreCylinder a p)
  rw [smul_inv_smul]
  simp only [deck, Int.cast_one, zpow_neg_one]
  change ellipticGenerator j •
    gaugeFibreCylinder a (p.1 + 1, (flatTorusAffine j v).symm p.2) = gaugeFibreCylinder a p
  rw [gaugeFibreCylinder_forward j v a ha, Homeomorph.apply_symm_apply]

/-- A one-deck equivariance identity propagates to every positive and negative integer. -/
theorem fibreDeck_of_one (φ : RealTorus₄ ≃ₜ RealTorus₄)
    (F : ℝ × RealTorus₄ → RealTorus₄) (g : TriangleGroup)
    (hF : ∀ p, F (deck φ 1 p) = g⁻¹ • F p) (k : ℤ) (p : ℝ × RealTorus₄) :
    F (deck φ k p) = (g ^ (-k)) • F p := by
  have hprev (q : ℝ × RealTorus₄) : F (deck φ (-1) q) = g • F q := by
    have h := congrArg (fun y : RealTorus₄ => g • y) (hF (deck φ (-1) q))
    simpa only [← deck_add, add_neg_cancel, deck_zero, smul_inv_smul] using h.symm
  have hall : ∀ k : ℤ, ∀ p : ℝ × RealTorus₄, F (deck φ k p) = (g ^ (-k)) • F p := by
    intro k
    induction k using Int.induction_on with
    | zero => intro p; simp only [deck_zero, neg_zero, zpow_zero, one_smul]
    | succ k ih =>
      intro p
      rw [deck_add, ih, hF, neg_add, zpow_add, zpow_neg_one, mul_smul]
    | pred k ih =>
      intro p
      rw [sub_eq_add_neg, deck_add, ih, hprev]
      simp only [neg_add, neg_neg, zpow_add, zpow_one, mul_smul]
  exact hall k p

/-- The complete original gauge respects the defining integer deck relation. -/
theorem gaugeFibreCylinder_deck (j : Kind) (v : Lattice)
    (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (k : ℤ) (p : ℝ × RealTorus₄) :
    gaugeFibreCylinder a (deck (flatTorusAffine j v) k p) =
      (ellipticGenerator j ^ (-k)) • gaugeFibreCylinder a p :=
  fibreDeck_of_one (flatTorusAffine j v) (gaugeFibreCylinder a) (ellipticGenerator j)
    (gaugeFibreCylinder_deck_one j v a ha) k p

/-- Every interpolation slice has the same full integer equivariance. -/
theorem interpolatedGaugeFibreCylinder_deck (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (s : unitInterval) (k : ℤ) (p : ℝ × RealTorus₄) :
    gaugeFibreCylinder (gaugeInterpolationSlice j v a s) (deck (flatTorusAffine j v) k p) =
      (ellipticGenerator j ^ (-k)) • gaugeFibreCylinder (gaugeInterpolationSlice j v a s) p :=
  gaugeFibreCylinder_deck j v (gaugeInterpolationSlice j v a s)
    (gaugeInterpolation_forward j v hv a ha s) k p

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

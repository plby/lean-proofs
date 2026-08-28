import Wikipedia.HopfProblem.CuspComplementOuterBoundaryHeight
import Wikipedia.HopfProblem.CuspBoundaryToricExtensionComparison

/-!
# The full original cusp mapping torus is the actual positive-radius level

The forward map is the existing boundary inclusion at the logarithmic
height of the specified radius. Its inverse is the mapping-torus
coordinate of the original punctured-product homeomorphism. Both maps
use the genuine quotient topology and retain all four period coordinates.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspComplement.OuterBoundary

open SpecialPeriods.CuspFamily ThreefoldOverlapMappingTorus.Cusp
open ThreefoldHomologyFinitenessCusp CuspUniformization

/-- A literal positive-radius level of the unchanged cusp quotient parameter. -/
abbrev LocalLevel (D : Data) (η : ℝ) :=
  {q : CuspQuotient.QuotientSpace D.correction D.radius //
    ‖CuspQuotient.projection D.correction D.radius q‖ = η}

/-- A positive-radius point lies in the actual punctured cusp. -/
def levelToPunctured (D : Data) (η : ℝ) (hη : 0 < η) (q : LocalLevel D η) :
    PuncturedQuotient D.correction D.radius :=
  ⟨q.val, by
    change CuspQuotient.projection D.correction D.radius q.val ≠ 0
    apply norm_ne_zero_iff.mp
    rw [q.property]
    exact ne_of_gt hη⟩

@[simp] theorem levelToPunctured_coe (D : Data) (η : ℝ) (hη : 0 < η)
    (q : LocalLevel D η) :
    (levelToPunctured D η hη q : CuspQuotient.QuotientSpace D.correction D.radius) = q := rfl

theorem levelToPunctured_continuous (D : Data) (η : ℝ) (hη : 0 < η) :
    Continuous (levelToPunctured D η hη) := continuous_subtype_val.subtype_mk _

/-- The height of every genuine level point is exactly the selected height. -/
theorem levelToPunctured_height (D : Data) (η : ℝ) (hη : 0 < η)
    (hηr : η < D.radius) (q : LocalLevel D η) :
    (puncturedProductHomeomorph D (levelToPunctured D η hη q)).1 =
      heightAtRadius D η hη hηr := by
  apply (exp_height_eq_radius_iff D η hη hηr _).mp
  rw [← parameterNorm_punctured]
  exact q.property

/-- The existing punctured-product inverse at this radius, valued in the actual level. -/
def levelPoint (D : Data) (η : ℝ) (hη : 0 < η) (hηr : η < D.radius)
    (q : Boundary) : LocalLevel D η :=
  ⟨((puncturedProductHomeomorph D).symm (heightAtRadius D η hη hηr, q)).val, by
    change parameterNorm D
      ((puncturedProductHomeomorph D).symm (heightAtRadius D η hη hηr, q)) = η
    rw [parameterNorm_product_symm, heightAtRadius_exp]⟩

@[simp] theorem levelToPunctured_levelPoint (D : Data) (η : ℝ) (hη : 0 < η)
    (hηr : η < D.radius) (q : Boundary) :
    levelToPunctured D η hη (levelPoint D η hη hηr q) =
      (puncturedProductHomeomorph D).symm (heightAtRadius D η hη hηr, q) :=
  Subtype.ext rfl

theorem levelPoint_continuous (D : Data) (η : ℝ) (hη : 0 < η) (hηr : η < D.radius) :
    Continuous (levelPoint D η hη hηr) := by
  have hp : Continuous (fun q : Boundary => (heightAtRadius D η hη hηr, q)) :=
    continuous_const.prodMk continuous_id
  have hi := (puncturedProductHomeomorph D).symm.continuous.comp hp
  exact (continuous_subtype_val.comp hi).subtype_mk _

/-- The full original `M₀` mapping torus is homeomorphic to the literal radius level. -/
def levelHomeomorph (D : Data) (η : ℝ) (hη : 0 < η) (hηr : η < D.radius) :
    Boundary ≃ₜ LocalLevel D η where
  toFun := levelPoint D η hη hηr
  invFun q := (puncturedProductHomeomorph D (levelToPunctured D η hη q)).2
  left_inv q := by
    change (puncturedProductHomeomorph D
      (levelToPunctured D η hη (levelPoint D η hη hηr q))).2 = q
    rw [levelToPunctured_levelPoint, Homeomorph.apply_symm_apply]
  right_inv q := by
    apply Subtype.ext
    change ((puncturedProductHomeomorph D).symm
      (heightAtRadius D η hη hηr,
        (puncturedProductHomeomorph D (levelToPunctured D η hη q)).2)).val = q.val
    have hp : (heightAtRadius D η hη hηr,
        (puncturedProductHomeomorph D (levelToPunctured D η hη q)).2) =
        puncturedProductHomeomorph D (levelToPunctured D η hη q) :=
      Prod.ext (levelToPunctured_height D η hη hηr q).symm rfl
    rw [hp, Homeomorph.symm_apply_apply]
    rfl
  continuous_toFun := levelPoint_continuous D η hη hηr
  continuous_invFun :=
    ((puncturedProductHomeomorph D).continuous.comp (levelToPunctured_continuous D η hη)).snd

/-- The forward map is exactly the preexisting whole-boundary inclusion into the full cusp. -/
@[simp] theorem levelHomeomorph_coe (D : Data) (η : ℝ) (hη : 0 < η)
    (hηr : η < D.radius) (q : Boundary) :
    (levelHomeomorph D η hη hηr q : CuspQuotient.QuotientSpace D.correction D.radius) =
      CuspBoundaryToricExtension.boundaryToFull D (heightAtRadius D η hη hηr) q := rfl

/-- The original full real-torus coordinate and logarithmic time are unchanged. -/
theorem levelHomeomorph_mk (D : Data) (η : ℝ) (hη : 0 < η) (hηr : η < D.radius)
    (t : ℝ) (x : RealTorus₄) :
    (levelHomeomorph D η hη hηr (MappingTorus.mk monodromy (t, x))).val =
      (puncturedFamilyHomeomorph D
        (D.quotient (logPoint D.radius D.radius_pos t (heightAtRadius D η hη hηr), x))).val :=
  congrArg Subtype.val (boundaryCylinder_apply D (heightAtRadius D η hη hηr) t x)

/-- The actual varying complex periods followed by the original toric exponential quotient. -/
theorem levelHomeomorph_realCoordinates (D : Data) (η : ℝ) (hη : 0 < η)
    (hηr : η < D.radius) (t : ℝ) (x : RealPlane₄) :
    (levelHomeomorph D η hη hηr
      (MappingTorus.mk monodromy (t, standardLattice.mkQ x))).val =
      (puncturedCuspCover D.correction D.radius
        ⟨((logPoint D.radius D.radius_pos t (heightAtRadius D η hη hηr) : ℂ),
          D.periods.periodEquiv
            (logPoint D.radius D.radius_pos t (heightAtRadius D η hη hηr)) x),
          (logPoint D.radius D.radius_pos t (heightAtRadius D η hη hηr)).property⟩).val :=
  congrArg Subtype.val (boundaryCylinder_realCoordinates D (heightAtRadius D η hη hηr) t x)

/-- The exact original endpoint gluing retains the full `M₀`, including its delta row. -/
theorem levelHomeomorph_endpoint (D : Data) (η : ℝ) (hη : 0 < η)
    (hηr : η < D.radius) (t : ℝ) (x : RealTorus₄) :
    levelHomeomorph D η hη hηr (MappingTorus.mk monodromy (t + 1, x)) =
      levelHomeomorph D η hη hηr (MappingTorus.mk monodromy (t, monodromy x)) :=
  congrArg (levelHomeomorph D η hη hηr) (MappingTorus.mk_add_one monodromy t x)

theorem levelHomeomorph_parameter (D : Data) (η : ℝ) (hη : 0 < η)
    (hηr : η < D.radius) (t : ℝ) (x : RealTorus₄) :
    CuspQuotient.projection D.correction D.radius
      (levelHomeomorph D η hη hηr (MappingTorus.mk monodromy (t, x))) =
        exponential ((t : ℂ) + (heightAtRadius D η hη hηr : ℝ) * Complex.I) :=
  boundaryCylinder_base D (heightAtRadius D η hη hηr) t x

end Wikipedia.HopfProblem.CuspComplement.OuterBoundary

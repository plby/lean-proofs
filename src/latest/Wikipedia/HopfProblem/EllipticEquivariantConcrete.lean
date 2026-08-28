import Wikipedia.HopfProblem.EllipticEquivariantLocalModel
import Wikipedia.HopfProblem.EllipticFillings

/-!
# The concrete elliptic fillings as equivariant-period constructions

The two previously constructed local period maps satisfy the general
covariance input.  Their affine lifts, actual orbit quotients, complex
atlases and base projections are exactly those of the general
construction.  In particular, the arbitrary-period construction does
not replace the supplied complex structure by a concrete example's.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant

@[simp] theorem concrete_complexLift (j : Kind) (v : Lattice) :
    (concrete j).complexLift v = familyLift j v := rfl

@[simp] theorem concrete_permutation (j : Kind) (v : Lattice) :
    (concrete j).permutation v = familyPermutation j v := rfl

@[simp] theorem concrete_action (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    (concrete j).action v hv = familyAction j v hv := rfl

/-- Equality with the concrete quotient atlas is checked explicitly;
it is not inferred from equality of the underlying topological spaces. -/
theorem concrete_chartedSpace_eq (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    (concrete j).chartedSpace v hv = fillingChartedSpace j v hv := rfl

/-- The actual generic quotient for the concrete periods is the
previously constructed quotient, with its original quotient topology. -/
def concreteHomeomorph (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    (concrete j).Space v hv ≃ₜ Filling j v hv := Homeomorph.refl _

@[simp] theorem concreteHomeomorph_quotient (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Family j) :
    concreteHomeomorph j v hv ((concrete j).quotient v hv x) =
      fillingQuotient j v hv x := rfl

@[simp] theorem concreteHomeomorph_projection (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : (concrete j).Space v hv) :
    fillingProjection j v hv (concreteHomeomorph j v hv x) =
      (concrete j).projection v hv x := rfl

/-- The identification also preserves the proved complex structures. -/
def concreteBiholomorph (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := (concrete j).chartedSpace v hv
    Diffeomorph (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel)
      ((concrete j).Space v hv) (Filling j v hv) ω := by
  letI := (concrete j).chartedSpace v hv
  exact Diffeomorph.refl (modelWithCornersSelf ℂ FamilyModel) _ ω

@[simp] theorem concreteBiholomorph_apply (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : (concrete j).Space v hv) :
    concreteBiholomorph j v hv x = concreteHomeomorph j v hv x := rfl

/-- The source's specified twists give a proper surjective holomorphic
filling for every supplied equivariant admissible period map. -/
theorem Data.main_projection_proper_holomorphic {j : Kind} (D : Data j) :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    IsProperMap (D.projection j.twist (mainTwist_admissible j)) ∧
      Function.Surjective (D.projection j.twist (mainTwist_admissible j)) ∧
      ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
        (D.projection j.twist (mainTwist_admissible j)) :=
  ⟨D.projection_proper j.twist (mainTwist_admissible j),
    D.projection_surjective j.twist (mainTwist_admissible j),
    D.projection_holomorphic j.twist (mainTwist_admissible j)⟩

end Wikipedia.HopfProblem.Elliptic.Equivariant

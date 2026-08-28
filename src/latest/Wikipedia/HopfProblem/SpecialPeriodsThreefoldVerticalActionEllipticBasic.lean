import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriodBasic
import Wikipedia.HopfProblem.EllipticEquivariantFillings

/-!
# Vertical translation on the actual affine elliptic quotients

Both source monodromy matrices fix the second complex coordinate.  Thus
the literal translation in that coordinate commutes with the actual
affine cyclic action, including its logarithmic twist, and descends to
the original finite-orbit filling.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic

open Wikipedia.HopfProblem.Elliptic

/-- The original two complex monodromy matrices fix every vertical
translation vector. -/
theorem linearMatrix_vector (j : Kind) (p : PeriodDomain) (s : ℂ) :
    linearMatrix j p *ᵥ Period.vector s = Period.vector s := by
  cases j <;> ext i <;> fin_cases i <;>
    simp [linearMatrix, PeriodPoint.R₁, PeriodPoint.R₂, Period.vector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

variable {j : Kind} (D : Equivariant.Data j)

/-- Commutation holds already on the original complex cover, before
taking either the varying lattice or the affine cyclic quotient. -/
theorem complexLift_vectorFlow (v : Lattice) (s : ℂ) (x : Disc × ComplexPlane₂) :
    D.complexLift v (Period.vectorFlow s x) =
      Period.vectorFlow s (D.complexLift v x) := by
  apply Prod.ext
  · rfl
  · change linearMatrix j (D.periods.point x.1) *ᵥ (x.2 + Period.vector s) + _ =
      (linearMatrix j (D.periods.point x.1) *ᵥ x.2 + _) + Period.vector s
    rw [Matrix.mulVec_add, linearMatrix_vector]
    abel

/-- The actual torus-family flow commutes with the affine generator. -/
theorem periodFlow_permutation (v : Lattice) (s : ℂ) (x : D.TotalSpace) :
    Period.flow D.periods s (D.permutation v x) =
      D.permutation v (Period.flow D.periods s x) := by
  obtain ⟨z, rfl⟩ := D.periods.quotientMap_surjective x
  rw [← D.complexLift_quotientMap, Period.flow_quotientMap,
    Period.flow_quotientMap, ← D.complexLift_quotientMap, complexLift_vectorFlow]

/-- Commutation with every element of the proved finite cyclic action. -/
theorem periodFlow_action (v : Lattice) (hv : j.matrix *ᵥ v = v) (s : ℂ)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    Period.flow D.periods s (g • x) = g • Period.flow D.periods s x := by
  let := D.action v hv
  have h : Function.Semiconj (Period.flow D.periods s) (D.permutation v)
      (D.permutation v) := periodFlow_permutation D v s
  change Period.flow D.periods s ((D.permutation v ^ g.toAdd.val) x) =
    (D.permutation v ^ g.toAdd.val) (Period.flow D.periods s x)
  simp only [Equiv.Perm.coe_pow]
  exact h.iterate_right g.toAdd.val x

/-- The vertical flow on the original finite-orbit filling. -/
def flow (v : Lattice) (hv : AdmissibleTwist j v) (s : ℂ) : D.Space v hv → D.Space v hv := by
  let := D.action v hv.1
  exact FiniteQuotient.descend
    (fun x => D.quotient v hv (Period.flow D.periods s x)) (by
      intro g x
      rw [periodFlow_action D v hv.1 s g x, D.quotient_smul])

/-- The descended flow has its literal translation formula on every
representative of the actual quotient. -/
@[simp] theorem flow_quotient (v : Lattice) (hv : AdmissibleTwist j v) (s : ℂ)
    (x : D.TotalSpace) :
    flow D v hv s (D.quotient v hv x) =
      D.quotient v hv (Period.flow D.periods s x) := rfl

@[simp] theorem flow_quotient_quotientMap (v : Lattice) (hv : AdmissibleTwist j v)
    (s : ℂ) (x : Disc × ComplexPlane₂) :
    flow D v hv s (D.quotient v hv (D.periods.quotientMap x)) =
      D.quotient v hv (D.periods.quotientMap (Period.vectorFlow s x)) := by
  rw [flow_quotient, Period.flow_quotientMap]

/-- The filling parameter is unchanged, including at the central fibre. -/
@[simp] theorem flow_projection (v : Lattice) (hv : AdmissibleTwist j v) (s : ℂ)
    (x : D.Space v hv) :
    D.projection v hv (flow D v hv s x) = D.projection v hv x := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective v hv x
  rw [flow_quotient, D.projection_quotient, D.projection_quotient]
  rfl

@[simp] theorem flow_zero (v : Lattice) (hv : AdmissibleTwist j v) (x : D.Space v hv) :
    flow D v hv 0 x = x := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective v hv x
  rw [flow_quotient, Period.flow_zero]

theorem flow_add (v : Lattice) (hv : AdmissibleTwist j v) (s t : ℂ)
    (x : D.Space v hv) :
    flow D v hv (s + t) x = flow D v hv s (flow D v hv t x) := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective v hv x
  rw [flow_quotient, flow_quotient, flow_quotient, Period.flow_add]

@[simp] theorem flow_int_cast (v : Lattice) (hv : AdmissibleTwist j v) (n : ℤ)
    (x : D.Space v hv) : flow D v hv (n : ℂ) x = x := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective v hv x
  rw [flow_quotient, Period.flow_int_cast]

@[simp] theorem flow_neg_flow (v : Lattice) (hv : AdmissibleTwist j v) (s : ℂ)
    (x : D.Space v hv) : flow D v hv (-s) (flow D v hv s x) = x := by
  rw [← flow_add, neg_add_cancel, flow_zero]

@[simp] theorem flow_flow_neg (v : Lattice) (hv : AdmissibleTwist j v) (s : ℂ)
    (x : D.Space v hv) : flow D v hv s (flow D v hv (-s) x) = x := by
  rw [← flow_add, add_neg_cancel, flow_zero]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic

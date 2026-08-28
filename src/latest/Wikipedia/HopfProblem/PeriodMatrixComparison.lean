import Wikipedia.HopfProblem.MatrixPeriodTori
import Wikipedia.HopfProblem.PeriodMonodromy

/-!
# Comparing the two markings of the same period torus

The period domain uses the four columns `[Z | I]`, whereas the cusp
uniformization uses `[I | Z]`.  Reordering these actual generators does
not change their integral lattice.  The identity on `ℂ²` consequently
induces a biholomorphism of the two quotient complex manifolds.
-/

noncomputable section

open Set
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem

namespace PeriodPoint

/-- The nonconstant left block of the period matrix of Definition 3.3. -/
def leftBlock (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![6 * p.μ, p.τ; p.β, p.μ]

theorem leftBlock_apply (p : PeriodPoint) (i j : Fin 2) :
    p.leftBlock i j = p.matrix i (Fin.castAdd 2 j) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem matrix_rightBlock (p : PeriodPoint) (i j : Fin 2) :
    p.matrix i (Fin.natAdd 2 j) = (Pi.single j (1 : ℂ) : ComplexPlane₂) i := by
  fin_cases i <;> fin_cases j <;> simp [matrix]

end PeriodPoint

namespace PeriodDomain

/-- Swapping the identity block and the period block preserves the full
integral lattice, not just its complex or real linear span. -/
theorem fullPeriodLattice_eq (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) : q.lattice = p.lattice := by
  have hrange : range q.basis = range (fun j i => p.val.matrix i j) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | inl j =>
        refine ⟨Fin.natAdd 2 j, ?_⟩
        ext i
        rw [q.basis_inl]
        exact p.val.matrix_rightBlock i j
      | inr j =>
        refine ⟨Fin.castAdd 2 j, ?_⟩
        ext i
        rw [q.basis_inr, h]
        exact (p.val.leftBlock_apply i j).symm
    · rintro ⟨j, rfl⟩
      fin_cases j
      · refine ⟨Sum.inr 0, ?_⟩
        rw [q.basis_inr, h]
        ext i
        exact p.val.leftBlock_apply i 0
      · refine ⟨Sum.inr 1, ?_⟩
        rw [q.basis_inr, h]
        ext i
        exact p.val.leftBlock_apply i 1
      · refine ⟨Sum.inl 0, ?_⟩
        rw [q.basis_inl]
        ext i
        exact (p.val.matrix_rightBlock i 0).symm
      · refine ⟨Sum.inl 1, ?_⟩
        rw [q.basis_inl]
        ext i
        exact (p.val.matrix_rightBlock i 1).symm
  exact congrArg (Submodule.span ℤ) hrange

/-- The identity of the covering vector space gives a genuine
biholomorphism between the differently marked period tori. -/
def fullPeriodBiholomorph (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus q.Torus ω :=
  DiscreteQuotient.linearBiholomorph p.lattice q.lattice
    (ContinuousLinearEquiv.refl ℂ ComplexPlane₂) (by
      change p.lattice.map (LinearMap.id : ComplexPlane₂ →ₗ[ℤ] ComplexPlane₂) = q.lattice
      simpa only [Submodule.map_id] using (p.fullPeriodLattice_eq q h).symm)

@[simp] theorem fullPeriodBiholomorph_mkQ (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) (z : ComplexPlane₂) :
    p.fullPeriodBiholomorph q h (p.lattice.mkQ z) = q.lattice.mkQ z := rfl

@[simp] theorem fullPeriodBiholomorph_symm_mkQ (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) (z : ComplexPlane₂) :
    (p.fullPeriodBiholomorph q h).symm (q.lattice.mkQ z) = p.lattice.mkQ z := rfl

end PeriodDomain

end Wikipedia.HopfProblem

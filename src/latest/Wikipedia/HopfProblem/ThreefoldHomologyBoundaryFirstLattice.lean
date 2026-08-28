import Wikipedia.HopfProblem.EllipticFirstHomologyLattice

/-!
# Integral coinvariants of the three boundary monodromies

The two elliptic matrices have the primitive quotient coordinates already
computed from their integral image lattices.  For the cusp matrix the
first two coordinates give the quotient, since its difference image is
exactly the last two coordinate axes.  These are integral quotient
equivalences, not computations of rational ranks.

The sign is the Wang convention `1 - A`, opposite to the lattice lemmas'
`A - 1`.  Negating a linear map does not change its image.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.BoundaryFirst

/-- The actual source-column matrix at each of the three punctures. -/
def latticeMonodromy : Option Elliptic.Kind → LatticeMatrix
  | none => M₀
  | some j => j.matrix

/-- The integral matrix difference with the sign of the actual Wang sequence. -/
def latticeDifference (i : Option Elliptic.Kind) : Lattice →ₗ[ℤ] Lattice :=
  -((latticeMonodromy i - 1).mulVecLin)

theorem latticeDifference_apply (i : Option Elliptic.Kind) (w : Lattice) :
    latticeDifference i w = w - latticeMonodromy i *ᵥ w := by
  simp [latticeDifference]

/-- The cusp's two primitive coinvariant coordinates. -/
def cuspCoinvariantMap : Lattice →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun w := ![w 0, w 1]
  map_add' w z := by ext k; fin_cases k <;> rfl
  map_smul' a w := by ext k; fin_cases k <;> rfl

/-- Integral coinvariant coordinates for the cusp and the two elliptic boundaries. -/
def latticeCoinvariantMap : Option Elliptic.Kind → Lattice →ₗ[ℤ] (Fin 2 → ℤ)
  | none => cuspCoinvariantMap
  | some j => Elliptic.coinvariantMap j

@[simp] theorem latticeCoinvariantMap_none (w : Lattice) :
    latticeCoinvariantMap none w = ![w 0, w 1] := rfl

@[simp] theorem latticeCoinvariantMap_some (j : Elliptic.Kind) (w : Lattice) :
    latticeCoinvariantMap (some j) w = ![γ w, Elliptic.psi j w] := rfl

/-- Both quotient coordinates have integral lifts. -/
theorem latticeCoinvariantMap_surjective (i : Option Elliptic.Kind) :
    Function.Surjective (latticeCoinvariantMap i) := by
  cases i with
  | none =>
    intro c
    refine ⟨![c 0, c 1, 0, 0], ?_⟩
    ext k
    fin_cases k <;> rfl
  | some j => exact Elliptic.coinvariantMap_surjective j

/-- The image of the integral Wang matrix is the full coordinate kernel. -/
theorem latticeDifference_range (i : Option Elliptic.Kind) :
    LinearMap.range (latticeDifference i) = LinearMap.ker (latticeCoinvariantMap i) := by
  rw [latticeDifference, LinearMap.range_neg]
  cases i with
  | none =>
    ext w
    change (∃ v : Lattice, (M₀ - 1) *ᵥ v = w) ↔ cuspCoinvariantMap w = 0
    rw [M₀_sub_one_range]
    constructor
    · rintro ⟨h0, h1⟩
      ext k
      fin_cases k <;> assumption
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
  | some j => exact (Elliptic.coinvariantMap_ker_eq_range j).symm

/-- Every integral boundary coinvariant group is genuinely free of rank two. -/
def latticeCokernelEquiv (i : Option Elliptic.Kind) :
    (Lattice ⧸ LinearMap.range (latticeDifference i)) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ (latticeDifference_range i)).trans
    ((latticeCoinvariantMap i).quotKerEquivOfSurjective
      (latticeCoinvariantMap_surjective i))

/-- The quotient equivalence evaluates the original representative's primitive coordinates. -/
@[simp] theorem latticeCokernelEquiv_mk (i : Option Elliptic.Kind) (w : Lattice) :
    latticeCokernelEquiv i (Submodule.Quotient.mk w) = latticeCoinvariantMap i w := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.BoundaryFirst

import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubicalBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexQuotientFaces

/-!
# From actual simplex boundaries to actual cubical boundaries

The nested-minimum quotient sends the cubical codimension-two boundary
into the simplex codimension-two boundary.  Its upper facets and final
lower facet are exactly the original simplex faces; every other lower
facet is constant.  Consequently the two alternating boundary values
are literally equal.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open CubicalBoundary

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The original singular simplex composed with the actual cube quotient. -/
def simplexBoundaryCube {n : ℕ} (τ : BasedSimplexBoundary n x) : BasedCubicalCell n x :=
  ⟨τ.val.comp (simplexQuotient n), fun u i j hij hi hj =>
    τ.property _ (simplexQuotient_codimTwo u ⟨i, j, hij, hi, hj⟩)⟩

@[simp] theorem simplexBoundaryCube_apply {n : ℕ} (τ : BasedSimplexBoundary n x)
    (u : Fin n → I) : (simplexBoundaryCube τ).val u = τ.val (simplexQuotient n u) := rfl

/-- Every upper cubical facet is the matching original based simplex loop. -/
theorem simplexBoundaryCube_upper {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x)
    (i : Fin (n + 1)) :
    cubicalUpperFace (simplexBoundaryCube τ) i =
      basedSimplexLoop (basedSimplexBoundaryFace τ i.castSucc) := by
  apply GenLoop.ext
  intro u
  change τ.val (simplexQuotient (n + 1) (cubeFacet n i 1 u)) =
    τ.val (FirstHurewicz.simplexFace n i.castSucc (simplexQuotient n u))
  rw [simplexQuotient_cubeFacet_one_apply]

/-- The final lower cubical facet is the final original based simplex loop. -/
theorem simplexBoundaryCube_lower_last {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) :
    cubicalLowerFace (simplexBoundaryCube τ) (Fin.last n) =
      basedSimplexLoop (basedSimplexBoundaryFace τ (Fin.last (n + 1))) := by
  apply GenLoop.ext
  intro u
  change τ.val (simplexQuotient (n + 1) (cubeFacet n (Fin.last n) 0 u)) =
    τ.val (FirstHurewicz.simplexFace n (Fin.last (n + 1)) (simplexQuotient n u))
  rw [simplexQuotient_cubeFacet_last_zero_apply]

/-- Every other lower cubical facet is literally the constant generalized loop. -/
theorem simplexBoundaryCube_lower_constant {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    cubicalLowerFace (simplexBoundaryCube τ) i = GenLoop.const := by
  apply GenLoop.ext
  intro u
  exact τ.property _ (simplexQuotient_bottom_not_last_twoBoundary n i hi u)

variable {A : Type*} [AddCommGroup A]

/-- The genuine cubical boundary value is the genuine simplex boundary value. -/
theorem simplexBoundaryCube_boundaryValue {n : ℕ} (E : CubicalEvaluator n x A)
    (τ : BasedSimplexBoundary (n + 1) x) :
    cubicalBoundaryValue E (simplexBoundaryCube τ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        E (basedSimplexLoop (basedSimplexBoundaryFace τ i)) := by
  have hzero (i : Fin n) :
      E (cubicalLowerFace (simplexBoundaryCube τ) i.castSucc) = 0 := by
    rw [simplexBoundaryCube_lower_constant τ i.castSucc (Fin.castSucc_ne_last i)]
    exact E.map_const
  have hlower : (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      E (cubicalLowerFace (simplexBoundaryCube τ) i)) =
      (-1 : ℤ) ^ n • E (basedSimplexLoop
        (basedSimplexBoundaryFace τ (Fin.last (n + 1)))) := by
    rw [Fin.sum_univ_castSucc]
    simp only [hzero, smul_zero, Finset.sum_const_zero, zero_add, Fin.val_last,
      simplexBoundaryCube_lower_last]
  unfold cubicalBoundaryValue
  simp_rw [simplexBoundaryCube_upper, smul_sub]
  rw [Finset.sum_sub_distrib, hlower]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, pow_succ', neg_mul, one_mul,
    neg_smul, sub_eq_add_neg]

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

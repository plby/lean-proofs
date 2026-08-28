import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinates
import Wikipedia.HopfProblem.CuspNormalizationSheafGermComplex

/-!
# Exactness of the source-oriented triple-point germ maps

Keep the natural coordinate-plane ordering. The actual positive and negative
lift restrictions differ from the standard three-plane differential only by
a signed permutation of the three axis terms. That permutation preserves
the source's alternating evaluation, so the genuine analytic-germ exact
complex applies without changing coordinates inside any branch.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricCharts ToricFan ToricSpace ToricComponent Triangle NormalizationCurves
open CuspNormalization.Germs CuspNormalization.SheafGermComplex

/-- The actual signed branch restrictions in the source double-curve order. -/
def orientedTripleDifference (s : Triangle) :
    (Fin 3 → BranchGerm) →+ (Fin 3 → AxisGerm) where
  toFun f k := axisRestriction (plusAxisIndex s k) (f (plusBranch s k)) -
    axisRestriction (minusAxisIndex s k) (f (minusBranch s k))
  map_zero' := by funext k; simp
  map_add' f g := by
    funext k
    simp only [Pi.add_apply, map_add]
    abel

@[simp] theorem orientedTripleDifference_apply (s : Triangle) (f : Fin 3 → BranchGerm)
    (k : Fin 3) :
    orientedTripleDifference s f k =
      axisRestriction (plusAxisIndex s k) (f (plusBranch s k)) -
        axisRestriction (minusAxisIndex s k) (f (minusBranch s k)) := rfl

/-- The signed edge reordering relating the standard and source conventions. -/
def orientedEdgeEquiv (s : Triangle) : (Fin 3 → AxisGerm) ≃+ (Fin 3 → AxisGerm) where
  toFun g := if s.upper then ![g 2, -g 0, -g 1] else ![g 0, -g 2, -g 1]
  invFun g := if s.upper then ![-g 1, -g 2, g 0] else ![g 0, -g 2, -g 1]
  left_inv g := by
    cases s.upper <;> funext k <;> fin_cases k <;> simp
  right_inv g := by
    cases s.upper <;> funext k <;> fin_cases k <;> simp
  map_add' g h := by
    cases s.upper <;> funext k <;> fin_cases k <;> simp [add_comm]

theorem orientedTripleDifference_eq_edgeEquiv (s : Triangle) (f : Fin 3 → BranchGerm) :
    orientedTripleDifference s f = orientedEdgeEquiv s (tripleDifference f) := by
  cases hs : s.upper
  · funext k
    fin_cases k <;>
      simp [orientedTripleDifference, orientedEdgeEquiv, hs, tripleDifference,
        plusBranch_lower s hs, minusBranch_lower s hs,
        plusAxisIndex_lower s hs, minusAxisIndex_lower s hs, neg_sub]
  · funext k
    fin_cases k <;>
      simp [orientedTripleDifference, orientedEdgeEquiv, hs, tripleDifference,
        plusBranch_upper s hs, minusBranch_upper s hs,
        plusAxisIndex_upper s hs, minusAxisIndex_upper s hs, neg_sub]

theorem orientedTripleDifference_eq_zero_iff (s : Triangle) (f : Fin 3 → BranchGerm) :
    orientedTripleDifference s f = 0 ↔ tripleDifference f = 0 := by
  rw [orientedTripleDifference_eq_edgeEquiv]
  constructor
  · intro h
    apply (orientedEdgeEquiv s).injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- The signed permutation preserves the single source sign convention at
both upper and lower triple points. -/
theorem tripleAugmentation_orientedEdgeEquiv (s : Triangle) (g : Fin 3 → AxisGerm) :
    tripleAugmentation (orientedEdgeEquiv s g) = tripleAugmentation g := by
  cases hs : s.upper <;>
    simp [tripleAugmentation, orientedEdgeEquiv, hs] <;> abel

theorem orientedTripleRestriction_exact (s : Triangle) :
    Function.Exact tripleRestriction.toAddMonoidHom (orientedTripleDifference s) := by
  intro f
  rw [orientedTripleDifference_eq_zero_iff]
  exact tripleRestriction_exact f

theorem orientedTripleAugmentation_difference (s : Triangle) (f : Fin 3 → BranchGerm) :
    tripleAugmentation (orientedTripleDifference s f) = 0 := by
  rw [orientedTripleDifference_eq_edgeEquiv, tripleAugmentation_orientedEdgeEquiv]
  exact tripleAugmentation_difference f

theorem orientedTripleDifference_exact (s : Triangle) :
    Function.Exact (orientedTripleDifference s) tripleAugmentation := by
  intro g
  constructor
  · intro hg
    have hg' : tripleAugmentation ((orientedEdgeEquiv s).symm g) = 0 := by
      have he := tripleAugmentation_orientedEdgeEquiv s ((orientedEdgeEquiv s).symm g)
      rw [AddEquiv.apply_symm_apply] at he
      exact he.symm.trans hg
    obtain ⟨f, hf⟩ := (tripleDifference_exact _).mp hg'
    refine ⟨f, ?_⟩
    rw [orientedTripleDifference_eq_edgeEquiv, hf, AddEquiv.apply_symm_apply]
  · rintro ⟨f, rfl⟩
    exact orientedTripleAugmentation_difference s f

theorem orientedTripleDifference_ker (s : Triangle) :
    (orientedTripleDifference s).ker = tripleRestriction.toAddMonoidHom.range :=
  AddMonoidHom.exact_iff.mp (orientedTripleRestriction_exact s)

theorem orientedTripleAugmentation_ker (s : Triangle) :
    tripleAugmentation.ker = (orientedTripleDifference s).range :=
  AddMonoidHom.exact_iff.mp (orientedTripleDifference_exact s)

/-- This exact difference is the pullback difference along the genuine two
lifts, expressed in the actual centered charts. -/
theorem orientedTripleDifference_eq_actualPullbacks
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (s : Triangle)
    (d : ∀ k, sourceDoubleCurve C ε hε k)
    (hd : ∀ k, d k ∈ (axisParametrization C ε hε hε1 hC hR s (sourceEdgeIndex k)).target)
    (f : Fin 3 → BranchGerm) (k : Fin 3) :
    orientedTripleDifference s f k =
      plusGermPullback C ε hε hε1 hC hR s k (d k) (hd k) (f (plusBranch s k)) -
        minusGermPullback C ε hε hε1 hC hR s k (d k) (hd k) (f (minusBranch s k)) := by
  rw [plusGermPullback_eq_axisRestriction, minusGermPullback_eq_axisRestriction]
  rfl

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

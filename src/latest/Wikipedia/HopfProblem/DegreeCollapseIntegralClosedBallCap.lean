import Wikipedia.HopfProblem.DegreeCollapseIntegralClosedBallCohomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralCapAugmentation
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportCap

/-!
# Bijectivity of the original integral cap map on closed-ball supports

The actual top cap followed by original augmentation is the computed
primitive-evaluation marking. Both augmentation and that marking are
isomorphisms, so the original cap map is bijective. In the other
complementary degrees the original source and target groups vanish.
-/

noncomputable section

open Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralClosedBallCap

open FirstHurewicz NoExoticSixSphere

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Cap with the constructed signed primitive on this original closed-ball support. -/
def capMap (R : ℝ) (hR : 0 ≤ R) (p q : ℕ) (h : p + q = n + 3) :
    IntegralSupportedCohomology.Cohomology (closedBall (0 : E) R) p →ₗ[ℤ]
      (singularComplex E).homology q :=
  IntegralCompactSupportCap.componentMap (closedBall (0 : E) R) h
    (IntegralBallOrientation.fundamentalClass E (n + 1) R hR)

theorem augmentation_topCap (R : ℝ) (hR : 0 ≤ R)
    (a : IntegralSupportedCohomology.Cohomology (closedBall (0 : E) R) (n + 3)) :
    IntegralCap.augmentation E (capMap E n R hR (n + 3) 0 (Nat.add_zero (n + 3)) a) =
      IntegralClosedBallCohomology.topEquiv E n R hR a :=
  (RelativeIntegralCap.augmentation_capProduct (closedBall (0 : E) R)ᶜ (n + 3) a
    (IntegralBallOrientation.fundamentalClass E (n + 1) R hR)).trans
      (IntegralClosedBallCohomology.topEquiv_apply_ballClass E n R hR a).symm

/-- Top duality is proved for the actual cap map, not for an independently chosen marking. -/
theorem topCap_bijective (R : ℝ) (hR : 0 ≤ R) :
    Function.Bijective (capMap E n R hR (n + 3) 0 (Nat.add_zero (n + 3))) := by
  let A : (singularComplex E).homology 0 ≃ₗ[ℤ] ℤ :=
    CoefficientChains.connectedZeroEquiv (ModuleCat.of ℤ ℤ) E
  let C := IntegralClosedBallCohomology.topEquiv E n R hR
  have he (a : IntegralSupportedCohomology.Cohomology (closedBall (0 : E) R) (n + 3)) :
      A (capMap E n R hR (n + 3) 0 (Nat.add_zero (n + 3)) a) = C a :=
    augmentation_topCap E n R hR a
  constructor
  · intro a b hab
    apply C.injective
    exact (he a).symm.trans ((congrArg A hab).trans (he b))
  · intro b
    refine ⟨C.symm (A b), A.injective ?_⟩
    exact (he _).trans (C.apply_symm_apply (A b))

/-- Every pair of complementary degrees is computed by the original integral cap. -/
theorem cap_bijective (R : ℝ) (hR : 0 ≤ R) (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (capMap E n R hR p q h) := by
  by_cases hq : q = 0
  · subst q
    have hp : p = n + 3 := by omega
    subst p
    exact topCap_bijective E n R hR
  · let := IntegralClosedBallCohomology.cohomology_subsingleton E n R hR p (by omega)
    let : Subsingleton ((singularComplex E).homology q) :=
      PeriodTorusHigherHomology.contractible_homology_subsingleton E q hq
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

def capEquiv (R : ℝ) (hR : 0 ≤ R) (p q : ℕ) (h : p + q = n + 3) :
    IntegralSupportedCohomology.Cohomology (closedBall (0 : E) R) p ≃ₗ[ℤ]
      (singularComplex E).homology q :=
  LinearEquiv.ofBijective (capMap E n R hR p q h) (cap_bijective E n R hR p q h)

theorem capEquiv_toLinearMap (R : ℝ) (hR : 0 ≤ R) (p q : ℕ) (h : p + q = n + 3) :
    (capEquiv E n R hR p q h).toLinearMap = capMap E n R hR p q h := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralClosedBallCap

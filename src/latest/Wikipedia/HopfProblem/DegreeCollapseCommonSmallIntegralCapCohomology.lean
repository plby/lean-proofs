import Wikipedia.HopfProblem.DegreeCollapseCommonSmallIntegralCapBoundary

/-!
# Cohomologous integral cochains give the same actual overlap cap class

An actual coboundary witness gives a primitive in the overlap itself.
The primitive has coefficient -(-1)^p; its boundary sign cancels by
the integer identity (-(-1)^p)^2 = 1. No absolute inclusion is cancelled.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- The actual overlap cycle obtained from a closed integral cochain and a relative cycle. -/
def capCycle {p q n : ℕ} (h : p + q = n)
    (α : SingularCohomologyFree.Cocycle (SmallRelativeIntegralCochains.complex A B) p)
    (c : (complex U A V B).X n)
    (hc : ((inclusion U A V B).f (n - 1)).hom
        (((complex U A V B).d n (n - 1)).hom c) ∈
      LinearMap.range (inducedChain (subtypeInclusion A) (n - 1))) :
    ModuleHomology.Cycle (singularComplex (U ∩ V : Set X)) q :=
  ModuleHomology.mkCycle _ q (capInDegree U A V B h α.val c)
    (cap_is_cycle U A V B h α.val
      (SingularCohomologyFree.cocycle_condition _ p α) c hc)

/-- Equal original cohomology classes give equal original overlap cap classes. -/
theorem capCycle_class_eq_of_cohomology_eq {p q n : ℕ} (h : (p + 1) + q = n)
    (α β : SingularCohomologyFree.Cocycle (SmallRelativeIntegralCochains.complex A B) (p + 1))
    (hαβ : SingularCohomologyFree.cocycleClass _ (p + 1) α =
      SingularCohomologyFree.cocycleClass _ (p + 1) β)
    (c : (complex U A V B).X n)
    (hc : ((inclusion U A V B).f (n - 1)).hom
        (((complex U A V B).d n (n - 1)).hom c) ∈
      LinearMap.range (inducedChain (subtypeInclusion A) (n - 1))) :
    ModuleHomology.cycleClass _ q (capCycle U A V B h α c hc) =
      ModuleHomology.cycleClass _ q (capCycle U A V B h β c hc) := by
  have he := (SingularCohomologyFree.cocycleClass_eq_iff _ (p + 1) α β).mp hαβ
  rw [Nat.add_sub_cancel] at he
  obtain ⟨μ, hμ⟩ := he
  have hc' : ((inclusion U A V B).f (p + q)).hom
      (((complex U A V B).d n (p + q)).hom c) ∈
    LinearMap.range (inducedChain (subtypeInclusion A) (p + q)) :=
    (congrArg (fun j => ((inclusion U A V B).f j).hom
      (((complex U A V B).d n j).hom c) ∈
        LinearMap.range (inducedChain (subtypeInclusion A) j))
      (show n - 1 = p + q by omega)).mp hc
  have hd := boundary_capInDegree_of_relative_cycle U A V B (p := p) (q := q) (n := n)
    (by omega) μ c hc'
  apply (ModuleHomology.cycleClass_eq_iff _ q _ _).mpr
  refine ⟨-((-1 : ℤ) ^ p) •
    capInDegree U A V B (p := p) (q := q + 1) (n := n) (by omega) μ c, ?_⟩
  calc
    _ = -((-1 : ℤ) ^ p) • (((singularComplex (U ∩ V : Set X)).d (q + 1) q).hom
        (capInDegree U A V B (p := p) (q := q + 1) (n := n) (by omega) μ c)) :=
      map_zsmul ((singularComplex (U ∩ V : Set X)).d (q + 1) q).hom _ _
    _ = -((-1 : ℤ) ^ p) • (-((-1 : ℤ) ^ p) • capInDegree U A V B h
        (SmallRelativeIntegralCochains.coboundary A B μ) c) :=
      congrArg (fun t => -((-1 : ℤ) ^ p) • t) hd
    _ = capInDegree U A V B h (SmallRelativeIntegralCochains.coboundary A B μ) c := by
      rw [← mul_zsmul, neg_mul_neg, IntegralCap.sign_mul_self, one_zsmul]
    _ = _ := (congrArg (fun γ => capInDegree U A V B h γ c) hμ).trans
      (LinearMap.congr_fun (capInDegree_sub U A V B h α.val β.val) c)

end Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap

import Wikipedia.NoExoticSixSphere.CommonSmallModTwoCapBoundary

/-!
# Cohomologous small-relative cochains give the same overlap cap class

The original coboundary witness caps to a primitive in the overlap
itself. Thus equality is proved in the actual overlap homology without
assuming injectivity of its map to ambient homology.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.CommonSmallModTwoCap

open ModTwoCapProduct (Coefficient)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- The original overlap cycle obtained by capping a common-small relative cycle. -/
def capCycle {p q n : ℕ} (h : p + q = n)
    (α : SingularCohomologyFree.Cocycle (SmallRelativeModTwoCochains.complex A B) p)
    (c : (complex U A V B).X n)
    (hc : ((inclusion U A V B).f (n - 1)).hom
        (((complex U A V B).d n (n - 1)).hom c) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f (n - 1)).hom) :
    ModuleHomology.Cycle (modComplex 2 (U ∩ V : Set X)) q :=
  ModuleHomology.mkCycle _ q (capInDegree U A V B h α.val c)
    (cap_is_cycle U A V B h α.val
      (SingularCohomologyFree.cocycle_condition _ p α) c hc)

/-- Equal actual small-relative cohomology classes have equal actual overlap cap classes. -/
theorem capCycle_class_eq_of_cohomology_eq {p q n : ℕ} (h : (p + 1) + q = n)
    (α β : SingularCohomologyFree.Cocycle (SmallRelativeModTwoCochains.complex A B) (p + 1))
    (hαβ : SingularCohomologyFree.cocycleClass _ (p + 1) α =
      SingularCohomologyFree.cocycleClass _ (p + 1) β)
    (c : (complex U A V B).X n)
    (hc : ((inclusion U A V B).f (n - 1)).hom
        (((complex U A V B).d n (n - 1)).hom c) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f (n - 1)).hom) :
    ModuleHomology.cycleClass _ q (capCycle U A V B h α c hc) =
      ModuleHomology.cycleClass _ q (capCycle U A V B h β c hc) := by
  have he := (SingularCohomologyFree.cocycleClass_eq_iff _ (p + 1) α β).mp hαβ
  rw [Nat.add_sub_cancel] at he
  obtain ⟨μ, hμ⟩ := he
  have hc' : ((inclusion U A V B).f (p + q)).hom
      (((complex U A V B).d n (p + q)).hom c) ∈
    LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f (p + q)).hom :=
    (congrArg (fun j => ((inclusion U A V B).f j).hom
      (((complex U A V B).d n j).hom c) ∈
        LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f j).hom)
      (show n - 1 = p + q by omega)).mp hc
  apply (ModuleHomology.cycleClass_eq_iff _ q _ _).mpr
  refine ⟨capInDegree U A V B (p := p) (q := q + 1) (n := n) (by omega) μ c, ?_⟩
  exact (boundary_capInDegree_of_relative_cycle U A V B (p := p) (q := q) (n := n)
    (by omega) μ c hc').trans
      ((congrArg (fun γ => capInDegree U A V B h γ c) hμ).trans
        (LinearMap.congr_fun (capInDegree_sub U A V B h α.val β.val) c))

end NoExoticSixSphere.CommonSmallModTwoCap

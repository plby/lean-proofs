import Wikipedia.HopfProblem.DegreeCollapsePointClassComponents

/-!
# Point classes generate actual degree-zero singular homology

Every zero-chain is a cycle. The actual categorical homology map from these
cycles is surjective, so linear maps out of degree-zero homology are
determined by their values on the original point classes.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X]

def zeroChainCycle : Chains X 0 →ₗ[ℤ] ModuleHomology.Cycle (singularComplex X) 0 where
  toFun z := ModuleHomology.mkCycle (singularComplex X) 0 z (by
    have h := (singularComplex X).shape 0 0 (by simp)
    exact congrArg (fun f => f.hom z) h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def zeroChainClass : Chains X 0 →ₗ[ℤ] SingularHomology X 0 :=
  (ModuleHomology.cycleClass (singularComplex X) 0).comp zeroChainCycle

theorem zeroChainClass_pointChain (x : X) : zeroChainClass (pointChain x) = pointClass x := rfl

theorem zeroChainClass_surjective : Function.Surjective (zeroChainClass (X := X)) := by
  intro a
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex X) 0 a
  exact ⟨c.val, rfl⟩

theorem homologyZero_linearMap_ext {A : Type} [AddCommGroup A] [Module ℤ A]
    {L K : SingularHomology X 0 →ₗ[ℤ] A}
    (h : ∀ x : X, L (pointClass x) = K (pointClass x)) : L = K := by
  have heq : L.comp zeroChainClass = K.comp zeroChainClass := by
    apply chainMap_ext X 0
    intro σ
    have hσ : σ = ContinuousMap.const (Simplex 0) (σ (stdSimplex.vertex 0)) := by
      ext t
      exact congrArg σ (simplexZero_eq_vertex t)
    rw [hσ]
    exact h _
  apply LinearMap.ext
  intro a
  obtain ⟨z, rfl⟩ := zeroChainClass_surjective a
  exact LinearMap.congr_fun heq z

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

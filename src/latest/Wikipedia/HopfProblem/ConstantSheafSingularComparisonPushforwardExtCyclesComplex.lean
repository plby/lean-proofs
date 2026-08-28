import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtCyclesBasic

/-!
# Degree-two cycle comparison under a composite left-exact functor
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt.Cycles

open LowExt.CycleCokernel

attribute [local instance] comp_preservesFiniteLimits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  (G : C ⥤ D) (H : D ⥤ E)
  [G.Additive] [H.Additive] [PreservesFiniteLimits G] [PreservesFiniteLimits H]

/-- The native comparison for the actual degree-two cycle object. -/
@[reassoc] theorem map_toCycles₂_kernelComparison (K : CochainComplex C ℕ) :
    G.map (toCycles₂ K) ≫ kernelComparison (K.d 2 3) G =
      toCycles₂ ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
  map_toKernel_kernelComparison G (K.sc' 1 2 3)

/-- The actual cokernel map induced by the native comparison of
degree-two cycles, with the identity in degree one. -/
def iteratedCokernelMap₂ (K : CochainComplex C ℕ) :
    cokernel ((G ⋙ H).map (toCycles₂ K)) ⟶
      cokernel (H.map (toCycles₂
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))) :=
  iteratedCokernelMap G H (K.sc' 1 2 3)

omit [H.Additive] [PreservesFiniteLimits H] in
/-- Explicitly, this is the cokernel map of the original differential
into cycles and the canonical kernel comparison. -/
theorem iteratedCokernelMap₂_eq (K : CochainComplex C ℕ) :
    iteratedCokernelMap₂ G H K =
      cokernel.map _ _ (𝟙 _) (H.map (kernelComparison (K.d 2 3) G)) (by
        change H.map (G.map (toCycles₂ K)) ≫ H.map (kernelComparison (K.d 2 3) G) =
          𝟙 (H.obj (G.obj (K.X 1))) ≫ H.map (toCycles₂
            ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))
        exact ((H.map_comp (G.map (toCycles₂ K)) (kernelComparison (K.d 2 3) G)).symm.trans
          (congrArg H.map (map_toCycles₂_kernelComparison G K))).trans
            (Category.id_comp _).symm) := rfl

/-- Compatibility with the native degree-two homology identification.
The full mapped cochain complexes on the two sides are literally the
same complex, so there is no extra homology transport or chosen map. -/
@[reassoc] theorem iteratedCokernelMap₂_homology (K : CochainComplex C ℕ) :
    iteratedCokernelMap₂ G H K ≫
        (cokernelIsoHomology₂ H
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).hom =
      (cokernelIsoHomology₂ (G ⋙ H) K).hom := by
  let S := K.sc' 1 2 3
  let B := ((G ⋙ H).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  change iteratedCokernelMap G H S ≫
      ((shortCokernelIsoHomology H (S.map G)).hom ≫ (windowHomologyIso₂ B).inv) =
    (shortCokernelIsoHomology (G ⋙ H) S).hom ≫ (windowHomologyIso₂ B).inv
  exact ((Category.assoc _ _ _).symm).trans
    (congrArg (fun h => h ≫ (windowHomologyIso₂ B).inv)
      (iteratedCokernelMap_shortHomology G H S))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt.Cycles

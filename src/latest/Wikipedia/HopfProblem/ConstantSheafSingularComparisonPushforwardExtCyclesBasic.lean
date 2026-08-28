import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtCokernel

/-!
# Cycle cokernels under a composite left-exact functor

The canonical kernel comparison gives the actual cokernel map from
mapping the original cycles to taking cycles after the first functor.
Both descriptions compute the same native homology, and their square
commutes by explicit left homology map data for the identity complex.
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

/-- The original boundary into cycles followed by the native kernel
comparison is the boundary into the mapped complex's actual cycles. -/
@[reassoc] theorem map_toKernel_kernelComparison (S : ShortComplex C) :
    G.map (toKernel S) ≫ kernelComparison S.g G = toKernel (S.map G) :=
  map_lift_kernelComparison S.g G S.zero

/-- The cokernel map induced by the actual kernel comparison; its
degree-one component is the identity. -/
def iteratedCokernelMap (S : ShortComplex C) :
    cokernel ((G ⋙ H).map (toKernel S)) ⟶
      cokernel (H.map (toKernel (S.map G))) :=
  cokernel.map _ _ (𝟙 _) (H.map (kernelComparison S.g G)) (by
    change H.map (G.map (toKernel S)) ≫ H.map (kernelComparison S.g G) =
      𝟙 (H.obj (G.obj S.X₁)) ≫ H.map (toKernel (S.map G))
    exact ((H.map_comp (G.map (toKernel S)) (kernelComparison S.g G)).symm.trans
      (congrArg H.map (map_toKernel_kernelComparison G S))).trans
        (Category.id_comp _).symm)

/-- The native cycle and cokernel maps give homology map data for the
identity on the literal twice-mapped short complex. -/
def iteratedLeftHomologyMapData (S : ShortComplex C) :
    ShortComplex.LeftHomologyMapData (𝟙 (S.map (G ⋙ H)))
      (mappedLeftHomologyData (G ⋙ H) S)
      (mappedLeftHomologyData H (S.map G)) where
  φK := H.map (kernelComparison S.g G)
  φH := iteratedCokernelMap G H S
  commi := by
    change H.map (kernelComparison S.g G) ≫ H.map (kernel.ι (G.map S.g)) =
      H.map (G.map (kernel.ι S.g)) ≫ 𝟙 _
    simp only [← H.map_comp, kernelComparison_comp_ι, Category.comp_id]
  commf' := by
    exact (congrArg (fun k => k ≫ H.map (kernelComparison S.g G))
      (mappedLeftHomologyData_f' (G ⋙ H) S)).trans
        (((H.map_comp (G.map (toKernel S)) (kernelComparison S.g G)).symm.trans
          (congrArg H.map (map_toKernel_kernelComparison G S))).trans
            ((Category.id_comp _).symm.trans
              (congrArg (fun k => 𝟙 (H.obj (G.obj S.X₁)) ≫ k)
                (mappedLeftHomologyData_f' H (S.map G))).symm))
  commπ := by
    change cokernel.π _ ≫ iteratedCokernelMap G H S = _
    exact cokernel.π_desc _ _ _

/-- The actual kernel-comparison cokernel map commutes with the
canonical identifications with the same native homology object. -/
@[reassoc] theorem iteratedCokernelMap_shortHomology (S : ShortComplex C) :
    iteratedCokernelMap G H S ≫ (shortCokernelIsoHomology H (S.map G)).hom =
      (shortCokernelIsoHomology (G ⋙ H) S).hom := by
  let hS := mappedLeftHomologyData (G ⋙ H) S
  let hT := mappedLeftHomologyData H (S.map G)
  let γ := iteratedLeftHomologyMapData G H S
  change γ.φH ≫ hT.homologyIso.inv = hS.homologyIso.inv
  calc
    _ = hS.homologyIso.inv ≫ ShortComplex.homologyMap (𝟙 (S.map (G ⋙ H))) :=
      ((congrArg (fun f => hS.homologyIso.inv ≫ f) γ.homologyMap_eq).trans
        (hS.homologyIso.inv_hom_id_assoc (γ.φH ≫ hT.homologyIso.inv))).symm
    _ = _ := by rw [ShortComplex.homologyMap_id, Category.comp_id]

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt.Cycles

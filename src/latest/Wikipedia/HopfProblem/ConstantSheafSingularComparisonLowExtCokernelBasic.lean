import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Cokernels of mapped boundary maps into cycles

For a left-exact additive functor, the image of a kernel is still a
kernel.  Consequently the homology of a mapped short complex is the
cokernel of the mapped boundary map into the original kernel.  No
preservation of cokernels or homology is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt.CycleCokernel

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]

/-- The original boundary map, with codomain the actual kernel of the
next differential. -/
def toKernel (S : ShortComplex C) : S.X₁ ⟶ kernel S.g :=
  kernel.lift S.g S.f S.zero

/-- Equality of the incoming arrow transports its actual cokernel
universal property, without any change of the cokernel projection. -/
def cokernelIsColimitOfEq {A B : D} {f g : A ⟶ B} (h : f = g)
    (w : f ≫ cokernel.π g = 0) :
    IsColimit (CokernelCofork.ofπ (cokernel.π g) w) := by
  subst g
  exact cokernelIsCokernel f

/-- The lift into the preserved kernel is the functor's image of the
original lift. -/
theorem preservedKernel_lift (S : ShortComplex C) :
    (isLimitOfHasKernelOfPreservesLimit G S.g).lift
        (KernelFork.ofι (G.map S.f) (by simp only [← G.map_comp, S.zero, G.map_zero])) =
      G.map (toKernel S) := by
  apply Fork.IsLimit.hom_ext (isLimitOfHasKernelOfPreservesLimit G S.g)
  change _ ≫ G.map (kernel.ι S.g) = G.map (toKernel S) ≫ G.map (kernel.ι S.g)
  calc
    _ = G.map S.f :=
      (isLimitOfHasKernelOfPreservesLimit G S.g).fac _ WalkingParallelPair.zero
    _ = _ := by simp only [toKernel, ← G.map_comp, kernel.lift_ι]

/-- Actual left homology data using the preserved original kernel and
the cokernel of the mapped boundary into that kernel. -/
def mappedLeftHomologyData (S : ShortComplex C) : (S.map G).LeftHomologyData where
  K := G.obj (kernel S.g)
  H := cokernel (G.map (toKernel S))
  i := G.map (kernel.ι S.g)
  π := cokernel.π (G.map (toKernel S))
  wi := (G.map_comp (kernel.ι S.g) S.g).symm.trans
    ((congrArg G.map (kernel.condition S.g)).trans (G.map_zero _ _))
  hi := isLimitOfHasKernelOfPreservesLimit G S.g
  wπ := (congrArg (fun f => f ≫ cokernel.π (G.map (toKernel S)))
    (preservedKernel_lift G S)).trans (cokernel.condition _)
  hπ := cokernelIsColimitOfEq (preservedKernel_lift G S) _

/-- The canonical identification with the native homology object. -/
def shortCokernelIsoHomology (S : ShortComplex C) :
    cokernel (G.map (toKernel S)) ≅ (S.map G).homology :=
  (mappedLeftHomologyData G S).homologyIso.symm

theorem mappedLeftHomologyData_f' (S : ShortComplex C) :
    (mappedLeftHomologyData G S).f' = G.map (toKernel S) :=
  preservedKernel_lift G S

variable {G} {S T : ShortComplex C}

/-- The actual induced morphism between the original kernels. -/
def kernelMap (φ : S ⟶ T) : kernel S.g ⟶ kernel T.g :=
  kernel.map S.g T.g φ.τ₂ φ.τ₃ φ.comm₂₃.symm

@[reassoc] theorem toKernel_naturality (φ : S ⟶ T) :
    toKernel S ≫ kernelMap φ = φ.τ₁ ≫ toKernel T :=
  kernel.lift_map S.f S.g S.zero T.f T.g T.zero
    φ.τ₁ φ.τ₂ φ.τ₃ φ.comm₁₂.symm φ.comm₂₃.symm

variable (G)

/-- The actual cokernel map for a mapped morphism of short complexes. -/
def mappedCokernelMap (φ : S ⟶ T) :
    cokernel (G.map (toKernel S)) ⟶ cokernel (G.map (toKernel T)) :=
  cokernel.map _ _ (G.map φ.τ₁) (G.map (kernelMap φ)) (by
    simp only [← G.map_comp, toKernel_naturality])

/-- The explicit kernel and cokernel maps form native homology map data. -/
def mappedLeftHomologyMapData (φ : S ⟶ T) :
    ShortComplex.LeftHomologyMapData (G.mapShortComplex.map φ)
      (mappedLeftHomologyData G S) (mappedLeftHomologyData G T) where
  φK := G.map (kernelMap φ)
  φH := mappedCokernelMap G φ
  commi := by
    change G.map (kernelMap φ) ≫ G.map (kernel.ι T.g) =
      G.map (kernel.ι S.g) ≫ G.map φ.τ₂
    simp only [← G.map_comp, kernelMap, kernel.lift_ι]
  commf' := by
    exact (congrArg (fun f => f ≫ G.map (kernelMap φ))
      (mappedLeftHomologyData_f' G S)).trans
        (((G.map_comp (toKernel S) (kernelMap φ)).symm.trans
          ((congrArg G.map (toKernel_naturality φ)).trans
            (G.map_comp φ.τ₁ (toKernel T)))).trans
          (congrArg (fun f => G.map φ.τ₁ ≫ f) (mappedLeftHomologyData_f' G T)).symm)
  commπ := by
    change cokernel.π _ ≫ mappedCokernelMap G φ = _
    exact cokernel.π_desc _ _ _

/-- The identification respects the actual induced maps, not just
isomorphism classes of groups. -/
@[reassoc] theorem shortCokernelIsoHomology_hom_naturality (φ : S ⟶ T) :
    mappedCokernelMap G φ ≫ (shortCokernelIsoHomology G T).hom =
      (shortCokernelIsoHomology G S).hom ≫
        ShortComplex.homologyMap (G.mapShortComplex.map φ) := by
  let hS := mappedLeftHomologyData G S
  let hT := mappedLeftHomologyData G T
  let γ := mappedLeftHomologyMapData G φ
  change γ.φH ≫ hT.homologyIso.inv = hS.homologyIso.inv ≫ _
  exact ((congrArg (fun f => hS.homologyIso.inv ≫ f) γ.homologyMap_eq).trans
    (hS.homologyIso.inv_hom_id_assoc (γ.φH ≫ hT.homologyIso.inv))).symm

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt.CycleCokernel

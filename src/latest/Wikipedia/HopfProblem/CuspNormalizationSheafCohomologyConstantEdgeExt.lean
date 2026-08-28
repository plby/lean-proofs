import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExtNaturality

/-!
# The genuine degree-two edge kernel of a length-two resolution

For an actual augmented resolution `F → A → B → D`, the composite of
the two genuine Ext connecting maps lands in the literal kernel of
`Ext²(P,F) → Ext²(P,A)`. It is onto that kernel when `Ext¹(P,B)=0`.
Its kernel is the last degree-zero image when `Ext¹(P,A)=0`.

No vanishing of `Ext²(P,A)` is used or asserted.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

open SheafCohomologyResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (R : AugmentedResolution C) (P : C)

/-- The actual edge map induced by the augmentation, with its original Ext target. -/
def extEdgeMap : AddCommGrpCat.of (Ext P R.F 2) ⟶
    AddCommGrpCat.of (Ext P R.complex.X₁ 2) :=
  (extFunctorObj P 2).map R.ι

theorem connectingTwo_edge_zero :
    AddCommGrpCat.ofHom (R.connectingTwo P) ≫ extEdgeMap R P = 0 := by
  have h : AddCommGrpCat.ofHom (connecting P R.first_shortExact 1) ≫
      extEdgeMap R P = 0 :=
    (Ext.covariantSequence_exact P R.first_shortExact 1 2 rfl).zero 2
  change (AddCommGrpCat.ofHom (connecting P R.second_shortExact 0) ≫
    AddCommGrpCat.ofHom (connecting P R.first_shortExact 1)) ≫ extEdgeMap R P = 0
  exact Eq.trans (Category.assoc _ _ _)
    (Eq.trans (congrArg (fun f => AddCommGrpCat.ofHom
      (connecting P R.second_shortExact 0) ≫ f) h) comp_zero)

/-- The genuine double connecting map, factored through the literal edge kernel. -/
def extEdgeConnecting : AddCommGrpCat.of (Ext P R.complex.X₃ 0) ⟶
    kernel (extEdgeMap R P) :=
  kernel.lift (extEdgeMap R P) (AddCommGrpCat.ofHom (R.connectingTwo P))
    (connectingTwo_edge_zero R P)

@[reassoc] theorem extEdgeConnecting_ι :
    extEdgeConnecting R P ≫ kernel.ι (extEdgeMap R P) =
      AddCommGrpCat.ofHom (R.connectingTwo P) :=
  kernel.lift_ι _ _ _

theorem extEdgeConnecting_exact [Subsingleton (Ext P R.complex.X₁ 1)] :
    Function.Exact ((extFunctorObj P 0).map R.complex.g) (extEdgeConnecting R P) := by
  have hi : Function.Injective (kernel.ι (extEdgeMap R P)) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  intro x
  constructor
  · intro hx
    apply (R.connectingTwo_exact P x).mp
    exact Eq.trans (ConcreteCategory.congr_hom (extEdgeConnecting_ι R P) x).symm
      (Eq.trans (congrArg (kernel.ι (extEdgeMap R P)) hx) (map_zero _))
  · intro hx
    apply hi
    exact Eq.trans (ConcreteCategory.congr_hom (extEdgeConnecting_ι R P) x)
      (Eq.trans ((R.connectingTwo_exact P x).mpr hx) (map_zero _).symm)

/-- Surjectivity onto the edge kernel needs only degree-one acyclicity
of the second resolution term, not degree-two acyclicity of the first. -/
theorem extEdgeConnecting_surjective [Subsingleton (Ext P R.complex.X₂ 1)] :
    Function.Surjective (extEdgeConnecting R P) := by
  have hi : Function.Injective (kernel.ι (extEdgeMap R P)) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  intro a
  let y : Ext P R.F 2 := kernel.ι (extEdgeMap R P) a
  have hy : y.comp (Ext.mk₀ R.ι) (add_zero 2) = 0 :=
    ConcreteCategory.congr_hom (kernel.condition (extEdgeMap R P)) a
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ P R.first_shortExact y hy (n₀ := 1) rfl
  obtain ⟨d, hd⟩ := connecting_surjective P R.second_shortExact 0 z
  refine ⟨d, ?_⟩
  apply hi
  exact Eq.trans (ConcreteCategory.congr_hom (extEdgeConnecting_ι R P) d)
    (Eq.trans (congrArg (connecting P R.first_shortExact 1) hd) hz)

theorem extEdgeConnecting_epi [Subsingleton (Ext P R.complex.X₂ 1)] :
    Epi (extEdgeConnecting R P) :=
  (AddCommGrpCat.epi_iff_surjective _).mpr (extEdgeConnecting_surjective R P)

/-- The actual last degree-zero map followed by the actual edge connecting map. -/
def extEdgeCokernelComplex : ShortComplex AddCommGrpCat.{w} :=
  ShortComplex.mk ((extFunctorObj P 0).map R.complex.g) (extEdgeConnecting R P) (by
    apply (cancel_mono (kernel.ι (extEdgeMap R P))).mp
    exact Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun f => (extFunctorObj P 0).map R.complex.g ≫ f)
        (extEdgeConnecting_ι R P))
        (Eq.trans (R.extTwoCokernelComplex P).zero zero_comp.symm)))

theorem extEdgeCokernelComplex_exact [Subsingleton (Ext P R.complex.X₁ 1)] :
    (extEdgeCokernelComplex R P).Exact :=
  (ShortComplex.ab_exact_iff_function_exact _).mpr (extEdgeConnecting_exact R P)

/-- Genuine edge-kernel comparison. Only the two actual degree-one
term vanishings are assumed; the first term's Ext² is retained. -/
def extEdgeIso [Subsingleton (Ext P R.complex.X₁ 1)]
    [Subsingleton (Ext P R.complex.X₂ 1)] :
    kernel (extEdgeMap R P) ≅ cokernel (R.extZeroComplex P).g := by
  have : Epi (extEdgeCokernelComplex R P).g := extEdgeConnecting_epi R P
  exact IsColimit.coconePointUniqueUpToIso (extEdgeCokernelComplex_exact R P).gIsCokernel
    (colimit.isColimit (parallelPair (R.extZeroComplex P).g 0))

/-- The comparison retains the literal double-connecting representatives. -/
theorem extEdgeIso_connecting [Subsingleton (Ext P R.complex.X₁ 1)]
    [Subsingleton (Ext P R.complex.X₂ 1)] :
    extEdgeConnecting R P ≫ (extEdgeIso R P).hom = cokernel.π (R.extZeroComplex P).g := by
  have : Epi (extEdgeCokernelComplex R P).g := extEdgeConnecting_epi R P
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (extEdgeCokernelComplex_exact R P).gIsCokernel
    (colimit.isColimit (parallelPair (R.extZeroComplex P).g 0)) WalkingParallelPair.one

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

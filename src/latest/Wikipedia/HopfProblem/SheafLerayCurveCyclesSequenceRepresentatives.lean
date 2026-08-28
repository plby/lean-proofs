import Wikipedia.HopfProblem.SheafLerayCurveCyclesSequence

/-!
# The actual cycles Leray edge map on native representatives

The edge map sends the native Hom-complex homology class of a morphism
`A → Zⁿ⁺¹(K)` to its composition with the original homology quotient
`Zⁿ⁺¹(K) → Hⁿ⁺¹(K)`. The proof keeps the actual cycles-kernel and
homology-cokernel comparisons and cancels only their genuine isomorphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

open SheafLerayLowDegrees.Abstract

private theorem iso_comp_inv {D : Type*} [Category D] {A B C T : D}
    (e : A ≅ B) (d : B ≅ C) (f : A ⟶ T) (g : B ⟶ T)
    (h : e.hom ≫ g = f) : (e ≪≫ d).inv ≫ f = d.inv ≫ g := by
  rw [← h]
  simp only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) (K : CochainComplex C ℕ) (n : ℕ)

/-- The genuine edge map is the native outgoing Hom-cokernel map under
the original Hom-complex homology comparison. -/
theorem cyclesEdgeMap_eq_homFromOpcycles :
    cyclesEdgeMap A K n = (cyclesHomMiddleIso A K n).inv ≫
      (cyclesHomAugmentedComplex A K n).fromOpcycles :=
  iso_comp_inv (extZeroHomOpcyclesIso A (cyclesComplex K n))
    (cyclesHomMiddleIso A K n)
    (Core.edgeMap A (cyclesResolution K n) ≫ (extZeroHomIso A (K.homology (n + 1))).hom)
    (cyclesHomAugmentedComplex A K n).fromOpcycles
    (extZeroHomOpcyclesIso_hom_fromOpcycles A (cyclesComplex K n))

/-- The exact native forward formula on an original Hom-cycle representative. -/
theorem cyclesEdgeMap_homologyClass (z : A ⟶ K.cycles (n + 1)) :
    cyclesEdgeMap A K n ((homComplex A K).homologyπ (n + 1)
      ((homCyclesIso A K (n + 1)).hom z)) = z ≫ K.homologyπ (n + 1) := by
  have h₀ := ConcreteCategory.congr_hom (cyclesEdgeMap_eq_homFromOpcycles A K n)
    ((homComplex A K).homologyπ (n + 1) ((homCyclesIso A K (n + 1)).hom z))
  have h₁ := ConcreteCategory.congr_hom
    (homCyclesIso_hom_homologyπ_cyclesHomMiddleIso_inv A K n) z
  have h₂ := ConcreteCategory.congr_hom
    (cyclesHomAugmentedComplex A K n).p_fromOpcycles z
  exact h₀.trans
    ((congrArg (cyclesHomAugmentedComplex A K n).fromOpcycles h₁).trans h₂)

/-- The native cycle-class map followed by the edge map is the original
postcomposition map through the native homology quotient. -/
@[reassoc] theorem homCyclesIso_hom_homologyπ_cyclesEdgeMap :
    (homCyclesIso A K (n + 1)).hom ≫ (homComplex A K).homologyπ (n + 1) ≫
        cyclesEdgeMap A K n =
      (preadditiveCoyoneda.obj (op A)).map (K.homologyπ (n + 1)) := by
  apply AddCommGrpCat.ext
  intro z
  exact cyclesEdgeMap_homologyClass A K n z

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract

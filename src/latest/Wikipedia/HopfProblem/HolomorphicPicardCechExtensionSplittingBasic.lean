import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSheafBasic

/-!
# The actual extension splitting furnished by a Čech solution

An actual solution `b` of the additive Čech cocycle gives compatible
extension data in every integer degree by multiplying the restrictions
of `b` by that integer. This defines a genuine presheaf splitting, whose
actual sheafification splits the degree projection.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- The literal extension section furnished by integer multiples of a
given actual Čech solution. -/
def solutionSectionHom (b : ∀ i : ι, Section F (U i))
    (hb : ∀ i j : ι, res F inf_le_left (b i) - res F inf_le_right (b j) = c.value i j)
    (V : Opens X) : ULift.{0} ℤ →+ ExtensionSection c V where
  toFun n := ⟨⟨n, fun i => n.down • res F inf_le_right (b i)⟩, by
    intro i j
    change res F _ (n.down • res F _ (b i)) -
      res F _ (n.down • res F _ (b j)) = n.down • res F _ (c.value i j)
    rw [map_zsmul, map_zsmul, res_trans, res_trans, ← smul_sub]
    apply congrArg (fun s => n.down • s)
    have h := congrArg (res F (V := V ⊓ (U i ⊓ U j)) inf_le_right) (hb i j)
    simpa only [map_sub, res_trans] using h⟩
  map_zero' := by
    apply extensionSection_ext
    · rfl
    · intro i
      exact zero_zsmul _
  map_add' n m := by
    apply extensionSection_ext
    · rfl
    · intro i
      exact add_zsmul _ _ _

@[simp] theorem solutionSectionHom_degree (b : ∀ i : ι, Section F (U i))
    (hb : ∀ i j : ι, res F inf_le_left (b i) - res F inf_le_right (b j) = c.value i j)
    (V : Opens X) (n : ULift.{0} ℤ) :
    degreeHom c V (solutionSectionHom c b hb V n) = n := rfl

@[simp] theorem solutionSectionHom_coordinate (b : ∀ i : ι, Section F (U i))
    (hb : ∀ i j : ι, res F inf_le_left (b i) - res F inf_le_right (b j) = c.value i j)
    (V : Opens X) (n : ULift.{0} ℤ) (i : ι) :
    coordinateHom c V i (solutionSectionHom c b hb V n) =
      n.down • res F inf_le_right (b i) := rfl

/-- The constructed integer-degree sections commute with actual
restriction, before any sheafification. -/
theorem restrict_solutionSectionHom (b : ∀ i : ι, Section F (U i))
    (hb : ∀ i j : ι, res F inf_le_left (b i) - res F inf_le_right (b j) = c.value i j)
    {V W : Opens X} (hWV : W ≤ V) (n : ULift.{0} ℤ) :
    restrict c hWV (solutionSectionHom c b hb V n) = solutionSectionHom c b hb W n := by
  apply extensionSection_ext
  · rfl
  · intro i
    change res F _ (n.down • res F _ (b i)) = n.down • res F _ (b i)
    rw [map_zsmul, res_trans]

/-- A Čech solution gives a genuine splitting of the constant-degree
presheaf map. -/
def solutionSplittingPre (b : ∀ i : ι, Section F (U i))
    (hb : ∀ i j : ι, res F inf_le_left (b i) - res F inf_le_right (b j) = c.value i j) :
    degreePresheaf X ⟶ presheaf c where
  app V := AddCommGrpCat.ofHom (solutionSectionHom c b hb V.unop)
  naturality V W f := by
    apply ConcreteCategory.hom_ext
    intro n
    exact (restrict_solutionSectionHom c b hb (leOfHom f.unop) n).symm

@[simp] theorem solutionSplittingPre_app (b : ∀ i : ι, Section F (U i))
    (hb : ∀ i j : ι, res F inf_le_left (b i) - res F inf_le_right (b j) = c.value i j)
    (V : Opens X) (n : ULift.{0} ℤ) :
    (solutionSplittingPre c b hb).app (op V) n = solutionSectionHom c b hb V n := rfl

theorem solutionSplittingPre_projectionPre (b : ∀ i : ι, Section F (U i))
    (hb : ∀ i j : ι, res F inf_le_left (b i) - res F inf_le_right (b j) = c.value i j) :
    solutionSplittingPre c b hb ≫ projectionPre c = 𝟙 (degreePresheaf X) := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro n
  rfl

/-- Genuine sheafification of the constructed presheaf splitting. -/
def splittingOfSolution (b : ∀ i : ι, Section F (U i))
    (hb : ∀ i j : ι, res F inf_le_left (b i) - res F inf_le_right (b j) = c.value i j) :
    degreeSheaf X ⟶ extensionSheaf c where
  hom := CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
    (solutionSplittingPre c b hb)

/-- The constructed actual sheaf morphism is a right inverse of the
original degree projection. -/
theorem splittingOfSolution_projection (b : ∀ i : ι, Section F (U i))
    (hb : ∀ i j : ι, res F inf_le_left (b i) - res F inf_le_right (b j) = c.value i j) :
    splittingOfSolution c b hb ≫ projection c = 𝟙 (degreeSheaf X) := by
  apply CategoryTheory.Sheaf.hom_ext
  change CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (solutionSplittingPre c b hb) ≫
      CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (projectionPre c) = 𝟙 _
  rw [← CategoryTheory.sheafifyMap_comp, solutionSplittingPre_projectionPre,
    CategoryTheory.sheafifyMap_id]

/-- Actual Čech solvability gives an actual splitting, without any
covering or local-representative premise. -/
theorem exists_splitting_of_solvable (hc : c.Solvable) :
    ∃ σ : degreeSheaf X ⟶ extensionSheaf c, σ ≫ projection c = 𝟙 (degreeSheaf X) := by
  obtain ⟨b, hb⟩ := hc
  exact ⟨splittingOfSolution c b hb, splittingOfSolution_projection c b hb⟩

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

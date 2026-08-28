import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalPatchLocal
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSheafBasic

/-!
# Global sections have original singular cochain representatives

On a normal paracompact space, a closed locally finite refinement allows
the actual local cochain representatives of a sheafified section to be
patched. The resulting object is a cochain on the original singular
chains of the original space; its image under the native sheafification
unit is the given global section.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ)

/-- The original global singular cochain followed by the actual unit on
the top open. No cohomology is redefined by this map. -/
def globalCochainUnit : AddCommGrpCat.of (Cochains X A n) ⟶
    (cochainSheaf X A n).obj.obj (op ⊤) :=
  (singularPullback A
    (⟨Subtype.val, continuous_subtype_val⟩ : C((⊤ : Opens X), X))).f n ≫
      (cochainSheafUnit X A n).app (op ⊤)

@[simp]
theorem globalCochainUnit_apply (φ : Cochains X A n) :
    globalCochainUnit X A n φ =
      (cochainSheafUnit X A n).app (op ⊤) (restrictGlobalCochain A n φ ⊤) := rfl

/-- Naturality of the native unit on actual open restrictions. -/
theorem cochainSheafUnit_restrict {U V : Opens X} (i : U ⟶ V)
    (t : Cochains V A n) :
    (cochainSheafUnit X A n).app (op U) ((cochainPresheaf X A n).map i.op t) =
      (cochainSheaf X A n).obj.map i.op ((cochainSheafUnit X A n).app (op V) t) :=
  congrArg (fun l => l t) ((cochainSheafUnit X A n).naturality i.op)

/-- Restriction of the global unit is the unit of the literal restricted
global cochain. -/
theorem globalCochainUnit_restrict (φ : Cochains X A n) (U : Opens X) :
    (cochainSheaf X A n).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      (globalCochainUnit X A n φ) =
        (cochainSheafUnit X A n).app (op U) (restrictGlobalCochain A n φ U) := by
  exact (cochainSheafUnit_restrict X A n (homOfLE le_top)
    (restrictGlobalCochain A n φ ⊤)).symm.trans
      (congrArg ((cochainSheafUnit X A n).app (op U))
        (restrictGlobalCochain_restrict A n φ (homOfLE le_top)))

/-- Germs of the global comparison are germs of actual restricted cochains. -/
theorem globalCochainUnit_germ (φ : Cochains X A n) (U : Opens X)
    (x : X) (hx : x ∈ U) :
    (cochainSheaf X A n).presheaf.germ ⊤ x (by trivial) (globalCochainUnit X A n φ) =
      (cochainSheaf X A n).presheaf.germ U x hx
        ((cochainSheafUnit X A n).app (op U) (restrictGlobalCochain A n φ U)) := by
  exact ((cochainSheaf X A n).presheaf.germ_res_apply (homOfLE le_top) x hx
    (globalCochainUnit X A n φ)).symm.trans
      (congrArg ((cochainSheaf X A n).presheaf.germ U x hx)
        (globalCochainUnit_restrict X A n φ U))

/-- Every global section of the genuine sheaf of cochains is represented
by a cochain on the original space, for arbitrary abelian coefficients. -/
theorem globalCochainUnit_surjective [NormalSpace X] [ParacompactSpace X] :
    Function.Surjective (globalCochainUnit X A n) := by
  classical
  intro s
  choose U hU t hxU ht using fun x : X =>
    Sheafification.exists_local_representative
      (cochainPresheaf X A n) ⊤ s x (by trivial)
  let R : ClosedRefinement U :=
    (exists_closedRefinement U (fun x => ⟨x, hxU x⟩)).some
  refine ⟨patchedCochain A n U R t, ?_⟩
  apply TopCat.Presheaf.section_ext (cochainSheaf X A n) ⊤
  intro x hx
  let j := R.index x
  have hxj := R.mem_support_index x
  have hlocal : ∀ i, x ∈ R.support i →
      ∃ V : Opens X, x ∈ V ∧ ∃ (f : V ⟶ U i) (g : V ⟶ U j),
        (cochainPresheaf X A n).map f.op (t i) =
          (cochainPresheaf X A n).map g.op (t j) := by
    intro i hi
    apply Sheafification.exists_restriction_eq_of_germ_unit_eq
      (cochainPresheaf X A n) (U i) (U j) x
      (R.subordinate i hi) (R.subordinate j hxj) (t i) (t j)
    rw [ht i, ht j]
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  obtain ⟨W, hxW, f, hf⟩ :=
    exists_neighborhood_patchedCochain_eq A n U R t x j hxj hlocal
  calc
    (cochainSheaf X A n).presheaf.germ ⊤ x hx
        (globalCochainUnit X A n (patchedCochain A n U R t)) =
      (cochainSheaf X A n).presheaf.germ W x hxW
        ((cochainSheafUnit X A n).app (op W)
          (restrictGlobalCochain A n (patchedCochain A n U R t) W)) :=
      globalCochainUnit_germ X A n _ W x hxW
    _ = (cochainSheaf X A n).presheaf.germ W x hxW
        ((cochainSheafUnit X A n).app (op W)
          ((cochainPresheaf X A n).map f.op (t j))) := by rw [hf]
    _ = (cochainSheaf X A n).presheaf.germ (U j) x (R.subordinate j hxj)
        ((cochainSheafUnit X A n).app (op (U j)) (t j)) := by
      rw [cochainSheafUnit_restrict, TopCat.Presheaf.germ_res_apply]
    _ = (cochainSheaf X A n).presheaf.germ ⊤ x hx s := by
      exact (congrArg ((cochainSheaf X A n).presheaf.germ (U j) x
        (R.subordinate j hxj)) (ht j)).trans
          ((cochainSheaf X A n).presheaf.germ_res_apply
            (homOfLE (hU j)) x (R.subordinate j hxj) s)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison

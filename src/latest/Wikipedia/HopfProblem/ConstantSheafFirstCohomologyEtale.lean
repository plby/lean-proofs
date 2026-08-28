import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyEtaleSections
import Mathlib.Topology.Homotopy.Lifting

/-!
# Global continuation through the actual étale covering

For a sheaf whose actual étale projection is a covering map, a prescribed
stalk element extends to an original global section on a simply connected,
locally path-connected base.  The proof lifts the identity of the base
through the covering and then glues its local original representatives.
The covering hypothesis can in particular be discharged by local
bijectivity of the original germ maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Function

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Etale

universe u v w

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C]
  {CC : C → Type u} {FC : C → C → Type w}
  [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
  [HasColimits.{u} C] [PreservesFilteredColimits (forget C)]
  [HasLimits C] [PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]
  [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]

/-- Every prescribed actual stalk element extends to an original global
section when the actual étale projection is a covering of a simply
connected, locally path-connected base. -/
theorem exists_global_section_with_germ_of_isCoveringMap (F : TopCat.Sheaf C X)
    (hc : IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := F.presheaf)))
    (x₀ : X) (g₀ : ToType (F.presheaf.stalk x₀)) :
    ∃ s : ToType (F.presheaf.obj (op ⊤)), F.presheaf.germ ⊤ x₀ trivial s = g₀ := by
  obtain ⟨σ, hσ, -⟩ := hc.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀ ⟨x₀, g₀⟩ rfl
  have hbase (x : X) : (σ x).base = x := congrFun hσ.2 x
  refine ⟨sectionOfEtaleSection F σ hbase, ?_⟩
  have hg := (sectionOfEtaleSection_germ F σ hbase x₀).trans hσ.1
  simpa only [sectionGerm, TopCat.Presheaf.EtaleSpace.mk.injEq, heq_eq_eq, true_and] using hg

/-- Local bijectivity of the original germ maps supplies the genuine
covering-space hypothesis for continuation. -/
theorem exists_global_section_with_germ_of_germ_bijective (F : TopCat.Sheaf C X)
    (hbij : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∀ (y : X) (hy : y ∈ U), Bijective (F.presheaf.germ U y hy))
    (x₀ : X) (g₀ : ToType (F.presheaf.stalk x₀)) :
    ∃ s : ToType (F.presheaf.obj (op ⊤)), F.presheaf.germ ⊤ x₀ trivial s = g₀ :=
  exists_global_section_with_germ_of_isCoveringMap F
    (TopCat.Presheaf.EtaleSpace.isCoveringMap_base hbij) x₀ g₀

/-- On this base, local germ bijectivity implies surjectivity of every
global-section germ map, not just local existence. -/
theorem global_germ_surjective_of_germ_bijective (F : TopCat.Sheaf C X)
    (hbij : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∀ (y : X) (hy : y ∈ U), Bijective (F.presheaf.germ U y hy)) (x₀ : X) :
    Surjective (F.presheaf.germ ⊤ x₀ trivial) :=
  exists_global_section_with_germ_of_germ_bijective F hbij x₀

/-- An inhabited stalk gives an original global section. -/
theorem nonempty_global_sections_of_isCoveringMap (F : TopCat.Sheaf C X)
    (hc : IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := F.presheaf)))
    (x₀ : X) (h₀ : Nonempty (ToType (F.presheaf.stalk x₀))) :
    Nonempty (ToType (F.presheaf.obj (op ⊤))) := by
  obtain ⟨g₀⟩ := h₀
  obtain ⟨s, -⟩ := exists_global_section_with_germ_of_isCoveringMap F hc x₀ g₀
  exact ⟨s⟩

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Etale

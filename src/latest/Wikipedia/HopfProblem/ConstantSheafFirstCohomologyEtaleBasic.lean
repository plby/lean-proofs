import Mathlib.Topology.Sheaves.EtaleSpace

/-!
# Local sections of the actual étale space of a presheaf

The points of the étale space below use the original colimit stalks.  A
continuous section of its projection is locally the germ of an original
presheaf section.  This construction works in any concrete category with
the colimit hypotheses used by Mathlib's étale space.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Filter Function Set
open scoped Topology

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Etale

universe u v w

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C]
  {CC : C → Type u} {FC : C → C → Type w}
  [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
  [HasColimits.{u} C]

/-- The actual germ of a section, as a point of the étale space. -/
def sectionGerm (F : TopCat.Presheaf C X) (U : Opens X)
    (s : ToType (F.obj (op U))) (x : U) : F.EtaleSpace :=
  ⟨x.1, F.germ U x.1 x.2 s⟩

@[simp]
theorem sectionGerm_base (F : TopCat.Presheaf C X) (U : Opens X)
    (s : ToType (F.obj (op U))) (x : U) :
    (sectionGerm F U s x).base = x.1 := rfl

/-- Equality of étale points over a fixed point is equality of their genuine
stalk elements. -/
theorem sectionGerm_eq_iff (F : TopCat.Presheaf C X) (U V : Opens X)
    (s : ToType (F.obj (op U))) (t : ToType (F.obj (op V)))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    sectionGerm F U s ⟨x, hxU⟩ = sectionGerm F V t ⟨x, hxV⟩ ↔
      F.germ U x hxU s = F.germ V x hxV t := by
  simp only [sectionGerm, TopCat.Presheaf.EtaleSpace.mk.injEq, heq_eq_eq, true_and]

variable [PreservesFilteredColimits (forget C)]

/-- Continuity of a section of the étale projection gives representatives
on an actual open neighborhood, with equality of germs at every point. -/
theorem etaleSection_localGerms (F : TopCat.Presheaf C X)
    (σ : C(X, F.EtaleSpace)) (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    ∃ (U : Opens X) (_hx : x ∈ U) (s : ToType (F.obj (op U))),
      ∀ (y : X) (hy : y ∈ U), σ y = sectionGerm F U s ⟨y, hy⟩ := by
  obtain ⟨U, hxU, s, hs⟩ :=
    TopCat.Presheaf.EtaleSpace.exists_section_of_tendsto
      (σ.continuous.continuousAt (x := x))
  have hvalues : ∀ᶠ y in 𝓝 x, ∃ hy : y ∈ U,
      σ y = sectionGerm F U s ⟨y, hy⟩ := by
    filter_upwards [hs] with y hy
    obtain ⟨hyU, hg⟩ := hy
    refine ⟨hσ y ▸ hyU, ?_⟩
    calc
      σ y = sectionGerm F U s ⟨(σ y).base, hyU⟩ := by
        change σ y = ⟨(σ y).base, F.germ U (σ y).base hyU s⟩
        rw [← hg]
      _ = sectionGerm F U s ⟨y, hσ y ▸ hyU⟩ :=
        congrArg (sectionGerm F U s) (Subtype.ext (hσ y))
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.mp hvalues
  let W : Opens X := ⟨V, hVo⟩
  have hWU : W ≤ U := fun y hy => (hV y hy).choose
  let i : W ⟶ U := homOfLE hWU
  refine ⟨W, hxV, F.map i.op s, ?_⟩
  intro y hy
  have hg := (hV y hy).choose_spec
  convert hg using 1
  dsimp only [sectionGerm]
  rw [F.germ_res_apply]

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Etale

import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSheafBasic
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Actual local kernel lifts and exactness after sheafification

An original presheaf element whose differential has zero germ becomes an
actual cocycle after restriction. Local lifts of such cocycles then prove
exactness on original colimit stalks. The native sheafification unit is an
isomorphism on those stalks, transporting this exactness to the original
sheafification of the short complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalExact

variable {X : TopCat.{0}}

/-- Actual local lifts of section kernels prove exactness on the
original presheaf stalks. -/
theorem presheaf_stalk_exact_of_local_kernels
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{0} X))
    (h : ∀ (U : Opens X) (x : X) (_hx : x ∈ U) (s : S.X₂.obj (op U)),
      S.g.app (op U) s = 0 →
      ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V) (t : S.X₁.obj (op V)),
        S.f.app (op V) t = S.X₂.map (homOfLE hVU).op s)
    (x : X) : (S.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat x)).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro a ha
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.exists_germ_eq a
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g
    (S.X₂.germ U x hxU s) = 0 at ha
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ha
  have hz : S.X₃.germ U x hxU (S.g.app (op U) s) = S.X₃.germ U x hxU 0 :=
    ha.trans (S.X₃.germ U x hxU).hom.map_zero.symm
  obtain ⟨V, hxV, iVU, jVU, he⟩ := S.X₃.germ_eq x hxU hxU _ _ hz
  have hv : S.g.app (op V) (S.X₂.map iVU.op s) = 0 :=
    ((ConcreteCategory.congr_hom (S.g.naturality iVU.op) s).trans he).trans
      (S.X₃.map jVU.op).hom.map_zero
  obtain ⟨W, hWV, hxW, t, ht⟩ := h V x hxV (S.X₂.map iVU.op s) hv
  refine ⟨S.X₁.germ W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f
    (S.X₁.germ W x hxW t) = S.X₂.germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht,
    S.X₂.germ_res_apply, S.X₂.germ_res_apply]

/-- The native unit gives an isomorphism from the original stalk short
complex to the stalk short complex of its original sheafification. -/
def sheafificationStalkIso
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{0} X)) (x : X) :
    S.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat x) ≅
      (S.map (cochainSheafification X)).map
        (TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x) := by
  let K := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let e (P : TopCat.Presheaf AddCommGrpCat.{0} X) :
      K.obj P ≅ K.obj (Sheafification.sheaf P).obj :=
    @asIso AddCommGrpCat.{0} _ _ _ (K.map (Sheafification.unit P))
      (Sheafification.unit_stalk_isIso P x)
  refine ShortComplex.isoMk
    (e S.X₁) (e S.X₂) (e S.X₃) ?_ ?_
  · change K.map (Sheafification.unit S.X₁) ≫
        K.map ((cochainSheafification X).map S.f).hom =
      K.map S.f ≫ K.map (Sheafification.unit S.X₂)
    rw [← K.map_comp, ← K.map_comp]
    exact congrArg K.map
      ((sheafificationAdjunction (Opens.grothendieckTopology X)
        AddCommGrpCat.{0}).unit.naturality S.f).symm
  · change K.map (Sheafification.unit S.X₂) ≫
        K.map ((cochainSheafification X).map S.g).hom =
      K.map S.g ≫ K.map (Sheafification.unit S.X₃)
    rw [← K.map_comp, ← K.map_comp]
    exact congrArg K.map
      ((sheafificationAdjunction (Opens.grothendieckTopology X)
        AddCommGrpCat.{0}).unit.naturality S.g).symm

/-- Local original section-kernel lifts prove exactness of the genuine
sheafification, using only its actual unit stalk isomorphisms. -/
theorem sheafify_exact_of_local_kernels
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{0} X))
    (h : ∀ (U : Opens X) (x : X) (_hx : x ∈ U) (s : S.X₂.obj (op U)),
      S.g.app (op U) s = 0 →
      ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V) (t : S.X₁.obj (op V)),
        S.f.app (op V) t = S.X₂.map (homOfLE hVU).op s) :
    (S.map (cochainSheafification X)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  exact ShortComplex.exact_of_iso (sheafificationStalkIso S x)
    (presheaf_stalk_exact_of_local_kernels S h x)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalExact

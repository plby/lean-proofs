import Wikipedia.HopfProblem.CuspNormalizationSheafBiproduct

/-!
# Passing actual local differential equations to exact sheaves

This file uses actual section representatives and actual stalk maps.
Pointwise section-kernel lifting implies exactness by shrinking a
representative whose image has zero germ. Actual local section lifting
implies epimorphy by representing each target germ. No analytic
exactness or cohomology comparison is assumed here.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DolbeaultLocal

open CuspNormalization.SheafBiproduct

variable {X : TopCat.{0}}

/-- Lifting the actual section kernels gives exactness of the actual
sheaf complex, via the genuine stalk criterion. -/
theorem exact_of_section_kernels (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (h : ∀ (U : Opens X) (s : S.X₂.presheaf.obj (op U)), S.g.hom.app (op U) s = 0 →
      ∃ t : S.X₁.presheaf.obj (op U), S.f.hom.app (op U) t = s) : S.Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mpr
  intro x
  let K := stalkFunctor X x
  apply (ShortComplex.ab_exact_iff_function_exact (S.map K)).mpr
  change Function.Exact (K.map S.f) (K.map S.g)
  intro a
  constructor
  · intro ha
    obtain ⟨U, hxU, s, rfl⟩ := S.X₂.presheaf.exists_germ_eq a
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
      (S.X₂.presheaf.germ U x hxU s) = 0 at ha
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ha
    have hz : S.X₃.presheaf.germ U x hxU (S.g.hom.app (op U) s) =
        S.X₃.presheaf.germ U x hxU 0 :=
      ha.trans (S.X₃.presheaf.germ U x hxU).hom.map_zero.symm
    obtain ⟨V, hxV, iVU, jVU, he⟩ := S.X₃.presheaf.germ_eq x hxU hxU _ _ hz
    have hv : S.g.hom.app (op V) (S.X₂.presheaf.map iVU.op s) = 0 :=
      ((ConcreteCategory.congr_hom (S.g.hom.naturality iVU.op) s).trans he).trans
        (S.X₃.presheaf.map jVU.op).hom.map_zero
    obtain ⟨t, ht⟩ := h V (S.X₂.presheaf.map iVU.op s) hv
    refine ⟨S.X₁.presheaf.germ V x hxV t, ?_⟩
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
      (S.X₁.presheaf.germ V x hxV t) = S.X₂.presheaf.germ U x hxU s
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht]
    exact S.X₂.presheaf.germ_res_apply iVU x hxV s
  · rintro ⟨t, rfl⟩
    have hz : K.map S.f ≫ K.map S.g = 0 :=
      (K.map_comp _ _).symm.trans ((congrArg K.map S.zero).trans (K.map_zero _ _))
    exact ConcreteCategory.congr_hom hz t

/-- Surjectivity of each actual stalk map implies epimorphy of the
actual additive sheaf morphism. -/
theorem epi_of_stalk_surjective {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G)
    (h : ∀ x : X, Function.Surjective ((stalkFunctor X x).map f)) : Epi f := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
    ShortComplex.mk f (0 : G ⟶ 0) (comp_zero)
  apply (S.exact_iff_epi rfl).mp
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mpr
  intro x
  let K := stalkFunctor X x
  have hz : (S.map K).g = 0 := K.map_zero _ _
  apply ((S.map K).exact_iff_epi hz).mpr
  exact ConcreteCategory.epi_of_surjective _ (h x)

/-- Actual local section lifts represent preimages of every actual
target germ. The smaller open set remains part of the construction. -/
theorem stalk_surjective_of_local_section_lifts
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G)
    (h : ∀ (U : Opens X) (x : X) (_hx : x ∈ U) (s : G.presheaf.obj (op U)),
      ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V) (t : F.presheaf.obj (op V)),
        f.hom.app (op V) t = G.presheaf.map (homOfLE hVU).op s)
    (x : X) : Function.Surjective ((stalkFunctor X x).map f) := by
  intro a
  obtain ⟨U, hxU, s, rfl⟩ := G.presheaf.exists_germ_eq a
  obtain ⟨V, hVU, hxV, t, ht⟩ := h U x hxU s
  refine ⟨F.presheaf.germ V x hxV t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom
    (F.presheaf.germ V x hxV t) = G.presheaf.germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht]
  exact G.presheaf.germ_res_apply (homOfLE hVU) x hxV s

/-- Constructed local section lifts imply an actual epimorphism of sheaves. -/
theorem epi_of_local_section_lifts
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G)
    (h : ∀ (U : Opens X) (x : X) (_hx : x ∈ U) (s : G.presheaf.obj (op U)),
      ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V) (t : F.presheaf.obj (op V)),
        f.hom.app (op V) t = G.presheaf.map (homOfLE hVU).op s) : Epi f :=
  epi_of_stalk_surjective f (stalk_surjective_of_local_section_lifts f h)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DolbeaultLocal

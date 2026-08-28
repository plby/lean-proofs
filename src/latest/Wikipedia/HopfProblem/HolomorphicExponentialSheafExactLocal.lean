import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDolbeaultSheafExact

/-!
# Exactness from genuine local section-kernel lifts

A kernel element in an actual stalk is represented by a section whose
image vanishes after shrinking. A further constructed local lift then
represents a preimage in the first stalk. This criterion allows local
logarithms and locally constant integer representatives to prove genuine
exactness in the category of abelian sheaves.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

open CuspNormalization.SheafBiproduct

/-- Actual local kernel lifts imply exactness of the actual sheaf complex.
There is no surjectivity assertion about sections on the original open set. -/
theorem exact_of_local_section_kernels {X : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (h : ∀ (U : Opens X) (x : X) (_hx : x ∈ U)
      (s : S.X₂.presheaf.obj (op U)), S.g.hom.app (op U) s = 0 →
      ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V)
        (t : S.X₁.presheaf.obj (op V)),
        S.f.hom.app (op V) t = S.X₂.presheaf.map (homOfLE hVU).op s) :
    S.Exact := by
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
    obtain ⟨W, hxW, iWU, jWU, he⟩ := S.X₃.presheaf.germ_eq x hxU hxU _ _ hz
    have hw : S.g.hom.app (op W) (S.X₂.presheaf.map iWU.op s) = 0 :=
      ((ConcreteCategory.congr_hom (S.g.hom.naturality iWU.op) s).trans he).trans
        (S.X₃.presheaf.map jWU.op).hom.map_zero
    obtain ⟨V, hVW, hxV, t, ht⟩ := h W x hxW (S.X₂.presheaf.map iWU.op s) hw
    refine ⟨S.X₁.presheaf.germ V x hxV t, ?_⟩
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
      (S.X₁.presheaf.germ V x hxV t) = S.X₂.presheaf.germ U x hxU s
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht]
    exact (S.X₂.presheaf.germ_res_apply (homOfLE hVW) x hxV _).trans
      (S.X₂.presheaf.germ_res_apply iWU x hxW s)
  · rintro ⟨t, rfl⟩
    have hz : K.map S.f ≫ K.map S.g = 0 :=
      (K.map_comp _ _).symm.trans ((congrArg K.map S.zero).trans (K.map_zero _ _))
    exact ConcreteCategory.congr_hom hz t

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf

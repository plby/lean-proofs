import Wikipedia.HopfProblem.OrbitPairNativeSubdivisionNormalForms

/-!
# Ordinary and dual subdivision preserve monomorphisms

A monomorphism preserves nondegeneracy of the original carrier simplex.
It therefore sends normal cell parameters to normal cell parameters.
Uniqueness of those parameters proves injectivity in every degree of the
actual left Kan extension.
-/

noncomputable section

universe u

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters

open SubdivisionColimit SubdivisionSupport Subdivision

variable (A : SimplexCategory ⥤ SSet.{u}) (k : ℕ) {X Y : SSet.{u}}

def mapParameters (f : X ⟶ Y) (p : Parameters A X k) : Parameters A Y k :=
  ⟨⟨p.1.1, f.app (Opposite.op ⦋p.1.1⦌) p.1.2⟩, p.2⟩

theorem mapParameters_injective (f : X ⟶ Y) [Mono f] :
    Function.Injective (mapParameters A k f) := by
  rintro ⟨⟨n, x⟩, t⟩ ⟨⟨m, y⟩, v⟩ h
  have hdim : n = m := congrArg (fun p ↦ p.1.1) h
  subst m
  have hxy : f.app (Opposite.op ⦋n⦌) x = f.app (Opposite.op ⦋n⦌) y :=
    eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Sigma.fst h)).2
  have hxy' : x = y := (injective_of_mono (f.app (Opposite.op ⦋n⦌))) hxy
  subst y
  have htv : t = v := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst v
  rfl

theorem mapParameters_isNormal (s : Law A k) (f : X ⟶ Y) [Mono f]
    (p : Parameters A X k) (hp : IsNormal s X p) : IsNormal s Y (mapParameters A k f p) :=
  ⟨(SSet.nonDegenerate_iff_of_mono f p.1.2).mpr hp.1, hp.2⟩

variable (L : SSet.{u} ⥤ SSet.{u}) (α : A ⟶ SSet.stdSimplex.{u} ⋙ L)

theorem mapParameters_projection (f : X ⟶ Y) (p : Parameters A X k) :
    projection A L α Y k (mapParameters A k f p) =
      (L.map f).app (Opposite.op ⦋k⦌) (projection A L α X k p) := by
  rcases p with ⟨⟨n, x⟩, t⟩
  have hc : cellMap A L α Y n (f.app (Opposite.op ⦋n⦌) x) =
      cellMap A L α X n x ≫ L.map f := by
    unfold cellMap
    rw [← SSet.yonedaEquiv_symm_comp, L.map_comp, Category.assoc]
  exact congrArg (fun g ↦ g.app (Opposite.op ⦋k⦌) t) hc

theorem map_injective_of_normalForms (s : Law A k) (faces : ∀ n t, Face s n t)
    [SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension A] [L.IsLeftKanExtension α]
    (f : X ⟶ Y) [Mono f] : Function.Injective ((L.map f).app (Opposite.op ⦋k⦌)) := by
  intro z w h
  obtain ⟨a, ha, _⟩ := existsUnique_normal s faces X L α z
  obtain ⟨b, hb, _⟩ := existsUnique_normal s faces X L α w
  have hproj : projection A L α Y k (mapParameters A k f a.val) =
      projection A L α Y k (mapParameters A k f b.val) := by
    rw [mapParameters_projection, mapParameters_projection, ha, hb]
    exact h
  have hab := normal_injective s faces Y L α
    (mapParameters_isNormal A k s f a.val a.property)
    (mapParameters_isNormal A k s f b.val b.property) hproj
  have hab' := mapParameters_injective A k f hab
  exact ha.symm.trans ((congrArg (projection A L α X k) hab').trans hb)

theorem sd_map_mono (f : X ⟶ Y) [Mono f] : Mono (SSet.sd.map f) := by
  let : SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension SimplexCategory.sd.{u} :=
    inferInstanceAs (Functor.HasPointwiseLeftKanExtension uliftYoneda.{u} SimplexCategory.sd.{u})
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨k⟩⟩
  apply ConcreteCategory.mono_of_injective
  exact map_injective_of_normalForms SimplexCategory.sd k SSet.sd SSet.stdSimplex.sdIso.inv
    (sdLaw k) (sdFace k) f

theorem dualSd_map_mono (f : X ⟶ Y) [Mono f] : Mono (dualSd.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨k⟩⟩
  apply ConcreteCategory.mono_of_injective
  exact map_injective_of_normalForms dualStandard k dualSd dualSdIso.inv
    (dualLaw k) (dualFace k) f

end Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters

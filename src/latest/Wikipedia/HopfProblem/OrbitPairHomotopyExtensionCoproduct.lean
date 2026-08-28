import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionPushout

/-!
# Homotopy extension for actual coproduct cocones

Component families are curried into the compact-open path space and
assembled by the given coproduct's universal property. The result is
jointly continuous and retains every component exactly. This applies to
realized native coproduct cocones without substituting a different model
of their underlying topological spaces.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

variable {J : Type v} {D : J → TopCat.{u}} {B Z : TopCat.{u}}
    (b : ∀ j, D j ⟶ B) (hb : IsColimit (Cofan.mk B b))

include hb in
theorem cofan_jointly_surjective (x : B) : ∃ j, ∃ y : D j, b j y = x :=
  Cofan.inj_jointly_surjective_of_isColimit
    (isColimitCofanMkObjOfIsColimit (forget TopCat) D b hb) x

def coproductFamilies (H : ∀ j, C(I × D j, Z)) : C(I × B, Z) :=
  (Cofan.IsColimit.desc hb (fun j ↦ PushoutHomotopy.familyPaths (H j))).hom.uncurry.comp
    ⟨Prod.swap, continuous_swap⟩

theorem coproductFamilies_inj (H : ∀ j, C(I × D j, Z)) (t : I) (j : J) (x : D j) :
    coproductFamilies b hb H (t, b j x) = H j (t, x) :=
  congrArg (fun F ↦ F x t)
    (Cofan.IsColimit.fac hb (fun j ↦ PushoutHomotopy.familyPaths (H j)) j)

theorem of_coproduct {A₀ B₀ : J → TopCat.{u}} {A B : TopCat.{u}}
    (a : ∀ j, A₀ j ⟶ A) (b : ∀ j, B₀ j ⟶ B)
    (ha : IsColimit (Cofan.mk A a)) (hb : IsColimit (Cofan.mk B b))
    (e : ∀ j, A₀ j ⟶ B₀ j) (i : A ⟶ B) (w : ∀ j, a j ≫ i = e j ≫ b j)
    (he : ∀ j, HasHomotopyExtension (e j)) : HasHomotopyExtension i := by
  intro Z F G h0
  have hex : ∀ j, ∃ K : C(I × B₀ j, Z),
      (∀ x, K (0, x) = F (b j x)) ∧ ∀ t x, K (t, e j x) = G (t, a j x) := by
    intro j
    apply he j Z (F.comp (b j).hom) (G.comp ((ContinuousMap.id I).prodMap (a j).hom))
    intro x
    exact (h0 (a j x)).trans (congrArg F (congrArg (fun m ↦ m x) (w j)))
  choose K hK0 hKe using hex
  let H := coproductFamilies b hb K
  refine ⟨H, ?_, ?_⟩
  · intro x
    obtain ⟨j, y, rfl⟩ := cofan_jointly_surjective b hb x
    exact (coproductFamilies_inj b hb K 0 j y).trans (hK0 j y)
  · intro t x
    obtain ⟨j, y, rfl⟩ := cofan_jointly_surjective a ha x
    have hw : i (a j y) = b j (e j y) := congrArg (fun m ↦ m y) (w j)
    rw [hw]
    exact (coproductFamilies_inj b hb K t j (e j y)).trans (hKe j t y)

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

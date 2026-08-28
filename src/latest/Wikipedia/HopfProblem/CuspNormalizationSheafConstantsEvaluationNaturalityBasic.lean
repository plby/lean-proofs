import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsOverBase

/-!
# Actual constant-germ values commute with continuous pullback

Local representatives from the actual sheafification show that a
constant-sheaf section and its pullback have the same scalar germ value.
Restriction invariance of germs gives the corresponding statement over
a common base, and hence naturality on the genuine pushforward stalks.
No holomorphicity, finiteness, or separation assumption is used.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

section GermValues

variable {X Y B : TopCat.{0}}

/-- Actual pullback preserves the scalar value of a constant-sheaf germ. -/
theorem constantGermValue_pullback (f : X ⟶ Y) (U : Opens Y)
    (y : X) (hy : f y ∈ U) (s : (complexAdditiveSheaf Y).obj.obj (op U)) :
    complexAdditiveSheafStalkEquiv X y
        (TopCat.Presheaf.germ (complexAdditiveSheaf X).obj
          ((Opens.map f).obj U) y hy ((additivePullbackMap f).hom.app (op U) s)) =
      complexAdditiveSheafStalkEquiv Y (f y)
        (TopCat.Presheaf.germ (complexAdditiveSheaf Y).obj U (f y) hy s) := by
  obtain ⟨V, hVU, c, hyV, hc⟩ := exists_constant_restriction U s (f y) hy
  change (additiveUnit Y).app (op V) c =
    (complexAdditiveSheaf Y).obj.map (homOfLE hVU).op s at hc
  let i : V ⟶ U := homOfLE hVU
  let j : (Opens.map f).obj V ⟶ (Opens.map f).obj U := (Opens.map f).map i
  have hyfV : y ∈ (Opens.map f).obj V := hyV
  have hs := (TopCat.Presheaf.germ_res_apply
    (complexAdditiveSheaf Y).obj i (f y) hyV s).symm.trans
    (congrArg (TopCat.Presheaf.germ (complexAdditiveSheaf Y).obj V (f y) hyV) hc.symm)
  have hn := ConcreteCategory.congr_hom ((additivePullbackMap f).hom.naturality i.op) s
  have ht : (complexAdditiveSheaf X).obj.map j.op
      ((additivePullbackMap f).hom.app (op U) s) =
        (additiveUnit X).app (op ((Opens.map f).obj V)) c :=
    hn.symm.trans ((congrArg ((additivePullbackMap f).hom.app (op V)) hc.symm).trans
      (additivePullbackMap_unit f V c))
  have htg := (TopCat.Presheaf.germ_res_apply (complexAdditiveSheaf X).obj j y hyfV
    ((additivePullbackMap f).hom.app (op U) s)).symm.trans
      (congrArg (TopCat.Presheaf.germ (complexAdditiveSheaf X).obj
        ((Opens.map f).obj V) y hyfV) ht)
  calc
    _ = complexAdditiveSheafStalkEquiv X y
        (TopCat.Presheaf.germ (complexAdditiveSheaf X).obj
          ((Opens.map f).obj V) y hyfV
            ((additiveUnit X).app (op ((Opens.map f).obj V)) c)) :=
      congrArg (complexAdditiveSheafStalkEquiv X y) htg
    _ = c := complexAdditiveSheafStalkEquiv_germ_unit X y ((Opens.map f).obj V) hyfV c
    _ = complexAdditiveSheafStalkEquiv Y (f y)
        (TopCat.Presheaf.germ (complexAdditiveSheaf Y).obj V (f y) hyV
          ((additiveUnit Y).app (op V) c)) :=
      (complexAdditiveSheafStalkEquiv_germ_unit Y (f y) V hyV c).symm
    _ = _ := congrArg (complexAdditiveSheafStalkEquiv Y (f y)) hs.symm

/-- Passing to a common base preserves the same actual scalar germ
value, because the extra operation is literal restriction. -/
theorem constantGermValue_overBase (p : Y ⟶ B) (q : X ⟶ B) (f : X ⟶ Y)
    (hf : ∀ x : X, p (f x) = q x) (U : Opens B)
    (s : (complexAdditiveSheaf Y).obj.obj (op ((Opens.map p).obj U)))
    (y : X) (hy : y ∈ (Opens.map q).obj U) :
    complexAdditiveSheafStalkEquiv X y
        (TopCat.Presheaf.germ (complexAdditiveSheaf X).obj ((Opens.map q).obj U) y hy
          ((additiveOverBaseMap p q f hf).hom.app (op U) s)) =
      complexAdditiveSheafStalkEquiv Y (f y)
        (TopCat.Presheaf.germ (complexAdditiveSheaf Y).obj ((Opens.map p).obj U)
          (f y) (overBasePreimageLE p q f hf U hy) s) := by
  exact (congrArg (complexAdditiveSheafStalkEquiv X y)
    (TopCat.Presheaf.germ_res_apply (complexAdditiveSheaf X).obj
      (homOfLE (overBasePreimageLE p q f hf U)) y hy
      ((additivePullbackMap f).hom.app (op ((Opens.map p).obj U)) s))).trans
    (constantGermValue_pullback f ((Opens.map p).obj U) y
      (overBasePreimageLE p q f hf U hy) s)

end GermValues

variable {M N B : Type} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace B]

/-- The actual scalar evaluation on a pushforward constant-sheaf stalk
commutes with every continuous map over the base. -/
theorem constantStalkEvaluationAt_naturality
    (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
    (f : TopCat.of N ⟶ TopCat.of M) (hf : ∀ x : N, p (f x) = q x)
    (y : N) (b : B) (hy : q y = b)
    (s : (pushedConstantSheaf p).presheaf.stalk b) :
    constantStalkEvaluationAt q y b hy
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
          (additiveOverBaseMap p q f hf).hom s) =
      constantStalkEvaluationAt p (f y) b ((hf y).trans hy) s := by
  obtain ⟨U, hbU, u, rfl⟩ := (pushedConstantSheaf p).presheaf.exists_germ_eq s
  change (complexAdditiveSheaf (TopCat.of M)).obj.obj (op ((Opens.map p).obj U)) at u
  calc
    _ = constantStalkEvaluationAt q y b hy
        ((pushedConstantSheaf q).presheaf.germ U b hbU
          ((additiveOverBaseMap p q f hf).hom.app (op U) u)) :=
      congrArg (constantStalkEvaluationAt q y b hy)
        (TopCat.Presheaf.stalkFunctor_map_germ_apply U b hbU
          (additiveOverBaseMap p q f hf).hom u)
    _ = complexAdditiveSheafStalkEquiv (TopCat.of N) y
        (TopCat.Presheaf.germ (complexAdditiveSheaf (TopCat.of N)).obj
          ((Opens.map q).obj U) y (SheafEvaluation.point_mem_preimage q y b hy U hbU)
            ((additiveOverBaseMap p q f hf).hom.app (op U) u)) :=
      constantStalkEvaluationAt_germ q y b hy U hbU _
    _ = complexAdditiveSheafStalkEquiv (TopCat.of M) (f y)
        (TopCat.Presheaf.germ (complexAdditiveSheaf (TopCat.of M)).obj
          ((Opens.map p).obj U) (f y)
            (SheafEvaluation.point_mem_preimage p (f y) b ((hf y).trans hy) U hbU) u) :=
      constantGermValue_overBase p q f hf U u y
        (SheafEvaluation.point_mem_preimage q y b hy U hbU)
    _ = _ := (constantStalkEvaluationAt_germ p (f y) b ((hf y).trans hy) U hbU u).symm

/-- The same compatibility as an equality of genuine additive stalk
morphisms, for use with the skyscraper adjunction. -/
theorem constantStalkEvaluationAt_naturality_hom
    (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
    (f : TopCat.of N ⟶ TopCat.of M) (hf : ∀ x : N, p (f x) = q x)
    (y : N) (b : B) (hy : q y = b) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
        (additiveOverBaseMap p q f hf).hom ≫ constantStalkEvaluationAtHom q y b hy =
      constantStalkEvaluationAtHom p (f y) b ((hf y).trans hy) := by
  ext s
  exact constantStalkEvaluationAt_naturality p q f hf y b hy s

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants

import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Naturality of the actual singular-chain homotopy prism

The prism here is the one constructed by Mathlib from the singular
simplicial homotopy, not an independently chosen chain homotopy. A
commuting continuous homotopy square gives its exact chain-level square.
-/

noncomputable section

open CategoryTheory Limits Simplicial Opposite MonoidalCategory Functor.LaxMonoidal
open scoped unitInterval
open Wikipedia.HopfProblem PeriodTorusHigherHomology SingularMayerVietoris FirstHurewicz

namespace NoExoticSixSphere.SingularHomotopyPrismNaturality

theorem alternating_natural {C : Type*} [Category C] [Preadditive C] {A B X Y : C}
    (n : ℕ) (H : Fin (n + 1) → (A ⟶ X)) (K : Fin (n + 1) → (B ⟶ Y))
    (u : A ⟶ B) (v : X ⟶ Y) (h : ∀ i, H i ≫ v = u ≫ K i) :
    (-∑ i, (-1 : ℤ) ^ i.val • H i) ≫ v = u ≫ (-∑ i, (-1 : ℤ) ^ i.val • K i) := by
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Preadditive.sum_comp,
    Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, h]

theorem simplex_of_square {A B X Y : SSet} {f g : A ⟶ X} {f' g' : B ⟶ Y}
    (H : SSet.Homotopy f g) (K : SSet.Homotopy f' g') (u : A ⟶ B) (v : X ⟶ Y)
    (h : H.h ≫ v = u ▷ Δ[1] ≫ K.h) (n : ℕ) (i : Fin (n + 1)) :
    H.toSimplicialObjectHomotopy.h i ≫ v.app (op ⦋n + 1⦌) =
      u.app (op ⦋n⦌) ≫ K.toSimplicialObjectHomotopy.h i := by
  ext s
  have he : (SSet.yonedaEquiv.symm s ▷ Δ[1] ≫ H.h) ≫ v =
      SSet.yonedaEquiv.symm (u.app (op ⦋n⦌) s) ▷ Δ[1] ≫ K.h := by
    rw [Category.assoc, h, ← Category.assoc, ← comp_whiskerRight,
      ← SSet.yonedaEquiv_symm_comp]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app he (op ⦋n + 1⦌))
    (SSet.prodStdSimplex.nonDegenerateEquiv₁ i).1

variable {A B X Y : Type} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(A, X)} {f' g' : C(B, Y)}
  (H : f.Homotopy g) (K : f'.Homotopy g') (u : C(A, B)) (v : C(X, Y))
  (h : v.comp H.toContinuousMap = K.toContinuousMap.comp ((ContinuousMap.id I).prodMap u))

abbrev simplexHomotopy : SimplicialObject.Homotopy
    (TopCat.toSSet.map (TopCat.ofHom f)) (TopCat.toSSet.map (TopCat.ofHom g)) :=
  SSet.Homotopy.toSimplicialObjectHomotopy
    (TopCat.Homotopy.toSSet (f := TopCat.ofHom f) (g := TopCat.ofHom g) H)

include h in
theorem singular_square :
    (TopCat.Homotopy.toSSet (f := TopCat.ofHom f) (g := TopCat.ofHom g) H).h ≫
        TopCat.toSSet.map (TopCat.ofHom v) =
      TopCat.toSSet.map (TopCat.ofHom u) ▷ Δ[1] ≫
        (TopCat.Homotopy.toSSet (f := TopCat.ofHom f') (g := TopCat.ofHom g') K).h := by
  have ht : TopCat.Homotopy.h (f₀ := TopCat.ofHom f) (f₁ := TopCat.ofHom g) H ≫
      TopCat.ofHom v = TopCat.ofHom u ▷ TopCat.I ≫
        TopCat.Homotopy.h (f₀ := TopCat.ofHom f') (f₁ := TopCat.ofHom g') K := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    exact ContinuousMap.congr_fun h (TopCat.I.homeomorph p.2, p.1)
  dsimp only [TopCat.Homotopy.toSSet]
  rw [Category.assoc, Category.assoc, ← TopCat.toSSet.map_comp, ht,
    TopCat.toSSet.map_comp, ← μ_natural_left_assoc, ← whisker_exchange_assoc]

include h in
theorem simplex_natural (n : ℕ) (i : Fin (n + 1)) :
    (simplexHomotopy H).h i ≫ (TopCat.toSSet.map (TopCat.ofHom v)).app (op ⦋n + 1⦌) =
      (TopCat.toSSet.map (TopCat.ofHom u)).app (op ⦋n⦌) ≫
        (simplexHomotopy K).h i := by
  exact simplex_of_square _ _ _ _ (singular_square H K u v h) n i

include h in
theorem component_natural (n : ℕ) :
    (singularChainHomotopy H).hom n (n + 1) ≫ (singularChainMap v).f (n + 1) =
      (singularChainMap u).f n ≫ (singularChainHomotopy K).hom n (n + 1) := by
  let F : Type ⥤ ModuleCat ℤ := sigmaConst.obj (ModuleCat.of ℤ ℤ)
  change SimplicialObject.Homotopy.ToChainHomotopy.hom
      ((simplexHomotopy H).whiskerRight F) n (n + 1) ≫
        F.map ((TopCat.toSSet.map (TopCat.ofHom v)).app (op ⦋n + 1⦌)) =
      F.map ((TopCat.toSSet.map (TopCat.ofHom u)).app (op ⦋n⦌)) ≫
        SimplicialObject.Homotopy.ToChainHomotopy.hom
          ((simplexHomotopy K).whiskerRight F) n (n + 1)
  rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  apply alternating_natural
  intro i
  change F.map ((simplexHomotopy H).h i) ≫
      F.map ((TopCat.toSSet.map (TopCat.ofHom v)).app (op ⦋n + 1⦌)) =
    F.map ((TopCat.toSSet.map (TopCat.ofHom u)).app (op ⦋n⦌)) ≫
      F.map ((simplexHomotopy K).h i)
  rw [← F.map_comp, ← F.map_comp, simplex_natural H K u v h n i]

include h in
theorem component_natural_apply (n : ℕ) (c : Chains A n) :
    inducedChain v (n + 1) (((singularChainHomotopy H).hom n (n + 1)).hom c) =
      ((singularChainHomotopy K).hom n (n + 1)).hom (inducedChain u n c) :=
  congrArg (fun k : Chains A n ⟶ Chains Y (n + 1) ↦ k.hom c)
    (component_natural H K u v h n)

end NoExoticSixSphere.SingularHomotopyPrismNaturality

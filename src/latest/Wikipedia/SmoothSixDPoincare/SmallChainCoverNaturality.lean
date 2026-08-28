import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# Maps of the actual small-chain Mayer–Vietoris sequences

A continuous map carrying each member of a two-set cover into the matching
target member induces a morphism of the actual short exact singular-chain
sequences. The third component is literal restriction of the original
singular-chain map, not an independently chosen homology map.
-/

noncomputable section

open Set CategoryTheory Limits

namespace Wikipedia.SmoothSixDPoincare.CoverNaturality

open Wikipedia.HopfProblem.FirstHurewicz
  Wikipedia.HopfProblem.SingularMayerVietoris

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def mapOn (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : MapsTo f A B) : C(A, B) :=
  ⟨fun x => ⟨f x.val, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem chainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    singularChainMap f ≫ singularChainMap g = singularChainMap (g.comp f) :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map_comp (TopCat.ofHom f) (TopCat.ofHom g)).symm

variable (U V : Set X) (U' V' : Set Y) (f : C(X, Y))
  (hU : MapsTo f U U') (hV : MapsTo f V V')

include hU hV

theorem map_intersection : MapsTo f (U ∩ V) (U' ∩ V') :=
  fun _ hx => ⟨hU hx.1, hV hx.2⟩

theorem inducedChain_mem_small (n : ℕ) (c : Chains X n)
    (hc : c ∈ smallChainSubmodule U V n) :
    inducedChain f n c ∈ smallChainSubmodule U' V' n := by
  have hle : smallChainSubmodule U V n ≤
      (smallChainSubmodule U' V' n).comap (inducedChain f n) := by
    rw [smallChainSubmodule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change inducedChain f n (simplexChain X n σ) ∈ smallChainSubmodule U' V' n
    rw [inducedChain_simplex]
    apply simplexChain_mem_small
    rcases hσ with hσ | hσ
    · left
      rintro _ ⟨t, rfl⟩
      exact hU (hσ ⟨t, rfl⟩)
    · right
      rintro _ ⟨t, rfl⟩
      exact hV (hσ ⟨t, rfl⟩)
  exact hle hc

def smallMap : smallComplex U V ⟶ smallComplex U' V' :=
  liftToSmall U' V' (smallInclusion U V ≫ singularChainMap f)
    (fun n c => inducedChain_mem_small U V U' V' f hU hV n c.val c.property)

theorem smallMap_inclusion :
    smallMap U V U' V' f hU hV ≫ smallInclusion U' V' =
      smallInclusion U V ≫ singularChainMap f :=
  liftToSmall_inclusion U' V' _ _

theorem smallMap_left :
    toSmallLeft U V ≫ smallMap U V U' V' f hU hV =
      singularChainMap (mapOn f U U' hU) ≫ toSmallLeft U' V' := by
  apply (cancel_mono (smallInclusion U' V')).mp
  rw [Category.assoc, smallMap_inclusion, ← Category.assoc, toSmallLeft_inclusion,
    Category.assoc, toSmallLeft_inclusion, chainMap_comp, chainMap_comp]
  rfl

theorem smallMap_right :
    toSmallRight U V ≫ smallMap U V U' V' f hU hV =
      singularChainMap (mapOn f V V' hV) ≫ toSmallRight U' V' := by
  apply (cancel_mono (smallInclusion U' V')).mp
  rw [Category.assoc, smallMap_inclusion, ← Category.assoc, toSmallRight_inclusion,
    Category.assoc, toSmallRight_inclusion, chainMap_comp, chainMap_comp]
  rfl

theorem intersection_left :
    singularChainMap (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV)) ≫
      intersectionToLeft U' V' =
        intersectionToLeft U V ≫ singularChainMap (mapOn f U U' hU) := by
  unfold intersectionToLeft
  rw [chainMap_comp, chainMap_comp]
  rfl

theorem intersection_right :
    singularChainMap (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV)) ≫
      intersectionToRight U' V' =
        intersectionToRight U V ≫ singularChainMap (mapOn f V V' hV) := by
  unfold intersectionToRight
  rw [chainMap_comp, chainMap_comp]
  rfl

/-- The original map induces a morphism of the genuine short exact chain sequences. -/
def chainSequenceMap : chainSequence U V ⟶ chainSequence U' V' where
  τ₁ := singularChainMap (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV))
  τ₂ := biprod.map (singularChainMap (mapOn f U U' hU))
    (singularChainMap (mapOn f V V' hV))
  τ₃ := smallMap U V U' V' f hU hV
  comm₁₂ := by
    dsimp only [chainSequence, leftMap, middleComplex]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      exact intersection_left U V U' V' f hU hV
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc,
        Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg (intersection_right U V U' V' f hU hV)
  comm₂₃ := by
    dsimp only [chainSequence, rightMap, middleComplex]
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
      exact (smallMap_left U V U' V' f hU hV).symm
    · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
      exact (smallMap_right U V U' V' f hU hV).symm

/-- Naturality before the small-to-ambient homology comparison. -/
theorem smallConnecting_naturality (n : ℕ) :
    (singularHomologyMap
      (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hU hV)) n).comp
        (smallConnectingMap U V n) =
      (smallConnectingMap U' V' n).comp
        (homologyLinearMap (smallMap U V U' V' f hU hV) (n + 1)) :=
  connectingMap_naturality (chainSequence_shortExact U V)
    (chainSequenceMap U V U' V' f hU hV) (chainSequence_shortExact U' V') n

theorem comparison_naturality (n : ℕ) :
    (smallHomologyComparison U' V' n).comp
      (homologyLinearMap (smallMap U V U' V' f hU hV) n) =
    (singularHomologyMap f n).comp (smallHomologyComparison U V n) := by
  unfold smallHomologyComparison
  rw [← homologyLinearMap_comp, smallMap_inclusion, homologyLinearMap_comp]

end Wikipedia.SmoothSixDPoincare.CoverNaturality

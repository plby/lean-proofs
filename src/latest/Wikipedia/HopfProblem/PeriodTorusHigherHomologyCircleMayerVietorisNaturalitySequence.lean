import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturalitySmallMap
import Wikipedia.HopfProblem.SingularMayerVietorisSequence

/-!
# Actual maps of the small-chain Mayer–Vietoris sequences

The continuous restrictions and the actual small-chain map form a morphism
of the proved short exact chain sequences. Its middle component is the
categorical biproduct of the two induced restriction maps. Naturality of
the genuine connecting homomorphism then applies without any additional
homological assumption.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
  (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')

/-- The actual biproduct of the maps induced on the two cover subsets. -/
def coverMiddleMap : middleComplex U V ⟶ middleComplex U' V' :=
  biprod.map (singularChainMap (coverRestriction f U U' hfU))
    (singularChainMap (coverRestriction f V V' hfV))

/-- The difference of the intersection inclusions commutes with the restriction maps. -/
theorem intersectionRestriction_leftMap :
    singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫ leftMap U' V' =
      leftMap U V ≫ coverMiddleMap f U V U' V' hfU hfV := by
  change singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫
      biprod.lift (intersectionToLeft U' V') (-(intersectionToRight U' V')) =
    biprod.lift (intersectionToLeft U V) (-(intersectionToRight U V)) ≫
      biprod.map (singularChainMap (coverRestriction f U U' hfU))
        (singularChainMap (coverRestriction f V V' hfV))
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst,
      biprod.lift_fst_assoc]
    exact (coverRestriction_intersection_left f U V U' V' hfU hfV).symm
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg (coverRestriction_intersection_right f U V U' V' hfU hfV).symm

/-- The sum map into small chains commutes with the actual cover-preserving map. -/
theorem coverMiddleMap_rightMap :
    coverMiddleMap f U V U' V' hfU hfV ≫ rightMap U' V' =
      rightMap U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV := by
  change biprod.map (singularChainMap (coverRestriction f U U' hfU))
      (singularChainMap (coverRestriction f V V' hfV)) ≫
        biprod.desc (toSmallLeft U' V') (toSmallRight U' V') =
    biprod.desc (toSmallLeft U V) (toSmallRight U V) ≫
      smallMapOfMapsTo f U V U' V' hfU hfV
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
    exact (toSmallLeft_smallMapOfMapsTo f U V U' V' hfU hfV).symm
  · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc]
    exact (toSmallRight_smallMapOfMapsTo f U V U' V' hfU hfV).symm

/-- A continuous map preserving the two cover subsets induces an actual morphism
of their small-chain short exact sequences. -/
def chainSequenceMapOfMapsTo : chainSequence U V ⟶ chainSequence U' V' where
  τ₁ := singularChainMap (intersectionRestriction f U V U' V' hfU hfV)
  τ₂ := coverMiddleMap f U V U' V' hfU hfV
  τ₃ := smallMapOfMapsTo f U V U' V' hfU hfV
  comm₁₂ := intersectionRestriction_leftMap f U V U' V' hfU hfV
  comm₂₃ := coverMiddleMap_rightMap f U V U' V' hfU hfV

@[simp] theorem chainSequenceMapOfMapsTo_τ₁ :
    (chainSequenceMapOfMapsTo f U V U' V' hfU hfV).τ₁ =
      singularChainMap (intersectionRestriction f U V U' V' hfU hfV) := rfl

@[simp] theorem chainSequenceMapOfMapsTo_τ₂ :
    (chainSequenceMapOfMapsTo f U V U' V' hfU hfV).τ₂ =
      coverMiddleMap f U V U' V' hfU hfV := rfl

@[simp] theorem chainSequenceMapOfMapsTo_τ₃ :
    (chainSequenceMapOfMapsTo f U V U' V' hfU hfV).τ₃ =
      smallMapOfMapsTo f U V U' V' hfU hfV := rfl

/-- Naturality of the actual small-chain connecting homomorphisms. -/
theorem smallConnectingMap_naturality (n : ℕ) :
    (singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n).comp
        (smallConnectingMap U V n) =
      (smallConnectingMap U' V' n).comp
        (homologyLinearMap (smallMapOfMapsTo f U V U' V' hfU hfV) (n + 1)) :=
  connectingMap_naturality (chainSequence_shortExact U V)
    (chainSequenceMapOfMapsTo f U V U' V' hfU hfV)
    (chainSequence_shortExact U' V') n

theorem smallConnectingMap_naturality_apply (n : ℕ) (a : SmallHomology U V (n + 1)) :
    singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n
        (smallConnectingMap U V n a) =
      smallConnectingMap U' V' n
        (homologyLinearMap (smallMapOfMapsTo f U V U' V' hfU hfV) (n + 1) a) :=
  LinearMap.congr_fun (smallConnectingMap_naturality f U V U' V' hfU hfV n) a

end Wikipedia.HopfProblem.SingularMayerVietoris

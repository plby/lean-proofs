import Wikipedia.SmoothSixDPoincare.SmallChainCoverNaturality

/-!
# Swapping the actual two-set singular-chain cover

Interchanging the two cover members swaps the middle biproduct. The first
map must be negated because Mayer–Vietoris uses the difference of the two
intersection inclusions. The small-chain map remains the identity on the
underlying ambient singular chains.
-/

noncomputable section

open Set CategoryTheory Limits

namespace Wikipedia.SmoothSixDPoincare.CoverNaturality

open Wikipedia.HopfProblem.FirstHurewicz
  Wikipedia.HopfProblem.SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] (U V : Set X)

def intersectionSwap : C(↥(U ∩ V), ↥(V ∩ U)) :=
  ⟨fun x => ⟨x.val, x.property.symm⟩, continuous_subtype_val.subtype_mk _⟩

def smallSwap : smallComplex U V ⟶ smallComplex V U :=
  liftToSmall V U (smallInclusion U V) (fun n c => by
    change c.val ∈ smallChainSubmodule V U n
    simpa only [smallChainSubmodule, sup_comm] using c.property)

theorem smallSwap_inclusion : smallSwap U V ≫ smallInclusion V U = smallInclusion U V :=
  liftToSmall_inclusion V U _ _

theorem smallSwap_left : toSmallLeft U V ≫ smallSwap U V = toSmallRight V U := by
  apply (cancel_mono (smallInclusion V U)).mp
  rw [Category.assoc, smallSwap_inclusion, toSmallLeft_inclusion, toSmallRight_inclusion]

theorem smallSwap_right : toSmallRight U V ≫ smallSwap U V = toSmallLeft V U := by
  apply (cancel_mono (smallInclusion V U)).mp
  rw [Category.assoc, smallSwap_inclusion, toSmallRight_inclusion, toSmallLeft_inclusion]

theorem intersectionSwap_left :
    singularChainMap (intersectionSwap U V) ≫ intersectionToLeft V U =
      intersectionToRight U V := by
  unfold intersectionToLeft intersectionToRight
  rw [chainMap_comp]
  rfl

theorem intersectionSwap_right :
    singularChainMap (intersectionSwap U V) ≫ intersectionToRight V U =
      intersectionToLeft U V := by
  unfold intersectionToLeft intersectionToRight
  rw [chainMap_comp]
  rfl

/-- The genuine sequence morphism has a minus sign on the intersection chains. -/
def chainSequenceSwap : chainSequence U V ⟶ chainSequence V U where
  τ₁ := -singularChainMap (intersectionSwap U V)
  τ₂ := biprod.lift biprod.snd biprod.fst
  τ₃ := smallSwap U V
  comm₁₂ := by
    dsimp only [chainSequence, leftMap, middleComplex]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd,
        Preadditive.neg_comp]
      exact congrArg Neg.neg (intersectionSwap_left U V)
    · simp only [Category.assoc, biprod.lift_snd, biprod.lift_fst,
        Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
      exact intersectionSwap_right U V
  comm₂₃ := by
    dsimp only [chainSequence, rightMap, middleComplex]
    apply biprod.hom_ext'
    · simp only [biprod.lift_desc, Preadditive.comp_add,
        biprod.inl_snd_assoc, biprod.inl_fst_assoc, zero_comp, zero_add,
        biprod.inl_desc_assoc]
      exact (smallSwap_left U V).symm
    · simp only [biprod.lift_desc, Preadditive.comp_add,
        biprod.inr_snd_assoc, biprod.inr_fst_assoc, zero_comp, add_zero,
        biprod.inr_desc_assoc]
      exact (smallSwap_right U V).symm

theorem smallConnecting_swap (n : ℕ) (a : SmallHomology U V (n + 1)) :
    smallConnectingMap V U n (homologyLinearMap (smallSwap U V) (n + 1) a) =
      -singularHomologyMap (intersectionSwap U V) n (smallConnectingMap U V n a) := by
  have h := LinearMap.congr_fun
    (connectingMap_naturality (chainSequence_shortExact U V)
      (chainSequenceSwap U V) (chainSequence_shortExact V U) n) a
  change homologyLinearMap (-singularChainMap (intersectionSwap U V)) n
    (smallConnectingMap U V n a) = _ at h
  rw [homologyLinearMap_neg] at h
  exact h.symm

theorem comparison_swap (n : ℕ) (a : SmallHomology U V n) :
    smallHomologyComparison V U n (homologyLinearMap (smallSwap U V) n a) =
      smallHomologyComparison U V n a := by
  change homologyLinearMap (smallInclusion V U) n
    (homologyLinearMap (smallSwap U V) n a) = _
  rw [← LinearMap.comp_apply, ← homologyLinearMap_comp, smallSwap_inclusion]
  rfl

end Wikipedia.SmoothSixDPoincare.CoverNaturality

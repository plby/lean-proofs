import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsExact
import Wikipedia.HopfProblem.SingularMayerVietorisSequenceTransport

/-!
# The actual Mayer–Vietoris sequence for small singular chains

For any two subsets, the actual short exact sequence of their singular
chain complexes has the small-chain complex as its third term. This file
constructs its connecting homomorphisms and proves the entire homology
sequence exact, with the middle term expressed as a product of the two
actual singular homology groups.

The third term is genuinely the homology of the small-chain complex. No
openness or covering hypothesis is needed for this result, and no
comparison with the ambient space's full singular homology is assumed.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]

/-- Integral singular homology computed by Mathlib's actual chain functor. -/
abbrev SingularHomology (Y : Type) [TopologicalSpace Y] (n : ℕ) :=
  (singularComplex Y).homology n

/-- The actual singular homology functor map in any degree. -/
abbrev singularHomologyMap {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) : SingularHomology Y n →ₗ[ℤ] SingularHomology Z n :=
  homologyLinearMap (singularChainMap f) n

theorem singularHomologyMap_eq {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) :
    singularHomologyMap f n =
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))).hom := rfl

@[simp] theorem singularHomologyMap_one {Y Z : Type}
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(Y, Z)) :
    singularHomologyMap f 1 = inducedHomology f := rfl

/-- The actual homology of the small-chain subcomplex. -/
abbrev SmallHomology (U V : Set X) (n : ℕ) := (smallComplex U V).homology n

/-- The genuine biproduct-homology isomorphism for the two subsets. -/
def middleHomologyEquiv (U V : Set X) (n : ℕ) :
    (middleComplex U V).homology n ≃ₗ[ℤ]
      (SingularHomology U n × SingularHomology V n) :=
  homologyBiprodEquiv (singularComplex U) (singularComplex V) n

/-- The actual homology map from the intersection, in product coordinates. -/
def smallLeftHomologyMap (U V : Set X) (n : ℕ) :
    SingularHomology (U ∩ V : Set X) n →ₗ[ℤ]
      (SingularHomology U n × SingularHomology V n) :=
  biprodSequenceFirstMap (leftMap U V) n

/-- The actual homology map from the pair of subsets into small-chain homology. -/
def smallRightHomologyMap (U V : Set X) (n : ℕ) :
    (SingularHomology U n × SingularHomology V n) →ₗ[ℤ] SmallHomology U V n :=
  biprodSequenceSecondMap (rightMap U V) n

/-- The actual connecting map supplied by the proved small-chain short exact sequence. -/
def smallConnectingMap (U V : Set X) (n : ℕ) :
    SmallHomology U V (n + 1) →ₗ[ℤ] SingularHomology (U ∩ V : Set X) n :=
  connectingMap (chainSequence_shortExact U V) n

/-- The actual comparison map induced by including the small subcomplex
in the ambient singular chain complex. No invertibility is asserted here. -/
def smallHomologyComparison (U V : Set X) (n : ℕ) :
    SmallHomology U V n →ₗ[ℤ] SingularHomology X n :=
  homologyLinearMap (smallInclusion U V) n

/-- Both components of the first map are actual induced homology maps
of the two chain-level projection composites. -/
theorem smallLeftHomologyMap_components (U V : Set X) (n : ℕ)
    (a : SingularHomology (U ∩ V : Set X) n) :
    smallLeftHomologyMap U V n a =
      (homologyLinearMap (leftMap U V ≫
        (biprod.fst : middleComplex U V ⟶ singularComplex U)) n a,
       homologyLinearMap (leftMap U V ≫
        (biprod.snd : middleComplex U V ⟶ singularComplex V)) n a) := by
  apply Prod.ext
  · exact (LinearMap.congr_fun
      (homologyLinearMap_comp (leftMap U V) biprod.fst n) a).symm
  · exact (LinearMap.congr_fun
      (homologyLinearMap_comp (leftMap U V) biprod.snd n) a).symm

/-- The second map is the sum of the two actual induced homology maps
obtained by restricting the chain-level map to the two summands. -/
theorem smallRightHomologyMap_components (U V : Set X) (n : ℕ)
    (a : SingularHomology U n × SingularHomology V n) :
    smallRightHomologyMap U V n a =
      homologyLinearMap ((biprod.inl : singularComplex U ⟶ middleComplex U V) ≫
        rightMap U V) n a.1 +
      homologyLinearMap ((biprod.inr : singularComplex V ⟶ middleComplex U V) ≫
        rightMap U V) n a.2 := by
  rw [inl_rightMap, inr_rightMap]
  exact biprodSequenceSecondMap_desc (toSmallLeft U V) (toSmallRight U V) n a

/-- The first map is the difference of the actual maps of the two
intersection inclusions. This fixes the sign convention on the sequence. -/
theorem smallLeftHomologyMap_apply (U V : Set X) (n : ℕ)
    (a : SingularHomology (U ∩ V : Set X) n) :
    smallLeftHomologyMap U V n a =
      (singularHomologyMap
        (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n a,
        -singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n a) := by
  rw [smallLeftHomologyMap_components, leftMap_fst, leftMap_snd,
    homologyLinearMap_neg]
  rfl

/-- The second map is the sum of the two actual maps into small-chain
homology, before making any comparison with ambient homology. -/
theorem smallRightHomologyMap_apply (U V : Set X) (n : ℕ)
    (a : SingularHomology U n × SingularHomology V n) :
    smallRightHomologyMap U V n a =
      homologyLinearMap (toSmallLeft U V) n a.1 +
        homologyLinearMap (toSmallRight U V) n a.2 := by
  rw [smallRightHomologyMap_components, inl_rightMap, inr_rightMap]

/-- After the genuine small-to-ambient comparison, the second map is
the sum of the homology maps induced by the actual subtype inclusions. -/
theorem smallHomologyComparison_right (U V : Set X) (n : ℕ)
    (a : SingularHomology U n × SingularHomology V n) :
    smallHomologyComparison U V n (smallRightHomologyMap U V n a) =
      singularHomologyMap (subtypeInclusion U) n a.1 +
        singularHomologyMap (subtypeInclusion V) n a.2 := by
  rw [smallRightHomologyMap_apply, map_add]
  apply congrArg₂ (· + ·)
  · change homologyLinearMap (smallInclusion U V) n
      (homologyLinearMap (toSmallLeft U V) n a.1) = _
    rw [← LinearMap.comp_apply, ← homologyLinearMap_comp, toSmallLeft_inclusion]
  · change homologyLinearMap (smallInclusion U V) n
      (homologyLinearMap (toSmallRight U V) n a.2) = _
    rw [← LinearMap.comp_apply, ← homologyLinearMap_comp, toSmallRight_inclusion]

/-- Exactness at the actual homology of the intersection, in every degree. -/
theorem small_exact_at_intersection (U V : Set X) (n : ℕ) :
    LinearMap.range (smallConnectingMap U V n) =
      LinearMap.ker (smallLeftHomologyMap U V n) :=
  biprodSequence_exact_at_leftHomology (chainSequence_shortExact U V) n

/-- Exactness at the product of the two actual singular homology groups. -/
theorem small_exact_at_pair (U V : Set X) (n : ℕ) :
    LinearMap.range (smallLeftHomologyMap U V n) =
      LinearMap.ker (smallRightHomologyMap U V n) :=
  biprodSequence_exact_at_middleHomology (chainSequence_shortExact U V) n

/-- Exactness at positive-degree actual small-chain homology. -/
theorem small_exact_at_smallHomology (U V : Set X) (n : ℕ) :
    LinearMap.range (smallRightHomologyMap U V (n + 1)) =
      LinearMap.ker (smallConnectingMap U V n) :=
  biprodSequence_exact_at_rightHomology (chainSequence_shortExact U V) n

/-- The degree-zero end of the actual small-chain Mayer–Vietoris sequence. -/
theorem smallRightHomologyMap_zero_surjective (U V : Set X) :
    Function.Surjective (smallRightHomologyMap U V 0) :=
  biprodSequence_second_zero_surjective (chainSequence_shortExact U V)

theorem smallConnectingMap_comp_left (U V : Set X) (n : ℕ) :
    (smallLeftHomologyMap U V n).comp (smallConnectingMap U V n) = 0 := by
  apply LinearMap.ext
  intro a
  have ha : smallConnectingMap U V n a ∈ LinearMap.range (smallConnectingMap U V n) :=
    ⟨a, rfl⟩
  rw [small_exact_at_intersection] at ha
  exact ha

theorem smallLeftHomologyMap_comp_right (U V : Set X) (n : ℕ) :
    (smallRightHomologyMap U V n).comp (smallLeftHomologyMap U V n) = 0 := by
  apply LinearMap.ext
  intro a
  have ha : smallLeftHomologyMap U V n a ∈ LinearMap.range (smallLeftHomologyMap U V n) :=
    ⟨a, rfl⟩
  rw [small_exact_at_pair] at ha
  exact ha

theorem smallRightHomologyMap_comp_connecting (U V : Set X) (n : ℕ) :
    (smallConnectingMap U V n).comp (smallRightHomologyMap U V (n + 1)) = 0 := by
  apply LinearMap.ext
  intro a
  have ha : smallRightHomologyMap U V (n + 1) a ∈
      LinearMap.range (smallRightHomologyMap U V (n + 1)) := ⟨a, rfl⟩
  rw [small_exact_at_smallHomology] at ha
  exact ha

/-- The three successive exactness statements together give the long exact
sequence of the actual small singular chains in all degrees. -/
theorem small_mayerVietoris_exact (U V : Set X) (n : ℕ) :
    LinearMap.range (smallConnectingMap U V n) =
        LinearMap.ker (smallLeftHomologyMap U V n) ∧
      LinearMap.range (smallLeftHomologyMap U V n) =
        LinearMap.ker (smallRightHomologyMap U V n) ∧
      LinearMap.range (smallRightHomologyMap U V (n + 1)) =
        LinearMap.ker (smallConnectingMap U V n) :=
  ⟨small_exact_at_intersection U V n, small_exact_at_pair U V n,
    small_exact_at_smallHomology U V n⟩

end Wikipedia.HopfProblem.SingularMayerVietoris

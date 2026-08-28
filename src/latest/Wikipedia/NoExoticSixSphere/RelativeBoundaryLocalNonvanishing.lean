import Wikipedia.NoExoticSixSphere.RelativeCoefficientTripleLift
import Wikipedia.NoExoticSixSphere.SupportedLocalZeroNeighborhood

/-!
# Nonzero local boundary values from actual relative localization

A zero local value of the connecting class allows the original class to
lift across a puncture in the subspace. If the ambient local homology at
that point vanishes, the lifted class vanishes on nearby smaller supports.
This contradicts nonzero localization in a dense complement.
-/

noncomputable section

open Set CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeCoefficients

variable {X : Type} [TopologicalSpace X]

theorem mapsTo_puncture_of_not_mem {B : Set X} {y : X} (hy : y ∉ B) :
    Set.MapsTo (ContinuousMap.id X) B ({y}ᶜ : Set X) := by
  intro z hz he
  have hzy : z = y := Set.mem_singleton_iff.mp he
  exact hy (hzy ▸ hz)

omit [TopologicalSpace X] in
theorem overlap_awayFromBoundaryPoint (B : Set X) (x : B) :
    RelativeSingularHomology.overlapIn B (Bᶜ ∪ {x.val})ᶜ = ({x}ᶜ : Set B) := by
  ext y
  change (¬ (y.val ∉ B ∨ y.val = x.val)) ↔ y ≠ x
  constructor
  · intro hy he
    exact hy (Or.inr (congrArg Subtype.val he))
  · intro hy he
    exact he.elim (fun h ↦ h y.property) (fun h ↦ hy (Subtype.ext h))

variable (A : ModuleCat.{0} ℤ) [T2Space X] (B : Set X) (n : ℕ)

theorem connecting_localize_ne_zero (F : (complex A B).homology (n + 1)) (x : B)
    (hpoint : Subsingleton ((complex A ({x.val}ᶜ : Set X)).homology (n + 1)))
    (hnear : ∀ (O : Set X), IsOpen O → x.val ∈ O → ∃ y : X, y ∈ O ∧ y ∉ B)
    (hinterior : ∀ (y : X) (hy : y ∉ B),
      homologyLinearMap (mapChain A (ContinuousMap.id X) (mapsTo_puncture_of_not_mem hy))
        (n + 1) F ≠ 0) :
    homologyLinearMap (projection A ({x}ᶜ : Set B)) n (connecting A B n F) ≠ 0 := by
  classical
  intro hzero
  let K : Set X := Bᶜ ∪ {x.val}
  have hKB : Kᶜ ⊆ B := by
    intro y hy
    by_contra hyB
    exact hy (Or.inl hyB)
  have hzero' : homologyLinearMap (projection A (RelativeSingularHomology.overlapIn B Kᶜ)) n
      (connecting A B n F) = 0 := by
    change homologyLinearMap (projection A
      (RelativeSingularHomology.overlapIn B (Bᶜ ∪ {x.val})ᶜ)) n (connecting A B n F) = 0
    rw [overlap_awayFromBoundaryPoint]
    exact hzero
  obtain ⟨G, hG⟩ := exists_lift_of_connecting_projection_zero A hKB n F hzero'
  have hxK : x.val ∈ K := Or.inr (Set.mem_singleton x.val)
  have hGzero : SupportedRelativeHomology.evaluate A K x.val hxK (n + 1) G = 0 :=
    hpoint.elim _ _
  obtain ⟨O, hO, hxO, hvanish⟩ :=
    SupportedRelativeHomology.exists_zero_restriction_neighborhood A K (n + 1) G x.val hxK hGzero
  obtain ⟨y, hyO, hyB⟩ := hnear O hO hxO
  have hyK : y ∈ K := Or.inl hyB
  have hyzero : SupportedRelativeHomology.evaluate A K y hyK (n + 1) G = 0 :=
    hvanish {y} (Set.singleton_subset_iff.mpr hyK) (Set.singleton_subset_iff.mpr hyO)
  have hcomp := mapChain_comp A (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) Kᶜ B from hKB)
    (ContinuousMap.id X) (mapsTo_puncture_of_not_mem hyB)
  simp only [ContinuousMap.id_comp] at hcomp
  have he := congrArg (fun m ↦ homologyLinearMap m (n + 1)) hcomp
  simp only [homologyLinearMap_comp] at he
  have hlocal : SupportedRelativeHomology.evaluate A K y hyK (n + 1) G =
      homologyLinearMap (mapChain A (ContinuousMap.id X) (mapsTo_puncture_of_not_mem hyB))
        (n + 1) F :=
    (LinearMap.congr_fun he G).trans
      (congrArg (homologyLinearMap
        (mapChain A (ContinuousMap.id X) (mapsTo_puncture_of_not_mem hyB)) (n + 1)) hG)
  exact hinterior y hyB (hlocal.symm.trans hyzero)

end NoExoticSixSphere.RelativeCoefficients

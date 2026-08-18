/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section93AffineRankBound
import ErdosProblems.Erdos186.CFP.Bilu.Section93LatticeSectionCoordinates

/-!
# Bilu Section 9.3: the homogeneous affine lattice

The source affine span is made linear without choosing a translation in the
target group: an integral lift `z` is sent to the homogeneous integral point
`(z, 1)`.  Its linear span has dimension at most affine-dimension plus one,
is spanned by its literal integral points, and therefore has the full
intersection-lattice coordinates constructed in
`Section93LatticeSectionCoordinates`.
-/

namespace Erdos186.CFP.Bilu.Section93HomogeneousAffineSpan

open Set Module Submodule
open scoped Pointwise
open CFP.BiluFreiman
open Mahler MinkowskiSecond
open Section7FreimanMap Section7AffineSlice
open Section9KernelAffineReduction
open Section4PresentationLiftSet Section8PresentationNormalization
open Section92PresentationDescent Section92OuterInjectivityBridge
open Proposition75Case2Construction
open Section93AffineRankBound
open SubspaceLattice

noncomputable section

set_option autoImplicit false

variable {n : ℕ}

/-- Append the homogeneous coordinate `1` to an integral point. -/
def homogeneousIntegralPoint (z : IntegralPoint n) : IntegralPoint (n + 1) :=
  joinIntegralCoordinates z (fun _ : Fin 1 ↦ 1)

/-- The homogeneous point in the standard real ambient space. -/
def homogeneousRealPoint (z : IntegralPoint n) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  integralReal (homogeneousIntegralPoint z)

theorem homogeneousIntegralPoint_injective :
    Function.Injective (@homogeneousIntegralPoint n) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy (Fin.castAdd 1 i)
  simpa [homogeneousIntegralPoint, joinIntegralCoordinates] using hi

/-- The finite set of homogeneous lifts. -/
def homogeneousLiftSet (K : Finset (IntegralPoint n)) :
    Finset (EuclideanSpace ℝ (Fin (n + 1))) :=
  K.image homogeneousRealPoint

/-- The linearized affine span used in Section 9.3. -/
def homogeneousSubspace (K : Finset (IntegralPoint n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  Submodule.span ℝ (homogeneousLiftSet K : Set _)

@[simp] theorem card_homogeneousLiftSet (K : Finset (IntegralPoint n)) :
    (homogeneousLiftSet K).card = K.card := by
  rw [homogeneousLiftSet, Finset.card_image_of_injective]
  exact Section93AffineRankBound.integralReal_injective_local.comp
    homogeneousIntegralPoint_injective

/-- The faithful real image of the original integral lifts. -/
def realLiftSet (K : Finset (IntegralPoint n)) :
    Finset (EuclideanSpace ℝ (Fin n)) :=
  K.image integralReal

/-- The cone map based at `a`: `(d,t) ↦ (d+t a,t)`. -/
def homogeneousConeMap (K : Finset (IntegralPoint n))
    (a : IntegralPoint n) (ha : a ∈ K) :
    (affineDirection (realLiftSet K) × ℝ) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) where
  toFun z := WithLp.toLp 2 <| fun j ↦
    Sum.elim
      ((z.1 : EuclideanSpace ℝ (Fin n)) +
        z.2 • integralReal a)
      (fun _ : Fin 1 ↦ z.2)
      (finSumFinEquiv.symm j)
  map_add' x y := by
    ext j
    generalize hs : finSumFinEquiv.symm j = s
    cases s <;> simp [hs, add_smul, add_assoc, add_left_comm,
      WithLp.toLp_add]
  map_smul' c x := by
    ext j
    generalize hs : finSumFinEquiv.symm j = s
    cases s
    · simp [hs, mul_smul]
      ring
    · simp [hs, mul_smul]

theorem integralReal_sub_mem_affineDirection_realLiftSet
    (K : Finset (IntegralPoint n)) {z a : IntegralPoint n}
    (hz : z ∈ K) (ha : a ∈ K) :
    integralReal z - integralReal a ∈
      (affineSpan ℝ
        (↑(realLiftSet K) : Set (EuclideanSpace ℝ (Fin n)))).direction := by
  exact AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ
      (↑(realLiftSet K) : Set (EuclideanSpace ℝ (Fin n)))
      (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
    (subset_affineSpan ℝ
      (↑(realLiftSet K) : Set (EuclideanSpace ℝ (Fin n)))
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩))

theorem homogeneousRealPoint_mem_range_coneMap
    (K : Finset (IntegralPoint n)) (a : IntegralPoint n) (ha : a ∈ K)
    {z : IntegralPoint n} (hz : z ∈ K) :
    homogeneousRealPoint z ∈ LinearMap.range (homogeneousConeMap K a ha) := by
  let za : affineDirection (realLiftSet K) :=
    ⟨integralReal z - integralReal a,
      by simpa only [affineDirection] using
        integralReal_sub_mem_affineDirection_realLiftSet K hz ha⟩
  refine ⟨(za, 1), ?_⟩
  ext j
  generalize hs : finSumFinEquiv.symm j = s
  cases s with
  | inl i =>
      simp [homogeneousConeMap, homogeneousRealPoint,
        homogeneousIntegralPoint, joinIntegralCoordinates, hs, za]
  | inr i =>
      simp [homogeneousConeMap, homogeneousRealPoint,
        homogeneousIntegralPoint, joinIntegralCoordinates, hs]

theorem homogeneousSubspace_le_range_coneMap
    (K : Finset (IntegralPoint n)) (a : IntegralPoint n) (ha : a ∈ K) :
    homogeneousSubspace K ≤ LinearMap.range (homogeneousConeMap K a ha) := by
  rw [homogeneousSubspace, Submodule.span_le]
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  exact homogeneousRealPoint_mem_range_coneMap K a ha hz

/-- Homogenization adds at most one to affine rank. -/
theorem finrank_homogeneousSubspace_le_affine_add_one
    (K : Finset (IntegralPoint n)) (a : IntegralPoint n) (ha : a ∈ K) :
    finrank ℝ (homogeneousSubspace K) ≤
      finrank ℝ (affineDirection (realLiftSet K)) + 1 := by
  calc
    finrank ℝ (homogeneousSubspace K) ≤
        finrank ℝ (LinearMap.range (homogeneousConeMap K a ha)) :=
      Submodule.finrank_mono (homogeneousSubspace_le_range_coneMap K a ha)
    _ ≤ finrank ℝ (affineDirection (realLiftSet K) × ℝ) :=
      LinearMap.finrank_range_le _
    _ = finrank ℝ (affineDirection (realLiftSet K)) + 1 := by
      simp [Module.finrank_prod]

/-- Every homogeneous generator is a literal integral point of its span. -/
theorem homogeneousRealPoint_mem_integralPoints
    (K : Finset (IntegralPoint n)) {z : IntegralPoint n} (hz : z ∈ K) :
    (⟨homogeneousRealPoint z,
      Submodule.subset_span (Finset.mem_image.mpr ⟨z, hz, rfl⟩)⟩ :
        homogeneousSubspace K) ∈ integralPoints (homogeneousSubspace K) := by
  rw [mem_integralPoints_iff]
  exact ⟨homogeneousIntegralPoint z, rfl⟩

/-- The full intersection lattice spans the homogeneous affine subspace. -/
theorem span_integralPoints_homogeneousSubspace
    (K : Finset (IntegralPoint n)) :
    Submodule.span ℝ
      ((integralPoints (homogeneousSubspace K) :
        Submodule ℤ (homogeneousSubspace K)) :
          Set (homogeneousSubspace K)) = ⊤ := by
  apply top_unique
  intro x hx
  let P := Submodule.span ℝ
    ((integralPoints (homogeneousSubspace K) :
      Submodule ℤ (homogeneousSubspace K)) :
        Set (homogeneousSubspace K))
  have hxP : ∀ hy : (x : EuclideanSpace ℝ (Fin (n + 1))) ∈
      homogeneousSubspace K, (⟨x, hy⟩ : homogeneousSubspace K) ∈ P :=
    Submodule.span_induction (p := fun y _ ↦
        ∀ hy : y ∈ homogeneousSubspace K,
          (⟨y, hy⟩ : homogeneousSubspace K) ∈ P)
      (by
        intro y hy hyL
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        exact Submodule.subset_span
          (homogeneousRealPoint_mem_integralPoints K hz))
      (by intro; exact Submodule.zero_mem P)
      (by
        intro y z hy hz hy' hz' hyz
        exact Submodule.add_mem P (hy' hy) (hz' hz))
      (by
        intro c y hy hy' hcy
        exact Submodule.smul_mem P c (hy' hy))
      x.property
  exact hxP x.property

/-- The source doubling hypothesis gives the uniform homogeneous rank bound. -/
theorem normalizedLiftSet_homogeneous_rank_le_two_mul_ceil
    {A : Finset ℤ} (s : ℕ) (hs : 0 < s)
    (X : RankedBodyPresentation A) (hX : EnlargedInjective s X)
    (hA : A.Nonempty) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hdouble : ((twoA A).card : ℝ) ≤ sigma * A.card) :
    finrank ℝ (homogeneousSubspace (Section8PresentationNormalization.normalizedLiftSet X))
      ≤ 2 * Nat.ceil sigma := by
  obtain ⟨a, ha⟩ : (Section8PresentationNormalization.normalizedLiftSet X).Nonempty := by
    rw [← Finset.card_pos,
      Section8PresentationNormalization.card_normalizedLiftSet]
    exact hA.card_pos
  refine (finrank_homogeneousSubspace_le_affine_add_one
    (Section8PresentationNormalization.normalizedLiftSet X) a ha).trans ?_
  exact normalizedLiftSet_affineRank_add_one_le_two_mul_ceil
    s hs X hX hA sigma hsigma hdouble

/-- Section 9.3 applied to the chosen source lifts of an arbitrary stopped
body presentation. -/
theorem presentationLiftSet_homogeneous_rank_le_two_mul_ceil
    {A : Finset ℤ} (s : ℕ) (hs : 0 < s)
    (X : RankedBodyPresentation A) (hX : EnlargedInjective s X)
    (hA : A.Nonempty) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hdouble : ((twoA A).card : ℝ) ≤ sigma * A.card) :
    finrank ℝ (homogeneousSubspace (presentationLiftSet X)) ≤
      2 * Nat.ceil sigma := by
  obtain ⟨a, ha⟩ : (presentationLiftSet X).Nonempty := by
    rw [← Finset.card_pos, card_presentationLiftSet]
    exact hA.card_pos
  refine (finrank_homogeneousSubspace_le_affine_add_one
    (presentationLiftSet X) a ha).trans ?_
  apply Section93AffineRankBound.finrank_affineDirection_add_one_le_two_mul
    (realLiftSet (presentationLiftSet X))
  · rw [← Finset.card_pos, realLiftSet,
      Finset.card_image_of_injective _
        Section93AffineRankBound.integralReal_injective_local,
      card_presentationLiftSet]
    exact hA.card_pos
  · have hpair :
        (pairSumset (realLiftSet (presentationLiftSet X))).card =
          (twoA A).card := by
      rw [realLiftSet,
        card_pairSumset_image_eq integralReal
          Section93AffineRankBound.integralReal_injective_local
          Section93AffineRankBound.integralReal_add_local]
      change (presentationLiftSet X + presentationLiftSet X).card =
        (twoA A).card
      exact card_pairSumset_presentationLiftSet_eq_twoA s hs X hX
    have hcard : (realLiftSet (presentationLiftSet X)).card = A.card := by
      rw [realLiftSet, Finset.card_image_of_injective _
        Section93AffineRankBound.integralReal_injective_local,
        card_presentationLiftSet]
    rw [hpair, hcard]
    have hsigmaCeil : sigma ≤ (Nat.ceil sigma : ℝ) := Nat.le_ceil sigma
    have hdoubleReal : ((twoA A).card : ℝ) ≤
        (Nat.ceil sigma : ℝ) * A.card :=
      hdouble.trans (mul_le_mul_of_nonneg_right hsigmaCeil (by positivity))
    exact_mod_cast hdoubleReal

end

end Erdos186.CFP.Bilu.Section93HomogeneousAffineSpan

#print axioms
  Erdos186.CFP.Bilu.Section93HomogeneousAffineSpan.normalizedLiftSet_homogeneous_rank_le_two_mul_ceil
#print axioms
  Erdos186.CFP.Bilu.Section93HomogeneousAffineSpan.span_integralPoints_homogeneousSubspace

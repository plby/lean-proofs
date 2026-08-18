/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section7BiasedNumerics
import ErdosProblems.Erdos186.CFP.Bilu.Section9Replacement

/-!
# Corrected Section 7--9 replacement seed

The old source constructor fixed every offset to zero and paid the crude
`2^r` cell loss in the doubling inequality.  Here the offsets come from
Lemma 6.1, the entropy gain from Lemma 6.3 pays that loss, and `2^r`
remains only as a harmless integral covering constant in the finite
replacement certificate.
-/

namespace Erdos186.CFP.Bilu.Section9BiasedReplacement

open Set Module Submodule MeasureTheory
open scoped ENNReal Pointwise RealInnerProductSpace
open DistortingMeasure BadlyApproximable Proposition75Data
open PolarSeparation Proposition74Construction
open Section7FreimanMap Section7AffineSlice Section7PlaneSeed
open Section8Synthesis SubspaceLattice
open Section6BiasedResidueCell Section7BiasedNumerics
open Proposition75Construction Section9Replacement

noncomputable section

/-- Proposition 7.4 applied to an already selected biased affine slice. -/
theorem exists_geometricData_of_sourceAffineSlice
    {m r proportionConstant : ℕ}
    {K : Finset (Mahler.IntegralPoint m)}
    {a : Fin r → EuclideanSpace ℝ (Fin m)} {b : Fin r → ℝ}
    {alpha : Fin r → Fin 2}
    (W : SourceAffineSlice a b proportionConstant (residueCell a b alpha K))
    (hcell : (residueCell a b alpha K).Nonempty)
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (hKB : ∀ x ∈ K, integralReal x ∈ B)
    (p : Seminorm ℝ (Fin m → ℝ))
    (hindependent : Mahler.AdmitsIndependent p m 1)
    (hunit : ∀ x : Mahler.IntegralPoint m,
      p (Mahler.integralEmbed x) ≤ 1 → integralReal x ∈ (2 : ℝ) • B) :
    ∃ D : GeometricData B a, ∃ x0 ∈ W.sourceSlice,
      ∀ x ∈ W.sourceSlice, freimanDifference a b x x0 ∈ D.C0 := by
  obtain ⟨planeSeed, hplaneBody, hplaneLattice, hplaneCard, hplaneSpan⟩ :=
    W.exists_planeSeed hbalanced hconvex (fun x hx ↦ hKB x
      ((mem_residueCell a b alpha K x).mp hx |>.1))
  let D := geometricDataOfPlaneAndAdmitsIndependent
    B a p planeSeed hindependent hunit hplaneBody hplaneLattice hplaneCard
  obtain ⟨x0, hx0⟩ := W.sourceSlice_nonempty hcell
  refine ⟨D, x0, hx0, ?_⟩
  intro x hx
  have hvec : freimanDifference a b x x0 ∈
      vectorSpan ℝ
        (freimanRealMap a b ''
          (W.sourceSlice : Set (Mahler.IntegralPoint m))) := by
    rw [vectorSpan_def]
    apply Submodule.subset_span
    exact ⟨freimanRealMap a b x, ⟨x, hx, rfl⟩,
      freimanRealMap a b x0, ⟨x0, hx0, rfl⟩, rfl⟩
  rw [← hplaneSpan] at hvec
  change freimanDifference a b x x0 ∈
    seedSubspace (planeSeed ∪ fullRankLiftSeed a hindependent.choose)
  exact Submodule.span_mono (by
    intro z hz
    exact Finset.mem_union_left _ hz) hvec

/-- The finite Lemma 4.5 seed, allowing the nonzero offsets selected by
Lemma 6.1. -/
def lemma45SectionSeedOfBiasedAffineSlice
    {m r proportionConstant : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)} {b : Fin r → ℝ}
    {K : Finset (Mahler.IntegralPoint m)} {alpha : Fin r → Fin 2}
    (W : SourceAffineSlice a b proportionConstant (residueCell a b alpha K))
    (hcell : (residueCell a b alpha K).Nonempty)
    (D : GeometricData B a) (hKB : ∀ x ∈ K, integralReal x ∈ B)
    (hlarge : K.card ≤
      (2 ^ r * proportionConstant) * W.sourceSlice.card)
    (x0 : Mahler.IntegralPoint m) (hx0 : x0 ∈ W.sourceSlice)
    (hdiff : ∀ x ∈ W.sourceSlice, freimanDifference a b x x0 ∈ D.C0) :
    Lemma45SectionSeed D K (2 ^ r * proportionConstant) where
  sourceSlice := W.sourceSlice
  sourceSlice_nonempty := W.sourceSlice_nonempty hcell
  sourceSlice_subset := fun x hx ↦
    ((mem_residueCell a b alpha K x).mp (W.sourceSlice_subset hx)).1
  base := x0
  base_mem := hx0
  offset := b
  embed :=
    { toFun := fun x ↦ ⟨freimanDifference a b x x0, hdiff x x.property⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        have hxy' := congrArg (fun z : D.C0 ↦ (z : Ambient m r)) hxy
        change freimanRealMap a b x - freimanRealMap a b x0 =
          freimanRealMap a b y - freimanRealMap a b x0 at hxy'
        exact freimanRealMap_injective a b (sub_left_inj.mp hxy') }
  embed_apply := fun _ ↦ rfl
  embed_body := by
    intro x
    exact freimanDifference_mem_distortionBody_of_mem hbalanced hconvex
      a b x x0
      (hKB x (((mem_residueCell a b alpha K x).mp
        (W.sourceSlice_subset x.property)).1))
      (hKB x0 (((mem_residueCell a b alpha K x0).mp
        (W.sourceSlice_subset hx0)).1))
  embed_lattice := by
    intro x
    exact freimanDifference_mem_ambientProductIntegralPoints a b x x0
  head_injective := by
    intro x y hxy
    apply Subtype.ext
    change integralReal (x : Mahler.IntegralPoint m) - integralReal x0 =
      integralReal (y : Mahler.IntegralPoint m) - integralReal x0 at hxy
    have hreal : integralReal (x : Mahler.IntegralPoint m) =
        integralReal (y : Mahler.IntegralPoint m) := sub_left_inj.mp hxy
    ext i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin m) ↦ z i) hreal
    change (((x : Mahler.IntegralPoint m) i : ℤ) : ℝ) =
      (((y : Mahler.IntegralPoint m) i : ℤ) : ℝ) at hi
    exact_mod_cast hi
  large := hlarge

/-- Source-correct Sections 5--8 synthesis into the Section 9 finite
replacement certificate.  There is no dyadic-rank premise: `r`, the
distortion amount, and the affine gap are chosen internally. -/
theorem exists_lemma45SectionSeed_of_proposition83_biased
    {m : ℕ} (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (sigma epsilon : ℝ) (hsigma : 1 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (hKB : ∀ x ∈ K, integralReal x ∈ B)
    (p : Seminorm ℝ (Fin m → ℝ))
    (hindependent : Mahler.AdmitsIndependent p m 1)
    (hunit : ∀ x : Mahler.IntegralPoint m,
      p (Mahler.integralEmbed x) ≤ 1 → integralReal x ∈ (2 : ℝ) • B)
    (hpolarMeasurable :
      MeasurableSet (euclideanPolar (WithLp.ofLp '' B)))
    (hpolarVolume :
      volume (euclideanPolar (WithLp.ofLp '' B)) ≤
        ENNReal.ofReal ((4 : ℝ) ^ m / (epsilon * K.card)))
    (hepsilon : proposition83Threshold m (distortionRank sigma) sigma < epsilon) :
    ∃ proportionConstant : ℕ,
      ∃ a : Fin (distortionRank sigma) → EuclideanSpace ℝ (Fin m),
        ∃ b : Fin (distortionRank sigma) → ℝ,
          ∃ D : GeometricData B a,
            (∀ i, WithLp.ofLp (a i) ∈
              cubeDistortingSet (distortionDelta sigma) K) ∧
            IsBadlyApproximable
              (euclideanPolar (WithLp.ofLp '' B))
              (epsilon ^ proposition83Exponent m (distortionRank sigma))
              (epsilon ^ proposition83Exponent m (distortionRank sigma))
              (fun i ↦ WithLp.ofLp (a i)) ∧
            Nonempty (Lemma45SectionSeed D K
              (2 ^ distortionRank sigma * proportionConstant)) := by
  obtain ⟨proportionConstant, a, b, alpha, haCube, haBad,
      _hbiased, hcover, W⟩ :=
    exists_biased_sourceAffineSlice_of_proposition83 K hK sigma epsilon
      hsigma hsum (euclideanPolar (WithLp.ofLp '' B)) hpolarMeasurable
      hpolarVolume hepsilon
  obtain ⟨W⟩ := W
  have hcell : (residueCell a b alpha K).Nonempty := by
    rw [← Finset.card_pos]
    by_contra hzero
    have hzero' : (residueCell a b alpha K).card = 0 :=
      Nat.eq_zero_of_not_pos hzero
    have hcover' := hcover
    rw [hzero', mul_zero] at hcover'
    exact (not_le_of_gt hK.card_pos) hcover'
  obtain ⟨D, x0, hx0, hdiff⟩ :=
    exists_geometricData_of_sourceAffineSlice W hcell B hbalanced hconvex
      hKB p hindependent hunit
  have hlarge : K.card ≤
      (2 ^ distortionRank sigma * proportionConstant) *
        W.sourceSlice.card := by
    calc
      K.card ≤ 2 ^ distortionRank sigma *
          (residueCell a b alpha K).card := hcover
      _ ≤ 2 ^ distortionRank sigma *
          (proportionConstant * W.sourceSlice.card) :=
        Nat.mul_le_mul_left _ W.card_le
      _ = (2 ^ distortionRank sigma * proportionConstant) *
          W.sourceSlice.card := by simp only [mul_assoc]
  let S : Lemma45SectionSeed D K
      (2 ^ distortionRank sigma * proportionConstant) :=
    lemma45SectionSeedOfBiasedAffineSlice hbalanced hconvex W hcell D hKB
      hlarge x0 hx0 hdiff
  exact ⟨proportionConstant, a, b, D, haCube, haBad, ⟨S⟩⟩

end

end Erdos186.CFP.Bilu.Section9BiasedReplacement

#print axioms
  Erdos186.CFP.Bilu.Section9BiasedReplacement.lemma45SectionSeedOfBiasedAffineSlice
#print axioms
  Erdos186.CFP.Bilu.Section9BiasedReplacement.exists_lemma45SectionSeed_of_proposition83_biased

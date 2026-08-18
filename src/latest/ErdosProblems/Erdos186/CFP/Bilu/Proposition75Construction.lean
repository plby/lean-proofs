/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Branches
import ErdosProblems.Erdos186.CFP.Bilu.Section7AffineSliceUnconditional
import ErdosProblems.Erdos186.CFP.Bilu.Section5RpowAffineSlice
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Case2Branch

/-!
# The source construction for Bilu Proposition 7.5

This file joins the unconditional affine-slice theorem of Sections 5--7
to the simultaneous distorting/badly-approximable system of Proposition
8.3.  The first lemmas perform the residue-cell selection and construct
the literal `GeometricData` used by Proposition 7.5.
-/

namespace Erdos186.CFP.Bilu.Proposition75Construction

open Set Module Submodule MeasureTheory
open scoped ENNReal Pointwise RealInnerProductSpace
open DistortingMeasure BadlyApproximable Proposition75Data
open Proposition75Case1 Proposition75Case2 Proposition75Branches
open Proposition75Case2Branch
open PolarSeparation
open Proposition74Construction
open Section7FreimanMap Section7AffineSlice Section7AffineSliceUnconditional
open Section7PlaneSeed Section8Synthesis SubspaceLattice
open Section5TwoN Section5RpowAffineSlice Section94RankThresholdBoundary

noncomputable section

/-- The two finite-set presentations of the double sumset used in Sections
7 and 8 agree literally. -/
theorem pairSumset_eq_sumset {m : ℕ}
    (K : Finset (Mahler.IntegralPoint m)) :
    pairSumset K = sumset K := by
  classical
  ext z
  simp only [mem_pairSumset, sumset, Finset.mem_image₂]

/-- Double sumsets are monotone under inclusion. -/
theorem pairSumset_mono {G : Type*} [Add G] [DecidableEq G]
    {S K : Finset G} (hSK : S ⊆ K) :
    pairSumset S ⊆ pairSumset K := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_pairSumset S _).mp hz
  exact (mem_pairSumset K _).mpr ⟨x, hSK hx, y, hSK hy, rfl⟩

/-- The Hilbert product used by Proposition 7.4, written in the ordinary
function coordinates required by the source `2^(d+1-delta)` theorem. -/
noncomputable def ambientFunctionEquiv (m r : ℕ) :
    Ambient m r ≃ₗ[ℝ] (Fin (m + r) → ℝ) :=
  (ambientEquiv m r).toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (Fin (m + r) → ℝ))

/-- Apply the genuine exponential affine-slice theorem to the real Freiman
image of a residue cell, then pull the selected slice and affine plane back
to Bilu's Hilbert-product coordinates. -/
theorem exists_sourceAffineSlice_of_rpow {m r proportionConstant : ℕ}
    (hr : 0 < r) {delta : ℝ}
    (hslice : RpowAffineSliceStatement (r - 1) proportionConstant delta)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (K : Finset (Mahler.IntegralPoint m))
    (hcell : (residueCell a b alpha K).Nonempty)
    (hdouble : ((pairSumset (residueCell a b alpha K)).card : ℝ) ≤
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - delta) *
        (residueCell a b alpha K).card) :
    Nonempty (SourceAffineSlice a b proportionConstant
      (residueCell a b alpha K)) := by
  let S := residueCell a b alpha K
  let e := ambientFunctionEquiv m r
  let f : Mahler.IntegralPoint m → (Fin (m + r) → ℝ) :=
    fun x ↦ e (freimanRealMap a b x)
  let T := S.image f
  have hf : Function.Injective f :=
    e.injective.comp (freimanRealMap_injective a b)
  have hTnonempty : T.Nonempty := hcell.image f
  have hTcard : T.card = S.card :=
    Finset.card_image_of_injective S hf
  have hTimage : T = (S.image (freimanRealMap a b)).image e := by
    change S.image (e ∘ freimanRealMap a b) =
      (S.image (freimanRealMap a b)).image e
    rw [Finset.image_image]
  have hTdouble : (pairSumset T).card = (pairSumset S).card := by
    rw [hTimage, card_pairSumset_image_eq e e.injective e.map_add]
    exact card_pairSumset_realResidueCell a b alpha K
  have hrank : (r - 1) + 1 ≤ m + r := by omega
  obtain ⟨W⟩ := hslice (m + r) hrank T hTnonempty (by
    rw [hTdouble, hTcard]
    exact hdouble)
  refine ⟨{
    sourceSlice := pullbackFinset f S W.slice
    sourceSlice_subset := fun x hx ↦
      (mem_pullbackFinset f S W.slice x |>.mp hx).1
    plane := W.plane.map e.symm.toAffineEquiv.toAffineMap
    dimension_lt := ?_
    image_mem_plane := ?_
    card_le := ?_ }⟩
  · rw [AffineSubspace.map_direction]
    change finrank ℝ (W.plane.direction.map e.symm.toLinearMap) < r
    rw [e.symm.finrank_map_eq]
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr.ne')]
      using W.dimension_lt
  · intro x hx
    rw [AffineSubspace.mem_map]
    refine ⟨f x, W.slice_mem_plane _
      (mem_pullbackFinset f S W.slice x |>.mp hx).2, ?_⟩
    exact e.symm_apply_apply (freimanRealMap a b x)
  · have hpull : (pullbackFinset f S W.slice).card = W.slice.card :=
      card_pullbackFinset_eq f hf S W.slice W.slice_subset
    rw [← hTcard, hpull]
    exact W.card_le

/-- Residue-cell selection in the exact exponential range used by Bilu.
The loss is `2^r`, and no linear `(2r-1)` threshold occurs. -/
theorem exists_large_rpow_residueCell {m r : ℕ}
    (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (sigma delta : ℝ) (hsigma : 0 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hrank : sigma * (2 : ℝ) ^ r ≤
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - delta)) :
    ∃ alpha : Fin r → Fin 2,
      K.card ≤ 2 ^ r * (residueCell a b alpha K).card ∧
      (residueCell a b alpha K).Nonempty ∧
      ((pairSumset (residueCell a b alpha K)).card : ℝ) ≤
        Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - delta) *
          (residueCell a b alpha K).card := by
  obtain ⟨alpha, hlarge⟩ := exists_large_residueCell a b K
  let S := residueCell a b alpha K
  have hSsub : S ⊆ K := by
    intro x hx
    exact (mem_residueCell a b alpha K x).mp hx |>.1
  have hScard : 0 < S.card := by
    by_contra hzero
    have hzero' : S.card = 0 := Nat.eq_zero_of_not_pos hzero
    have hlarge' := hlarge
    change K.card ≤ 2 ^ r * S.card at hlarge'
    rw [hzero', mul_zero] at hlarge'
    exact (not_le_of_gt hK.card_pos) hlarge'
  have hpair_le : (pairSumset S).card ≤ (sumset K).card := by
    apply Finset.card_le_card
    rw [← pairSumset_eq_sumset K]
    exact pairSumset_mono hSsub
  have hlarge_real : (K.card : ℝ) ≤
      (2 : ℝ) ^ r * (S.card : ℝ) := by
    exact_mod_cast hlarge
  refine ⟨alpha, hlarge, Finset.card_pos.mp hScard, ?_⟩
  calc
    ((pairSumset S).card : ℝ) ≤ (sumset K).card := by
      exact_mod_cast hpair_le
    _ ≤ sigma * K.card := hsum
    _ ≤ sigma * ((2 : ℝ) ^ r * S.card) := by
      exact mul_le_mul_of_nonneg_left hlarge_real hsigma
    _ = (sigma * (2 : ℝ) ^ r) * S.card := by ring
    _ ≤ Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - delta) * S.card := by
      exact mul_le_mul_of_nonneg_right hrank (by positivity)

/-- The large residue cell has the strict doubling bound required by the
unconditional `2n` theorem.  This is the quantitative calculation in
Section 7.1. -/
theorem exists_large_lowDoubling_residueCell {m r : ℕ}
    (hr : 0 < r) (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hrank : sigma * (2 : ℝ) ^ r < ((2 * r - 1 : ℕ) : ℝ)) :
    ∃ alpha : Fin r → Fin 2,
      K.card ≤ 2 ^ r * (residueCell a b alpha K).card ∧
      (residueCell a b alpha K).Nonempty ∧
      (pairSumset (residueCell a b alpha K)).card <
        (2 * r - 1) * (residueCell a b alpha K).card := by
  obtain ⟨alpha, hlarge⟩ := exists_large_residueCell a b K
  let S := residueCell a b alpha K
  have hSsub : S ⊆ K := by
    intro x hx
    exact (mem_residueCell a b alpha K x).mp hx |>.1
  have hScard : 0 < S.card := by
    by_contra hzero
    have hzero' : S.card = 0 := Nat.eq_zero_of_not_pos hzero
    have hlarge' := hlarge
    change K.card ≤ 2 ^ r * S.card at hlarge'
    rw [hzero', mul_zero] at hlarge'
    exact (not_le_of_gt hK.card_pos) hlarge'
  have hpair_le : (pairSumset S).card ≤ (sumset K).card := by
    apply Finset.card_le_card
    rw [← pairSumset_eq_sumset K]
    exact pairSumset_mono hSsub
  have hlarge_real : (K.card : ℝ) ≤
      (2 : ℝ) ^ r * (S.card : ℝ) := by
    exact_mod_cast hlarge
  have hScard_real : (0 : ℝ) < S.card := by exact_mod_cast hScard
  have hstrict : ((pairSumset S).card : ℝ) <
      (((2 * r - 1) * S.card : ℕ) : ℝ) := by
    calc
      ((pairSumset S).card : ℝ) ≤ (sumset K).card := by
        exact_mod_cast hpair_le
      _ ≤ sigma * K.card := hsum
      _ ≤ sigma * ((2 : ℝ) ^ r * S.card) := by
        exact mul_le_mul_of_nonneg_left hlarge_real hsigma
      _ = (sigma * (2 : ℝ) ^ r) * S.card := by ring
      _ < ((2 * r - 1 : ℕ) : ℝ) * S.card :=
        mul_lt_mul_of_pos_right hrank hScard_real
      _ = (((2 * r - 1) * S.card : ℕ) : ℝ) := by simp
  refine ⟨alpha, hlarge, Finset.card_pos.mp ?_, ?_⟩
  · simpa only [S] using hScard
  · exact_mod_cast hstrict

/-- Proposition 8.3 returns ordinary coordinate functions; this is their
canonical Euclidean-space restriction to the first `r` entries. -/
def euclideanSystem {m r : ℕ} (a : ℕ → Fin m → ℝ) :
    Fin r → EuclideanSpace ℝ (Fin m) :=
  fun i ↦ WithLp.toLp 2 (a i)

@[simp] theorem ofLp_euclideanSystem {m r : ℕ}
    (a : ℕ → Fin m → ℝ) (i : Fin r) :
    WithLp.ofLp (euclideanSystem (r := r) a i) = a i := rfl

/-- The Section 7 affine slice and Mahler full-rank family construct the
literal Proposition 7.4 subspace for the system selected in Section 8. -/
theorem exists_geometricData_of_lowDoubling {m r : ℕ}
    (hr : 0 < r) (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hrank : sigma * (2 : ℝ) ^ r < ((2 * r - 1 : ℕ) : ℝ))
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (hKB : ∀ x ∈ K, integralReal x ∈ B)
    (p : Seminorm ℝ (Fin m → ℝ))
    (hindependent : Mahler.AdmitsIndependent p m 1)
    (hunit : ∀ x : Mahler.IntegralPoint m,
      p (Mahler.integralEmbed x) ≤ 1 → integralReal x ∈ (2 : ℝ) • B)
    (a : ℕ → Fin m → ℝ) :
    ∃ proportionConstant : ℕ,
      ∃ D : GeometricData B (euclideanSystem (r := r) a),
        ∃ alpha : Fin r → Fin 2,
          ∃ W : SourceAffineSlice (euclideanSystem (r := r) a) 0
            proportionConstant
            (residueCell (euclideanSystem (r := r) a) 0 alpha K),
            K.card ≤
                (2 ^ r * proportionConstant) * W.sourceSlice.card ∧
              ∃ x0 ∈ W.sourceSlice, ∀ x ∈ W.sourceSlice,
                freimanDifference (euclideanSystem (r := r) a) 0 x x0 ∈
                  D.C0 := by
  obtain ⟨proportionConstant, hslice⟩ :=
    exists_constant_sourceAffineSlice r hr
  obtain ⟨alpha, hlarge, hcell, hdouble⟩ :=
    exists_large_lowDoubling_residueCell hr K hK
      (euclideanSystem (r := r) a) 0 sigma hsigma hsum hrank
  obtain ⟨W⟩ := hslice m (euclideanSystem (r := r) a) 0 alpha K
    hcell hdouble
  obtain ⟨planeSeed, hplaneBody, hplaneLattice, hplaneCard, hplaneSpan⟩ :=
    W.exists_planeSeed hbalanced hconvex (fun x hx ↦ hKB x
      ((mem_residueCell (euclideanSystem (r := r) a) 0 alpha K x).mp
        hx |>.1))
  let D := geometricDataOfPlaneAndAdmitsIndependent
    B (euclideanSystem (r := r) a) p planeSeed hindependent hunit
      hplaneBody hplaneLattice hplaneCard
  obtain ⟨x0, hx0⟩ := W.sourceSlice_nonempty hcell
  refine ⟨proportionConstant, D, alpha, W, ?_, x0, hx0, ?_⟩
  · calc
      K.card ≤ 2 ^ r *
          (residueCell (euclideanSystem (r := r) a) 0 alpha K).card := hlarge
      _ ≤ 2 ^ r * (proportionConstant * W.sourceSlice.card) :=
        Nat.mul_le_mul_left (2 ^ r) W.card_le
      _ = (2 ^ r * proportionConstant) * W.sourceSlice.card := by
        simp only [mul_assoc]
  · intro x hx
    have hvec : freimanDifference (euclideanSystem (r := r) a) 0 x x0 ∈
        vectorSpan ℝ
          (freimanRealMap (euclideanSystem (r := r) a) 0 ''
            (W.sourceSlice : Set (Mahler.IntegralPoint m))) := by
      rw [vectorSpan_def]
      apply Submodule.subset_span
      exact ⟨freimanRealMap (euclideanSystem (r := r) a) 0 x,
        ⟨x, hx, rfl⟩,
        freimanRealMap (euclideanSystem (r := r) a) 0 x0,
        ⟨x0, hx0, rfl⟩, rfl⟩
    rw [← hplaneSpan] at hvec
    change freimanDifference (euclideanSystem (r := r) a) 0 x x0 ∈
      seedSubspace (planeSeed ∪
        fullRankLiftSeed (euclideanSystem (r := r) a)
          hindependent.choose)
    exact Submodule.span_mono (by
      intro z hz
      exact Finset.mem_union_left _ hz) hvec

/-- The same Proposition 7.4 construction in the genuine source
`2^(r-delta)` range.  The affine slice is supplied by Freiman's exponential
theorem, not by the interim linear `2r-1` theorem. -/
theorem exists_geometricData_of_rpowDoubling {m r : ℕ}
    (hr : 0 < r) {delta : ℝ} (hdelta : 0 < delta)
    (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hrank : sigma * (2 : ℝ) ^ r ≤
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - delta))
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (hKB : ∀ x ∈ K, integralReal x ∈ B)
    (p : Seminorm ℝ (Fin m → ℝ))
    (hindependent : Mahler.AdmitsIndependent p m 1)
    (hunit : ∀ x : Mahler.IntegralPoint m,
      p (Mahler.integralEmbed x) ≤ 1 → integralReal x ∈ (2 : ℝ) • B)
    (a : ℕ → Fin m → ℝ) :
    ∃ proportionConstant : ℕ,
      ∃ D : GeometricData B (euclideanSystem (r := r) a),
        ∃ alpha : Fin r → Fin 2,
          ∃ W : SourceAffineSlice (euclideanSystem (r := r) a) 0
            proportionConstant
            (residueCell (euclideanSystem (r := r) a) 0 alpha K),
            K.card ≤
                (2 ^ r * proportionConstant) * W.sourceSlice.card ∧
              ∃ x0 ∈ W.sourceSlice, ∀ x ∈ W.sourceSlice,
                freimanDifference (euclideanSystem (r := r) a) 0 x x0 ∈
                  D.C0 := by
  obtain ⟨proportionConstant, hslice⟩ :=
    exists_rpowAffineSliceStatement (r - 1) delta hdelta
  obtain ⟨alpha, hlarge, hcell, hdouble⟩ :=
    exists_large_rpow_residueCell K hK
      (euclideanSystem (r := r) a) 0 sigma delta hsigma hsum hrank
  obtain ⟨W⟩ := exists_sourceAffineSlice_of_rpow hr hslice
    (euclideanSystem (r := r) a) 0 alpha K hcell hdouble
  obtain ⟨planeSeed, hplaneBody, hplaneLattice, hplaneCard, hplaneSpan⟩ :=
    W.exists_planeSeed hbalanced hconvex (fun x hx ↦ hKB x
      ((mem_residueCell (euclideanSystem (r := r) a) 0 alpha K x).mp
        hx |>.1))
  let D := geometricDataOfPlaneAndAdmitsIndependent
    B (euclideanSystem (r := r) a) p planeSeed hindependent hunit
      hplaneBody hplaneLattice hplaneCard
  obtain ⟨x0, hx0⟩ := W.sourceSlice_nonempty hcell
  refine ⟨proportionConstant, D, alpha, W, ?_, x0, hx0, ?_⟩
  · calc
      K.card ≤ 2 ^ r *
          (residueCell (euclideanSystem (r := r) a) 0 alpha K).card := hlarge
      _ ≤ 2 ^ r * (proportionConstant * W.sourceSlice.card) :=
        Nat.mul_le_mul_left (2 ^ r) W.card_le
      _ = (2 ^ r * proportionConstant) * W.sourceSlice.card := by
        simp only [mul_assoc]
  · intro x hx
    have hvec : freimanDifference (euclideanSystem (r := r) a) 0 x x0 ∈
        vectorSpan ℝ
          (freimanRealMap (euclideanSystem (r := r) a) 0 ''
            (W.sourceSlice : Set (Mahler.IntegralPoint m))) := by
      rw [vectorSpan_def]
      apply Submodule.subset_span
      exact ⟨freimanRealMap (euclideanSystem (r := r) a) 0 x,
        ⟨x, hx, rfl⟩,
        freimanRealMap (euclideanSystem (r := r) a) 0 x0,
        ⟨x0, hx0, rfl⟩, rfl⟩
    rw [← hplaneSpan] at hvec
    change freimanDifference (euclideanSystem (r := r) a) 0 x x0 ∈
      seedSubspace (planeSeed ∪
        fullRankLiftSeed (euclideanSystem (r := r) a)
          hindependent.choose)
    exact Submodule.span_mono (by
      intro z hz
      exact Finset.mem_union_left _ hz) hvec

/-- The complete Sections 7--8 synthesis up to Proposition 7.4.  The same
system is simultaneously badly approximable, lies in the distorting unit
cube, and defines the constructed section `D.C0`. -/
theorem exists_geometricData_of_proposition83 {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (sigma epsilon : ℝ) (hsigma : 1 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hrank : sigma * (2 : ℝ) ^ r < ((2 * r - 1 : ℕ) : ℝ))
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
    (hepsilon : proposition83Threshold m r sigma < epsilon) :
    ∃ proportionConstant : ℕ,
      ∃ a : Fin r → EuclideanSpace ℝ (Fin m),
        ∃ D : GeometricData B a,
          ∃ alpha : Fin r → Fin 2,
            ∃ W : SourceAffineSlice a 0 proportionConstant
              (residueCell a 0 alpha K),
              (∀ i, WithLp.ofLp (a i) ∈
                cubeDistortingSet (1 / (2 * Real.sqrt sigma)) K) ∧
              IsBadlyApproximable
                (euclideanPolar (WithLp.ofLp '' B))
                (epsilon ^ proposition83Exponent m r)
                (epsilon ^ proposition83Exponent m r)
                (fun i ↦ WithLp.ofLp (a i)) ∧
              K.card ≤
                  (2 ^ r * proportionConstant) * W.sourceSlice.card ∧
                ∃ x0 ∈ W.sourceSlice, ∀ x ∈ W.sourceSlice,
                  freimanDifference a 0 x x0 ∈ D.C0 := by
  have hdim : 0 < 2 * m + r := by omega
  obtain ⟨aSeq, haCube, haBad⟩ := bilu_proposition_8_3
    K (euclideanPolar (WithLp.ofLp '' B)) sigma epsilon hK hsigma hdim
    hsum hpolarMeasurable hpolarVolume hepsilon
  obtain ⟨proportionConstant, D, alpha, W, hlarge, x0, hx0, hdiff⟩ :=
    exists_geometricData_of_lowDoubling hr K hK sigma
      (zero_le_one.trans hsigma) hsum hrank B hbalanced hconvex hKB
      p hindependent hunit aSeq
  refine ⟨proportionConstant, euclideanSystem (r := r) aSeq,
    D, alpha, W, ?_, ?_, hlarge, x0, hx0, hdiff⟩
  · intro i
    exact haCube i i.isLt
  · simpa only [BadlyApproximable.IsBadlyApproximableUpTo,
      ofLp_euclideanSystem] using haBad

/-- Complete Sections 7--8 synthesis in the genuine exponential doubling
range.  This is the source-correct constructor to be consumed by
Proposition 7.5 and Section 9. -/
theorem exists_geometricData_of_proposition83_rpow {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r) {delta : ℝ} (hdelta : 0 < delta)
    (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (sigma epsilon : ℝ) (hsigma : 1 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hrank : sigma * (2 : ℝ) ^ r ≤
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - delta))
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
    (hepsilon : proposition83Threshold m r sigma < epsilon) :
    ∃ proportionConstant : ℕ,
      ∃ a : Fin r → EuclideanSpace ℝ (Fin m),
        ∃ D : GeometricData B a,
          ∃ alpha : Fin r → Fin 2,
            ∃ W : SourceAffineSlice a 0 proportionConstant
              (residueCell a 0 alpha K),
              (∀ i, WithLp.ofLp (a i) ∈
                cubeDistortingSet (1 / (2 * Real.sqrt sigma)) K) ∧
              IsBadlyApproximable
                (euclideanPolar (WithLp.ofLp '' B))
                (epsilon ^ proposition83Exponent m r)
                (epsilon ^ proposition83Exponent m r)
                (fun i ↦ WithLp.ofLp (a i)) ∧
              K.card ≤
                  (2 ^ r * proportionConstant) * W.sourceSlice.card ∧
                ∃ x0 ∈ W.sourceSlice, ∀ x ∈ W.sourceSlice,
                  freimanDifference a 0 x x0 ∈ D.C0 := by
  have hdim : 0 < 2 * m + r := by omega
  obtain ⟨aSeq, haCube, haBad⟩ := bilu_proposition_8_3
    K (euclideanPolar (WithLp.ofLp '' B)) sigma epsilon hK hsigma hdim
    hsum hpolarMeasurable hpolarVolume hepsilon
  obtain ⟨proportionConstant, D, alpha, W, hlarge, x0, hx0, hdiff⟩ :=
    exists_geometricData_of_rpowDoubling hr hdelta K hK sigma
      (zero_le_one.trans hsigma) hsum hrank B hbalanced hconvex hKB
      p hindependent hunit aSeq
  refine ⟨proportionConstant, euclideanSystem (r := r) aSeq,
    D, alpha, W, ?_, ?_, hlarge, x0, hx0, hdiff⟩
  · intro i
    exact haCube i i.isLt
  · simpa only [BadlyApproximable.IsBadlyApproximableUpTo,
      ofLp_euclideanSystem] using haBad

/-- The common expansion parameter `X=C=epsilon^q` in Proposition 8.3 is
strictly positive in the nondegenerate source range. -/
theorem proposition83Parameter_pos {m r : ℕ} {sigma epsilon : ℝ}
    (hsigma : 1 ≤ sigma) (hdim : 0 < 2 * m + r)
    (hepsilon : proposition83Threshold m r sigma < epsilon) :
    0 < epsilon ^ proposition83Exponent m r := by
  have hsigma_pos : 0 < sigma := zero_lt_one.trans_le hsigma
  have hthreshold : 0 < proposition83Threshold m r sigma := by
    simp only [proposition83Threshold]
    positivity
  have hepsilon_pos : 0 < epsilon := hthreshold.trans hepsilon
  exact Real.rpow_pos_of_pos hepsilon_pos _

/-- The large-covolume side of the Proposition 7.5 dichotomy, with the
source's explicit uniform constant `c81` and scale `X⁻¹`. -/
theorem case1Branch_of_covolume_ge {m r : ℕ} (hm : 0 < m)
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hmeasurable : MeasurableSet B) (hconvex : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (ha : ∀ i, WithLp.ofLp (a i) ∈ Section8Synthesis.unitCubeIoc m)
    (hhead : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m))
      (((m : ℝ) + 1)⁻¹) ⊆ (2 : ℝ) • B)
    (D : GeometricData B a) {X : ℝ} (hX : 0 < X)
    (hcovol : X ≤ ZLattice.covolume
      D.latticePoints μHE[finrank ℝ D.C0]) :
    Case1Branch D (case1SourceConstant m r)
      (ENNReal.ofReal X)⁻¹ := by
  let W : Case1Witness D (((m : ℝ) + 1)⁻¹) :=
    case1WitnessOfUnitCubeIoc hm D hmeasurable hconvex hhead ha
  refine ⟨((m : ℝ) + 1)⁻¹, W,
    case1GeometryFactor_le_sourceConstant D, ?_⟩
  have hX0 : ENNReal.ofReal X ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hX
  have hXtop : ENNReal.ofReal X ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    1 = (ENNReal.ofReal X)⁻¹ * ENNReal.ofReal X :=
      (ENNReal.inv_mul_cancel hX0 hXtop).symm
    _ ≤ (ENNReal.ofReal X)⁻¹ * ENNReal.ofReal
        (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0]) := by
      gcongr

/-- The dimension part of the Case 2 estimate after extracting the common
factor `X⁻¹`. -/
noncomputable def case2SourceFactor (m r d k : ℕ) : ENNReal :=
  (2 : ENNReal)⁻¹ *
    (((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ *
      ((2 : ENNReal) ^ (m + r)) *
      (((d.factorial : ENNReal) *
        ENNReal.ofReal ((((m : ℝ) + 1)⁻¹) ^ k))⁻¹ *
        ((d + k).factorial : ENNReal))) *
    ENNReal.ofReal (Real.sqrt (m + r))

/-- A finite maximum makes the Case 2 constant independent of the
dimension of the selected Proposition 7.4 section. -/
noncomputable def case2SourceConstant (m r : ℕ) : ENNReal :=
  (Finset.range (m + r + 1)).sup fun d ↦
    (Finset.range (m + r + 1)).sup fun k ↦
      case2SourceFactor m r d k

theorem case2SourceFactor_le_constant {m r d k : ℕ}
    (hd : d ≤ m + r) (hk : k ≤ m + r) :
    case2SourceFactor m r d k ≤ case2SourceConstant m r := by
  exact (Finset.le_sup (f := fun k ↦ case2SourceFactor m r d k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans
    (Finset.le_sup (f := fun d ↦
        (Finset.range (m + r + 1)).sup fun k ↦
          case2SourceFactor m r d k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hd)))

/-- The single dimension-only constant used on both sides of the
Proposition 7.5 dichotomy. -/
noncomputable def proposition75SourceConstant (m r : ℕ) : ENNReal :=
  max (case1SourceConstant m r) (case2SourceConstant m r)

/-- The complete Proposition 7.5 alternative, constructed from the
badly-approximable system and the Proposition 7.4 section.  The covolume
comparison is decided internally. -/
theorem proposition75Cases_of_badlyApproximable {m r : ℕ}
    (hm : 0 < m)
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B)
    (hmeasurable : MeasurableSet B) (hconvex : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (haCube : ∀ i, WithLp.ofLp (a i) ∈ Section8Synthesis.unitCubeIoc m)
    (hhead : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m))
      (((m : ℝ) + 1)⁻¹) ⊆ (2 : ℝ) • B)
    (hcompact : IsCompact B)
    (D : GeometricData B a) {X : ℝ}
    (hbad : IsBadlyApproximable
      (euclideanPolar (WithLp.ofLp '' B)) X X
      (fun i ↦ WithLp.ofLp (a i)))
    (hX : 0 < X) :
    Proposition75Cases D (proposition75SourceConstant m r)
      (ENNReal.ofReal X)⁻¹ := by
  by_cases hcovol : X ≤ ZLattice.covolume
      D.latticePoints μHE[finrank ℝ D.C0]
  · left
    obtain ⟨rho, W, hfactor, hthreshold⟩ :=
      case1Branch_of_covolume_ge hm hmeasurable hconvex haCube hhead D hX hcovol
    exact ⟨rho, W, hfactor.trans (le_max_left _ _), hthreshold⟩
  · right
    let d := finrank ℝ D.C0
    let k := m + r - d - 1
    have hdlt : d < m + r := by
      dsimp only [d]
      have h := D.C0.finrank_lt D.proper
      rw [(WithLp.linearEquiv 2 ℝ
        (EuclideanSpace ℝ (Fin m) ×
          EuclideanSpace ℝ (Fin r))).finrank_eq] at h
      simpa [Module.finrank_prod] using h
    have hdim : d + k + 1 = m + r := by
      dsimp only [k]
      omega
    have hcovol' : ZLattice.covolume
        D.latticePoints μHE[finrank ℝ D.C0] < X := lt_of_not_ge hcovol
    apply case2Branch_of_unitCubeIoc hm hbalanced hmeasurable hconvex
      haCube hhead D rfl hdim hbad hX hcovol' hcompact
    have hdle : d ≤ m + r := hdlt.le
    have hkle : k ≤ m + r := by dsimp only [k]; omega
    have hfactor := case2SourceFactor_le_constant (m := m) (r := r)
      (d := d) (k := k) hdle hkle
    have hsource : case2SourceFactor m r d k ≤
        proposition75SourceConstant m r :=
      hfactor.trans (le_max_right _ _)
    calc
      (2 * ENNReal.ofReal X)⁻¹ *
            (((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ *
              ((2 : ENNReal) ^ (m + r)) *
              (((d.factorial : ENNReal) *
                  ENNReal.ofReal ((((m : ℝ) + 1)⁻¹) ^ k))⁻¹ *
                ((d + k).factorial : ENNReal))) *
            ENNReal.ofReal (Real.sqrt (m + r)) =
          case2SourceFactor m r d k * (ENNReal.ofReal X)⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl (by norm_num))
          (Or.inl (by norm_num))]
        simp only [case2SourceFactor]
        ring
      _ ≤ proposition75SourceConstant m r * (ENNReal.ofReal X)⁻¹ := by
        gcongr

/-- Equation (7.8), with a single explicit dimension-only constant, after
eliminating the internally constructed Case 1/Case 2 alternative. -/
theorem proposition75Conclusion_of_badlyApproximable {m r : ℕ}
    (hm : 0 < m)
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B)
    (hmeasurable : MeasurableSet B) (hconvex : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (haCube : ∀ i, WithLp.ofLp (a i) ∈ Section8Synthesis.unitCubeIoc m)
    (hhead : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m))
      (((m : ℝ) + 1)⁻¹) ⊆ (2 : ℝ) • B)
    (hcompact : IsCompact B)
    (D : GeometricData B a) {X : ℝ}
    (hbad : IsBadlyApproximable
      (euclideanPolar (WithLp.ofLp '' B)) X X
      (fun i ↦ WithLp.ofLp (a i)))
    (hX : 0 < X) :
    Proposition75Conclusion D (proposition75SourceConstant m r)
      (ENNReal.ofReal X)⁻¹ :=
  proposition75Conclusion_of_cases
    (proposition75Cases_of_badlyApproximable hm hbalanced hmeasurable
      hconvex haCube hhead hcompact D hbad hX)

end

end Erdos186.CFP.Bilu.Proposition75Construction

#print axioms Erdos186.CFP.Bilu.Proposition75Construction.exists_large_lowDoubling_residueCell
#print axioms Erdos186.CFP.Bilu.Proposition75Construction.exists_large_rpow_residueCell
#print axioms Erdos186.CFP.Bilu.Proposition75Construction.exists_sourceAffineSlice_of_rpow
#print axioms Erdos186.CFP.Bilu.Proposition75Construction.exists_geometricData_of_lowDoubling
#print axioms Erdos186.CFP.Bilu.Proposition75Construction.exists_geometricData_of_rpowDoubling
#print axioms Erdos186.CFP.Bilu.Proposition75Construction.exists_geometricData_of_proposition83
#print axioms Erdos186.CFP.Bilu.Proposition75Construction.exists_geometricData_of_proposition83_rpow
#print axioms Erdos186.CFP.Bilu.Proposition75Construction.case1Branch_of_covolume_ge
#print axioms Erdos186.CFP.Bilu.Proposition75Construction.proposition75Cases_of_badlyApproximable
#print axioms Erdos186.CFP.Bilu.Proposition75Construction.proposition75Conclusion_of_badlyApproximable

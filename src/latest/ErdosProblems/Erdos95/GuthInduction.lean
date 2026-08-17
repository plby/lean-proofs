/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.IncidenceArithmetic

/-!
# The strong low-degree incidence induction

This file closes the finite induction underlying Guth's rich-point theorem.
The induction is organized around an admissible surface collection whose
residual rich-point set has minimum cardinality.
-/

namespace Erdos95.GuthInduction

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.CellLines Erdos95.PartitionCells
open Erdos95.PartitionBookkeeping Erdos95.PartitionStep
open Erdos95.PartitionRemainders Erdos95.RemainderBounds
open Erdos95.RichPointCombinatorics Erdos95.SurfacePruning
open Erdos95.SurfaceCollections
open Erdos95.SurfaceFactors Erdos95.GuthStructure
open Erdos95.GuthParameters Erdos95.ScaleBounds
open Erdos95.PruneAdmissible Erdos95.TemporarySurfaces
open Erdos95.IncidenceArithmetic

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space := ES.Space3

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

theorem residual_eq_of_minimal_admissible
    {η : ℝ} {D : ℕ} {L : Finset LineIndex} {r : ℕ}
    {F G : Finset Poly3}
    (hmin : ∀ H : Finset Poly3, Admissible η D L H →
      (residualRichPoints L F r).card ≤
        (residualRichPoints L H r).card)
    (hG : Admissible η D L G) (hFG : F ⊆ G) :
    residualRichPoints L G r = residualRichPoints L F r := by
  apply Finset.eq_of_subset_of_card_le
  · exact residualRichPoints_antitone_surfaces L hFG r
  · exact hmin G hG

theorem card_le_five_of_subset_union
    {α : Type*} [DecidableEq α]
    {S A B C D E : Finset α}
    (h : S ⊆ A ∪ B ∪ C ∪ D ∪ E) :
    S.card ≤ A.card + B.card + C.card + D.card + E.card := by
  calc
    S.card ≤ (A ∪ B ∪ C ∪ D ∪ E).card := Finset.card_le_card h
    _ ≤ (A ∪ B ∪ C ∪ D).card + E.card := Finset.card_union_le _ _
    _ ≤ (A ∪ B ∪ C).card + D.card + E.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ (A ∪ B).card + C.card + D.card + E.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ A.card + B.card + C.card + D.card + E.card := by
      gcongr
      exact Finset.card_union_le _ _

theorem ceil_rpow_le_twice {M : ℕ} (hM : 0 < M) {a : ℝ}
    (ha : 0 ≤ a) :
    (⌈(M : ℝ) ^ a⌉₊ : ℝ) ≤ 2 * (M : ℝ) ^ a := by
  have hpowone : 1 ≤ (M : ℝ) ^ a := by
    exact Real.one_le_rpow (by exact_mod_cast hM) ha
  have hceil : (⌈(M : ℝ) ^ a⌉₊ : ℝ) < (M : ℝ) ^ a + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  linarith

theorem one_le_natCast_rpow {M : ℕ} (hM : 0 < M) {a : ℝ}
    (ha : 0 ≤ a) :
    1 ≤ (M : ℝ) ^ a := by
  exact Real.one_le_rpow (by exact_mod_cast hM) ha

theorem high_remainder_real_bound
    {η : ℝ} (hη : 0 ≤ η)
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r W : ℕ)
    (hL : 0 < L.card) (hrange : r ^ 2 ≤ 4 * L.card)
    (hdeg : (partitionPolynomial p).totalDegree + 1 ≤ W) :
    ((r * (r - 1) * (highCellRichPoints L S p c r).card : ℕ) : ℝ) ≤
      4 * W * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  have hnat := root_pair_mul_card_highCellRichPoints_le_crossing
    L S p c r
  have hcast :
      ((r * (r - 1) * (highCellRichPoints L S p c r).card : ℕ) : ℝ) ≤
        ((2 * r * (L.card *
          ((partitionPolynomial p).totalDegree + 1)) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hr := richness_le_two_mul_rpow_half hL hrange
  have hdegR :
      (((partitionPolynomial p).totalDegree + 1 : ℕ) : ℝ) ≤ (W : ℝ) := by
    exact_mod_cast hdeg
  have hthree := rpow_three_halves_le_with_eta hL hη
  calc
    ((r * (r - 1) * (highCellRichPoints L S p c r).card : ℕ) : ℝ) ≤
        ((2 * r * (L.card *
          ((partitionPolynomial p).totalDegree + 1)) : ℕ) : ℝ) := hcast
    _ = 2 * (r : ℝ) * (L.card : ℝ) *
        (((partitionPolynomial p).totalDegree + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ 2 * (2 * (L.card : ℝ) ^ ((1 : ℝ) / 2)) *
        (L.card : ℝ) * (W : ℝ) := by gcongr
    _ = 4 * W * ((L.card : ℝ) ^ ((1 : ℝ) / 2) *
        (L.card : ℝ)) := by ring
    _ = 4 * W * (L.card : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [rpow_half_mul_self hL]
    _ ≤ 4 * W * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by gcongr

theorem wall_remainder_real_bound
    {η : ℝ} (hη : 0 ≤ η)
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (r D : ℕ)
    (hr : 2 ≤ r) (hL : 0 < L.card)
    (hrange : r ^ 2 ≤ 4 * L.card)
    (hp : ∀ j, p j ≠ 0)
    (hSrich : S ⊆ richPoints L r)
    (hdeg : (partitionPolynomial p).totalDegree ≤ D) :
    ((r * (r - 1) * (wallRemainder L S p r).card : ℕ) : ℝ) ≤
      4 * D * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  have hnat := root_pair_mul_card_wallRemainder_le
    L S p r hr hp hSrich
  have hcast :
      ((r * (r - 1) * (wallRemainder L S p r).card : ℕ) : ℝ) ≤
        ((2 * r * ((partitionPolynomial p).totalDegree * L.card) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hrroot := richness_le_two_mul_rpow_half hL hrange
  have hdegR : ((partitionPolynomial p).totalDegree : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hdeg
  have hthree := rpow_three_halves_le_with_eta hL hη
  calc
    ((r * (r - 1) * (wallRemainder L S p r).card : ℕ) : ℝ) ≤
        ((2 * r * ((partitionPolynomial p).totalDegree * L.card) : ℕ) : ℝ) :=
      hcast
    _ = 2 * (r : ℝ) * (partitionPolynomial p).totalDegree *
        (L.card : ℝ) := by
      push_cast
      ring
    _ ≤ 2 * (2 * (L.card : ℝ) ^ ((1 : ℝ) / 2)) *
        (D : ℝ) * (L.card : ℝ) := by gcongr
    _ = 4 * D * ((L.card : ℝ) ^ ((1 : ℝ) / 2) *
        (L.card : ℝ)) := by ring
    _ = 4 * D * (L.card : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [rpow_half_mul_self hL]
    _ ≤ 4 * D * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by gcongr

theorem temporary_surface_count_bound
    {η : ℝ} (hηle : η ≤ (1 : ℝ) / 2)
    (D : ℕ) (L : Finset LineIndex) (hL : 0 < L.card)
    (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ)
    (F₀ : Finset Poly3)
    (cellF : (Fin J → Bool) → Finset Poly3)
    (hF₀ : (F₀.card : ℝ) ≤
      2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η))
    (hcell : ∀ sign ∈ lowSigns L S p c r,
      ((cellF sign).card : ℝ) ≤
        2 * ((cellLines L S p sign).card : ℝ) ^
          ((1 : ℝ) / 2 - η))
    (hQ : partitionPolynomial p ≠ 0)
    (hQdeg : (partitionPolynomial p).totalDegree ≤ D) :
    ((temporarySurfaces F₀ L S p c r cellF).card : ℝ) ≤
      (2 + 2 * (2 ^ J : ℕ) + D) *
        (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) := by
  classical
  let T := lowSigns L S p c r
  let q : ℝ := (1 : ℝ) / 2 - η
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hcellcard : ∀ sign ∈ T,
      ((cellF sign).card : ℝ) ≤
        2 * (L.card : ℝ) ^ q := by
    intro sign hsign
    have hsub := cellLines_subset L S p sign
    have hcard : (cellLines L S p sign).card ≤ L.card :=
      Finset.card_le_card hsub
    have hcardR : ((cellLines L S p sign).card : ℝ) ≤
        (L.card : ℝ) := by exact_mod_cast hcard
    have hpow := Real.rpow_le_rpow (by positivity) hcardR hq
    exact (hcell sign hsign).trans (by
      dsimp [q] at hpow ⊢
      gcongr)
  have hTcard : T.card ≤ 2 ^ J := by
    calc
      T.card ≤ (Finset.univ : Finset (Fin J → Bool)).card :=
        Finset.card_le_card (fun _ _ ↦ Finset.mem_univ _)
      _ = 2 ^ J := by simp
  have hsum :
      (((∑ sign ∈ T, (cellF sign).card : ℕ)) : ℝ) ≤
        2 * (2 ^ J : ℕ) * (L.card : ℝ) ^ q := by
    calc
      (((∑ sign ∈ T, (cellF sign).card : ℕ)) : ℝ) =
          ∑ sign ∈ T, ((cellF sign).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _sign ∈ T, 2 * (L.card : ℝ) ^ q := by
        exact Finset.sum_le_sum fun sign hsign ↦ hcellcard sign hsign
      _ = (T.card : ℝ) * (2 * (L.card : ℝ) ^ q) := by simp
      _ ≤ ((2 ^ J : ℕ) : ℝ) * (2 * (L.card : ℝ) ^ q) := by
        gcongr
      _ = 2 * (2 ^ J : ℕ) * (L.card : ℝ) ^ q := by ring
  have hone : 1 ≤ (L.card : ℝ) ^ q := by
    exact one_le_natCast_rpow hL hq
  have hfacNat : (irreducibleFactors (partitionPolynomial p)).card ≤ D :=
    (card_irreducibleFactors_le_totalDegree hQ).trans hQdeg
  have hfac :
      ((irreducibleFactors (partitionPolynomial p)).card : ℝ) ≤
        D * (L.card : ℝ) ^ q := by
    have hfacD :
        ((irreducibleFactors (partitionPolynomial p)).card : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast hfacNat
    calc
      ((irreducibleFactors (partitionPolynomial p)).card : ℝ) ≤ (D : ℝ) := hfacD
      _ ≤ D * (L.card : ℝ) ^ q := by
        have hD : 0 ≤ (D : ℝ) := by positivity
        nlinarith
  have htempNat := card_temporary_le F₀ L S p c r cellF
  have htemp :
      ((temporarySurfaces F₀ L S p c r cellF).card : ℝ) ≤
        (F₀.card : ℝ) +
          ((∑ sign ∈ T, (cellF sign).card : ℕ) : ℝ) +
          ((irreducibleFactors (partitionPolynomial p)).card : ℝ) := by
    exact_mod_cast htempNat
  dsimp [q] at hsum hfac hone ⊢
  calc
    ((temporarySurfaces F₀ L S p c r cellF).card : ℝ) ≤
        (F₀.card : ℝ) +
          ((∑ sign ∈ T, (cellF sign).card : ℕ) : ℝ) +
          ((irreducibleFactors (partitionPolynomial p)).card : ℝ) := htemp
    _ ≤ 2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) +
        2 * (2 ^ J : ℕ) * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) +
        D * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) := by gcongr
    _ = (2 + 2 * (2 ^ J : ℕ) + D) *
        (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) := by ring

theorem small_surface_remainder_real_bound
    {η C : ℝ} (hη : 0 < η)
    (hC : 0 ≤ C)
    (L : Finset LineIndex) (hL : 0 < L.card)
    (F : Finset Poly3) (r : ℕ) (hr : 2 ≤ r)
    (hF : (F.card : ℝ) ≤
      C * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)) :
    ((r * (r - 1) *
        (surfaceRichPoints L
          (smallSurfaces L F
            ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊)
          (reducedRichness r)).card : ℕ) : ℝ) ≤
      32 * C * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  let A : ℕ := ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊
  have ha : 0 ≤ (1 : ℝ) / 2 + η := by linarith
  have hceil := ceil_rpow_le_twice hL ha
  have hLR : 0 < (L.card : ℝ) := by exact_mod_cast hL
  have hAsq : (A : ℝ) ^ 2 ≤
      4 * (L.card : ℝ) ^ (1 + 2 * η) := by
    calc
      (A : ℝ) ^ 2 ≤
          (2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 := by
        gcongr
      _ = 4 * (((L.card : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2) := by ring
      _ = 4 * (L.card : ℝ) ^ (1 + 2 * η) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hLR.le]
        congr 2
        ring
  have hnat := root_pair_mul_card_small_surfaceRichPoints_le L F A r hr
  have hcast :
      ((r * (r - 1) *
          (surfaceRichPoints L (smallSurfaces L F A)
            (reducedRichness r)).card : ℕ) : ℝ) ≤
        ((8 * (F.card * A ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hpow :
      (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) *
          (L.card : ℝ) ^ (1 + 2 * η) =
        (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
    rw [← Real.rpow_add hLR]
    congr 1
    ring
  change ((r * (r - 1) *
        (surfaceRichPoints L (smallSurfaces L F A)
          (reducedRichness r)).card : ℕ) : ℝ) ≤ _
  calc
    ((r * (r - 1) *
        (surfaceRichPoints L (smallSurfaces L F A)
          (reducedRichness r)).card : ℕ) : ℝ) ≤
        ((8 * (F.card * A ^ 2) : ℕ) : ℝ) := hcast
    _ = 8 * (F.card : ℝ) * (A : ℝ) ^ 2 := by
      push_cast
      ring
    _ ≤ 8 *
        (C * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)) *
        (4 * (L.card : ℝ) ^ (1 + 2 * η)) := by
      gcongr
    _ = 32 * C * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
      rw [← hpow]
      ring

theorem sixteen_mul_low_remainder_le
    {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K)
    (par : Parameters η)
    (L : Finset LineIndex) (S : Finset Space)
    (p : Fin par.J → Poly3) (r : ℕ)
    (hdeg : (partitionPolynomial p).totalDegree ≤ wallDegree par.k)
    (cellF : (Fin par.J → Bool) → Finset Poly3)
    (hcell : ∀ sign ∈ lowSigns L S p par.c r,
      ((r * (r - 1) *
          (residualRichPoints (cellLines L S p sign)
            (cellF sign) r).card : ℕ) : ℝ) ≤
        K * ((cellLines L S p sign).card : ℝ) ^
          ((3 : ℝ) / 2 + η)) :
    16 * ((r * (r - 1) *
        (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) ≤
      K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  classical
  let T := lowSigns L S p par.c r
  have hcard := card_lowResidualPoints_le_sum L S p par.c r cellF
  have hnat :
      r * (r - 1) *
          (lowResidualPoints L S p par.c r cellF).card ≤
        ∑ sign ∈ T,
          r * (r - 1) *
            (residualRichPoints (cellLines L S p sign)
              (cellF sign) r).card := by
    calc
      r * (r - 1) *
          (lowResidualPoints L S p par.c r cellF).card ≤
          r * (r - 1) *
            (∑ sign ∈ T,
              (residualRichPoints (cellLines L S p sign)
                (cellF sign) r).card) := by gcongr
      _ = ∑ sign ∈ T,
          r * (r - 1) *
            (residualRichPoints (cellLines L S p sign)
              (cellF sign) r).card := by
        rw [Finset.mul_sum]
  have hcast :
      ((r * (r - 1) *
          (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) ≤
        ∑ sign ∈ T,
          ((r * (r - 1) *
            (residualRichPoints (cellLines L S p sign)
              (cellF sign) r).card : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hsum :
      ∑ sign ∈ T,
          ((r * (r - 1) *
            (residualRichPoints (cellLines L S p sign)
              (cellF sign) r).card : ℕ) : ℝ) ≤
        K * ∑ sign ∈ T,
          ((cellLines L S p sign).card : ℝ) ^
            ((3 : ℝ) / 2 + η) := by
    calc
      ∑ sign ∈ T,
          ((r * (r - 1) *
            (residualRichPoints (cellLines L S p sign)
              (cellF sign) r).card : ℕ) : ℝ) ≤
          ∑ sign ∈ T,
            K * ((cellLines L S p sign).card : ℝ) ^
              ((3 : ℝ) / 2 + η) := by
        exact Finset.sum_le_sum fun sign hsign ↦ hcell sign hsign
      _ = K * ∑ sign ∈ T,
          ((cellLines L S p sign).card : ℝ) ^
            ((3 : ℝ) / 2 + η) := by rw [Finset.mul_sum]
  have hmoment := sixteen_mul_sum_low_cell_rpow_le
    hη par L S p r hdeg
  calc
    16 * ((r * (r - 1) *
        (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) ≤
        16 * (K * ∑ sign ∈ T,
          ((cellLines L S p sign).card : ℝ) ^
            ((3 : ℝ) / 2 + η)) := by
      gcongr
      exact hcast.trans hsum
    _ = K * (16 * ∑ sign ∈ T,
          ((cellLines L S p sign).card : ℝ) ^
            ((3 : ℝ) / 2 + η)) := by ring
    _ ≤ K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by gcongr

theorem weighted_card_le_twice_four_of_half
    {α : Type*} [DecidableEq α]
    (w : ℕ) {S A B C D E : Finset α}
    (hcover : S ⊆ A ∪ B ∪ C ∪ D ∪ E)
    (hhalf : 2 * A.card ≤ S.card) :
    ((w * S.card : ℕ) : ℝ) ≤
      2 * (((w * B.card : ℕ) : ℝ) +
        ((w * C.card : ℕ) : ℝ) +
        ((w * D.card : ℕ) : ℝ) +
        ((w * E.card : ℕ) : ℝ)) := by
  have hcard := card_le_five_of_subset_union hcover
  have htotalNat :
      w * S.card ≤
        w * A.card + w * B.card + w * C.card + w * D.card + w * E.card := by
    calc
      w * S.card ≤
          w * (A.card + B.card + C.card + D.card + E.card) := by gcongr
      _ = w * A.card + w * B.card + w * C.card + w * D.card +
          w * E.card := by ring
  have htotal :
      ((w * S.card : ℕ) : ℝ) ≤
        ((w * A.card : ℕ) : ℝ) + ((w * B.card : ℕ) : ℝ) +
        ((w * C.card : ℕ) : ℝ) + ((w * D.card : ℕ) : ℝ) +
        ((w * E.card : ℕ) : ℝ) := by exact_mod_cast htotalNat
  have hhalfNat : 2 * (w * A.card) ≤ w * S.card := by
    calc
      2 * (w * A.card) = w * (2 * A.card) := by ring
      _ ≤ w * S.card := by gcongr
  have hhalfR :
      2 * ((w * A.card : ℕ) : ℝ) ≤ ((w * S.card : ℕ) : ℝ) := by
    exact_mod_cast hhalfNat
  nlinarith [show 0 ≤ ((w * A.card : ℕ) : ℝ) by positivity]

/-- Guth's strong rich-point theorem in the finite, denominator-free form
needed for the Elekes--Sharir line family. -/
theorem exists_certificate_constant
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ (1 : ℝ) / 4)
    (par : Parameters η) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L : Finset LineIndex) (r : ℕ), 2 ≤ r →
        r ^ 2 ≤ 4 * L.card →
        Nonempty (Certificate η (wallDegree par.k) K L r) := by
  classical
  let D : ℕ := wallDegree par.k
  let W : ℕ := crossingBudget par.k
  let R : ℕ := 2 ^ par.J
  let Csurf : ℝ := 2 + 2 * R + D
  let B : ℝ := 4 * W + 4 * D + 32 * Csurf
  obtain ⟨N, hNpos, hNscale⟩ :=
    exists_pos_nat_forall_le_rpow (show 0 < 2 * η by positivity)
      (4 * (commonLineConstant D : ℝ) + 1)
  let K : ℝ := 4 * (B + (N : ℝ) ^ 2 + 1)
  have hCsurf : 0 ≤ Csurf := by
    dsimp [Csurf]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro L
  induction L using Finset.strongInduction with
  | H L ih =>
      intro r hr hrange
      have hL : 0 < L.card := by
        have hr2 : 0 < r ^ 2 := by positivity
        omega
      by_cases hsmall : L.card < N
      · obtain ⟨hirr, hnorm, hdegree, hmany, hcount⟩ :=
          admissible_empty η D L
        refine ⟨
          { surfaces := ∅
            irreducible := hirr
            normalized := hnorm
            degree_le := hdegree
            many_lines := hmany
            surface_count := hcount
            residual_bound := ?_ }⟩
        have hres : residualRichPoints L ∅ r ⊆ richPoints L r := by
          intro x hx
          exact (mem_residualRichPoints_iff.mp hx).1
        have hnat :
            r * (r - 1) * (residualRichPoints L ∅ r).card ≤
              L.card ^ 2 := by
          calc
            r * (r - 1) * (residualRichPoints L ∅ r).card ≤
                r * (r - 1) * (richPoints L r).card := by
              gcongr
            _ ≤ L.card ^ 2 := richness_mul_pred_mul_card_le_sq L r
        have hcast :
            ((r * (r - 1) * (residualRichPoints L ∅ r).card : ℕ) : ℝ) ≤
              (L.card : ℝ) ^ 2 := by exact_mod_cast hnat
        have hLN : (L.card : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
          gcongr
        have hNK : (N : ℝ) ^ 2 ≤ K := by
          dsimp [K]
          nlinarith
        have hp : 0 ≤ (3 : ℝ) / 2 + η := by linarith
        have hone := one_le_natCast_rpow hL hp
        calc
          ((r * (r - 1) * (residualRichPoints L ∅ r).card : ℕ) : ℝ) ≤
              (L.card : ℝ) ^ 2 := hcast
          _ ≤ (N : ℝ) ^ 2 := hLN
          _ ≤ K := hNK
          _ ≤ K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
            nlinarith [hK.le]
      · have hNL : N ≤ L.card := Nat.le_of_not_gt hsmall
        have hscaleWeak := hNscale L.card hNL
        have hscale :
            4 * (commonLineConstant D : ℝ) <
              (L.card : ℝ) ^ (2 * η) := by linarith
        obtain ⟨F₀, hF₀, hmin⟩ :=
          exists_minimal_admissible η D L r
        let S : Finset Space := residualRichPoints L F₀ r
        obtain ⟨p, hp, hcells⟩ :=
          exists_partition_cuts_of_finiteLinearBisection
            Erdos95.StoneTukey.finiteLinearBisection S par.J par.k par.fit
        have hpne : ∀ j, p j ≠ 0 := fun j ↦ (hp j).1
        have hQ : partitionPolynomial p ≠ 0 :=
          partitionPolynomial_ne_zero p hpne
        have hQdeg : (partitionPolynomial p).totalDegree ≤ D := by
          dsimp [D]
          exact totalDegree_partitionPolynomial_le_sum_three_mul p par.k
            (fun j ↦ (hp j).2)
        have hQcross : (partitionPolynomial p).totalDegree + 1 ≤ W := by
          dsimp [W, crossingBudget]
          omega
        have hbadScale :
            2 * (par.c * ((partitionPolynomial p).totalDegree + 1)) ≤
              2 ^ par.J := by
          exact (Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left par.c hQcross)).trans par.bad_half
        have hbad :
            2 * (badCellPoints L S p par.c).card ≤ S.card :=
          two_mul_card_badCellPoints_le L S p par.c (2 ^ par.J)
            hL (by positivity) hbadScale hcells
        have hproper : ∀ sign ∈ lowSigns L S p par.c r,
            cellLines L S p sign ⊂ L := by
          intro sign hsign
          have hgood := (mem_lowSigns_iff.mp hsign).1
          have hnotbad := mem_goodSigns_iff.mp hgood
          have hlt :
              par.c * (cellLines L S p sign).card < L.card :=
            Nat.lt_of_not_ge (fun hge ↦
              hnotbad (mem_badSigns_iff.mpr hge))
          have hcardlt : (cellLines L S p sign).card < L.card := by
            have hcOne : 1 ≤ par.c := par.c_pos
            have hmle : (cellLines L S p sign).card ≤
                par.c * (cellLines L S p sign).card := by
              nlinarith
            omega
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨cellLines_subset L S p sign, ?_⟩
          intro heq
          have := congrArg Finset.card heq
          omega
        have hchildCert : ∀ sign
            (hsign : sign ∈ lowSigns L S p par.c r),
            Certificate η D K (cellLines L S p sign) r := by
          intro sign hsign
          exact Classical.choice <| ih (cellLines L S p sign)
            (hproper sign hsign) r hr (mem_lowSigns_iff.mp hsign).2
        let cellF : (Fin par.J → Bool) → Finset Poly3 := fun sign ↦
          if hsign : sign ∈ lowSigns L S p par.c r then
            (hchildCert sign hsign).surfaces
          else ∅
        have hcellEq : ∀ sign
            (hsign : sign ∈ lowSigns L S p par.c r),
            cellF sign = (hchildCert sign hsign).surfaces := by
          intro sign hsign
          simp [cellF, hsign]
        have hcellIrr : ∀ sign ∈ lowSigns L S p par.c r,
            ∀ Q ∈ cellF sign, Irreducible Q := by
          intro sign hsign
          rw [hcellEq sign hsign]
          exact (hchildCert sign hsign).irreducible
        have hcellNorm : ∀ sign ∈ lowSigns L S p par.c r,
            ∀ Q ∈ cellF sign, normalize Q = Q := by
          intro sign hsign
          rw [hcellEq sign hsign]
          exact (hchildCert sign hsign).normalized
        have hcellDegree : ∀ sign ∈ lowSigns L S p par.c r,
            ∀ Q ∈ cellF sign, Q.totalDegree ≤ D := by
          intro sign hsign
          rw [hcellEq sign hsign]
          exact (hchildCert sign hsign).degree_le
        have hcellCount : ∀ sign ∈ lowSigns L S p par.c r,
            ((cellF sign).card : ℝ) ≤
              2 * ((cellLines L S p sign).card : ℝ) ^
                ((1 : ℝ) / 2 - η) := by
          intro sign hsign
          rw [hcellEq sign hsign]
          exact (hchildCert sign hsign).surface_count
        have hcellResidual : ∀ sign ∈ lowSigns L S p par.c r,
            ((r * (r - 1) *
                (residualRichPoints (cellLines L S p sign)
                  (cellF sign) r).card : ℕ) : ℝ) ≤
              K * ((cellLines L S p sign).card : ℝ) ^
                ((3 : ℝ) / 2 + η) := by
          intro sign hsign
          rw [hcellEq sign hsign]
          exact (hchildCert sign hsign).residual_bound
        let Ftemp := temporarySurfaces F₀ L S p par.c r cellF
        have htempIrr : ∀ Q ∈ Ftemp, Irreducible Q := by
          exact temporary_irreducible F₀ L S p par.c r cellF
            hF₀.1 hcellIrr
        have htempNorm : ∀ Q ∈ Ftemp, normalize Q = Q := by
          exact temporary_normalized F₀ L S p par.c r cellF
            hF₀.2.1 hcellNorm
        have htempDegree : ∀ Q ∈ Ftemp, Q.totalDegree ≤ D := by
          exact temporary_degree_le F₀ L S p par.c r D cellF
            hQ hQdeg hF₀.2.2.1 hcellDegree
        let A : ℕ := ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊
        let G : Finset Poly3 := largeSurfaces L Ftemp A
        have hG : Admissible η D L G := by
          change Admissible η D L
            (largeSurfaces L Ftemp
              ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊)
          exact admissible_largeSurfaces hη hηle D L hL Ftemp
            htempIrr htempNorm htempDegree hscale
        have hF₀G : F₀ ⊆ G := by
          intro Q hQF
          apply mem_largeSurfaces_iff.mpr
          refine ⟨base_subset_temporary F₀ L S p par.c r cellF hQF, ?_⟩
          change ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊ ≤
            (surfaceLines L Q).card
          exact Nat.ceil_le.mpr (hF₀.2.2.2.1 Q hQF)
        have hresEq : residualRichPoints L G r = S := by
          change residualRichPoints L G r = residualRichPoints L F₀ r
          exact residual_eq_of_minimal_admissible hmin hG hF₀G
        have hSrich : S ⊆ richPoints L r := by
          intro x hx
          exact (mem_residualRichPoints_iff.mp hx).1
        have hAvoid : ∀ x ∈ S,
            x ∉ surfaceRichPoints L G (reducedRichness r) := by
          intro x hx
          have hxG : x ∈ residualRichPoints L G r := by
            rw [hresEq]
            exact hx
          exact (mem_residualRichPoints_iff.mp hxG).2
        have hcover : S ⊆
            badCellPoints L S p par.c ∪
            lowResidualPoints L S p par.c r cellF ∪
            highCellRichPoints L S p par.c r ∪
            wallRemainder L S p r ∪
            surfaceRichPoints L (smallSurfaces L Ftemp A)
              (reducedRichness r) := by
          exact subset_partition_remainders hr F₀ cellF hSrich hAvoid
        have htempCount : (Ftemp.card : ℝ) ≤
            Csurf * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) := by
          change (Ftemp.card : ℝ) ≤
            (2 + 2 * R + D) *
              (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)
          have hetaHalf : η ≤ (1 : ℝ) / 2 := hηle.trans (by norm_num)
          exact temporary_surface_count_bound hetaHalf D L hL S p par.c r
            F₀ cellF hF₀.2.2.2.2 hcellCount hQ hQdeg
        have hlow16 := sixteen_mul_low_remainder_le hη hK.le par
          L S p r hQdeg cellF hcellResidual
        have hhigh := high_remainder_real_bound hη.le L S p par.c r W
          hL hrange hQcross
        have hwall := wall_remainder_real_bound hη.le L S p r D hr hL
          hrange hpne hSrich hQdeg
        have hsmallSurf := small_surface_remainder_real_bound hη hCsurf
          L hL Ftemp r hr htempCount
        have hdecomp := weighted_card_le_twice_four_of_half
          (r * (r - 1)) hcover hbad
        have hLp : 0 ≤ (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) :=
          Real.rpow_nonneg (by positivity) _
        have hlow :
            ((r * (r - 1) *
                (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) ≤
              (K / 16) * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
          nlinarith
        have hrest :
            ((r * (r - 1) *
                (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) +
              ((r * (r - 1) *
                (highCellRichPoints L S p par.c r).card : ℕ) : ℝ) +
              ((r * (r - 1) *
                (wallRemainder L S p r).card : ℕ) : ℝ) +
              ((r * (r - 1) *
                (surfaceRichPoints L (smallSurfaces L Ftemp A)
                  (reducedRichness r)).card : ℕ) : ℝ) ≤
              (K / 16 + B) *
                (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
          calc
            _ ≤ (K / 16) * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) +
                4 * W * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) +
                4 * D * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) +
                32 * Csurf * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
              gcongr
            _ = (K / 16 + B) *
                (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
              dsimp [B]
              ring
        have hcoef : 2 * (K / 16 + B) ≤ K := by
          dsimp [K]
          nlinarith [hB, show 0 ≤ (N : ℝ) ^ 2 by positivity]
        have hfinal :
            ((r * (r - 1) * S.card : ℕ) : ℝ) ≤
              K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
          calc
            ((r * (r - 1) * S.card : ℕ) : ℝ) ≤
                2 * (((r * (r - 1) *
                    (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) +
                  ((r * (r - 1) *
                    (highCellRichPoints L S p par.c r).card : ℕ) : ℝ) +
                  ((r * (r - 1) *
                    (wallRemainder L S p r).card : ℕ) : ℝ) +
                  ((r * (r - 1) *
                    (surfaceRichPoints L (smallSurfaces L Ftemp A)
                      (reducedRichness r)).card : ℕ) : ℝ)) := hdecomp
            _ ≤ 2 * ((K / 16 + B) *
                (L.card : ℝ) ^ ((3 : ℝ) / 2 + η)) := by gcongr
            _ = (2 * (K / 16 + B)) *
                (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by ring
            _ ≤ K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
              gcongr
        refine ⟨
          { surfaces := F₀
            irreducible := hF₀.1
            normalized := hF₀.2.1
            degree_le := hF₀.2.2.1
            many_lines := hF₀.2.2.2.1
            surface_count := hF₀.2.2.2.2
            residual_bound := ?_ }⟩
        change ((r * (r - 1) * S.card : ℕ) : ℝ) ≤ _
        exact hfinal

end Erdos95.GuthInduction

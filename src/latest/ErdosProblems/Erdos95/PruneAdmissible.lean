/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.ScaleBounds

/-!
# Pruning a temporary surface collection
-/

namespace Erdos95.PruneAdmissible

open Erdos95.ES Erdos95.LineFamilies Erdos95.GuthStructure
open Erdos95.SurfaceCollections Erdos95.SurfacePruning

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- Above the degree-dependent scale, retaining precisely the surfaces with
at least `L^(1/2+η)` lines produces an admissible collection. -/
theorem admissible_largeSurfaces
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ (1 : ℝ) / 4)
    (D : ℕ) (L : Finset LineIndex) (hL : 0 < L.card)
    (F : Finset Poly3)
    (hirr : ∀ Q ∈ F, Irreducible Q)
    (hnorm : ∀ Q ∈ F, normalize Q = Q)
    (hdegree : ∀ Q ∈ F, Q.totalDegree ≤ D)
    (hscale : 4 * (commonLineConstant D : ℝ) <
      (L.card : ℝ) ^ (2 * η)) :
    Admissible η D L
      (largeSurfaces L F
        ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊) := by
  classical
  let A : ℕ := ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊
  let G : Finset Poly3 := largeSurfaces L F A
  have hLR : 0 < (L.card : ℝ) := by exact_mod_cast hL
  have ha : 0 < (1 : ℝ) / 2 + η := by linarith
  have hq : 0 ≤ (1 : ℝ) / 2 - η := by linarith
  have hA : (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) ≤ (A : ℝ) := by
    exact Nat.le_ceil _
  have hquadratic :
      4 * commonLineConstant D * L.card < A ^ 2 := by
    have hmul :
        4 * (commonLineConstant D : ℝ) * (L.card : ℝ) <
          ((L.card : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 := by
      calc
        4 * (commonLineConstant D : ℝ) * (L.card : ℝ) <
            (L.card : ℝ) ^ (2 * η) * (L.card : ℝ) := by
          exact mul_lt_mul_of_pos_right hscale hLR
        _ = (L.card : ℝ) ^ (2 * η) *
            (L.card : ℝ) ^ (1 : ℝ) := by simp
        _ = (L.card : ℝ) ^ (2 * η + 1) := by
          rw [Real.rpow_add hLR]
        _ = (L.card : ℝ) ^ (1 + 2 * η) := by ring_nf
        _ = ((L.card : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul (le_of_lt hLR)]
          congr 2
          ring
    have hceilSq :
        ((L.card : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 ≤
          (A : ℝ) ^ 2 := by gcongr
    exact_mod_cast hmul.trans_le hceilSq
  have hlargeNat : ∀ Q ∈ G, A ≤ (surfaceLines L Q).card := by
    intro Q hQ
    exact (mem_largeSurfaces_iff.mp hQ).2
  have hboundNat : A * G.card ≤ 2 * L.card := by
    apply large_surface_collection_bound L G A D
    · intro Q hQ
      exact hirr Q (mem_largeSurfaces_iff.mp hQ).1
    · intro Q hQ
      exact hnorm Q (mem_largeSurfaces_iff.mp hQ).1
    · intro Q hQ
      exact hdegree Q (mem_largeSurfaces_iff.mp hQ).1
    · exact hlargeNat
    · exact hquadratic
  have hboundReal :
      (G.card : ℝ) ≤
        2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) := by
    have hcast : (A : ℝ) * (G.card : ℝ) ≤
        2 * (L.card : ℝ) := by exact_mod_cast hboundNat
    have hleft :
        (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) * (G.card : ℝ) ≤
          2 * (L.card : ℝ) :=
      (mul_le_mul_of_nonneg_right hA (by positivity)).trans hcast
    have hpow :
        (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) *
          (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) =
            (L.card : ℝ) := by
      rw [← Real.rpow_add hLR]
      norm_num
    have hapos :
        0 < (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) :=
      Real.rpow_pos_of_pos hLR _
    have hrightEq :
        (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) *
          (2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)) =
            2 * (L.card : ℝ) := by
      calc
        (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) *
            (2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)) =
          2 * ((L.card : ℝ) ^ ((1 : ℝ) / 2 + η) *
            (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)) := by ring
        _ = 2 * (L.card : ℝ) := by rw [hpow]
    nlinarith
  change Admissible η D L G
  unfold Admissible
  refine ⟨?_, ?_, ?_, ?_, hboundReal⟩
  · intro Q hQ
    exact hirr Q (mem_largeSurfaces_iff.mp hQ).1
  · intro Q hQ
    exact hnorm Q (mem_largeSurfaces_iff.mp hQ).1
  · intro Q hQ
    exact hdegree Q (mem_largeSurfaces_iff.mp hQ).1
  · intro Q hQ
    exact hA.trans (by exact_mod_cast hlargeNat Q hQ)

end Erdos95.PruneAdmissible

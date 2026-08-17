/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.PartitionCells

/-!
# The finite strong incidence statement

This is the denominator-free form of Guth's Theorem 2.1 used by the
low-degree induction.  The output is a small collection of normalized
irreducible low-degree surfaces accounting for all but a controlled number
of rich points.
-/

namespace Erdos95.GuthStructure

open Erdos95.ES Erdos95.LineFamilies
open Erdos95.RichPointCombinatorics Erdos95.SurfaceFactors

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- A richness threshold comparable to `r/2`, but always at least two. -/
def reducedRichness (r : ℕ) : ℕ := max 2 ((r + 1) / 2)

theorem two_le_reducedRichness (r : ℕ) : 2 ≤ reducedRichness r := by
  simp [reducedRichness]

theorem reducedRichness_le {r : ℕ} (hr : 2 ≤ r) :
    reducedRichness r ≤ r := by
  unfold reducedRichness
  apply max_le hr
  omega

theorem richness_le_two_mul_reduced (r : ℕ) :
    r ≤ 2 * reducedRichness r := by
  unfold reducedRichness
  omega

theorem richness_le_two_mul_loss {r : ℕ} (hr : 2 ≤ r) :
    r ≤ 2 * (r - (reducedRichness r - 1)) := by
  have hs := reducedRichness_le hr
  unfold reducedRichness at hs ⊢
  omega

theorem richness_pair_le_eight_reduced_pair {r : ℕ} (hr : 2 ≤ r) :
    r * (r - 1) ≤
      8 * (reducedRichness r * (reducedRichness r - 1)) := by
  have htwo := two_le_reducedRichness r
  have hhalf := richness_le_two_mul_reduced r
  have hpred : reducedRichness r ≤ 2 * (reducedRichness r - 1) := by
    omega
  calc
    r * (r - 1) ≤
        (2 * reducedRichness r) * (2 * reducedRichness r) := by
      gcongr
      omega
    _ = 4 * reducedRichness r * reducedRichness r := by ring
    _ ≤ 4 * reducedRichness r * (2 * (reducedRichness r - 1)) := by
      gcongr
    _ = 8 * (reducedRichness r * (reducedRichness r - 1)) := by ring

/-- The rich points not accounted for by the selected surfaces. -/
noncomputable def residualRichPoints (L : Finset LineIndex)
    (F : Finset Poly3) (r : ℕ) : Finset Space3 := by
  classical
  exact richPoints L r \ surfaceRichPoints L F (reducedRichness r)

theorem mem_residualRichPoints_iff {L : Finset LineIndex}
    {F : Finset Poly3} {r : ℕ} {x : Space3} :
    x ∈ residualRichPoints L F r ↔
      x ∈ richPoints L r ∧
        x ∉ surfaceRichPoints L F (reducedRichness r) := by
  classical
  simp [residualRichPoints]

theorem residualRichPoints_antitone_surfaces
    (L : Finset LineIndex) {F G : Finset Poly3} (hFG : F ⊆ G) (r : ℕ) :
    residualRichPoints L G r ⊆ residualRichPoints L F r := by
  intro x hx
  have hxdata := mem_residualRichPoints_iff.mp hx
  exact mem_residualRichPoints_iff.mpr ⟨hxdata.1, fun hxF ↦
    hxdata.2 (surfaceRichPoints_mono_collection L hFG _ hxF)⟩

/-- One instance of the strong low-degree incidence conclusion. -/
structure Certificate (epsilon : ℝ) (D : ℕ) (K : ℝ)
    (L : Finset LineIndex) (r : ℕ) where
  surfaces : Finset Poly3
  irreducible : ∀ Q ∈ surfaces, Irreducible Q
  normalized : ∀ Q ∈ surfaces, normalize Q = Q
  degree_le : ∀ Q ∈ surfaces, Q.totalDegree ≤ D
  many_lines : ∀ Q ∈ surfaces,
    (L.card : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤
      ((surfaceLines L Q).card : ℝ)
  surface_count :
    (surfaces.card : ℝ) ≤
      2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - epsilon)
  residual_bound :
    ((r * (r - 1) * (residualRichPoints L surfaces r).card : ℕ) : ℝ) ≤
      K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + epsilon)

/-- The structural part of a certificate, before proving its residual
incidence estimate. -/
def Admissible (epsilon : ℝ) (D : ℕ) (L : Finset LineIndex)
    (F : Finset Poly3) : Prop :=
  (∀ Q ∈ F, Irreducible Q) ∧
  (∀ Q ∈ F, normalize Q = Q) ∧
  (∀ Q ∈ F, Q.totalDegree ≤ D) ∧
  (∀ Q ∈ F,
    (L.card : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤
      ((surfaceLines L Q).card : ℝ)) ∧
  ((F.card : ℝ) ≤
    2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - epsilon))

theorem admissible_empty (epsilon : ℝ) (D : ℕ)
    (L : Finset LineIndex) : Admissible epsilon D L ∅ := by
  unfold Admissible
  refine ⟨by simp, by simp, by simp, by simp, ?_⟩
  norm_num
  exact Real.rpow_nonneg (by positivity) _

/-- Among all admissible collections, choose one whose unexplained rich
point set has minimum cardinality.  This well-ordering device replaces an
explicit logarithmic iteration of the bad-cell step. -/
theorem exists_minimal_admissible (epsilon : ℝ) (D : ℕ)
    (L : Finset LineIndex) (r : ℕ) :
    ∃ F : Finset Poly3, Admissible epsilon D L F ∧
      ∀ G : Finset Poly3, Admissible epsilon D L G →
        (residualRichPoints L F r).card ≤
          (residualRichPoints L G r).card := by
  classical
  let score : ℕ → Prop := fun n ↦
    ∃ F : Finset Poly3, Admissible epsilon D L F ∧
      (residualRichPoints L F r).card = n
  have hex : ∃ n, score n := by
    refine ⟨(residualRichPoints L ∅ r).card, ∅,
      admissible_empty epsilon D L, rfl⟩
  let n := Nat.find hex
  obtain ⟨F, hF, hscore⟩ := Nat.find_spec hex
  refine ⟨F, hF, ?_⟩
  intro G hG
  have hGn : score (residualRichPoints L G r).card := ⟨G, hG, rfl⟩
  rw [hscore]
  exact Nat.find_min' hex hGn

end Erdos95.GuthStructure

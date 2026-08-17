/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.GuthStructure

/-!
# Rich points on a reducible partition wall

A point on a product wall lies on an irreducible factor.  Applying the
external-line incidence estimate factor by factor bounds wall points not
already rich in one of the factor line subfamilies.
-/

open scoped BigOperators

namespace Erdos95.WallFactors

open Erdos95.ES Erdos95.LineFamilies Erdos95.SurfaceFactors
open Erdos95.RichPointCombinatorics Erdos95.WallIncidences

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- Selected points on one irreducible factor wall. -/
noncomputable def pointsOnFactor (S : Finset Space3) (R : Poly3) :
    Finset Space3 := by
  classical
  exact S.filter fun x ↦ MvPolynomial.eval x R = 0

theorem mem_pointsOnFactor_iff {S : Finset Space3} {R : Poly3}
    {x : Space3} :
    x ∈ pointsOnFactor S R ↔ x ∈ S ∧ MvPolynomial.eval x R = 0 := by
  classical
  simp [pointsOnFactor]

theorem subset_biUnion_pointsOnFactor {S : Finset Space3} {Q : Poly3}
    (hQ : Q ≠ 0) (hwall : ∀ x ∈ S, MvPolynomial.eval x Q = 0) :
    S ⊆ (irreducibleFactors Q).biUnion (pointsOnFactor S) := by
  classical
  intro x hx
  obtain ⟨R, hRQ, hRx⟩ := exists_factor_eval_eq_zero hQ (hwall x hx)
  exact Finset.mem_biUnion.mpr ⟨R, hRQ,
    mem_pointsOnFactor_iff.mpr ⟨hx, hRx⟩⟩

/-- Factorwise denominator-free estimate for points on a reducible wall
which are not rich on any irreducible factor. -/
theorem strict_loss_mul_card_le_wall_degree_mul_lines
    {S : Finset Space3} {L : Finset LineIndex} {Q : Poly3}
    {r r' : ℕ} (hQ : Q ≠ 0) (hr' : 2 ≤ r')
    (hSrich : ∀ x ∈ S, r ≤ (linesThrough L x).card)
    (hSnot : ∀ x ∈ S,
      x ∉ surfaceRichPoints L (irreducibleFactors Q) r')
    (hwall : ∀ x ∈ S, MvPolynomial.eval x Q = 0) :
    (r - (r' - 1)) * S.card ≤ Q.totalDegree * L.card := by
  classical
  have hcover := subset_biUnion_pointsOnFactor hQ hwall
  calc
    (r - (r' - 1)) * S.card ≤
        (r - (r' - 1)) *
          ((irreducibleFactors Q).biUnion (pointsOnFactor S)).card := by
      exact Nat.mul_le_mul_left _ (Finset.card_le_card hcover)
    _ ≤ (r - (r' - 1)) *
          ∑ R ∈ irreducibleFactors Q, (pointsOnFactor S R).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ = ∑ R ∈ irreducibleFactors Q,
        (r - (r' - 1)) * (pointsOnFactor S R).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ R ∈ irreducibleFactors Q, R.totalDegree * L.card := by
      apply Finset.sum_le_sum
      intro R hRQ
      apply richness_strict_loss_mul_card_le_degree_mul_lines hr'
      · intro x hx
        exact hSrich x (mem_pointsOnFactor_iff.mp hx).1
      · intro x hx hxr
        exact hSnot x (mem_pointsOnFactor_iff.mp hx).1
          (mem_surfaceRichPoints_iff.mpr ⟨R, hRQ, hxr⟩)
      · intro x hx
        exact (mem_pointsOnFactor_iff.mp hx).2
    _ = (∑ R ∈ irreducibleFactors Q, R.totalDegree) * L.card := by
      rw [Finset.sum_mul]
    _ ≤ Q.totalDegree * L.card := by
      gcongr
      exact sum_totalDegree_irreducibleFactors_le hQ

end Erdos95.WallFactors

/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.PippengerSpencerInnerMarginal

/-!
# Interface for the sharp two-sided inner marginal

This small upstream module exposes the exact generator statement needed by
the outer Pippenger--Spencer iteration without importing that iteration.
-/

namespace Erdos76

noncomputable section

namespace FiniteHypergraph

universe uV uE

/-- Two-sided fixed-parameter form of the sharp inner-generator theorem. -/
def TwoSidedFixedLengthInnerMarginalAt
    (k : ℕ) (zeta eta : ℝ) (L D₀ : ℕ) : Prop :=
  ∀ (V' : Type uV) (E' : Type uE)
      [DecidableEq V'] [Fintype E'] [DecidableEq E'],
    ∀ (H : FiniteHypergraph V' E') (D : ℕ),
      D₀ ≤ D → H.IsUniform k →
      (∀ v ∈ H.vertexSet,
        (1 - eta) * (D : ℝ) ≤ (H.edgeDegree v : ℝ)) →
      (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
      (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
        (H.edgePairDegree u v : ℝ) < eta * (D : ℝ)) →
      ∃ prob : E' → ℝ,
        (∀ e, 0 ≤ prob e) ∧ (∀ e, prob e ≤ 1) ∧
        ∀ e, (1 - zeta) / (D : ℝ) ≤ H.innerAcceptanceMass L prob e ∧
        H.innerAcceptanceMass L prob e ≤ (1 + zeta) / (D : ℝ)

/-- Exact-regular form of the sharp inner-generator theorem.  This is the
minimal form needed by the outer iteration, which freshly completes every
residual hypergraph to an exactly regular one before invoking the generator. -/
def ExactRegularTwoSidedFixedLengthInnerMarginalAt
    (k : ℕ) (zeta eta : ℝ) (L D₀ : ℕ) : Prop :=
  ∀ (V' : Type uV) (E' : Type uE)
      [DecidableEq V'] [Fintype E'] [DecidableEq E'],
    ∀ (H : FiniteHypergraph V' E') (D : ℕ),
      D₀ ≤ D → H.IsUniform k →
      (∀ v ∈ H.vertexSet, H.edgeDegree v = D) →
      (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
        (H.edgePairDegree u v : ℝ) < eta * (D : ℝ)) →
      ∃ prob : E' → ℝ,
        (∀ e, 0 ≤ prob e) ∧ (∀ e, prob e ≤ 1) ∧
        ∀ e, (1 - zeta) / (D : ℝ) ≤ H.innerAcceptanceMass L prob e ∧
          H.innerAcceptanceMass L prob e ≤ (1 + zeta) / (D : ℝ)

/-- Uniform two-sided sharp fixed-length inner marginal. -/
def SharpTwoSidedFixedLengthInnerMarginal : Prop :=
  ∀ k : ℕ, 0 < k → ∀ zeta : ℝ, 0 < zeta → zeta < 1 →
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∃ L D₀ : ℕ, 0 < D₀ ∧
        TwoSidedFixedLengthInnerMarginalAt.{0, 0} k zeta eta L D₀

/-- Uniform sharp inner marginal restricted to exactly regular inputs. -/
def SharpExactRegularTwoSidedFixedLengthInnerMarginal : Prop :=
  ∀ k : ℕ, 0 < k → ∀ zeta : ℝ, 0 < zeta → zeta < 1 →
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∃ L D₀ : ℕ, 0 < D₀ ∧
        ExactRegularTwoSidedFixedLengthInnerMarginalAt.{0, 0}
          k zeta eta L D₀

/-- The historical near-regular interface specializes to the exact-regular
interface. -/
theorem twoSidedFixedLengthInnerMarginalAt_to_exactRegular
    {k L D₀ : ℕ} {zeta eta : ℝ} (heta : 0 ≤ eta)
    (h : TwoSidedFixedLengthInnerMarginalAt.{uV, uE} k zeta eta L D₀) :
    ExactRegularTwoSidedFixedLengthInnerMarginalAt.{uV, uE}
      k zeta eta L D₀ := by
  intro V' E' _ _ _ H D hD₀ hunif hreg hpair
  apply h V' E' H D hD₀ hunif
  · intro v hv
    rw [hreg v hv]
    nlinarith [mul_nonneg heta (Nat.cast_nonneg D)]
  · intro v hv
    exact (hreg v hv).le
  · exact hpair

/-- The uniform near-regular theorem likewise specializes to its exact-regular
counterpart. -/
theorem sharpTwoSidedFixedLengthInnerMarginal_to_exactRegular
    (h : SharpTwoSidedFixedLengthInnerMarginal) :
    SharpExactRegularTwoSidedFixedLengthInnerMarginal := by
  intro k hk zeta hzeta₀ hzeta₁
  obtain ⟨eta, heta₀, heta₁, L, D₀, hD₀, hgen⟩ :=
    h k hk zeta hzeta₀ hzeta₁
  exact ⟨eta, heta₀, heta₁, L, D₀, hD₀,
    twoSidedFixedLengthInnerMarginalAt_to_exactRegular heta₀.le hgen⟩

end FiniteHypergraph

end

end Erdos76

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
import ErdosProblems.Erdos76.Kahn
import ErdosProblems.Erdos76.TriangleHypergraph
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Specializing weighted hypergraph rounding to monochromatic triangles

This file is the exact bridge between the finite weighted matching theorem
and the packing number used in the statement of Erdős Problem 76.  It keeps
the probabilistic content isolated in `KahnWeightedMatching` and proves all
representation and cardinality conversions here.
-/

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

open Filter

/-- Kahn's finite weighted matching theorem, specialized to the
three-uniform hypergraph whose vertices are the edges of a complete graph and
whose hyperedges are the monochromatic triangles of a red--blue colouring. -/
theorem kahn_monochromatic_triangle_rounding
    (hKahn : KahnWeightedMatching) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (A : Type) [Fintype A] [DecidableEq A],
        ∀ (G : SimpleGraph A) (w : MonoTriangle G → ℝ),
          (monochromaticTriangleHypergraph G).IsFractionalMatching w →
          (monochromaticTriangleHypergraph G).PairCodegreeLT w δ →
          (monochromaticTriangleHypergraph G).totalWeight w ≤
            (monoPackingNumber G : ℝ) +
              ζ * ((Fintype.card A).choose 2 : ℝ) := by
  obtain ⟨δ, hδ, hround⟩ := hKahn 3 (by omega) ζ hζ
  refine ⟨δ, hδ, ?_⟩
  intro A _ _ G w hw hcodeg
  obtain ⟨M, hM, hsize⟩ := hround
    (Finset A) (MonoTriangle G) (monochromaticTriangleHypergraph G) w
    (monochromaticTriangleHypergraph_isUniform G) hw hcodeg
  calc
    (monochromaticTriangleHypergraph G).totalWeight w ≤
        (M.card : ℝ) +
          ζ * (monochromaticTriangleHypergraph G).vertexSet.card := hsize
    _ ≤ (monoPackingNumber G : ℝ) +
          ζ * (monochromaticTriangleHypergraph G).vertexSet.card := by
      gcongr
      exact_mod_cast matching_card_le_monoPackingNumber hM
    _ = (monoPackingNumber G : ℝ) +
          ζ * ((Fintype.card A).choose 2 : ℝ) := by
      rw [card_monochromaticTriangleHypergraph_vertexSet]

/-- The exact problem-specific consequence required from local-subset
averaging.  Besides the asymptotically sharp total weight, it records that the
weighted codegree can be made smaller than any prescribed positive constant.
This is strictly weaker than the sharp finite Gruslys--Letzter theorem. -/
def SmoothedFractionalMonochromaticTriangles : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin n),
      ∃ w : MonoTriangle G → ℝ,
        (monochromaticTriangleHypergraph G).IsFractionalMatching w ∧
        (monochromaticTriangleHypergraph G).PairCodegreeLT w δ ∧
        (1 / 12 - ε) * (n : ℝ) ^ 2 ≤
          (monochromaticTriangleHypergraph G).totalWeight w

/-- The smoothed fractional lower bound and Kahn's finite weighted matching
theorem imply the exact eventual-epsilon resolution of Erdős Problem 76. -/
theorem resolution_of_smoothed_fractional_and_kahn
    (hfrac : SmoothedFractionalMonochromaticTriangles)
    (hKahn : KahnWeightedMatching) : Resolution := by
  intro ε hε
  obtain ⟨δ, hδ, hround⟩ :=
    kahn_monochromatic_triangle_rounding hKahn (ζ := ε) hε
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [hfrac (ε / 2) hhalf δ hδ] with n hn
  intro G
  obtain ⟨w, hw, hcodeg, hsize⟩ := hn G
  have hrounded :
      (monochromaticTriangleHypergraph G).totalWeight w ≤
        (monoPackingNumber G : ℝ) + ε * ((n.choose 2 : ℕ) : ℝ) := by
    simpa using hround (Fin n) G w hw hcodeg
  have hchoose : ((n.choose 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : (n : ℝ) - 1 ≤ n := by linarith
    nlinarith
  have herr : ε * ((n.choose 2 : ℕ) : ℝ) ≤ ε * ((n : ℝ) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hchoose hε.le
  nlinarith

end

end Erdos76

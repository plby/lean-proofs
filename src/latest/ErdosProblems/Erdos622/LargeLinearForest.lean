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
import ErdosProblems.Erdos622.LinearArboricity

/-!
# Extracting one large linear forest

The almost-bipartite argument for Erdős 622 does not use an entire
linear-forest decomposition after it has been constructed: it only uses one
color class whose size is at least the average.  This file records that
weaker, quantifier-level interface and proves that the asymptotic
linear-arboricity theorem supplies it.

The coefficient is written as `2 - epsilon`.  This is deliberately an
asymptotic assertion.  The corresponding exact coefficient `2` is false:
in a complete graph on `D + 1` vertices, every forest has at most `D` edges,
whereas `2 * |E| / D = D + 1`.
-/

open Finset

namespace Erdos622

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

namespace LinearArboricity

/-- Every sufficiently high-maximum-degree graph contains one linear forest
with asymptotically at least twice its edge count divided by the degree
bound.  The threshold is uniform in the finite vertex type and graph. -/
def OneLargeLinearForest : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ D₀ : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (D : ℕ),
        D₀ ≤ D →
        (∀ v, G.degree v ≤ D) →
        ∃ F : SimpleGraph V,
          F ≤ G ∧ Erdos622.SimpleGraph.IsLinearForest F ∧
          (2 - epsilon) * (G.edgeSet.ncard : ℝ) / (D : ℝ) ≤
            (F.edgeSet.ncard : ℝ)

/-- Alon's asymptotic linear-arboricity statement implies the one-large-class
form used in the DKM proof. -/
theorem AsymptoticLinearArboricity.oneLargeLinearForest
    (hLA : AsymptoticLinearArboricity.{u}) : OneLargeLinearForest.{u} := by
  intro epsilon hepsilon
  by_cases htwo : 2 ≤ epsilon
  · refine ⟨1, ?_⟩
    intro V _ G _ D hD _hdegree
    refine ⟨⊥, bot_le, Erdos622.SimpleGraph.isLinearForest_bot, ?_⟩
    have hcoefficient : 2 - epsilon ≤ 0 := sub_nonpos.mpr htwo
    have hedge_nonneg : (0 : ℝ) ≤ G.edgeSet.ncard := by positivity
    have hnumerator :
        (2 - epsilon) * (G.edgeSet.ncard : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoefficient hedge_nonneg
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    simpa using div_nonpos_of_nonpos_of_nonneg hnumerator hDpos.le
  · have hepsilon_lt_two : epsilon < 2 := lt_of_not_ge htwo
    have heta : 0 < epsilon / 2 := div_pos hepsilon (by norm_num)
    obtain ⟨D₁, hD₁⟩ := hLA (epsilon / 2) heta
    refine ⟨max 1 D₁, ?_⟩
    intro V _ G _ D hD hdegree
    have hD₁D : D₁ ≤ D := (le_max_right 1 D₁).trans hD
    obtain ⟨k, hk, hk_upper, hd⟩ := hD₁ V G D hD₁D hdegree
    let _ : DecidableEq V := Classical.decEq V
    obtain ⟨F, hFG, hlinear, havg⟩ :=
      hd.some.exists_large_linearForest hk
    have havg' :
        (G.edgeSet.ncard : ℝ) / (k : ℝ) ≤ (F.edgeSet.ncard : ℝ) := by
      simpa only [Set.fintypeCard_eq_ncard] using havg
    refine ⟨F, hFG, hlinear, ?_⟩
    have hDone : 1 ≤ D := (le_max_left 1 D₁).trans hD
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hDone
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hcoefficient : (0 : ℝ) ≤ 2 - epsilon :=
      (sub_pos.mpr hepsilon_lt_two).le
    have hfactor :
        (2 - epsilon) * (1 + epsilon / 2) / 2 ≤ (1 : ℝ) := by
      nlinarith [sq_nonneg epsilon]
    have hcoefficient_mul_k :
        (2 - epsilon) * (k : ℝ) ≤ (D : ℝ) := by
      calc
        (2 - epsilon) * (k : ℝ) ≤
            (2 - epsilon) * ((1 + epsilon / 2) * (D : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hk_upper hcoefficient
        _ = ((2 - epsilon) * (1 + epsilon / 2) / 2) * (D : ℝ) := by ring
        _ ≤ 1 * (D : ℝ) :=
          mul_le_mul_of_nonneg_right hfactor hDpos.le
        _ = (D : ℝ) := one_mul _
    have hedge_nonneg : (0 : ℝ) ≤ G.edgeSet.ncard := by positivity
    apply le_trans ?_ havg'
    rw [div_le_div_iff₀ hDpos hkpos]
    have hmul :=
      mul_le_mul_of_nonneg_left hcoefficient_mul_k hedge_nonneg
    simpa [mul_left_comm, mul_comm, mul_assoc] using hmul

end LinearArboricity

end

end Erdos622

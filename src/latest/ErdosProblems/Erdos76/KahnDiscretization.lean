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
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Discretizing Pippenger--Spencer to Kahn's weighted matching theorem

A fractional edge of weight `w e` is replaced by
`floor (D * w e)` parallel indexed copies.  The copy index retains the original edge index,
so parallel original supports are never identified.  This file proves that the unweighted
maximum-degree Pippenger--Spencer theorem implies the multiplicative weighted theorem.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

namespace KahnDiscretization

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Indexed parallel copies of the edges, with `floor (D * w e)` copies of edge `e`. -/
abbrev CopyIndex (D : ℕ) (w : E → ℝ) :=
  Σ e : E, Fin ⌊(D : ℝ) * w e⌋₊

/-- The unweighted hypergraph of integer copies. -/
def copyHypergraph (H : FiniteHypergraph V E) (D : ℕ) (w : E → ℝ) :
    FiniteHypergraph V (CopyIndex D w) where
  vertexSet := H.vertexSet
  support c := H.support c.1
  support_subset_vertexSet c := H.support_subset_vertexSet c.1

@[simp] lemma copyHypergraph_vertexSet (H : FiniteHypergraph V E) (D : ℕ) (w : E → ℝ) :
    (copyHypergraph H D w).vertexSet = H.vertexSet := rfl

@[simp] lemma copyHypergraph_support (H : FiniteHypergraph V E) (D : ℕ) (w : E → ℝ)
    (c : CopyIndex D w) :
    (copyHypergraph H D w).support c = H.support c.1 := rfl

lemma copyHypergraph_isUniform {H : FiniteHypergraph V E} {D : ℕ} {w : E → ℝ} {k : ℕ}
    (hH : H.IsUniform k) : (copyHypergraph H D w).IsUniform k := by
  intro c
  exact hH c.1

lemma card_copyIndex (D : ℕ) (w : E → ℝ) :
    Fintype.card (CopyIndex D w) = ∑ e, ⌊(D : ℝ) * w e⌋₊ := by
  simp [CopyIndex, Fintype.card_sigma]

/-- Filtering the copy type by a predicate on original edges is the sigma type over the
filtered original edges. -/
def copySubtypeEquiv (D : ℕ) (w : E → ℝ) (p : E → Prop) :
    {c : CopyIndex D w // p c.1} ≃ Σ e : {e : E // p e}, Fin ⌊(D : ℝ) * w e.val⌋₊ where
  toFun c := ⟨⟨c.val.1, c.property⟩, c.val.2⟩
  invFun c := ⟨⟨c.1.val, c.2⟩, c.1.property⟩
  left_inv c := by cases c with | mk c hc => cases c; rfl
  right_inv c := by cases c with | mk e i => cases e; rfl

lemma card_copyIndex_filter (D : ℕ) (w : E → ℝ) (p : E → Prop) [DecidablePred p] :
    #{c : CopyIndex D w | p c.1} = ∑ e with p e, ⌊(D : ℝ) * w e⌋₊ := by
  calc
    #{c : CopyIndex D w | p c.1} = Fintype.card {c : CopyIndex D w // p c.1} :=
      (Fintype.card_subtype (fun c : CopyIndex D w ↦ p c.1)).symm
    _ = Fintype.card (Σ e : {e : E // p e}, Fin ⌊(D : ℝ) * w e.val⌋₊) :=
      Fintype.card_congr (copySubtypeEquiv D w p)
    _ = ∑ e : {e : E // p e}, ⌊(D : ℝ) * w e.val⌋₊ := by
      simp [Fintype.card_sigma]
    _ = ∑ e with p e, ⌊(D : ℝ) * w e⌋₊ :=
      (Finset.sum_subtype ((Finset.univ : Finset E).filter p) (by simp)
        (fun e ↦ ⌊(D : ℝ) * w e⌋₊)).symm

lemma edgeDegree_copyHypergraph (H : FiniteHypergraph V E) (D : ℕ) (w : E → ℝ)
    (v : V) :
    (copyHypergraph H D w).edgeDegree v =
      ∑ e with v ∈ H.support e, ⌊(D : ℝ) * w e⌋₊ := by
  rw [FiniteHypergraph.edgeDegree]
  change #{c : CopyIndex D w | v ∈ H.support c.1} = _
  exact card_copyIndex_filter D w (fun e ↦ v ∈ H.support e)

lemma edgePairDegree_copyHypergraph (H : FiniteHypergraph V E) (D : ℕ) (w : E → ℝ)
    (u v : V) :
    (copyHypergraph H D w).edgePairDegree u v =
      ∑ e with u ∈ H.support e ∧ v ∈ H.support e, ⌊(D : ℝ) * w e⌋₊ := by
  rw [FiniteHypergraph.edgePairDegree]
  change #{c : CopyIndex D w | u ∈ H.support c.1 ∧ v ∈ H.support c.1} = _
  exact card_copyIndex_filter D w (fun e ↦ u ∈ H.support e ∧ v ∈ H.support e)

lemma edgeDegree_copyHypergraph_le {H : FiniteHypergraph V E} {D : ℕ} {w : E → ℝ}
    (hw : H.IsFractionalMatching w) {v : V} (hv : v ∈ H.vertexSet) :
    (copyHypergraph H D w).edgeDegree v ≤ D := by
  rw [edgeDegree_copyHypergraph]
  apply_mod_cast (show
    (∑ e with v ∈ H.support e, (⌊(D : ℝ) * w e⌋₊ : ℝ)) ≤ (D : ℝ) from ?_)
  calc
    (∑ e with v ∈ H.support e, (⌊(D : ℝ) * w e⌋₊ : ℝ)) ≤
        ∑ e with v ∈ H.support e, (D : ℝ) * w e := by
      apply Finset.sum_le_sum
      intro e _he
      exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg D) (hw.nonneg e))
    _ = (D : ℝ) * H.vertexLoad w v := by
      rw [FiniteHypergraph.vertexLoad, Finset.mul_sum]
    _ ≤ (D : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (hw.vertexLoad_le_one hv) (Nat.cast_nonneg D)
    _ = (D : ℝ) := mul_one _

lemma edgePairDegree_copyHypergraph_lt {H : FiniteHypergraph V E} {D : ℕ} {w : E → ℝ}
    {eta : ℝ} (hD : 0 < D) (hw : H.IsFractionalMatching w)
    (hpair : H.PairCodegreeLT w eta) {u v : V} (huv : u ≠ v) :
    ((copyHypergraph H D w).edgePairDegree u v : ℝ) < eta * (D : ℝ) := by
  rw [edgePairDegree_copyHypergraph, Nat.cast_sum]
  calc
    (∑ e with u ∈ H.support e ∧ v ∈ H.support e,
        (⌊(D : ℝ) * w e⌋₊ : ℝ)) ≤
        ∑ e with u ∈ H.support e ∧ v ∈ H.support e, (D : ℝ) * w e := by
      apply Finset.sum_le_sum
      intro e _he
      exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg D) (hw.nonneg e))
    _ = (D : ℝ) * H.pairLoad w u v := by
      rw [FiniteHypergraph.pairLoad, Finset.mul_sum]
    _ < (D : ℝ) * eta :=
      mul_lt_mul_of_pos_left (hpair u v huv) (Nat.cast_pos.mpr hD)
    _ = eta * (D : ℝ) := mul_comm _ _

/-- The total number of copies loses less than one copy per original indexed edge. -/
lemma card_copyIndex_lower {H : FiniteHypergraph V E} {D : ℕ} {w : E → ℝ}
    (hw : H.IsFractionalMatching w) :
    (D : ℝ) * H.totalWeight w - Fintype.card E ≤ Fintype.card (CopyIndex D w) := by
  rw [card_copyIndex, Nat.cast_sum]
  calc
    (D : ℝ) * H.totalWeight w - Fintype.card E =
        ∑ e, ((D : ℝ) * w e - 1) := by
      rw [FiniteHypergraph.totalWeight, Finset.mul_sum]
      simp [Finset.sum_sub_distrib]
    _ ≤ ∑ e, (⌊(D : ℝ) * w e⌋₊ : ℝ) := by
      apply Finset.sum_le_sum
      intro e _he
      have hfloor := (Nat.lt_floor_add_one ((D : ℝ) * w e)).le
      linarith

/-- Project a matching of parallel copies back to its original indexed edges. -/
def projectMatching (D : ℕ) (w : E → ℝ) (M : Finset (CopyIndex D w)) : Finset E :=
  M.image Sigma.fst

lemma projectMatching_isMatching {H : FiniteHypergraph V E} {D : ℕ} {w : E → ℝ}
    {M : Finset (CopyIndex D w)} (hM : (copyHypergraph H D w).IsMatching M) :
    H.IsMatching (projectMatching D w M) := by
  rw [FiniteHypergraph.IsMatching]
  rintro e he f hf hef
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hf
  have hcd : c ≠ d := by
    intro h
    apply hef
    simpa [h]
  exact hM hc hd hcd

lemma projectMatching_card {H : FiniteHypergraph V E} {D : ℕ} {w : E → ℝ}
    {k : ℕ} (hk : 0 < k) (hunif : H.IsUniform k)
    {M : Finset (CopyIndex D w)} (hM : (copyHypergraph H D w).IsMatching M) :
    (projectMatching D w M).card = M.card := by
  rw [projectMatching, Finset.card_image_iff]
  intro c hc d hd hfst
  by_contra hcd
  have hdis : Disjoint (H.support c.1) (H.support d.1) := hM hc hd hcd
  rw [hfst] at hdis
  have hempty : H.support d.1 = ∅ :=
    (Finset.disjoint_self_iff_empty (H.support d.1)).mp hdis
  have hcard := hunif d.1
  rw [hempty] at hcard
  simp at hcard
  omega

end KahnDiscretization

open KahnDiscretization

/-- The maximum-degree Pippenger--Spencer theorem implies the multiplicative weighted
matching theorem.  Integer copies preserve the original indexed edge, including parallel
supports; the loss from flooring is absorbed by choosing the copy scale after seeing the
finite fractional matching. -/
theorem pippengerSpencerMatching_to_kahnMultiplicative
    (hPS : PippengerSpencerMatching) : KahnMultiplicativeMatching := by
  intro k hk rho hrho
  by_cases hrho_one : 1 ≤ rho
  · refine ⟨1, zero_lt_one, ?_⟩
    intro V E _ _ _ H w _hunif hw _hpair
    refine ⟨∅, H.empty_isMatching, ?_⟩
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrho_one) (H.totalWeight_nonneg hw)
  · have hrho_lt_one : rho < 1 := lt_of_not_ge hrho_one
    let epsilon : ℝ := rho / 2
    have hepsilon : 0 < epsilon := div_pos hrho (by norm_num)
    have hepsilon_lt_one : epsilon < 1 := by
      dsimp [epsilon]
      linarith
    obtain ⟨eta, heta, D₀, hround⟩ := hPS k hk epsilon hepsilon
    refine ⟨eta, heta, ?_⟩
    intro V E _ _ _ H w hunif hw hpair
    by_cases hweight : H.totalWeight w = 0
    · refine ⟨∅, H.empty_isMatching, ?_⟩
      simp [hweight]
    · have hweight_pos : 0 < H.totalWeight w :=
        (H.totalWeight_nonneg hw).lt_of_ne (Ne.symm hweight)
      obtain ⟨D, hDlarge⟩ := exists_nat_gt
        (max (D₀ : ℝ) ((Fintype.card E : ℝ) / (epsilon * H.totalWeight w)))
      have hD₀_real : (D₀ : ℝ) < D := (le_max_left _ _).trans_lt hDlarge
      have hD₀ : D₀ ≤ D := by exact_mod_cast hD₀_real.le
      have hratio : (Fintype.card E : ℝ) / (epsilon * H.totalWeight w) < D :=
        (le_max_right _ _).trans_lt hDlarge
      have hdenom : 0 < epsilon * H.totalWeight w := mul_pos hepsilon hweight_pos
      have hDpos_real : (0 : ℝ) < D := by
        exact lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (D₀ : ℝ)) hD₀_real
      have hDpos : 0 < D := by exact_mod_cast hDpos_real
      have hfloor_loss : (Fintype.card E : ℝ) ≤
          epsilon * (D : ℝ) * H.totalWeight w := by
        have := (div_lt_iff₀ hdenom).mp hratio
        nlinarith
      let HC : FiniteHypergraph V (CopyIndex D w) := copyHypergraph H D w
      obtain ⟨MC, hMC, hMCsize⟩ := hround V (CopyIndex D w) HC D hD₀
        (copyHypergraph_isUniform hunif)
        (by
          intro v hv
          exact edgeDegree_copyHypergraph_le hw hv)
        (by
          intro u hu v hv huv
          exact edgePairDegree_copyHypergraph_lt hDpos hw hpair huv)
      let M : Finset E := projectMatching D w MC
      refine ⟨M, projectMatching_isMatching hMC, ?_⟩
      have hcopy_lower : (D : ℝ) * H.totalWeight w - Fintype.card E ≤
          Fintype.card (CopyIndex D w) := card_copyIndex_lower hw
      have hcopy_scaled : (1 - epsilon) * ((D : ℝ) * H.totalWeight w) ≤
          Fintype.card (CopyIndex D w) := by
        calc
          (1 - epsilon) * ((D : ℝ) * H.totalWeight w) ≤
              (D : ℝ) * H.totalWeight w - Fintype.card E := by
            nlinarith
          _ ≤ Fintype.card (CopyIndex D w) := hcopy_lower
      have hcopy_div : (1 - epsilon) * H.totalWeight w ≤
          (Fintype.card (CopyIndex D w) : ℝ) / (D : ℝ) := by
        rw [le_div_iff₀ hDpos_real]
        calc
          (1 - epsilon) * H.totalWeight w * (D : ℝ) =
              (1 - epsilon) * ((D : ℝ) * H.totalWeight w) := by ring
          _ ≤ Fintype.card (CopyIndex D w) := hcopy_scaled
      have hone_minus_epsilon : 0 ≤ 1 - epsilon := sub_nonneg.mpr hepsilon_lt_one.le
      have hsquared : (1 - epsilon) ^ 2 * H.totalWeight w ≤
          (1 - epsilon) * (Fintype.card (CopyIndex D w) : ℝ) / (D : ℝ) := by
        calc
          (1 - epsilon) ^ 2 * H.totalWeight w =
              (1 - epsilon) * ((1 - epsilon) * H.totalWeight w) := by ring
          _ ≤ (1 - epsilon) *
              ((Fintype.card (CopyIndex D w) : ℝ) / (D : ℝ)) :=
            mul_le_mul_of_nonneg_left hcopy_div hone_minus_epsilon
          _ = (1 - epsilon) * (Fintype.card (CopyIndex D w) : ℝ) / (D : ℝ) := by
            ring
      calc
        (1 - rho) * H.totalWeight w ≤ (1 - epsilon) ^ 2 * H.totalWeight w := by
          apply mul_le_mul_of_nonneg_right _ (H.totalWeight_nonneg hw)
          dsimp [epsilon]
          nlinarith [sq_nonneg rho]
        _ ≤ (1 - epsilon) * (Fintype.card (CopyIndex D w) : ℝ) / (D : ℝ) := hsquared
        _ ≤ (MC.card : ℝ) := hMCsize
        _ = (M.card : ℝ) := by
          exact_mod_cast (projectMatching_card hk hunif hMC).symm

end

end Erdos76

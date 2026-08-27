/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualAugmentedReserveAdjoin
import ErdosProblems.Erdos207.ResidualAugmentedReserveScalars
import ErdosProblems.Erdos207.ResidualGraphAdjoinNumeric

/-! # Quantitative propagation through a correlated augmented-reserve update -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.jointBind_augmentedReserve_numeric
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ} {W : Vortex V ell} {k next : Fin (ell + 1)}
    {G : SimpleGraph V} {initial later : Ω → TripleSystemOn V}
    {reserve : Ω → Finset (Sym2 V)} {p reserveDensity C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p reserveDensity C b)
    (working : Ω → SimpleGraph V) (U : Finset V)
    (added : Ω → Ξ → TripleSystemOn V) (alpha eta J factor delta reserveDensity' : ℝ≥0)
    (hC : 1 ≤ C) (hJ : 1 ≤ J) (hfactor : 1 ≤ factor) (halpha : alpha ≤ 1)
    (heta : eta ≤ 1) (hr : reserveDensity ≤ reserveDensity') (hetar : eta ≤ reserveDensity')
    (hkn : k ≤ next) (hnonempty : ∀ i, (W.U i).Nonempty)
    (hnew : alpha * p ^ 3 ≤ factor * (p / ((W.U k).card : ℝ≥0)))
    (hpre : ∀ ω, 0 < L.mass ω → ∀ Q E,
      (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ ∧
        E ⊆ preliminaryResidualCrossingEdges (working ω) U (added ω ξ) \ reserve ω) ≤
          alpha ^ Q.card * eta ^ E.card + J ^ (Q.card + E.card) * delta)
    (hstruct : ∀ ω, 0 < L.mass ω → (K ω).SupportedOn fun ξ ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ added ω ξ) ∧
      Disjoint (initial ω ∪ later ω) (added ω ξ) ∧
      ∀ T ∈ added ω ξ, tripleEdgeFinset T ⊆ graphEdges G)
    (hscope : ∀ ω, 0 < L.mass ω → (K ω).SupportedOn fun ξ ↦
      ∀ T ∈ added ω ξ, T.1 ⊆ W.U k) :
    IsResidualReserveStronglyWellDistributed (L.jointBind K) W next G
      (jointInitial initial) (jointLater later added) (fun z ↦ preliminaryAugmentedReserve (working z.1) U (reserve z.1) (added z.1 z.2))
      p reserveDensity' (2 * max (C ^ 3 * factor) J) (b + delta) := by
  classical
  let Scope := fun Q : TripleSystemOn V ↦ ∀ T ∈ Q, T.1 ⊆ W.U k
  let bound := fun Q : TripleSystemOn V ↦ fun E : Finset (Sym2 V) ↦
    if Scope Q then alpha ^ Q.card * eta ^ E.card + J ^ (Q.card + E.card) * delta else 0
  have hbound : ∀ ω, 0 < L.mass ω → ∀ Q E,
      (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ ∧
        E ⊆ preliminaryResidualCrossingEdges (working ω) U (added ω ξ) \ reserve ω) ≤ bound Q E := by
    intro ω hω Q E
    by_cases hQ : Scope Q
    · simpa only [bound, if_pos hQ] using hpre ω hω Q E
    · have hzero : (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ ∧
          E ⊆ preliminaryResidualCrossingEdges (working ω) U (added ω ξ) \ reserve ω) ≤ (K ω).probability (fun _ ↦ False) := by
        apply (K ω).probability_mono_of_supported (hscope ω hω)
        intro ξ hξ hQnew
        exact hQ (fun T hT ↦ hξ T (hQnew.1 hT))
      simpa only [bound, if_neg hQ, FiniteLaw.probability_false] using hzero
  intro Ifix Dfix Efix Rfix hdis hE
  let Cnext := max (C ^ 3 * factor) J
  let m := Ifix.card + Dfix.card + Efix.card + Rfix.card
  let X := p ^ Efix.card * reserveDensity' ^ Rfix.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card * laterTriangleScale W next p Dfix + (b + delta)
  have hCnext : 1 ≤ Cnext := hJ.trans (le_max_right _ _)
  have hraw := L.jointBind_residual_augmentedReserve_probability_le_on_support K G initial later reserve working U added bound hbound hstruct
    Ifix Dfix Efix Rfix
  calc
    _ ≤ ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset, if IsPackingOn (Dfix \ S) ∧
        (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
        Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix then
        bound (Dfix \ S) (Rfix \ T) * L.probability
          (ResidualReserveDistributionEvent initial later reserve Ifix S (pendingSurvivalEdges (Dfix \ S) Efix) T) else 0 := hraw
    _ ≤ ∑ _S ∈ Dfix.powerset, ∑ _T ∈ Rfix.powerset, Cnext ^ m * X := by
      apply sum_le_sum
      intro S hS
      apply sum_le_sum
      intro T hT
      split_ifs with hgood
      · by_cases hQ : Scope (Dfix \ S)
        · simp only [bound, if_pos hQ]
          have hSD := mem_powerset.mp hS
          have hcard : Dfix.card = S.card + (Dfix \ S).card := by
            rw [card_sdiff_of_subset hSD]
            have := card_le_card hSD
            omega
          have hRcard : Rfix.card = T.card + (Rfix \ T).card := by
            rw [card_sdiff_of_subset (mem_powerset.mp hT)]
            have := card_le_card (mem_powerset.mp hT)
            omega
          have hscale := laterTriangleScale_mul_pow_le_factor W k next p p (alpha * p ^ 3) factor Dfix S hSD
            (fun T _ ↦ W.laterTrianglePointScale_mono hnonempty hkn (le_refl p) T)
            (fun T hT ↦ hnew.trans (mul_le_mul_of_nonneg_left
              (W.laterTrianglePointScale_ge_of_supported hnonempty hkn p T (hQ T hT)) zero_le))
          have hterm := residualAugmentedReserveAdjoinPartitionTerm_le p alpha eta C factor b (Fintype.card V : ℝ≥0)⁻¹
            (laterTriangleScale W k p S) (laterTriangleScale W next p Dfix) reserveDensity reserveDensity'
            Ifix.card S.card Efix.card (Dfix \ S).card Dfix.card T.card (Rfix \ T).card Rfix.card
            hcard hRcard hC hfactor halpha heta hr hetar hscale
          have hprior := hstrong Ifix S (pendingSurvivalEdges (Dfix \ S) Efix) T
            (Disjoint.mono_right hSD hdis) (union_subset hgood.2.1 hE)
          rw [card_pendingSurvivalEdges hgood.1 hgood.2.2] at hprior
          have hcount : (Dfix \ S).card + (Rfix \ T).card ≤ m := by dsimp only [m]; omega
          have hjpow : J ^ ((Dfix \ S).card + (Rfix \ T).card) ≤ Cnext ^ m :=
            (pow_le_pow_left' (le_max_right _ _) _).trans (pow_le_pow_right₀ hCnext hcount)
          calc
            _ ≤ (alpha ^ (Dfix \ S).card * eta ^ (Rfix \ T).card) *
                (C ^ (Ifix.card + S.card + (3 * (Dfix \ S).card + Efix.card) + T.card) *
                  (p ^ (3 * (Dfix \ S).card + Efix.card) * reserveDensity ^ T.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                    laterTriangleScale W k p S + b)) + J ^ ((Dfix \ S).card + (Rfix \ T).card) * delta := by
              rw [add_mul]
              apply add_le_add (mul_le_mul_of_nonneg_left hprior zero_le)
              exact mul_le_of_le_one_right zero_le (L.probability_le_one _)
            _ ≤ (C ^ 3 * factor) ^ m *
                (p ^ Efix.card * reserveDensity' ^ Rfix.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card * laterTriangleScale W next p Dfix + b) +
                Cnext ^ m * delta := add_le_add hterm (mul_le_mul_of_nonneg_right hjpow zero_le)
            _ ≤ Cnext ^ m *
                (p ^ Efix.card * reserveDensity' ^ Rfix.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card * laterTriangleScale W next p Dfix + b) +
                Cnext ^ m * delta := by
              exact add_le_add
                (mul_le_mul_of_nonneg_right (pow_le_pow_left' (le_max_left _ _) m) zero_le) le_rfl
            _ = _ := by dsimp only [X]; ring
        · simp only [bound, if_neg hQ, zero_mul]
          exact zero_le
      · exact zero_le
    _ = ((2 : ℝ≥0) ^ Dfix.card * 2 ^ Rfix.card) * (Cnext ^ m * X) := by simp [mul_assoc]
    _ ≤ (2 : ℝ≥0) ^ m * (Cnext ^ m * X) := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by dsimp only [m]; omega)
    _ = _ := by rw [mul_pow]; dsimp only [m, X, Cnext]; ring

end

end Erdos207

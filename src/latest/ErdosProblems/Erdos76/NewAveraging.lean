import ErdosProblems.Erdos76.FractionalBound
import ErdosProblems.Erdos76.LocalAveraging

/-!
# Smoothing the new fractional bound

Average the explicit bound over fixed-size induced subgraphs. The existing
finite averaging identities supply arbitrarily small weighted codegrees.
-/

open Filter Finset
open scoped BigOperators

namespace Erdos76.NewProof

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem exists_localAveragingFamily_new (G : SimpleGraph A) (m : ℕ) :
    ∃ fam : Finset A → MonoTriangle G → ℝ,
      IsLocalAveragingFamily G m fam ∧
        ∀ S ∈ fixedCardSubsets m,
          (m : ℝ) ^ 2 / 12 - (m : ℝ) / 2 ≤
            (monochromaticTriangleHypergraph G).totalWeight (fam S) := by
  let Valid := {S : Finset A // S ∈ fixedCardSubsets (A := A) m}
  have hex : ∀ S : Valid, ∃ wR wB : Finset A → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
        (∀ t, ¬t ⊆ S.1 → wR t = 0 ∧ wB t = 0) ∧
        (m : ℝ) ^ 2 / 12 - (m : ℝ) / 2 ≤ fractionalSize G wR + fractionalSize Gᶜ wB := by
    intro S
    have hcard : Fintype.card S.1 = m := by
      rw [Fintype.card_coe]
      exact mem_fixedCardSubsets.mp S.2
    have hcard' : Fintype.card (S.1 : Set A) = m := by
      calc
        _ = Nat.card (S.1 : Set A) := Nat.card_eq_fintype_card.symm
        _ = Fintype.card S.1 := Nat.card_eq_fintype_card
        _ = m := hcard
    obtain ⟨uR, uB, huR, huB, hsize⟩ := explicit_fractional_bound (G.induce (S.1 : Set A))
    obtain ⟨heR, heB, heSize⟩ := extendInduced_pair huR huB
    refine ⟨extendInducedWeight S.1 uR, extendInducedWeight S.1 uB, heR, heB, ?_, ?_⟩
    · intro t ht
      exact ⟨extendInducedWeight_eq_zero ht, extendInducedWeight_eq_zero ht⟩
    · rw [hcard'] at hsize
      simp only [fractionalCoveredSize] at heSize
      linarith
  choose wR wB hw using hex
  let fam : Finset A → MonoTriangle G → ℝ := fun S t ↦
    if hS : S ∈ fixedCardSubsets (A := A) m then
      monoColorWeight G (wR ⟨S, hS⟩) (wB ⟨S, hS⟩) t
    else 0
  refine ⟨fam, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro S hS t
      simp only [fam, dif_pos hS]
      exact monoColorWeight_nonneg G (hw ⟨S, hS⟩).1 (hw ⟨S, hS⟩).2.1 t
    · intro S hS t
      simp only [fam, dif_pos hS]
      by_cases ht : t.1 ⊆ S
      · rw [if_pos ht]
        exact monoColorWeight_le_one G (hw ⟨S, hS⟩).1 (hw ⟨S, hS⟩).2.1 t
      · rw [if_neg ht]
        obtain ⟨hzR, hzB⟩ := (hw ⟨S, hS⟩).2.2.1 t.1 ht
        simp only [monoColorWeight]
        split_ifs
        · rw [hzR]
        · rw [hzB]
    · intro S hS e he
      simp only [fam, dif_pos hS]
      by_cases heS : e ⊆ S
      · rw [if_pos heS]
        exact (monoColorWeight_isFractionalMatching G
          (hw ⟨S, hS⟩).1 (hw ⟨S, hS⟩).2.1).2 e he
      · rw [if_neg heS]
        unfold FiniteHypergraph.vertexLoad
        apply le_of_eq
        apply sum_eq_zero
        intro t ht
        simp only [mem_filter, mem_univ, true_and] at ht
        have het : e ⊆ t.1 := (mem_powersetCard.mp ht).1
        have htS : ¬t.1 ⊆ S := fun h ↦ heS (het.trans h)
        obtain ⟨hzR, hzB⟩ := (hw ⟨S, hS⟩).2.2.1 t.1 htS
        simp only [monoColorWeight]
        split_ifs <;> assumption
  · intro S hS
    simp only [fam, dif_pos hS, totalWeight_monoColorWeight]
    exact (hw ⟨S, hS⟩).2.2.2

theorem exists_averagedMonoWeight_new (G : SimpleGraph A) (m : ℕ)
    (hm : 3 ≤ m) (hmA : m ≤ Fintype.card A) :
    ∃ w : MonoTriangle G → ℝ,
      (monochromaticTriangleHypergraph G).IsFractionalMatching w ∧
      ((Fintype.card A).choose m : ℝ) /
          ((Fintype.card A - 2).choose (m - 2) : ℝ) *
            ((m : ℝ) ^ 2 / 12 - (m : ℝ) / 2) ≤
        (monochromaticTriangleHypergraph G).totalWeight w ∧
      ∀ e f : Finset A, e ≠ f →
        (monochromaticTriangleHypergraph G).pairLoad w e f ≤
          ((m - 2 : ℕ) : ℝ) / ((Fintype.card A - 2 : ℕ) : ℝ) := by
  obtain ⟨fam, hlocal, hsize⟩ := exists_localAveragingFamily_new G m
  refine ⟨averagedMonoWeight G m fam,
    averagedMonoWeight_isFractionalMatching G m hlocal (by omega) hmA,
    averagedMonoWeight_totalWeight_lower G m (by omega) hmA hsize, ?_⟩
  intro e f hef
  exact averagedMonoWeight_pairLoad_le_ratio G m hlocal hm hmA hef

private lemma real_averaging_factor_lower {c x y : ℝ}
    (hc : 0 ≤ c) (hx : 1 < x) (hy : 1 ≤ y) :
    c * y * (y - 1) ≤ y * (y - 1) / (x * (x - 1)) * (c * x ^ 2) := by
  have hxsub : 0 < x - 1 := sub_pos.mpr hx
  have hxratio : 1 ≤ x / (x - 1) := (one_le_div hxsub).2 (by linarith)
  have hcy : 0 ≤ c * y * (y - 1) := by positivity
  calc
    c * y * (y - 1) = c * y * (y - 1) * 1 := by ring
    _ ≤ c * y * (y - 1) * (x / (x - 1)) := mul_le_mul_of_nonneg_left hxratio hcy
    _ = y * (y - 1) / (x * (x - 1)) * (c * x ^ 2) := by field_simp

/-- The new elementary fractional bound supplies precisely the small-codegree
input required for the proved hypergraph rounding theorem. -/
theorem smoothed_fractional : SmoothedFractionalMonochromaticTriangles := by
  intro ε hε δ hδ
  by_cases hlargeε : (1 / 12 : ℝ) ≤ ε
  · apply Filter.Eventually.of_forall
    intro n G
    let w : MonoTriangle G → ℝ := fun _ ↦ 0
    refine ⟨w, FiniteHypergraph.isFractionalMatching_zero _, ?_, ?_⟩
    · intro e f hef
      simpa only [w, FiniteHypergraph.pairLoad_zero] using hδ
    · calc
        (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlargeε) (sq_nonneg _)
        _ = (monochromaticTriangleHypergraph G).totalWeight w := by
          simp only [w, FiniteHypergraph.totalWeight_zero]
  · have hsmallε : ε < (1 / 12 : ℝ) := lt_of_not_ge hlargeε
    obtain ⟨m, hm⟩ := exists_nat_gt (max 3 (1 / ε))
    have hm3 : 3 ≤ m := by
      have : (3 : ℝ) < m := (le_max_left _ _).trans_lt hm
      exact_mod_cast this.le
    have hmq : (1 / 12 - ε / 2) * (m : ℝ) ^ 2 ≤
        (m : ℝ) ^ 2 / 12 - (m : ℝ) / 2 := by
      have hmε : 1 / ε < (m : ℝ) := (le_max_right _ _).trans_lt hm
      have hone := (div_lt_iff₀ hε).mp hmε
      have hmul := mul_le_mul_of_nonneg_right hone.le (Nat.cast_nonneg m)
      nlinarith
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / (6 * ε)) (2 + (m : ℝ) / δ))
    filter_upwards [eventually_ge_atTop (max m N)] with n hn
    intro G
    have hmn : m ≤ n := (le_max_left m N).trans hn
    have hNn : N ≤ n := (le_max_right m N).trans hn
    have hnreal : max (1 / (6 * ε)) (2 + (m : ℝ) / δ) < (n : ℝ) :=
      hN.trans_le (by exact_mod_cast hNn)
    have hnlinear : 1 / (6 * ε) < (n : ℝ) := (le_max_left _ _).trans_lt hnreal
    have hncodeg : 2 + (m : ℝ) / δ < (n : ℝ) := (le_max_right _ _).trans_lt hnreal
    obtain ⟨w, hw, hweight, hcodeg⟩ :=
      exists_averagedMonoWeight_new G m hm3 (by simpa using hmn)
    simp only [Fintype.card_fin] at hweight hcodeg
    refine ⟨w, hw, ?_, ?_⟩
    · intro e f hef
      apply (hcodeg e f hef).trans_lt
      have hn2 : 2 < n := by omega
      have hden : (0 : ℝ) < ((n - 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt hn2
      rw [div_lt_iff₀ hden]
      have hquot : (m : ℝ) / δ < (n : ℝ) - 2 := by linarith
      have hmprod : (m : ℝ) < ((n : ℝ) - 2) * δ := (div_lt_iff₀ hδ).1 hquot
      rw [Nat.cast_sub hn2.le]
      calc
        ((m - 2 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 2
        _ < ((n : ℝ) - 2) * δ := hmprod
        _ = δ * ((n : ℝ) - 2) := by ring
    · let q : ℝ := (m : ℝ) ^ 2 / 12 - (m : ℝ) / 2
      let c : ℝ := 1 / 12 - ε / 2
      have hc : 0 ≤ c := by dsimp only [c]; linarith
      have hm1 : 1 ≤ m := by omega
      have hn1 : 1 ≤ n := hm1.trans hmn
      have hmq' : c * (m : ℝ) ^ 2 ≤ q := hmq
      have hratio := cast_choose_div_choose_sub_two (m := m) (n := n) (by omega) hmn
      have hweight' :
          (n : ℝ) * ((n - 1 : ℕ) : ℝ) /
                ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * q ≤
            (monochromaticTriangleHypergraph G).totalWeight w := by
        rw [← hratio]
        exact hweight
      have hfactor : 0 ≤ (n : ℝ) * ((n - 1 : ℕ) : ℝ) /
          ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hmq' hfactor
      have hbase : c * (n : ℝ) * ((n : ℝ) - 1) ≤
          (n : ℝ) * ((n - 1 : ℕ) : ℝ) /
              ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * (c * (m : ℝ) ^ 2) := by
        simpa only [Nat.cast_sub hn1, Nat.cast_sub hm1, Nat.cast_one] using
          (real_averaging_factor_lower hc
            (by exact_mod_cast (show 1 < m by omega)) (by exact_mod_cast hn1))
      have hsixε : 0 < 6 * ε := mul_pos (by norm_num) hε
      have hone : (1 : ℝ) < 6 * ε * (n : ℝ) := by
        have := (div_lt_iff₀ hsixε).1 hnlinear
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right hone.le (Nat.cast_nonneg n)
      have hlinear : (n : ℝ) / 12 ≤ ε / 2 * (n : ℝ) ^ 2 := by nlinarith
      have htarget : (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ c * (n : ℝ) * ((n : ℝ) - 1) := by
        dsimp only [c]
        nlinarith
      exact htarget.trans (hbase.trans (hscaled.trans hweight'))

end

end Erdos76.NewProof

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FixedRandomOrderInputs

/-! # Finite all-order regularization with deterministic source envelopes -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

structure FixedRandomOrderResult
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell : ℕ} (P : FiniteLaw D) (W : Vortex V ell) (e : (d : D) → I d ↪ TripleOn V)
    (j b : ℕ) (L earlier : (d : D) → Finset (Finset (I d)))
    (F C : ForbiddenFamilyOn V) (y z a rho : ℝ≥0)
    (Lstar : (d : D) → Finset (Finset (I d))) (R : ForbiddenFamilyOn V) : Prop where
  support : R ⊆ C
  spread : SourceVortexWellSpread W j (F ∪ R) (y + a) (z + 3 * a)
  counts : SourceAugmentationCounts j W.terminalSize F R a
  uniform : ∀ d E, E ∈ Lstar d → E.card = j - 2
  maximum : ∀ d, finiteHypergraphMaxDegree (Lstar d) ≤ 9 * finiteHypergraphMaxDegree (L d)
  no_earlier_subset : ∀ d E, E ∈ Lstar d → ∀ A ∈ earlier d, ¬ A ⊆ E
  covers_original : ∀ d E, E ∈ L d → ∃ A ∈ earlier d ∪ Lstar d, A ⊆ E
  contains_new_constraints : ∀ d, (Lstar d \ L d).image (Finset.map (e d)) ⊆ F ∪ R
  failure : P.probability (fun d ↦ b < finiteHypergraphDegreeGap (Lstar d)) < rho

theorem finset_biUnion_update_apply_of_not_mem
    {D K : Type*} [DecidableEq K] {J : D → Type*} [∀ d, DecidableEq (J d)]
    (S : Finset K) (f : K → (d : D) → Finset (J d)) (k : K)
    (v : (d : D) → Finset (J d)) (hk : k ∉ S) (d : D) :
    S.biUnion (fun i ↦ Function.update f k v i d) = S.biUnion (fun i ↦ f i d) := by
  apply biUnion_congr rfl
  intro i hi
  rw [Function.update_of_ne (show i ≠ k from fun heq ↦ hk (heq ▸ hi))]

theorem exists_fixed_random_all_orders
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell : ℕ} (P : FiniteLaw D) (W : Vortex V ell) (e : (d : D) → I d ↪ TripleOn V)
    (hsupport : ∀ d i, (e d i).1 ⊆ W.U (Fin.last ell)) (q : ℕ) (hq : q ≤ W.terminalSize)
    (L : ℕ → (d : D) → Finset (Finset (I d))) (F C : ℕ → ForbiddenFamilyOn V)
    (b s : ℕ → ℕ) (y z a delta epsilon rho : ℕ → ℝ≥0) (sigma constant B : ℕ → D → ℝ≥0)
    (hinputs : ∀ j ∈ Icc 4 q, ∀ d, SourceRegularizationOrderInput W j (L j d) (F j)
      (b j) (s j) (y j) (z j) (a j) (delta j) (sigma j d) (constant j d) (B j d))
    (hC : ∀ j ∈ Icc 4 q, C j ⊆ terminalRandomConfigurations W j)
    (hgeometry : ∀ j ∈ Icc 4 q, ∀ d (E : Finset (I d)), E.card = j - 2 →
      E.map (e d) ∈ terminalRandomConfigurations W j → E.map (e d) ∈ C j)
    (hrho : ∀ j ∈ Icc 4 q, 0 < rho j)
    (hepsilon : ∀ j ∈ Icc 4 q, ∀ d, (finiteHypergraphMaxDegree (L j d) : ℝ) *
      (2 * Fintype.card (I d) * Real.exp (-(b j : ℝ) / 8192)) ≤ epsilon j)
    (hbudget : ∀ j ∈ Icc 4 q, sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s j)⁻¹ +
      epsilon j / rho j < 1) :
    ∃ Lstar : ℕ → (d : D) → Finset (Finset (I d)), ∃ R : ℕ → ForbiddenFamilyOn V,
      ∀ j ∈ Icc 4 q, FixedRandomOrderResult P W e j (b j) (L j)
        (fun d ↦ (Ico 4 j).biUnion (fun i ↦ Lstar i d)) (F j) (C j)
        (y j) (z j) (a j) (rho j) (Lstar j) (R j) := by
  have hbuild : ∀ r : ℕ, r ≤ q →
      ∃ Lstar : ℕ → (d : D) → Finset (Finset (I d)), ∃ R : ℕ → ForbiddenFamilyOn V,
        ∀ j ∈ Icc 4 r, FixedRandomOrderResult P W e j (b j) (L j)
          (fun d ↦ (Ico 4 j).biUnion (fun i ↦ Lstar i d)) (F j) (C j)
          (y j) (z j) (a j) (rho j) (Lstar j) (R j) := by
    intro r
    induction r with
    | zero =>
        intro _
        refine ⟨fun _ _ ↦ ∅, fun _ ↦ ∅, ?_⟩
        intro j hj
        have hh := mem_Icc.mp hj
        omega
    | succ r ih =>
        intro hr
        obtain ⟨Lprev, Rprev, hprev⟩ := ih (by omega)
        by_cases hfour : 4 ≤ r + 1
        · have hcur : r + 1 ∈ Icc 4 q := mem_Icc.mpr ⟨hfour, hr⟩
          have hprevIndex : ∀ i ∈ Ico 4 (r + 1), i ∈ Icc 4 r := by
            intro i hi
            have hh := mem_Ico.mp hi
            exact mem_Icc.mpr ⟨hh.1, by omega⟩
          have hglobalIndex : ∀ i ∈ Ico 4 (r + 1), i ∈ Icc 4 q := by
            intro i hi
            have hh := mem_Icc.mp (hprevIndex i hi)
            exact mem_Icc.mpr ⟨hh.1, by omega⟩
          obtain ⟨Rnew, Lnew, hRC, hspread, hcounts, hstruct, hfail⟩ :=
            exists_fixed_random_order_of_inputs P e hsupport (L (r + 1)) (F (r + 1))
              (sigma (r + 1)) (constant (r + 1)) (B (r + 1)) (hinputs (r + 1) hcur)
              (Ico 4 (r + 1)) (fun d i ↦ Lprev i d) (fun i ↦ i - 2)
              (by rw [Nat.card_Ico]; omega)
              (fun i hi ↦ by have hh := mem_Ico.mp hi; constructor <;> omega)
              (fun d i hi ↦ (hprev i (hprevIndex i hi)).uniform d)
              (fun d i hi ↦ by
                have hb := ((hprev i (hprevIndex i hi)).maximum d).trans
                  (hinputs i (hglobalIndex i hi) d).maximum_power
                have he : i - 2 - 1 = i - 3 := by omega
                simpa only [he] using hb)
              (C (r + 1)) (hC (r + 1) hcur) (hgeometry (r + 1) hcur)
              (epsilon (r + 1)) (rho (r + 1)) (hrho (r + 1) hcur)
              (hepsilon (r + 1) hcur) (hbudget (r + 1) hcur)
          have hnew : FixedRandomOrderResult P W e (r + 1) (b (r + 1)) (L (r + 1))
              (fun d ↦ (Ico 4 (r + 1)).biUnion (fun i ↦ Lprev i d)) (F (r + 1)) (C (r + 1))
              (y (r + 1)) (z (r + 1)) (a (r + 1)) (rho (r + 1)) Lnew Rnew :=
            ⟨hRC, hspread, hcounts, fun d ↦ (hstruct d).1, fun d ↦ (hstruct d).2.1,
              fun d ↦ (hstruct d).2.2.1, fun d ↦ (hstruct d).2.2.2.1,
              fun d ↦ (hstruct d).2.2.2.2, hfail⟩
          refine ⟨Function.update Lprev (r + 1) Lnew, Function.update Rprev (r + 1) Rnew, ?_⟩
          intro j hj
          by_cases hjeq : j = r + 1
          · subst j
            have hnot : r + 1 ∉ Ico 4 (r + 1) := by simp
            simpa only [Function.update_self, finset_biUnion_update_apply_of_not_mem
              (Ico 4 (r + 1)) Lprev (r + 1) Lnew hnot] using hnew
          · have hjbounds := mem_Icc.mp hj
            have hjold : j ∈ Icc 4 r := mem_Icc.mpr ⟨hjbounds.1, by omega⟩
            have hnot : r + 1 ∉ Ico 4 j := by
              intro hmem
              have hh := mem_Ico.mp hmem
              omega
            simpa only [Function.update_of_ne hjeq, finset_biUnion_update_apply_of_not_mem
              (Ico 4 j) Lprev (r + 1) Lnew hnot] using hprev j hjold
        · refine ⟨Lprev, Rprev, ?_⟩
          intro j hj
          have hh := mem_Icc.mp hj
          omega
  exact hbuild q le_rfl

theorem fixedRandomAllOrders_gap_failure
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell : ℕ} (P : FiniteLaw D) (W : Vortex V ell) (e : (d : D) → I d ↪ TripleOn V)
    (q : ℕ) (b : ℕ → ℕ) (L Lstar : ℕ → (d : D) → Finset (Finset (I d)))
    (F C R : ℕ → ForbiddenFamilyOn V) (y z a rho : ℕ → ℝ≥0)
    (h : ∀ j ∈ Icc 4 q, FixedRandomOrderResult P W e j (b j) (L j)
      (fun d ↦ (Ico 4 j).biUnion (fun i ↦ Lstar i d)) (F j) (C j)
      (y j) (z j) (a j) (rho j) (Lstar j) (R j)) :
    P.probability (fun d ↦ ∃ j ∈ Icc 4 q, b j < finiteHypergraphDegreeGap (Lstar j d)) ≤
      ∑ j ∈ Icc 4 q, rho j := by
  apply (P.probability_exists_le (Icc 4 q) _).trans
  exact sum_le_sum (fun j hj ↦ (h j hj).failure.le)

end

end Erdos207

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Exact cardinalities and uniform probabilities of finite product boxes.
Informal source: the product measure notation in BBMST Section 2.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GridIndependence
import Mathlib.Data.Fintype.BigOperators

namespace Erdos1189.Grid

open Finset

variable {ι : Type*} {q : ι → ℕ}

def boxCoordinate (H : Box q) (i : ι) : Finset (Fin (q i)) :=
  (H i).elim univ singleton

lemma mem_boxCoordinate {H : Box q} {i : ι} {v : Fin (q i)} :
    v ∈ boxCoordinate H i ↔ ∀ w, H i = some w → v = w := by
  cases hi : H i with
  | none => simp [boxCoordinate, hi]
  | some w => simp [boxCoordinate, hi]

lemma boxEvent_eq_piFinset [Fintype ι] [DecidableEq ι] (H : Box q) :
    boxEvent H = Fintype.piFinset (boxCoordinate H) := by
  ext u
  simp only [mem_boxEvent, Fintype.mem_piFinset, mem_boxCoordinate, Contains]

lemma boxCoordinate_card (H : Box q) (i : ι) :
    (boxCoordinate H i).card = (H i).elim (q i) (fun _ => 1) := by
  cases hi : H i <;> simp [boxCoordinate, hi]

lemma boxEvent_card [Fintype ι] [DecidableEq ι] (H : Box q) :
    (boxEvent H).card = ∏ i, (H i).elim (q i) (fun _ => 1) := by
  rw [boxEvent_eq_piFinset, Fintype.card_piFinset]
  exact prod_congr rfl (fun i _ => boxCoordinate_card H i)

noncomputable def boxMeasureOn (I : Finset ι) (H : Box q) : ℝ :=
  ∏ i ∈ I, (H i).elim 1 (fun _ => 1 / (q i : ℝ))

lemma boxMeasureOn_nonneg (I : Finset ι) (H : Box q) : 0 ≤ boxMeasureOn I H := by
  apply prod_nonneg
  intro i _
  cases H i <;> simp only [Option.elim_none, Option.elim_some] <;> positivity

lemma boxMeasureOn_eq_fixed [Fintype ι] [DecidableEq ι] (I : Finset ι) (H : Box q) :
    boxMeasureOn I H = ∏ i ∈ I ∩ fixed H, (1 / (q i : ℝ)) := by
  have hinter : I ∩ fixed H = I.filter (fun i => i ∈ fixed H) := by ext i; simp
  rw [hinter, prod_filter]
  apply prod_congr rfl
  intro i _
  cases hi : H i with
  | none =>
    have hn : i ∉ fixed H := by simp [mem_fixed, hi]
    simp only [Option.elim_none, if_neg hn]
  | some v =>
    have hm : i ∈ fixed H := mem_fixed.mpr ⟨v, hi⟩
    simp only [Option.elim_some, if_pos hm]

lemma finiteProbability_boxEvent [Fintype ι] [DecidableEq ι]
    (H : Box q) (hq : ∀ i, 0 < q i) :
    finiteProbability (boxEvent H) = boxMeasureOn univ H := by
  rw [finiteProbability, boxEvent_card]
  change ((∏ i, (H i).elim (q i) (fun _ => 1) : ℕ) : ℝ) /
    (Fintype.card ((i : ι) → Fin (q i)) : ℝ) = _
  rw [Fintype.card_pi, Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
  apply prod_congr rfl
  intro i _
  have hqi : (q i : ℝ) ≠ 0 := by exact_mod_cast (hq i).ne'
  cases H i <;> simp [hqi]

lemma finiteProbability_boxEvent_eq_fixed [Fintype ι] [DecidableEq ι]
    (H : Box q) (hq : ∀ i, 0 < q i) :
    finiteProbability (boxEvent H) = ∏ i ∈ fixed H, (1 / (q i : ℝ)) := by
  rw [finiteProbability_boxEvent H hq, boxMeasureOn_eq_fixed, univ_inter]

lemma boxMeasureOn_erase [Fintype ι] [DecidableEq ι] {H : Box q} {I : Finset ι} {i : ι}
    (hi : i ∈ I) (hfixed : i ∈ fixed H) :
    boxMeasureOn I H = (1 / (q i : ℝ)) * boxMeasureOn (I.erase i) H := by
  obtain ⟨v, hv⟩ := mem_fixed.mp hfixed
  have h := mul_prod_erase I (fun j => (H j).elim (1 : ℝ) (fun _ => 1 / (q j : ℝ))) hi
  simpa only [hv, Option.elim_some, boxMeasureOn] using h.symm

end Erdos1189.Grid

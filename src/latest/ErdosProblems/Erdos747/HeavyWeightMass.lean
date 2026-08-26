import ErdosProblems.Erdos747.Core

open scoped BigOperators

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Total atypical weight and an adjustable heavy cutoff

The exact weight-average identity turns a bound on the number of atypical
edges into a bound on their total weight.  Raising the heavy cutoff then
divides the exceptional cardinality by the cutoff factor, as required by
Kahn's thinning parameter hierarchy.
-/

lemma finset_atypical_weight_sum_le {α : Type*}
    (s : Finset α) (W : α → ℝ) (w delta eta : ℝ)
    (hw : 0 ≤ w) (hdelta : 0 ≤ delta)
    (hsum : ∑ x ∈ s, W x = (s.card : ℝ) * w)
    (hspread :
      ((s.filter fun x ↦ ¬ |W x - w| ≤ delta * w).card : ℝ) ≤
        eta * s.card) :
    ∑ x ∈ s.filter (fun x ↦ ¬ |W x - w| ≤ delta * w), W x ≤
      (delta + eta) * s.card * w := by
  let P : α → Prop := fun x ↦ |W x - w| ≤ delta * w
  let G := s.filter P
  let B := s.filter fun x ↦ ¬ P x
  have hcard : (G.card : ℝ) + B.card = s.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := s) P)
  have hsplit : (∑ x ∈ G, W x) + (∑ x ∈ B, W x) =
      (s.card : ℝ) * w := by
    exact (Finset.sum_filter_add_sum_filter_not s P W).trans hsum
  have hgood : (G.card : ℝ) * ((1 - delta) * w) ≤
      ∑ x ∈ G, W x := by
    calc
      (G.card : ℝ) * ((1 - delta) * w) =
          ∑ _x ∈ G, (1 - delta) * w := by simp
      _ ≤ ∑ x ∈ G, W x := by
        apply Finset.sum_le_sum
        intro x hx
        have hclose : |W x - w| ≤ delta * w :=
          (Finset.mem_filter.mp hx).2
        have hlower := (abs_le.mp hclose).1
        linarith
  have hbadW : (B.card : ℝ) * w ≤ (eta * s.card) * w :=
    mul_le_mul_of_nonneg_right hspread hw
  have hnonneg : 0 ≤ delta * (B.card : ℝ) * w := by positivity
  change (∑ x ∈ B, W x) ≤ _
  calc
    (∑ x ∈ B, W x) = (s.card : ℝ) * w - (∑ x ∈ G, W x) := by
      linarith [hsplit]
    _ ≤ (s.card : ℝ) * w - (G.card : ℝ) * ((1 - delta) * w) :=
      sub_le_sub_left hgood _
    _ = delta * s.card * w + (B.card : ℝ) * w -
        delta * (B.card : ℝ) * w := by
      rw [← hcard]
      ring
    _ ≤ delta * s.card * w + (B.card : ℝ) * w :=
      sub_le_self _ hnonneg
    _ ≤ delta * s.card * w + (eta * s.card) * w := by
      linarith [hbadW]
    _ = (delta + eta) * s.card * w := by ring

lemma finset_heavy_weight_sum_le {α : Type*}
    (s : Finset α) (W : α → ℝ) (w delta eta h : ℝ)
    (hw : 0 ≤ w) (hdelta : 0 ≤ delta)
    (hW : ∀ x ∈ s, 0 ≤ W x)
    (hsum : ∑ x ∈ s, W x = (s.card : ℝ) * w)
    (hspread :
      ((s.filter fun x ↦ ¬ |W x - w| ≤ delta * w).card : ℝ) ≤
        eta * s.card)
    (hh : 1 + delta ≤ h) :
    ∑ x ∈ s.filter (fun x ↦ h * w < W x), W x ≤
      (delta + eta) * s.card * w := by
  have hsub : s.filter (fun x ↦ h * w < W x) ⊆
      s.filter (fun x ↦ ¬ |W x - w| ≤ delta * w) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxs, hxheavy⟩
    refine Finset.mem_filter.mpr ⟨hxs, ?_⟩
    intro hclose
    have hupper := (abs_le.mp hclose).2
    have hscale := mul_le_mul_of_nonneg_right hh hw
    nlinarith
  calc
    ∑ x ∈ s.filter (fun x ↦ h * w < W x), W x ≤
        ∑ x ∈ s.filter (fun x ↦ ¬ |W x - w| ≤ delta * w), W x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro x hx hnot
      exact hW x (Finset.mem_filter.mp hx).1
    _ ≤ (delta + eta) * s.card * w :=
      finset_atypical_weight_sum_le s W w delta eta hw hdelta hsum hspread

lemma finset_heavy_card_mul_le {α : Type*}
    (s : Finset α) (W : α → ℝ) (w delta eta h : ℝ)
    (hw : 0 < w) (hdelta : 0 ≤ delta)
    (hW : ∀ x ∈ s, 0 ≤ W x)
    (hsum : ∑ x ∈ s, W x = (s.card : ℝ) * w)
    (hspread :
      ((s.filter fun x ↦ ¬ |W x - w| ≤ delta * w).card : ℝ) ≤
        eta * s.card)
    (hh : 1 + delta ≤ h) :
    ((s.filter fun x ↦ h * w < W x).card : ℝ) * h ≤
      (delta + eta) * s.card := by
  let B := s.filter fun x ↦ h * w < W x
  have hlow : (B.card : ℝ) * (h * w) ≤ ∑ x ∈ B, W x := by
    calc
      (B.card : ℝ) * (h * w) = ∑ _x ∈ B, h * w := by simp
      _ ≤ ∑ x ∈ B, W x := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_filter.mp hx).2.le
  have hmass := finset_heavy_weight_sum_le s W w delta eta h
    hw.le hdelta hW hsum hspread hh
  apply (mul_le_mul_iff_of_pos_right hw).mp
  change (B.card : ℝ) * h * w ≤ _
  calc
    (B.card : ℝ) * h * w = (B.card : ℝ) * (h * w) := by ring
    _ ≤ ∑ x ∈ B, W x := hlow
    _ ≤ (delta + eta) * s.card * w := hmass

lemma sum_completionWeight_eq_card_mul_target {n : ℕ}
    (H : Finset (Edge n)) :
    ∑ A ∈ H, (completionWeight H A : ℝ) =
      (H.card : ℝ) * matchingWeightTarget n H := by
  by_cases hH : H.card = 0
  · have hEmpty := Finset.card_eq_zero.mp hH
    simp [hEmpty]
  have hHR : (H.card : ℝ) ≠ 0 := by exact_mod_cast hH
  calc
    ∑ A ∈ H, (completionWeight H A : ℝ) =
        ∑ A ∈ H, (matchingWeight H A : ℝ) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [completionWeight_eq_matchingWeight_of_mem H hA]
    _ = ((perfectMatchings n H).card : ℝ) * n := by
      exact_mod_cast sum_matchingWeight n H
    _ = (H.card : ℝ) * matchingWeightTarget n H := by
      unfold matchingWeightTarget
      field_simp

lemma present_atypical_weight_sum_le {n : ℕ}
    (H : Finset (Edge n)) (delta eta : ℝ)
    (hdelta : 0 ≤ delta) (hspread : PresentWeightSpread H delta eta) :
    ∑ A ∈ H.filter (fun A ↦ ¬ CompletionWeightClose H delta A),
        (completionWeight H A : ℝ) ≤
      (delta + eta) * H.card * matchingWeightTarget n H := by
  exact finset_atypical_weight_sum_le H (fun A ↦ (completionWeight H A : ℝ))
    (matchingWeightTarget n H) delta eta
    (by unfold matchingWeightTarget; positivity) hdelta
    (sum_completionWeight_eq_card_mul_target H) hspread

lemma card_mul_matchingWeightTarget_eq {n : ℕ}
    (H : Finset (Edge n)) :
    (H.card : ℝ) * matchingWeightTarget n H =
      ((perfectMatchings n H).card : ℝ) * n := by
  calc
    (H.card : ℝ) * matchingWeightTarget n H =
        ∑ A ∈ H, (completionWeight H A : ℝ) :=
      (sum_completionWeight_eq_card_mul_target H).symm
    _ = ∑ A ∈ H, (matchingWeight H A : ℝ) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [completionWeight_eq_matchingWeight_of_mem H hA]
    _ = ((perfectMatchings n H).card : ℝ) * n := by
      exact_mod_cast sum_matchingWeight n H

end

end Erdos747

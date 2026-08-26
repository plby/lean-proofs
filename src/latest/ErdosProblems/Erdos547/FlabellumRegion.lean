import ErdosProblems.Erdos547.TwoTailBlocks
import ErdosProblems.Erdos547.IsolatedTailFinish

/-!
# Constructing the anchored pair from a flabellum region

The large tail budget is an integer, so the fully occupied tail is a genuine
finite set of exactly the required size.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

open scoped Classical in
theorem anchoredTotals_of_flabellum_region (w : EdgeWeights G) {c d : V} (hcd : G.Adj c d)
    (a₁ a₂ b₁ : ℝ) (m : ℕ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁)
    (hhalf : (a₁ + a₂ + b₁ + m) / 2 ≤ (m : ℝ))
    (C Z R W X : Finset V) (hCZ : C ⊆ Z) (hZR : Disjoint Z R) (hWR : W ⊆ R)
    (hX : Disjoint X (R ∪ C))
    (hW : (a₁ + a₂ + b₁ + m) / 2 ≤ (W.card : ℝ))
    (hsize : (m : ℝ) ≤ ((R ∪ X).card : ℝ))
    (hR : ∀ y ∈ R, b₁ ≤ w.degreeOn (C.filter (G.Adj y)) d)
    (hlargeX : ∀ y ∈ X, b₁ / 2 ≤ w.degreeOn (C.filter (G.Adj y)) d)
    (hno : ∀ y ∈ W, ∀ x, G.Adj x y → x ∈ Z)
    (hZ : w.degreeOn Z c ≤ b₁)
    (hhigh : a₁ + a₂ + b₁ + m ≤ w.degree c)
    (hdegree : ∀ x, (a₁ + a₂ + b₁ + m) / 2 ≤ w.degree x) :
    HasAnchoredTotals w (a₂ / a₁) ((m : ℝ) / b₁) (a₁ + a₂) (b₁ + m) := by
  classical
  have hm : 0 < (m : ℝ) := by linarith
  let γ := (m : ℝ) / b₁
  have hγ : 0 < γ := div_pos hm hb₁
  obtain ⟨Q, hQW, hQcard⟩ := Finset.exists_subset_card_eq (min_le_left W.card m)
  have hQlarge : (a₁ + a₂ + b₁ + m) / 2 ≤ (Q.card : ℝ) := by
    rw [hQcard, Nat.cast_min]
    exact le_min hW hhalf
  have hQm : (Q.card : ℝ) ≤ m := by
    rw [hQcard, Nat.cast_min]
    exact min_le_right _ _
  let P := X ∪ (R \ W)
  let p := (m : ℝ) - Q.card
  let q := (Q.card : ℝ)
  have hp : 0 ≤ p := sub_nonneg.mpr hQm
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have hpq : p + q = (m : ℝ) := by dsimp [p, q]; ring
  have hPQ : Disjoint P Q := Finset.disjoint_left.mpr fun u hu hv ↦ by
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Finset.disjoint_left.mp hX hu (Finset.mem_union_left _ (hWR (hQW hv)))
    · exact (Finset.mem_sdiff.mp hu).2 (hQW hv)
  have hCP : Disjoint C P := Finset.disjoint_left.mpr fun u hu hv ↦ by
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.disjoint_left.mp hX hv (Finset.mem_union_right _ hu)
    · exact Finset.disjoint_left.mp hZR (hCZ hu) (Finset.mem_sdiff.mp hv).1
  have hCQ : Disjoint C Q := Finset.disjoint_left.mpr fun u hu hv ↦
    Finset.disjoint_left.mp hZR (hCZ hu) (hWR (hQW hv))
  have hPsize : p ≤ (P.card : ℝ) := by
    by_cases hWm : W.card ≤ m
    · have heq : P ∪ W = R ∪ X := by
        ext u
        simp only [P, Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inr h
          · exact Or.inl h.1
          · exact Or.inl (hWR h)
        · rintro (h | h)
          · by_cases huW : u ∈ W
            · exact Or.inr huW
            · exact Or.inl (Or.inr ⟨h, huW⟩)
          · exact Or.inl (Or.inl h)
      have hPW : Disjoint P W := Finset.disjoint_left.mpr fun u hu hv ↦ by
        rcases Finset.mem_union.mp hu with hu | hu
        · exact Finset.disjoint_left.mp hX hu (Finset.mem_union_left _ (hWR hv))
        · exact (Finset.mem_sdiff.mp hu).2 hv
      have hcard : (P.card : ℝ) + W.card = ((R ∪ X).card : ℝ) := by
        exact_mod_cast (Finset.card_union_of_disjoint hPW).symm.trans (congrArg Finset.card heq)
      have hqW : (Q.card : ℝ) = (W.card : ℝ) := by rw [hQcard, min_eq_left hWm]
      dsimp [p]
      linarith
    · have hqM : Q.card = m := by rw [hQcard, min_eq_right (le_of_not_ge hWm)]
      simp only [p, hqM, sub_self]
      exact Nat.cast_nonneg _
  have hpHalf : p / γ ≤ b₁ / 2 := by
    have hpM : p ≤ (m : ℝ) / 2 := by dsimp [p]; linarith
    calc
      _ ≤ ((m : ℝ) / 2) / γ := div_le_div_of_nonneg_right hpM hγ.le
      _ = _ := by dsimp [γ]; field_simp
  have hpBound : γ * (p / γ) ≤ (P.card : ℝ) := by
    rw [mul_div_cancel₀ _ hγ.ne']
    exact hPsize
  have hqExact : γ * (q / γ) = (Q.card : ℝ) := by
    rw [mul_div_cancel₀ _ hγ.ne']
  have hfirst : ∀ y ∈ P, p / γ ≤ w.degreeOn (C.filter (G.Adj y)) d := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hpHalf.trans (hlargeX y hy)
    · exact hpHalf.trans ((by linarith : b₁ / 2 ≤ b₁).trans (hR y (Finset.mem_sdiff.mp hy).1))
  have hsum : p / γ + q / γ = b₁ := by
    rw [← add_div, hpq]
    dsimp [γ]
    field_simp
  have hsecond : ∀ y ∈ Q, p / γ + q / γ ≤ w.degreeOn (C.filter (G.Adj y)) d := by
    intro y hy
    rw [hsum]
    exact hR y (hWR (hQW hy))
  obtain ⟨β, hfitβ, htβ, hheadβ, hloadβ⟩ := exists_skew_two_tail_blocks w hcd γ hγ C P Q
    hCP hCQ hPQ (p / γ) (q / γ) (div_nonneg hp hγ.le) (div_nonneg hq hγ.le)
    hpBound hqExact hfirst hsecond
  have htotal : β.total = b₁ + m := by
    rw [htβ, hsum]
    dsimp [γ]
    field_simp
  apply finish_from_isolated_tail w hcd a₁ a₂ b₁ m ha₁ ha₂ hb₁ (Nat.cast_nonneg _) β
    hfitβ htotal Z Q
  · exact hZR.mono_right (hQW.trans hWR)
  · exact fun u hu ↦ hheadβ u (fun h ↦ hu (hCZ h))
  · exact hloadβ
  · exact hQlarge
  · exact fun y hy x hxy ↦ hno y (hQW hy) x hxy
  · exact hZ
  · exact hhigh
  · exact hdegree

end Erdos547.DPRS

#print axioms Erdos547.DPRS.anchoredTotals_of_flabellum_region

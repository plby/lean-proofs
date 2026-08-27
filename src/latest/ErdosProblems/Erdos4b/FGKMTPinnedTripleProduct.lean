/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedSurvivalProduct

/-! # The exact three-set correction in the pinned second moment -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

variable {α : Type*} [DecidableEq α]

def pinnedTripleRatio (P : α → ℝ) (e A B : Finset α) (v : α) : ℝ :=
  P v ^ 2 * survivalProduct P (e ∪ A ∪ B) /
    (survivalProduct P e * survivalProduct P A * survivalProduct P B)

def tripleExtraIndicator (e A B : Finset α) (v : α) : ℝ :=
  (if (e.erase v ∩ A).Nonempty then 1 else 0) +
    (if (e.erase v ∩ B).Nonempty then 1 else 0) +
    (if (A.erase v ∩ B).Nonempty then 1 else 0)

theorem pinnedTripleRatio_factor {P : α → ℝ} {V e A B : Finset α} {v : α}
    (hP : ∀ u ∈ V, 0 < P u) (he : e ⊆ V) (hA : A ⊆ V) (hB : B ⊆ V)
    (hve : v ∈ e) (hvA : v ∈ A) (hvB : v ∈ B) :
    pinnedTripleRatio P e A B v =
      1 / (survivalProduct P (A ∩ e.erase v) *
        survivalProduct P (B ∩ (e ∪ A).erase v)) := by
  have hU : e ∪ A ⊆ V := Finset.union_subset he hA
  have hPe := survivalProduct_pos (fun u hu => hP u (he hu))
  have hPA := survivalProduct_pos (fun u hu => hP u (hA hu))
  have hPB := survivalProduct_pos (fun u hu => hP u (hB hu))
  have hPU := survivalProduct_pos (fun u hu => hP u (hU hu))
  have hPv := hP v (he hve)
  have hT1 := survivalProduct_pos (A := A ∩ e.erase v)
    (fun u hu => hP u (hA (Finset.mem_inter.mp hu).1))
  have hT2 := survivalProduct_pos (A := B ∩ (e ∪ A).erase v)
    (fun u hu => hP u (hB (Finset.mem_inter.mp hu).1))
  have hfirst := survivalProduct_pinned_union_ratio hP hA he hvA hve
  have hsecond := survivalProduct_pinned_union_ratio hP hB hU hvB
    (Finset.mem_union_left A hve)
  calc
    _ = P v ^ 2 *
        (survivalProduct P (e ∪ A) / (survivalProduct P e * survivalProduct P A)) *
        (survivalProduct P (e ∪ A ∪ B) /
          (survivalProduct P (e ∪ A) * survivalProduct P B)) := by
      unfold pinnedTripleRatio
      field_simp [hPe.ne', hPA.ne', hPB.ne', hPU.ne']
    _ = _ := by
      rw [hfirst, hsecond]
      field_simp [hPv.ne', hT1.ne', hT2.ne']

theorem pinnedTripleRatio_bounds {P : α → ℝ} {V e A B : Finset α} {v : α}
    {κ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ V, κ ≤ P u) (hP1 : ∀ u ∈ V, P u ≤ 1)
    (he : e ⊆ V) (hA : A ⊆ V) (hB : B ⊆ V)
    (hAc : A.card ≤ r) (hBc : B.card ≤ r) (hve : v ∈ e) (hvA : v ∈ A) (hvB : v ∈ B) :
    1 ≤ pinnedTripleRatio P e A B v ∧ pinnedTripleRatio P e A B v ≤ 1 / κ ^ (2 * r) := by
  have hpos : ∀ u ∈ V, 0 < P u := fun u hu => hκ0.trans_le (hP0 u hu)
  have hT1V : A ∩ e.erase v ⊆ V := fun u hu => hA (Finset.mem_inter.mp hu).1
  have hT2V : B ∩ (e ∪ A).erase v ⊆ V := fun u hu => hB (Finset.mem_inter.mp hu).1
  have hp1 := survivalProduct_pos (fun u hu => hpos u (hT1V hu))
  have hp2 := survivalProduct_pos (fun u hu => hpos u (hT2V hu))
  have hlo1 := survivalProduct_ge_pow hκ0.le hκ1 (fun u hu => hP0 u (hT1V hu))
    ((Finset.card_le_card Finset.inter_subset_left).trans hAc)
  have hlo2 := survivalProduct_ge_pow hκ0.le hκ1 (fun u hu => hP0 u (hT2V hu))
    ((Finset.card_le_card Finset.inter_subset_left).trans hBc)
  have hhi1 := survivalProduct_le_one (fun u hu => (hpos u (hT1V hu)).le)
    (fun u hu => hP1 u (hT1V hu))
  have hhi2 := survivalProduct_le_one (fun u hu => (hpos u (hT2V hu)).le)
    (fun u hu => hP1 u (hT2V hu))
  rw [pinnedTripleRatio_factor hpos he hA hB hve hvA hvB]
  constructor
  · apply (le_div_iff₀ (mul_pos hp1 hp2)).mpr
    simpa only [one_mul] using mul_le_mul hhi1 hhi2 hp2.le (by norm_num : (0 : ℝ) ≤ 1)
  · apply one_div_le_one_div_of_le (pow_pos hκ0 (2 * r))
    rw [two_mul, pow_add]
    exact mul_le_mul hlo1 hlo2 (pow_pos hκ0 r).le hp1.le

theorem pinnedTripleRatio_eq_one_of_no_extra {P : α → ℝ} {V e A B : Finset α} {v : α}
    (hP : ∀ u ∈ V, 0 < P u) (he : e ⊆ V) (hA : A ⊆ V) (hB : B ⊆ V)
    (hve : v ∈ e) (hvA : v ∈ A) (hvB : v ∈ B)
    (h1 : ¬ (e.erase v ∩ A).Nonempty) (h2 : ¬ (e.erase v ∩ B).Nonempty)
    (h3 : ¬ (A.erase v ∩ B).Nonempty) : pinnedTripleRatio P e A B v = 1 := by
  have hT1 : A ∩ e.erase v = ∅ := by
    rw [Finset.inter_comm]
    exact Finset.not_nonempty_iff_eq_empty.mp h1
  have hT2 : B ∩ (e ∪ A).erase v = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨u, hu⟩
    have huB := (Finset.mem_inter.mp hu).1
    have huU := Finset.mem_erase.mp (Finset.mem_inter.mp hu).2
    rcases Finset.mem_union.mp huU.2 with hue | huA
    · exact h2 ⟨u, Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨huU.1, hue⟩, huB⟩⟩
    · exact h3 ⟨u, Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨huU.1, huA⟩, huB⟩⟩
  rw [pinnedTripleRatio_factor hP he hA hB hve hvA hvB, hT1, hT2]
  simp [survivalProduct]

theorem pinnedTripleRatio_error {P : α → ℝ} {V e A B : Finset α} {v : α}
    {κ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ V, κ ≤ P u) (hP1 : ∀ u ∈ V, P u ≤ 1)
    (he : e ⊆ V) (hA : A ⊆ V) (hB : B ⊆ V)
    (hAc : A.card ≤ r) (hBc : B.card ≤ r) (hve : v ∈ e) (hvA : v ∈ A) (hvB : v ∈ B) :
    |pinnedTripleRatio P e A B v - 1| ≤ (1 / κ ^ (2 * r)) * tripleExtraIndicator e A B v := by
  obtain ⟨hlo, hhi⟩ := pinnedTripleRatio_bounds hκ0 hκ1 hP0 hP1 he hA hB hAc hBc hve hvA hvB
  rw [abs_of_nonneg (by linarith : 0 ≤ pinnedTripleRatio P e A B v - 1)]
  have hcoef : 0 ≤ 1 / κ ^ (2 * r) := by positivity
  by_cases h1 : (e.erase v ∩ A).Nonempty <;>
    by_cases h2 : (e.erase v ∩ B).Nonempty <;>
    by_cases h3 : (A.erase v ∩ B).Nonempty
  all_goals simp only [tripleExtraIndicator, h1, h2, h3, if_true, if_false]
  all_goals try linarith
  rw [pinnedTripleRatio_eq_one_of_no_extra
    (fun u hu => hκ0.trans_le (hP0 u hu)) he hA hB hve hvA hvB h1 h2 h3]
  norm_num

end

end Erdos4b.FGKMT.FiniteEdgeFamily

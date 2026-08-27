/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSurvivalProduct

/-! # Factoring the survival correction at a common pinned vertex -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

variable {α : Type*} [DecidableEq α]

theorem survivalProduct_inter_pin (P : α → ℝ) {A e : Finset α} {v : α}
    (hA : v ∈ A) (he : v ∈ e) :
    survivalProduct P (A ∩ e) = P v * survivalProduct P (A ∩ e.erase v) := by
  have hset : (A ∩ e).erase v = A ∩ e.erase v := by
    ext u
    simp only [Finset.mem_erase, Finset.mem_inter]
    tauto
  have h := Finset.mul_prod_erase (A ∩ e) P (Finset.mem_inter.mpr ⟨hA, he⟩)
  simpa only [hset, survivalProduct] using h.symm

theorem survivalProduct_pinned_union_ratio {P : α → ℝ} {V A e : Finset α} {v : α}
    (hP : ∀ u ∈ V, 0 < P u) (hA : A ⊆ V) (he : e ⊆ V)
    (hvA : v ∈ A) (hve : v ∈ e) :
    survivalProduct P (e ∪ A) / (survivalProduct P e * survivalProduct P A) =
      (1 / P v) * (1 / survivalProduct P (A ∩ e.erase v)) := by
  rw [survivalProduct_union_ratio hP he hA, Finset.inter_comm e A,
    survivalProduct_inter_pin P hvA hve]
  ring

theorem survivalProduct_pinned_ratio_error {P : α → ℝ} {V A e : Finset α}
    {v : α} {κ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ u ∈ V, κ ≤ P u) (hP1 : ∀ u ∈ V, P u ≤ 1)
    (hA : A ⊆ V) (he : e ⊆ V) (hcard : A.card ≤ r) (hvA : v ∈ A) (hve : v ∈ e) :
    |survivalProduct P (e ∪ A) / (survivalProduct P e * survivalProduct P A) - 1 / P v| ≤
      (1 / P v) * (1 / κ ^ r) *
        (if (e.erase v ∩ A).Nonempty then 1 else 0) := by
  have hpos : ∀ u ∈ V, 0 < P u := fun u hu => hκ0.trans_le (hP0 u hu)
  have hvpos := hpos v (hA hvA)
  rw [survivalProduct_pinned_union_ratio hpos hA he hvA hve]
  by_cases hhit : (e.erase v ∩ A).Nonempty
  · rw [if_pos hhit, mul_one]
    have hhit' : (A ∩ e.erase v).Nonempty := by
      simpa only [Finset.inter_comm] using hhit
    have hlo : 1 ≤ 1 / survivalProduct P (A ∩ e.erase v) := by
      have hp := survivalProduct_pos (A := A ∩ e.erase v)
        (fun u hu => hpos u (hA (Finset.mem_inter.mp hu).1))
      apply (le_div_iff₀ hp).mpr
      simpa only [one_mul] using survivalProduct_le_one
        (fun u hu => (hpos u (hA (Finset.mem_inter.mp hu).1)).le)
        (fun u hu => hP1 u (hA (Finset.mem_inter.mp hu).1))
    have hhi := survivalProduct_inter_inv_le (B := e.erase v) hκ0 hκ1 hP0 hA hcard
    rw [if_pos hhit'] at hhi
    have hdiff : 0 ≤ (1 / P v) * (1 / survivalProduct P (A ∩ e.erase v)) - 1 / P v := by
      nlinarith [mul_le_mul_of_nonneg_left hlo (one_div_nonneg.mpr hvpos.le)]
    rw [abs_of_nonneg hdiff]
    nlinarith [mul_le_mul_of_nonneg_left hhi (one_div_nonneg.mpr hvpos.le)]
  · have hzero : A ∩ e.erase v = ∅ := by
      rw [Finset.inter_comm]
      exact Finset.not_nonempty_iff_eq_empty.mp hhit
    rw [if_neg hhit, hzero]
    simp [survivalProduct]

end

end Erdos4b.FGKMT.FiniteEdgeFamily

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFiniteEdgeFamily

/-! # Explicit independent edge copies and their intersection probability -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def hitMass (F : FiniteEdgeFamily I Ω α) (i : I) (A : Finset α) : ℝ :=
  ∑ w, if (A ∩ F.edge i w).Nonempty then F.mass i w else 0

def independentIntersectionMass (F : FiniteEdgeFamily I Ω α) (i j : I) : ℝ :=
  ∑ w, F.mass i w * F.hitMass j (F.edge i w)

theorem hitMass_le_sum_vertexMass (F : FiniteEdgeFamily I Ω α) (i : I) (A : Finset α) :
    F.hitMass i A ≤ ∑ v ∈ A, F.vertexMass i v := by
  classical
  calc
    _ ≤ ∑ w, ∑ v ∈ A, if v ∈ F.edge i w then F.mass i w else 0 := by
      apply Finset.sum_le_sum
      intro w _hw
      have hnonneg (v : α) : 0 ≤ (if v ∈ F.edge i w then F.mass i w else 0) := by
        split_ifs
        · exact F.mass_nonneg i w
        · exact le_rfl
      by_cases h : (A ∩ F.edge i w).Nonempty
      · rw [if_pos h]
        obtain ⟨v, hv⟩ := h
        have hvA := (Finset.mem_inter.mp hv).1
        have hvE := (Finset.mem_inter.mp hv).2
        have hle := Finset.single_le_sum (s := A)
          (f := fun v : α => if v ∈ F.edge i w then F.mass i w else 0) (a := v)
          (fun v _hv => hnonneg v) hvA
        simpa only [if_pos hvE] using hle
      · rw [if_neg h]
        exact Finset.sum_nonneg fun v _hv => hnonneg v
    _ = _ := Finset.sum_comm

theorem hitMass_le_card_mul (F : FiniteEdgeFamily I Ω α) (i : I) (A : Finset α)
    {b : ℝ} (hcap : ∀ v ∈ A, F.vertexMass i v ≤ b) : F.hitMass i A ≤ (A.card : ℝ) * b := by
  calc
    _ ≤ ∑ v ∈ A, F.vertexMass i v := F.hitMass_le_sum_vertexMass i A
    _ ≤ ∑ _v ∈ A, b := Finset.sum_le_sum hcap
    _ = _ := by simp

theorem independent_pair_mass_sum (F : FiniteEdgeFamily I Ω α) (i j : I) :
    (∑ w, ∑ z, F.mass i w * F.mass j z) = 1 := by
  simp only [← Finset.mul_sum, F.mass_sum_one, mul_one]

theorem independentIntersectionMass_eq (F : FiniteEdgeFamily I Ω α) (i j : I) :
    F.independentIntersectionMass i j =
      ∑ w, ∑ z, if (F.edge i w ∩ F.edge j z).Nonempty
        then F.mass i w * F.mass j z else 0 := by
  simp only [independentIntersectionMass, hitMass, Finset.mul_sum, mul_ite, mul_zero]

theorem independentIntersectionMass_le_rank_mul (F : FiniteEdgeFamily I Ω α)
    (i j : I) {b : ℝ} (hb : 0 ≤ b) (hcap : ∀ v ∈ F.vertices, F.vertexMass j v ≤ b) :
    F.independentIntersectionMass i j ≤ (F.rank : ℝ) * b := by
  have hhit (w : Ω) : F.hitMass j (F.edge i w) ≤ (F.rank : ℝ) * b := by
    calc
      _ ≤ ((F.edge i w).card : ℝ) * b :=
        F.hitMass_le_card_mul j (F.edge i w) (fun v hv => hcap v (F.edge_subset i w hv))
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast F.edge_card_le i w) hb
  calc
    _ ≤ ∑ w, F.mass i w * ((F.rank : ℝ) * b) :=
      Finset.sum_le_sum fun w _hw => mul_le_mul_of_nonneg_left (hhit w) (F.mass_nonneg i w)
    _ = _ := by rw [← Finset.sum_mul, F.mass_sum_one, one_mul]

end

end Erdos4b.FGKMT.FiniteEdgeFamily

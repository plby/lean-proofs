import Arxiv.Arxiv2411_18291.SignedCliqueSlots
import Arxiv.Arxiv2411_18291.RepeatedCliqueRoots

/-! # Signed slots with a separate capacity for every clique

The root degrees count the actual capacities. Neither the boundary identity
nor the degree and overlap bounds use the maximum capacity or a uniform
edge-multiplicity bound.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def cliqueCapacityDegree (D : Finset (Block V q)) (C : Block V q → ℕ) (S : Finset V) : ℕ :=
  ∑ Q ∈ D.filter (fun Q => S ⊆ Q.val), C Q

def IsCliqueCapacityBounded (r : ℕ) (D : Finset (Block V q))
    (C : Block V q → ℕ) (θ : ℝ) : Prop :=
  ∀ S : Block V r, (cliqueCapacityDegree D C S.val : ℝ) < θ * Fintype.card V

theorem IsCliqueCapacityBounded.mono {D : Finset (Block V q)} {C : Block V q → ℕ}
    {θ θ' : ℝ} (hD : IsCliqueCapacityBounded r D C θ) (hθ : θ ≤ θ') :
    IsCliqueCapacityBounded r D C θ' := by
  intro S
  exact (hD S).trans_le (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _))

abbrev VariableCliqueSlots (D : Finset (Block V q)) (C : Block V q → ℕ) :=
  Σ P : D, Bool × Fin (C P.val)

omit [Fintype V] in
theorem variableCliqueSlots_degree (D : Finset (Block V q)) (C : Block V q → ℕ)
    (S : Finset V) :
    familyDegree (fun s : VariableCliqueSlots D C => s.1.val) S =
      2 * cliqueCapacityDegree D C S := by
  classical
  rw [familyDegree, card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  have hinner (P : D) :
      (∑ _s : Bool × Fin (C P.val), if S ⊆ P.val.val then 1 else 0) =
        if S ⊆ P.val.val then 2 * C P.val else 0 := by
    by_cases hS : S ⊆ P.val.val <;> simp [hS]
  simp only [hinner]
  rw [Finset.sum_coe_sort D (fun P => if S ⊆ P.val then 2 * C P else 0)]
  simp only [cliqueCapacityDegree, sum_filter, mul_sum, mul_ite, mul_zero]

theorem variableCliqueSlots_boundary (D : Finset (Block V q)) (C : Block V q → ℕ)
    (Φ : Block V q → ℤ) (hΦ : ∀ P, |Φ P| ≤ C P) (hs : ∀ P, P ∉ D → Φ P = 0) :
    (∑ s : VariableCliqueSlots D C, fun e =>
      signedSlotWeight (Φ s.1.val) s.2 * indicator (cliqueEdges r s.1.val) e) =
        boundary r Φ := by
  funext e
  rw [Finset.sum_apply, Fintype.sum_sigma]
  calc
    _ = ∑ P : D, Φ P.val * indicator (cliqueEdges r P.val) e := by
      apply sum_congr rfl
      intro P _
      dsimp only
      rw [← sum_mul, sum_signedSlotWeight _ (hΦ P.val)]
    _ = _ := by
      rw [Finset.sum_coe_sort D (fun P => Φ P * indicator (cliqueEdges r P) e),
        boundary_eq_sum_supported D Φ hs e, sum_filter]
      apply sum_congr rfl
      intro P _
      simp only [indicator, mem_cliqueEdges]
      split_ifs <;> simp only [mul_one, mul_zero]

theorem IsCliqueFamilyBounded.constant_capacity (hqr : r + 1 ≤ q)
    {D : Finset (Block V q)} {θ : ℝ} (hD : IsCliqueFamilyBounded r D θ)
    {C : ℕ} (hC : 0 < C) : IsCliqueCapacityBounded r D (fun _ => C) (C * θ) := by
  intro S
  have hdegree : ((D.filter fun P => S.val ⊆ P.val).card : ℝ) ≤
      ((degree (boundary (r + 1) (indicator D)) S.val : ℤ) : ℝ) := by
    exact_mod_cast face_clique_count_le_boundary_degree hqr D S
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hh := mul_lt_mul_of_pos_left (hdegree.trans_lt (hD S)) hCpos
  simpa only [cliqueCapacityDegree, sum_const, nsmul_eq_mul, Nat.cast_mul, Nat.cast_id,
    mul_comm, mul_left_comm, mul_assoc] using hh

theorem IsCliqueCapacityBounded.variable_edgeFamily
    {D : Finset (Block V q)} {C : Block V q → ℕ} {θ : ℝ}
    (hD : IsCliqueCapacityBounded r D C θ)
    (E : VariableCliqueSlots D C → Block V (r + 1))
    (hE : ∀ s, (E s).val ⊆ s.1.val.val) : IsEdgeFamilyBounded E (2 * θ) := by
  intro S
  have hsub : familyDegree E S.val ≤
      familyDegree (fun s : VariableCliqueSlots D C => s.1.val) S.val := by
    apply card_le_card
    intro s hs
    exact mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp hs).2).trans (hE s)⟩
  rw [variableCliqueSlots_degree] at hsub
  have hcount : (familyDegree E S.val : ℝ) ≤ 2 * cliqueCapacityDegree D C S.val := by
    exact_mod_cast hsub
  have hh := mul_lt_mul_of_pos_left (hD S) (by norm_num : (0 : ℝ) < 2)
  exact hcount.trans_lt (by simpa only [mul_assoc] using hh)

theorem IsCliqueCapacityBounded.variable_overlap_le
    {D : Finset (Block V q)} {C : Block V q → ℕ} {θ : ℝ}
    (hD : IsCliqueCapacityBounded r D C θ) (P : Block V q) :
    ((cliqueOverlapIndices (r + 1)
      (fun s : VariableCliqueSlots D C => s.1.val) P).card : ℝ) ≤
        q.choose r * (2 * θ * Fintype.card V) := by
  classical
  let Q : VariableCliqueSlots D C → Block V q := fun s => s.1.val
  have hsub : cliqueOverlapIndices (r + 1) Q P ⊆
      (cliqueEdges r P).biUnion (fun S => univ.filter fun s => S.val ⊆ (Q s).val) := by
    intro s hs
    have hsize := (mem_filter.mp hs).2
    obtain ⟨T, hT, hTr⟩ := exists_subset_card_eq
      (show r ≤ ((Q s).val ∩ P.val).card by omega)
    exact mem_biUnion.mpr ⟨⟨T, hTr⟩, (mem_cliqueEdges _ _).mpr (hT.trans inter_subset_right),
      mem_filter.mpr ⟨mem_univ _, hT.trans inter_subset_left⟩⟩
  calc
    _ ≤ ∑ S ∈ cliqueEdges r P, (familyDegree Q S.val : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _S ∈ cliqueEdges r P, 2 * θ * Fintype.card V := by
      apply sum_le_sum
      intro S _
      have hh := mul_lt_mul_of_pos_left (hD S) (by norm_num : (0 : ℝ) < 2)
      simpa only [Q, variableCliqueSlots_degree, Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
        using hh.le
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_cliqueEdges]

end Arxiv2411_18291

import ErdosProblems.Erdos547.RegularityTypical

/-!
# Many vertices are typical to most members of a finite family
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V I : Type*}

open scoped Classical in
theorem sum_incidence_counts (P : V → I → Prop) [∀ v i, Decidable (P v i)]
    (S : Finset V) (J : Finset I) :
    (∑ u ∈ S, (J.filter (P u)).card) = ∑ i ∈ J, (S.filter (fun u ↦ P u i)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

open scoped Classical in
theorem card_many_incidents_le (P : V → I → Prop) [∀ v i, Decidable (P v i)]
    (S : Finset V) (J : Finset I)
    (ε δ : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (hcol : ∀ i ∈ J, ((S.filter (fun u ↦ P u i)).card : ℝ) ≤ ε * S.card) :
    ((S.filter (fun u ↦ δ * J.card < ((J.filter (P u)).card : ℝ))).card : ℝ) ≤
      δ * S.card := by
  classical
  by_cases hJ : J.Nonempty
  · let B := S.filter (fun u ↦ δ * J.card < ((J.filter (P u)).card : ℝ))
    have hJpos : 0 < (J.card : ℝ) := by exact_mod_cast hJ.card_pos
    have hsum : (∑ u ∈ S, ((J.filter (P u)).card : ℝ)) ≤ (J.card : ℝ) * (ε * S.card) := by
      calc
        _ = ∑ i ∈ J, ((S.filter (fun u ↦ P u i)).card : ℝ) := by
          exact_mod_cast sum_incidence_counts P S J
        _ ≤ ∑ _i ∈ J, ε * S.card := Finset.sum_le_sum hcol
        _ = _ := by simp
    have hlow : (B.card : ℝ) * (δ * J.card) ≤
        ∑ u ∈ S, ((J.filter (P u)).card : ℝ) := by
      calc
        _ = ∑ _u ∈ B, δ * J.card := by simp
        _ ≤ ∑ u ∈ B, ((J.filter (P u)).card : ℝ) :=
          Finset.sum_le_sum fun u hu ↦ (Finset.mem_filter.mp hu).2.le
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun u _ _ ↦ Nat.cast_nonneg _)
    have hprod : ((B.card : ℝ) * δ) * J.card ≤ (ε * S.card) * J.card := by
      nlinarith only [hlow, hsum]
    have hbound : (B.card : ℝ) * δ ≤ ε * S.card :=
      (mul_le_mul_iff_of_pos_right hJpos).mp hprod
    apply (mul_le_mul_iff_of_pos_right hδ).mp
    calc
      (B.card : ℝ) * δ ≤ ε * S.card := hbound
      _ ≤ δ ^ 2 * S.card := mul_le_mul_of_nonneg_right hεδ (Nat.cast_nonneg _)
      _ = (δ * S.card) * δ := by ring
  · have hJe : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    simp only [hJe, Finset.card_empty, Nat.cast_zero, mul_zero, Finset.filter_empty,
      lt_self_iff_false, Finset.filter_false]
    exact mul_nonneg hδ.le (Nat.cast_nonneg _)

open scoped Classical in
theorem card_many_nonTypical_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (J : Finset I) (T B : I → Finset V) (ε δ : ℝ)
    (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (hreg : ∀ i ∈ J, G.IsUniform ε S (T i))
    (hB : ∀ i ∈ J, B i ⊆ T i)
    (hsize : ∀ i ∈ J, ((T i).card : ℝ) * ε ≤ (B i).card) :
    ((S.filter (fun u ↦ δ * J.card < ((J.filter (fun i ↦
      (degreeIn G (B i) u : ℝ) <
        ((G.edgeDensity S (T i) : ℝ) - ε) * (B i).card)).card : ℝ))).card : ℝ)
      ≤ δ * S.card := by
  classical
  apply card_many_incidents_le _ S J ε δ hδ hεδ
  intro i hi
  simpa only [mul_comm ε] using card_nonTypical_le G (hreg i hi) (hB i hi) (hsize i hi)

end Erdos547

#print axioms Erdos547.card_many_nonTypical_le

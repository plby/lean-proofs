import ErdosProblems.Erdos547.RegularityManyTypical
import ErdosProblems.Erdos547.RegularityPruning

/-!
# Seed pools typical to the partner cluster and to two external families
-/

noncomputable section

namespace Erdos547

open Finset SimpleGraph

variable {V I : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def nonTypicalPartners (ε : ℝ) (X : Finset V) (J : Finset I)
    (C B : I → Finset V) (v : V) : Finset I :=
  J.filter (fun i ↦ (degreeIn G (B i) v : ℝ) <
    ((G.edgeDensity X (C i) : ℝ) - ε) * (B i).card)

def manyNonTypicalVertices (ε δ : ℝ) (X : Finset V) (J : Finset I)
    (C B : I → Finset V) : Finset V :=
  X.filter (fun v ↦ δ * J.card < ((nonTypicalPartners G ε X J C B v).card : ℝ))

theorem card_manyNonTypicalVertices_le (ε δ : ℝ) (X : Finset V) (J : Finset I)
    (C B : I → Finset V) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (hreg : ∀ i ∈ J, G.IsUniform ε X (C i))
    (hB : ∀ i ∈ J, B i ⊆ C i)
    (hsize : ∀ i ∈ J, ((C i).card : ℝ) * ε ≤ (B i).card) :
    ((manyNonTypicalVertices G ε δ X J C B).card : ℝ) ≤ δ * X.card := by
  exact card_many_nonTypical_le G X J C B ε δ hδ hεδ hreg hB hsize

theorem exists_seed_typical_pool {ε δ : ℝ} (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (hεone : ε ≤ 1) (X Y : Finset V) (hXY : G.IsUniform ε X Y)
    (J : Finset I) (C B Q : I → Finset V)
    (hreg : ∀ i ∈ J, G.IsUniform ε X (C i))
    (hB : ∀ i ∈ J, B i ⊆ C i) (hQ : ∀ i ∈ J, Q i ⊆ C i)
    (hBsize : ∀ i ∈ J, ((C i).card : ℝ) * ε ≤ (B i).card)
    (hQsize : ∀ i ∈ J, ((C i).card : ℝ) * ε ≤ (Q i).card) :
    ∃ P : Finset V, P ⊆ X ∧ ((X \ P).card : ℝ) ≤ (ε + 2 * δ) * X.card ∧
      ∀ v ∈ P,
        ((G.edgeDensity X Y : ℝ) - ε) * Y.card ≤ (degreeIn G Y v : ℝ) ∧
        ((nonTypicalPartners G ε X J C B v).card : ℝ) ≤ δ * J.card ∧
        ((nonTypicalPartners G ε X J C Q v).card : ℝ) ≤ δ * J.card := by
  classical
  let bad₀ := nonTypicalVertices G ε X Y Y
  let bad₁ := manyNonTypicalVertices G ε δ X J C B
  let bad₂ := manyNonTypicalVertices G ε δ X J C Q
  let bad := (bad₀ ∪ bad₁) ∪ bad₂
  let P := X \ bad
  have hbad₀ : (bad₀.card : ℝ) ≤ ε * X.card := by
    have hh := card_nonTypical_le G hXY (Finset.Subset.refl Y)
      (show (Y.card : ℝ) * ε ≤ Y.card by
        simpa using mul_le_mul_of_nonneg_left hεone (Nat.cast_nonneg Y.card))
    simpa only [bad₀, nonTypicalVertices, mul_comm ε] using hh
  have hbad₁ : (bad₁.card : ℝ) ≤ δ * X.card :=
    card_manyNonTypicalVertices_le G ε δ X J C B hδ hεδ hreg hB hBsize
  have hbad₂ : (bad₂.card : ℝ) ≤ δ * X.card :=
    card_manyNonTypicalVertices_le G ε δ X J C Q hδ hεδ hreg hQ hQsize
  have hbad : (bad.card : ℝ) ≤ (ε + 2 * δ) * X.card := by
    have hcount : bad.card ≤ bad₀.card + bad₁.card + bad₂.card :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hcount' : (bad.card : ℝ) ≤ bad₀.card + bad₁.card + bad₂.card := by
      exact_mod_cast hcount
    nlinarith only [hcount', hbad₀, hbad₁, hbad₂]
  have hlost : X \ P ⊆ bad := by
    intro v hv
    by_contra hn
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, hn⟩)
  refine ⟨P, Finset.sdiff_subset, ?_, ?_⟩
  · exact (show ((X \ P).card : ℝ) ≤ bad.card by
      exact_mod_cast Finset.card_le_card hlost).trans hbad
  · intro v hv
    obtain ⟨hvX, hvbad⟩ := Finset.mem_sdiff.mp hv
    have hv₀ : v ∉ bad₀ := fun hh ↦
      hvbad (Finset.mem_union_left _ (Finset.mem_union_left _ hh))
    have hv₁ : v ∉ bad₁ := fun hh ↦
      hvbad (Finset.mem_union_left _ (Finset.mem_union_right _ hh))
    have hv₂ : v ∉ bad₂ := fun hh ↦ hvbad (Finset.mem_union_right _ hh)
    refine ⟨degreeIn_of_not_nonTypical G hvX hv₀, ?_, ?_⟩
    · exact le_of_not_gt fun hh ↦ hv₁ (Finset.mem_filter.mpr ⟨hvX, hh⟩)
    · exact le_of_not_gt fun hh ↦ hv₂ (Finset.mem_filter.mpr ⟨hvX, hh⟩)

end Erdos547

#print axioms Erdos547.exists_seed_typical_pool

import ErdosProblems.Erdos1010.WeightedPairs

/-! # Incidence counts for families of unordered pairs -/

open Finset

namespace Erdos1010

variable {V : Type*} [DecidableEq V]

/-- The number of members of the finite family containing a given vertex. -/
def pairDegree (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter (fun p ↦ v ∈ p)).card

/-- Sum of endpoint weights over a family of unordered pairs. -/
def pairCharge (H : Finset (Finset V)) (w : V → ℤ) : ℤ :=
  ∑ p ∈ H, ∑ v ∈ p, w v

lemma pairDegree_le_card (H : Finset (Finset V)) (v : V) :
    pairDegree H v ≤ H.card := card_le_card (filter_subset _ _)

lemma pairCharge_eq_sum_degree (s : Finset V) (H : Finset (Finset V))
    (w : V → ℤ) (hH : ∀ p ∈ H, p ⊆ s) :
    pairCharge H w = ∑ v ∈ s, (pairDegree H v : ℤ) * w v := by
  unfold pairCharge
  calc
    _ = ∑ p ∈ H, ∑ v ∈ s, if v ∈ p then w v else 0 := by
      apply sum_congr rfl
      intro p hp
      rw [← sum_filter]
      congr 1
      ext v
      simp only [mem_filter]
      exact ⟨fun hv ↦ ⟨hH p hp hv, hv⟩, fun hv ↦ hv.2⟩
    _ = ∑ v ∈ s, ∑ p ∈ H, if v ∈ p then w v else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro v hv
      rw [← sum_filter]
      simp [pairDegree]

lemma pairCharge_le_baseline (s : Finset V) (H : Finset (Finset V))
    (w : V → ℤ) (k : ℤ) (hH : H ⊆ s.powersetCard 2) :
    pairCharge H w ≤ k * H.card + pairExcess s w k := by
  have hpoint : pairCharge H w ≤
      ∑ p ∈ H, (k + max ((∑ v ∈ p, w v) - k) 0) := by
    apply sum_le_sum
    intro p hp
    have := le_max_left ((∑ v ∈ p, w v) - k) 0
    omega
  have hsub : (∑ p ∈ H, max ((∑ v ∈ p, w v) - k) 0) ≤
      pairExcess s w k :=
    sum_le_sum_of_subset_of_nonneg hH (fun _ _ _ ↦ le_max_right _ _)
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at hpoint
  nlinarith

lemma pairCharge_add (H : Finset (Finset V)) (w z : V → ℤ) :
    pairCharge H (fun v ↦ w v + z v) = pairCharge H w + pairCharge H z := by
  simp [pairCharge, sum_add_distrib]

lemma pairCharge_single_weight (s : Finset V) (H : Finset (Finset V))
    (u : V) (c : ℤ) (hH : ∀ p ∈ H, p ⊆ s) :
    pairCharge H (fun v ↦ if v = u then c else 0) = (pairDegree H u : ℤ) * c := by
  by_cases hu : u ∈ s
  · rw [pairCharge_eq_sum_degree s H _ hH]
    simp [mul_ite, hu]
  · have hd : pairDegree H u = 0 := by
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro p hp hup
      exact hu (hH p hp hup)
    rw [hd, Nat.cast_zero, zero_mul]
    apply sum_eq_zero
    intro p hp
    apply sum_eq_zero
    intro v hv
    rw [if_neg]
    intro hvu
    subst v
    exact hu (hH p hp hv)

/-- A hub correction costs its incidence degree, not the total edge count. -/
lemma pairCharge_le_hub_baseline (s : Finset V) (H : Finset (Finset V))
    (w : V → ℤ) (k c : ℤ) (u : V) (hH : H ⊆ s.powersetCard 2) :
    pairCharge H w ≤ k * H.card + c * pairDegree H u +
      pairExcess s (fun v ↦ w v - if v = u then c else 0) k := by
  let z : V → ℤ := fun v ↦ w v - if v = u then c else 0
  have hsplit : pairCharge H w = pairCharge H z + (pairDegree H u : ℤ) * c := by
    rw [← pairCharge_single_weight s H u c (fun p hp ↦ (mem_powersetCard.mp (hH hp)).1),
      ← pairCharge_add]
    congr 1
    funext v
    simp [z]
  have hb := pairCharge_le_baseline s H z k hH
  rw [hsplit]
  dsimp [z] at hb ⊢
  nlinarith

end Erdos1010

import Arxiv.Arxiv2411_18291.SaturationCounts
import Arxiv.Arxiv2411_18291.CliqueFamilyBoundedness

/-!
# Removing edges with too many saturated cliques

Real thresholds avoid rounding losses. Double counting bounds the deleted
edges, while every surviving edge loses fewer than the threshold number
of cliques. Face-load caps also give the required boundary-multigraph bound.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem saturatedCliques_card_bound_real (D G : Finset (Block V q)) (r cap : ℕ) {L : ℝ}
    (hL : ∀ S ∈ saturatedFaces G r cap, ((D.filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ L) :
    ((saturatedCliques D G r cap).card : ℝ) ≤ (saturatedFaces G r cap).card * L := by
  rw [saturatedCliques_eq_biUnion]
  have hc : (((saturatedFaces G r cap).biUnion fun S =>
      D.filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤
      ∑ S ∈ saturatedFaces G r cap, ((D.filter fun Q => S.val ⊆ Q.val).card : ℝ) := by
    exact_mod_cast card_biUnion_le
  exact hc.trans ((sum_le_sum hL).trans_eq (by simp))

theorem saturatedCliques_weighted_bound (D G : Finset (Block V q)) (r cap M : ℕ)
    (hG : G.card ≤ M) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ S ∈ saturatedFaces G r cap, ((D.filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ L) :
    (cap : ℝ) * (saturatedCliques D G r cap).card ≤ (q.choose r * M : ℕ) * L := by
  have hfaces : (cap : ℝ) * (saturatedFaces G r cap).card ≤ (q.choose r * M : ℕ) := by
    exact_mod_cast (saturatedFaces_card_bound G r cap).trans (Nat.mul_le_mul_left _ hG)
  calc
    _ ≤ (cap : ℝ) * ((saturatedFaces G r cap).card * L) :=
      mul_le_mul_of_nonneg_left (saturatedCliques_card_bound_real D G r cap hL) (Nat.cast_nonneg _)
    _ = ((cap : ℝ) * (saturatedFaces G r cap).card) * L := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hfaces hL0

def goodCliqueEdges (K : Hypergraph V r) (D : Finset (Block V q)) (threshold : ℝ) :=
  K.filter fun e => ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) < threshold

omit [Fintype V] in
theorem goodCliqueEdges_bad_count [Finite V] (K : Hypergraph V r)
    (D : Finset (Block V q)) (threshold : ℝ) :
    threshold * (K \ goodCliqueEdges K D threshold).card ≤ (q.choose r : ℝ) * D.card := by
  let : Fintype V := Fintype.ofFinite V
  have hload (e : Block V r) (he : e ∈ K \ goodCliqueEdges K D threshold) :
      threshold ≤ ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) := by
    apply le_of_not_gt
    intro h
    exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨(mem_sdiff.mp he).1, h⟩)
  calc
    _ = ∑ _ ∈ K \ goodCliqueEdges K D threshold, threshold := by simp [mul_comm]
    _ ≤ ∑ e ∈ K \ goodCliqueEdges K D threshold,
        ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) := sum_le_sum hload
    _ ≤ ∑ e : Block V r, ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := by rw [← Nat.cast_sum, sum_clique_face_load, Nat.cast_mul]

omit [Fintype V] in
theorem goodCliqueEdges_remaining_error (K : Hypergraph V r) (D S : Finset (Block V q))
    (hSD : S ⊆ D) {threshold μ ε : ℝ}
    (hcount : ∀ e ∈ K, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| ≤ ε * μ)
    {e : Block V r} (he : e ∈ goodCliqueEdges K S threshold) :
    |(((D \ S).filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| < ε * μ + threshold := by
  obtain ⟨heK, hsmall⟩ := mem_filter.mp he
  have hc : ((D \ S).filter fun Q => e.val ⊆ Q.val).card +
      (S.filter fun Q => e.val ⊆ Q.val).card = (D.filter fun Q => e.val ⊆ Q.val).card := by
    have hfilter : (D \ S).filter (fun Q => e.val ⊆ Q.val) =
        (D.filter fun Q => e.val ⊆ Q.val) \ (S.filter fun Q => e.val ⊆ Q.val) := by
      ext Q
      simp only [mem_filter, mem_sdiff]
      tauto
    rw [hfilter]
    exact card_sdiff_add_card_eq_card (filter_subset_filter _ hSD)
  have hc' : (((D \ S).filter fun Q => e.val ⊆ Q.val).card : ℝ) +
      (S.filter fun Q => e.val ⊆ Q.val).card = (D.filter fun Q => e.val ⊆ Q.val).card := by
    exact_mod_cast hc
  have hs0 : (0 : ℝ) ≤ (S.filter fun Q => e.val ⊆ Q.val).card := Nat.cast_nonneg _
  obtain ⟨hlo, hup⟩ := abs_le.mp (hcount e heK)
  apply abs_lt.mpr
  constructor <;> linarith

theorem cliqueFamilyBounded_of_face_load (G : Finset (Block V q)) (cap : ℕ)
    (hcap : ∀ S : Block V r, (G.filter fun Q => S.val ⊆ Q.val).card ≤ cap) {θ : ℝ}
    (hθ : ((q - r : ℕ) : ℝ) * cap < θ * Fintype.card V) : IsCliqueFamilyBounded r G θ := by
  intro S
  have hd := degree_boundary (r := r + 1) (indicator G) S.val
    (show S.val.card ≤ r + 1 by rw [S.property]; omega)
  rw [degree_indicator, S.property, show r + 1 - r = 1 by omega, Nat.choose_one_right] at hd
  have hd' : ((degree (boundary (r + 1) (indicator G)) S.val : ℤ) : ℝ) =
      ((q - r : ℕ) : ℝ) * (G.filter fun Q => S.val ⊆ Q.val).card := by exact_mod_cast hd
  rw [hd']
  have hc : ((G.filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ cap := by exact_mod_cast hcap S
  exact (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)).trans_lt hθ

end Arxiv2411_18291

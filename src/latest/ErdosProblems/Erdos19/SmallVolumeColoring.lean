import ErdosProblems.Erdos19.CoreConcentration
import ErdosProblems.Erdos19.PeelableColoring

/-! # Elementary coloring from a small pair volume

A high-minimum-degree core forces a definite pair volume, even when its
edge sizes are unbounded. The contrapositive gives a greedy coloring bound
for large edges consuming a sufficiently small part of the pair budget.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {X : Type*} [Fintype X]

theorem dense_core_pair_weight_lower (H : SetHypergraph X)
    (hlinear : H.IsLinear) (S : Finset H) (h : ℕ) (hh : 1 ≤ h)
    (hmin : ∀ e ∈ S, 4 * h + 1 ≤ e.1.ncard)
    (hdense : IsDenseCore H.lineGraph S (4 * (Fintype.card X / (4 * h) + 1) + 1))
    (hne : S.Nonempty) :
    (Fintype.card X) ^ 2 ≤
      (32 * h ^ 2 * (1 + 4 * h * (1 + 4 * h))) *
        (∑ e ∈ S, e.1.ncard * (e.1.ncard - 1)) := by
  classical
  obtain ⟨e, heS, hemin⟩ := exists_min_image S (fun e : H ↦ e.1.ncard) hne
  let n := Fintype.card X
  let r := e.1.ncard
  let b := n / (4 * h)
  let m := 4 * (b + 1) + 1
  let R₁ := r * (1 + 4 * h)
  let R₂ := r * (1 + 4 * h * (1 + 4 * h))
  let W := S.filter fun f ↦ f.1.ncard ≤ R₂
  have hrge : 4 * h + 1 ≤ r := hmin e heS
  have hrpos : 0 < r := by omega
  have hapos : 0 < 4 * h := by omega
  have hR₁pos : 0 < R₁ := Nat.mul_pos hrpos (by omega)
  have hR : R₁ ≤ R₂ := by
    dsimp only [R₁, R₂]
    apply Nat.mul_le_mul_left
    nlinarith only [Nat.zero_le (h * h)]
  have hlarge₁ : ((S.filter (H.lineGraph.Adj e)).filter
      fun f ↦ R₁ < f.1.ncard).card ≤ b := by
    apply H.neighbor_card_le_div_of_scaled_rank hlinear e _
      (fun f hf ↦ (mem_filter.mp (mem_filter.mp hf).1).2)
      (4 * h) r R₁ hapos hrpos (le_refl _)
    · dsimp only [R₁]; nlinarith only [Nat.zero_le r]
    · intro f hf
      have hx := (mem_filter.mp hf).2
      omega
  have hlarge₂ : ∀ f ∈ S, H.lineGraph.Adj e f → f.1.ncard ≤ R₁ →
      ((S.filter (H.lineGraph.Adj f)).filter fun g ↦ R₂ < g.1.ncard).card ≤ b := by
    intro f hfS hef hfsize
    apply H.neighbor_card_le_div_of_scaled_rank hlinear f _
      (fun g hg ↦ (mem_filter.mp (mem_filter.mp hg).1).2)
      (4 * h) R₁ R₂ hapos hR₁pos hfsize
    · dsimp only [R₁, R₂]; nlinarith only [Nat.zero_le r]
    · intro g hg
      have hx := (mem_filter.mp hg).2
      omega
  have hcount := H.dense_core_rank_window_card hlinear S m r R₁ R₂ b b
    (by omega) hR hemin hdense e heS rfl hlarge₁ hlarge₂
  have hq : (n - 1) / (r - 1) ≤ b := by
    exact (Nat.div_le_div_right (Nat.sub_le n 1)).trans
      (Nat.div_le_div_left (by omega : 4 * h ≤ r - 1) hapos)
  have hfirst : b + 1 ≤ m - b := by dsimp only [m]; omega
  have hsecond : b + 1 ≤ m - (b + (n - 1) / (r - 1) + 1) := by
    dsimp only [m]
    omega
  have hwindow : (b + 1) ^ 2 ≤ W.card * (r * R₂) := by
    have hp := Nat.mul_le_mul hfirst hsecond
    have hp' : (b + 1) ^ 2 ≤ (m - b) * (m - (b + (n - 1) / (r - 1) + 1)) := by
      simpa only [pow_two] using hp
    exact hp'.trans hcount
  have hround : n ≤ 4 * h * (b + 1) := (Nat.lt_mul_div_succ n hapos).le
  have hroundsq : n ^ 2 ≤ 16 * h ^ 2 * (b + 1) ^ 2 := by
    nlinarith only [Nat.mul_le_mul hround hround]
  have hratio : r * R₂ ≤
      2 * (1 + 4 * h * (1 + 4 * h)) * (r * (r - 1)) := by
    have hx : r ≤ 2 * (r - 1) := by omega
    have hy := Nat.mul_le_mul_left (r * (1 + 4 * h * (1 + 4 * h))) hx
    dsimp only [R₂]
    nlinarith only [hy]
  have hsum : W.card * (r * (r - 1)) ≤ ∑ f ∈ S, f.1.ncard * (f.1.ncard - 1) := by
    calc
      W.card * (r * (r - 1)) = ∑ _f ∈ W, r * (r - 1) := by simp
      _ ≤ ∑ f ∈ W, f.1.ncard * (f.1.ncard - 1) := by
        apply sum_le_sum
        intro f hf
        have hrf := hemin f (mem_filter.mp hf).1
        exact Nat.mul_le_mul hrf (Nat.sub_le_sub_right hrf 1)
      _ ≤ ∑ f ∈ S, f.1.ncard * (f.1.ncard - 1) :=
        sum_le_sum_of_subset (filter_subset _ _)
  calc
    n ^ 2 ≤ 16 * h ^ 2 * (b + 1) ^ 2 := hroundsq
    _ ≤ 16 * h ^ 2 * (W.card * (r * R₂)) := Nat.mul_le_mul_left _ hwindow
    _ ≤ 16 * h ^ 2 * (W.card *
        (2 * (1 + 4 * h * (1 + 4 * h)) * (r * (r - 1)))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hratio)
    _ = (32 * h ^ 2 * (1 + 4 * h * (1 + 4 * h))) *
        (W.card * (r * (r - 1))) := by ring
    _ ≤ (32 * h ^ 2 * (1 + 4 * h * (1 + 4 * h))) *
        (∑ f ∈ S, f.1.ncard * (f.1.ncard - 1)) := Nat.mul_le_mul_left _ hsum

/-- A quantitative, elementary small-volume coloring theorem. No upper
bound on edge sizes is required. -/
theorem edgeColorable_of_small_pair_volume (H : SetHypergraph X)
    (hlinear : H.IsLinear) (h : ℕ) (hh : 1 ≤ h)
    (hmin : ∀ e : H, 4 * h + 1 ≤ e.1.ncard)
    (hvolume : (32 * h ^ 2 * (1 + 4 * h * (1 + 4 * h))) *
      (∑ e : H, e.1.ncard * (e.1.ncard - 1)) < (Fintype.card X) ^ 2) :
    H.EdgeColorable (4 * (Fintype.card X / (4 * h) + 1) + 1) := by
  classical
  let m := 4 * (Fintype.card X / (4 * h) + 1) + 1
  obtain ⟨S, hS, hdense, hpeel⟩ :=
    exists_dense_core_with_peelable_remainder H.lineGraph univ m
  have hSempty : S = ∅ := by
    by_contra hne
    have hbound := H.dense_core_pair_weight_lower hlinear S h hh
      (fun e _ ↦ hmin e) hdense (nonempty_iff_ne_empty.mpr hne)
    have hsum : (∑ e ∈ S, e.1.ncard * (e.1.ncard - 1)) ≤
        ∑ e : H, e.1.ncard * (e.1.ncard - 1) :=
      sum_le_sum_of_subset (subset_univ _)
    exact (not_lt_of_ge (hbound.trans (Nat.mul_le_mul_left _ hsum))) hvolume
  let c₀ : H → Fin m := fun _ ↦ ⟨0, by dsimp only [m]; omega⟩
  obtain ⟨c, _, _, hc⟩ := hpeel.exists_list_coloring_extension hS
    (fun _ ↦ (univ : Finset (Fin m))) (fun _ _ ↦ by simp)
    c₀ (by simp only [hSempty, notMem_empty, false_implies, implies_true])
  refine ⟨{ color := c, valid := ?_ }⟩
  intro e f hef hinter
  exact hc e (mem_univ _) f (mem_univ _) ⟨hef, hinter⟩

#print axioms dense_core_pair_weight_lower
#print axioms edgeColorable_of_small_pair_volume

theorem sum_pair_weight_mono {H J : SetHypergraph X} (hJH : J ⊆ H) :
    (∑ e : J, e.1.ncard * (e.1.ncard - 1)) ≤
      ∑ e : H, e.1.ncard * (e.1.ncard - 1) := by
  classical
  let incl : J ↪ H := ⟨fun e ↦ ⟨e.1, hJH e.2⟩, by
    intro e f hef
    exact Subtype.ext (congrArg (fun e : H ↦ e.val) hef)⟩
  calc
    (∑ e : J, e.1.ncard * (e.1.ncard - 1)) =
        ∑ e ∈ univ.map incl, e.1.ncard * (e.1.ncard - 1) := by
      rw [sum_map]
      rfl
    _ ≤ ∑ e : H, e.1.ncard * (e.1.ncard - 1) :=
      sum_le_sum_of_subset (subset_univ _)

theorem edgeColorable_of_small_pair_volume_le_two_div (H : SetHypergraph X)
    (hlinear : H.IsLinear) (h : ℕ) (hh : 1 ≤ h) (hn : 5 * h ≤ Fintype.card X)
    (hmin : ∀ e : H, 4 * h + 1 ≤ e.1.ncard)
    (hvolume : (32 * h ^ 2 * (1 + 4 * h * (1 + 4 * h))) *
      (∑ e : H, e.1.ncard * (e.1.ncard - 1)) < (Fintype.card X) ^ 2) :
    H.EdgeColorable (2 * Fintype.card X / h) := by
  apply (H.edgeColorable_of_small_pair_volume hlinear h hh hmin hvolume).mono
  apply (Nat.le_div_iff_mul_le (by omega : 0 < h)).2
  have hq := Nat.div_mul_le_self (Fintype.card X) (4 * h)
  nlinarith only [hq, hn]

#print axioms edgeColorable_of_small_pair_volume_le_two_div

end Erdos19.SetHypergraph

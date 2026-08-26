import ErdosProblems.Erdos19.EdgeRestriction
import ErdosProblems.Erdos19.SmallVolumeColoring

/-! # Coloring the small complement of a window with almost full pair volume -/

namespace Erdos19

theorem small_complement_pair_volume (n b C x y : ℕ) (hn : 0 < n) (hb : 10 ≤ b)
    (hC : 10 * C < b) (htotal : x + y ≤ n ^ 2) (hwindow : (b - 10) * n ^ 2 ≤ b * x) :
    C * y < n ^ 2 := by
  have hbsub : b - 10 + 10 = b := by omega
  have hsum := Nat.mul_le_mul_left b htotal
  have hrest : b * y ≤ 10 * n ^ 2 := by
    nlinarith only [hwindow, hsum, congrArg (fun z ↦ z * n ^ 2) hbsub]
  by_contra hnot
  have hbad : n ^ 2 ≤ C * y := by omega
  have h₁ := Nat.mul_le_mul_left b hbad
  have h₂ := Nat.mul_le_mul_left C hrest
  have h₃ := Nat.mul_lt_mul_of_pos_right hC (show 0 < n ^ 2 by positivity)
  nlinarith only [h₁, h₂, h₃]

theorem high_volume_palette_saving (n q : ℕ) (hq : 0 < q) :
    (n - n / (2 * q)) + 2 * n / (16 * q) ≤ n - n / (4 * q) := by
  have hq2 : 0 < 2 * q := by positivity
  have hq4 : 0 < 4 * q := by positivity
  have hdiv : 2 * (n / (4 * q)) ≤ n / (2 * q) := by
    apply (Nat.le_div_iff_mul_le hq2).mpr
    have h := Nat.mul_div_le n (4 * q)
    nlinarith only [h]
  have hrest : 2 * n / (16 * q) ≤ n / (4 * q) := by
    have heq : 2 * n / (16 * q) = n / (8 * q) := by
      rw [show 16 * q = 2 * (8 * q) by ring, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]
    rw [heq]
    exact Nat.div_le_div_left (by omega) hq4
  have hle := Nat.div_le_self n (2 * q)
  omega

namespace SetHypergraph

theorem edgeColorable_of_high_volume_window {V : Type*} [Fintype V]
    (H : SetHypergraph V) (hlinear : H.IsLinear) (W : Finset H) (b s k : ℕ)
    (hb : 10 ≤ b) (hs : 1 ≤ s) (hn : 5 * s ≤ Fintype.card V)
    (hmin : ∀ e : H, 4 * s + 1 ≤ e.1.ncard)
    (hcoefficient : 10 * (32 * s ^ 2 * (1 + 4 * s * (1 + 4 * s))) < b)
    (hvolume : (b - 10) * (Fintype.card V) ^ 2 ≤
      b * (∑ e ∈ W, e.1.ncard * (e.1.ncard - 1)))
    (hcolor : (H.restrictEdges (W : Set H)).EdgeColorable k) :
    H.EdgeColorable (k + 2 * Fintype.card V / s) := by
  classical
  let J := H.restrictEdges (W : Set H)
  let R := H.restrictEdges (W : Set H)ᶜ
  have hrest : (32 * s ^ 2 * (1 + 4 * s * (1 + 4 * s))) *
      (∑ e : R, e.1.ncard * (e.1.ncard - 1)) < (Fintype.card V) ^ 2 := by
    apply small_complement_pair_volume (Fintype.card V) b
      (32 * s ^ 2 * (1 + 4 * s * (1 + 4 * s)))
      (∑ e : J, e.1.ncard * (e.1.ncard - 1)) _ (by omega) hb hcoefficient
    · have hsplit := H.sum_restrictEdges_add_compl (W : Set H) (fun e ↦ e.ncard * (e.ncard - 1))
      have htotal := H.sum_ncard_mul_sub_one_le hlinear
      have hupper : Fintype.card V * (Fintype.card V - 1) ≤ (Fintype.card V) ^ 2 := by
        simpa only [pow_two] using Nat.mul_le_mul_left (Fintype.card V) (Nat.sub_le (Fintype.card V) 1)
      change (∑ e : J, e.1.ncard * (e.1.ncard - 1)) +
        (∑ e : R, e.1.ncard * (e.1.ncard - 1)) = _ at hsplit
      omega
    · change (b - 10) * (Fintype.card V) ^ 2 ≤ b *
        (∑ e : H.restrictEdges (W : Set H), e.1.ncard * (e.1.ncard - 1))
      rw [H.sum_restrictEdges_finset W (fun e ↦ e.ncard * (e.ncard - 1))]
      exact hvolume
  have hRcolor := R.edgeColorable_of_small_pair_volume_le_two_div
    (H.restrictEdges_linear hlinear _) s hs hn
    (fun e ↦ hmin ⟨e.1, H.restrictEdges_subset _ e.2⟩) hrest
  have hc := J.edgeColorable_union R hcolor hRcolor
  rw [H.restrictEdges_union_compl] at hc
  exact hc

#print axioms edgeColorable_of_high_volume_window

end SetHypergraph
end Erdos19

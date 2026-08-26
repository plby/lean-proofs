import ErdosProblems.Erdos547.RootedRegularEmbedding

/-!
# Explicit margins for embedding a small rooted tree in a regular pair
-/

namespace Erdos547

open Finset SimpleGraph

theorem regular_pair_room (ε d D η m n a : ℝ)
    (hε : 0 ≤ ε) (hd : d ≤ D) (hdone : d ≤ 1) (hη : 0 ≤ η) (hm : 0 ≤ m)
    (hde : 2 * ε ≤ d) (hmargin : 4 * ε ≤ d * η)
    (ha : η * m ≤ a) (hn : n ≤ ε * m) :
    ε * m ≤ a ∧ n ≤ (D - ε) * a - ε * m := by
  have hηε : ε ≤ η := by
    have hh := mul_le_mul_of_nonneg_right hdone hη
    linarith
  have hda : 0 ≤ d - ε := by linarith
  have han : 0 ≤ a := (mul_nonneg hη hm).trans ha
  have hp : 2 * ε ≤ (d - ε) * η := by
    have hh := mul_le_mul_of_nonneg_right hde hη
    nlinarith only [hh, hmargin]
  have hlarge : 2 * ε * m ≤ (D - ε) * a := by
    calc
      _ ≤ ((d - ε) * η) * m := mul_le_mul_of_nonneg_right hp hm
      _ = (d - ε) * (η * m) := by ring
      _ ≤ (d - ε) * a := mul_le_mul_of_nonneg_left ha hda
      _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_right hd ε) han
  exact ⟨(mul_le_mul_of_nonneg_right hηε hm).trans ha, by linarith⟩

variable {U V : Type*} [Fintype U]

theorem exists_small_rooted_copy_in_regular_pair (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : T.IsTree) {ε d η : ℝ} {X Y A B : Finset V}
    (hreg : G.IsUniform ε X Y) (hdis : Disjoint X Y) (heq : X.card = Y.card)
    (hd : d ≤ (G.edgeDensity X Y : ℝ)) (hη : 0 ≤ η)
    (hde : 2 * ε ≤ d) (hmargin : 4 * ε ≤ d * η)
    (hA : A ⊆ X) (hB : B ⊆ Y)
    (hAsize : η * (X.card : ℝ) ≤ A.card) (hBsize : η * (X.card : ℝ) ≤ B.card)
    (hsmall : (Fintype.card U : ℝ) ≤ ε * X.card)
    (r : U) (v : V) (hv : v ∈ X) (hroot : 2 * ε * X.card ≤ (degreeIn G B v : ℝ)) :
    ∃ f : T.Copy G, f r = v ∧ ∀ u, u ≠ r →
      (T.dist r u % 2 = 0 → f u ∈ A) ∧ (T.dist r u % 2 ≠ 0 → f u ∈ B) := by
  have hdone : d ≤ 1 := hd.trans (by exact_mod_cast G.edgeDensity_le_one X Y)
  have hε := hreg.pos.le
  have hroomA := regular_pair_room ε d (G.edgeDensity X Y : ℝ) η X.card (Fintype.card U)
    A.card hε hd hdone hη (Nat.cast_nonneg _) hde hmargin hAsize hsmall
  have hroomB := regular_pair_room ε d (G.edgeDensity X Y : ℝ) η X.card (Fintype.card U)
    B.card hε hd hdone hη (Nat.cast_nonneg _) hde hmargin hBsize hsmall
  apply exists_rooted_copy_in_regular_pair T G hT hreg hdis hA hB
    (by simpa only [mul_comm ε] using hroomA.1)
    (by simpa only [← heq, mul_comm ε] using hroomB.1)
    (by simpa only [← heq, mul_comm ε] using hroomB.2)
    (by simpa only [mul_comm ε] using hroomA.2) r v hv
  rw [← heq]
  linarith

end Erdos547

#print axioms Erdos547.exists_small_rooted_copy_in_regular_pair

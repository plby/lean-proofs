import ErdosProblems.Erdos547.TwoRootRegularEmbedding
import ErdosProblems.Erdos547.RootedRegularMargins

/-!
# Explicit margins for a regular-pair shrub with two roots
-/

namespace Erdos547

open Finset SimpleGraph

theorem regular_shrub_room (ε d D η m n a : ℝ)
    (hε : 0 ≤ ε) (hd : d ≤ D) (hdone : d ≤ 1) (hη : 0 ≤ η) (hm : 0 ≤ m)
    (hde : 2 * ε ≤ d) (hmargin : 8 * ε ≤ d ^ 2 * η)
    (ha : η * m ≤ a) (hn : n ≤ ε * m) :
    ε * m ≤ a ∧ n ≤ (D - ε) * a - ε * m ∧ n ≤ (D - ε) ^ 2 * a - ε * m := by
  have hd0 : 0 ≤ d := by linarith
  have hweak : 4 * ε ≤ d * η := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hd0 hdone) hη
    nlinarith only [hh, hmargin, hε]
  have hbase := regular_pair_room ε d D η m n a hε hd hdone hη hm hde hweak ha hn
  have han : 0 ≤ a := (mul_nonneg hη hm).trans ha
  have hhalf : d / 2 ≤ D - ε := by linarith
  have hD0 : 0 ≤ D - ε := by linarith
  have hpow : d ^ 2 / 4 ≤ (D - ε) ^ 2 := by
    have hh := mul_le_mul hhalf hhalf (by linarith : 0 ≤ d / 2) hD0
    nlinarith only [hh]
  have hlarge : 2 * ε * m ≤ (D - ε) ^ 2 * a := by
    calc
      _ ≤ (d ^ 2 * η / 4) * m := mul_le_mul_of_nonneg_right (by linarith) hm
      _ = (d ^ 2 / 4) * (η * m) := by ring
      _ ≤ (d ^ 2 / 4) * a := mul_le_mul_of_nonneg_left ha (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow han
  exact ⟨hbase.1, hbase.2, by linarith⟩

variable {U V : Type*} [Fintype U]

theorem exists_small_two_rooted_copy_in_regular_pair (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : T.IsTree) (r x : U)
    (hxeven : T.dist r x % 2 = 0) (hxdist : 4 ≤ T.dist r x)
    {ε d η : ℝ} {X Y A B P : Finset V}
    (hreg : G.IsUniform ε X Y) (hdis : Disjoint X Y) (heq : X.card = Y.card)
    (hd : d ≤ (G.edgeDensity X Y : ℝ)) (hη : 0 ≤ η)
    (hde : 2 * ε ≤ d) (hmargin : 8 * ε ≤ d ^ 2 * η)
    (hA : A ⊆ X) (hB : B ⊆ Y) (hP : P ⊆ X) (hPA : Disjoint P A)
    (hAsize : η * (X.card : ℝ) ≤ A.card) (hBsize : η * (X.card : ℝ) ≤ B.card)
    (hPsize : 2 * ε * (X.card : ℝ) ≤ P.card)
    (hsmall : (Fintype.card U : ℝ) ≤ ε * X.card)
    (v : V) (hvP : v ∉ P) (hroot : 2 * ε * X.card ≤ (degreeIn G B v : ℝ)) :
    ∃ f : T.Copy G, f r = v ∧ f x ∈ P ∧ ∀ u, u ≠ r → u ≠ x →
      (T.dist r u % 2 = 0 → f u ∈ A) ∧ (T.dist r u % 2 ≠ 0 → f u ∈ B) := by
  have hdone : d ≤ 1 := hd.trans (by exact_mod_cast G.edgeDensity_le_one X Y)
  have hε := hreg.pos.le
  have hroomA := regular_shrub_room ε d (G.edgeDensity X Y : ℝ) η X.card (Fintype.card U)
    A.card hε hd hdone hη (Nat.cast_nonneg _) hde hmargin hAsize hsmall
  have hroomB := regular_shrub_room ε d (G.edgeDensity X Y : ℝ) η X.card (Fintype.card U)
    B.card hε hd hdone hη (Nat.cast_nonneg _) hde hmargin hBsize hsmall
  have hnpos : (0 : ℝ) < Fintype.card U := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty U from ⟨r⟩)
  have hPbig : (X.card : ℝ) * ε < P.card := by nlinarith only [hnpos, hsmall, hPsize]
  have hεD : ε ≤ (G.edgeDensity X Y : ℝ) := by linarith
  apply exists_two_rooted_copy_in_regular_pair T G hT r x hxeven hxdist hreg hdis
    hA hB hP hPA (by simpa only [mul_comm ε] using hroomA.1)
    (by simpa only [← heq, mul_comm ε] using hroomB.1) hPbig hεD
    (by rw [← heq]; nlinarith only [hroomB.2.1])
    (by simpa only [← heq, mul_comm ε] using hroomB.2.2)
    (by simpa only [mul_comm ε] using hroomA.2.1) v hvP
  rw [← heq]
  linarith

end Erdos547

#print axioms Erdos547.exists_small_two_rooted_copy_in_regular_pair

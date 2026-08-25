import ErdosProblems.Erdos490.Dyadic
import ErdosProblems.Erdos490.Deletion

noncomputable section

namespace Erdos490

open Finset BigOperators

def rectangleWeight (m : ℕ → ℕ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  if m k < N_layer 2 k then
    g k / (Y_val 2 k * Real.sqrt (M_layer 2 k) * Real.sqrt ((m k : ℝ) + 1))
  else 0

lemma rectangleWeight_nonneg (m : ℕ → ℕ) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (k : ℕ) :
    0 ≤ rectangleWeight m g k := by
  unfold rectangleWeight
  split_ifs
  · have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
    exact div_nonneg (hg k) (by positivity)
  · rfl

lemma quotient_rectangles_disjoint {n : ℕ} {A B : Finset ℕ}
    (hAB : ProductAdmissible n A B)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Disjoint ((sinv A p) ×ˢ (sinv B p)) ((sinv A q) ×ˢ (sinv B q)) := by
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  have hA : (sinv A p ∩ sinv A q).Nonempty :=
    ⟨z.1, Finset.mem_inter.mpr
      ⟨(Finset.mem_product.mp hz₁).1, (Finset.mem_product.mp hz₂).1⟩⟩
  have hB := collision_lemma n A B p q hAB hp hq hpq hA
  have hz : z.2 ∈ sinv B p ∩ sinv B q :=
    Finset.mem_inter.mpr
      ⟨(Finset.mem_product.mp hz₁).2, (Finset.mem_product.mp hz₂).2⟩
  simp [hB] at hz

lemma quotient_rectangle_count {n : ℕ} {A B : Finset ℕ}
    (hAB : ProductAdmissible n A B) (L : Finset ℕ) (hL : ∀ p ∈ L, p.Prime) :
    ∑ p ∈ L, (sinv A p).card * (sinv B p).card ≤
      (L.biUnion (sinv A)).card * (L.biUnion (sinv B)).card := by
  classical
  calc
    _ = (L.biUnion (fun p => sinv A p ×ˢ sinv B p)).card := by
      rw [Finset.card_biUnion]
      · simp only [Finset.card_product]
      · intro p hp q hq hpq
        exact quotient_rectangles_disjoint hAB (hL p hp) (hL q hq) hpq
    _ ≤ ((L.biUnion (sinv A)) ×ˢ (L.biUnion (sinv B))).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      exact Finset.mem_product.mpr
        ⟨Finset.mem_biUnion.mpr ⟨p, hp, (Finset.mem_product.mp hz).1⟩,
         Finset.mem_biUnion.mpr ⟨p, hp, (Finset.mem_product.mp hz).2⟩⟩
    _ = _ := Finset.card_product _ _

lemma regular_rectangle_cross_bound (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 1 ≤ g k) {n : ℕ} {A B : Finset ℕ}
    (hAB : ProductAdmissible n A B)
    (hA : WeightRegular (rectangleWeight m g) A)
    (hB : WeightRegular (rectangleWeight m g) B)
    (k : ℕ) (hk : m k < (L_common 2 k A B).card) :
    ((A.card : ℝ) * B.card) * (g k)^2 ≤
      (Y_val 2 k)^2 * M_layer 2 k *
        ((L_common 2 k A B).biUnion (sinv A)).card *
          ((L_common 2 k A B).biUnion (sinv B)).card := by
  let L := L_common 2 k A B
  let w := rectangleWeight m g k
  have hm : m k < N_layer 2 k := hk.trans_le (Finset.card_filter_le _ _)
  have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
  have hM : 0 < M_layer 2 k := M_layer_positive _ _
  have hgpos : 0 < g k := lt_of_lt_of_le zero_lt_one (hg k)
  have hw : 0 < w := by
    dsimp [w, rectangleWeight]
    rw [if_pos hm]
    positivity
  have hL (p : ℕ) (hp : p ∈ L) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hlocal (p : ℕ) (hp : p ∈ L) :
      w^2 * ((A.card : ℝ) * B.card) ≤ (sinv A p).card * (sinv B p).card := by
    have hp' := Finset.mem_filter.mp hp
    have ha := hA k p hp'.1 hw hp'.2.1
    have hb := hB k p hp'.1 hw hp'.2.2
    rw [← division_lemma A p (hL p hp)] at ha
    rw [← division_lemma B p (hL p hp)] at hb
    have h := mul_le_mul ha.le hb.le (by positivity) (by positivity)
    nlinarith
  have hsum : (L.card : ℝ) * (w^2 * ((A.card : ℝ) * B.card)) ≤
      ((L.biUnion (sinv A)).card : ℝ) * (L.biUnion (sinv B)).card := by
    calc
      _ = ∑ p ∈ L, w^2 * ((A.card : ℝ) * B.card) := by simp
      _ ≤ ∑ p ∈ L, ((sinv A p).card : ℝ) * (sinv B p).card := Finset.sum_le_sum hlocal
      _ ≤ _ := by exact_mod_cast quotient_rectangle_count hAB L hL
  have hcard : (m k : ℝ) + 1 ≤ L.card := by exact_mod_cast hk
  have hsum' : ((m k : ℝ) + 1) * w^2 * ((A.card : ℝ) * B.card) ≤
      ((L.biUnion (sinv A)).card : ℝ) * (L.biUnion (sinv B)).card := by
    have h := mul_le_mul_of_nonneg_right hcard
      (by positivity : 0 ≤ w^2 * ((A.card : ℝ) * B.card))
    nlinarith
  have hidentity : ((m k : ℝ) + 1) * w^2 = (g k)^2 / ((Y_val 2 k)^2 * M_layer 2 k) := by
    dsimp [w, rectangleWeight]
    rw [if_pos hm, div_pow, mul_pow, mul_pow,
      Real.sq_sqrt hM.le, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m k + 1)]
    field_simp
  rw [hidentity, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hsum'
  dsimp [L] at hsum'
  nlinarith

end Erdos490

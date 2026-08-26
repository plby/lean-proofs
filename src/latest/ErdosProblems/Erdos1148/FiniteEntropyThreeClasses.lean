import ErdosProblems.Erdos1148.FiniteEntropyCrossBound

/-! # Entropy controlled by nested high-mass families and their cardinalities -/

namespace Erdos1148.DukeArithmetic

theorem finiteEntropy_le_three_class_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H : Finset ι) (hGH : G ⊆ H) {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hGA : (G.card : ℝ) ≤ A) (hHB : (H.card : ℝ) ≤ B) (hIC : (Fintype.card ι : ℝ) ≤ C)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    finiteEntropy p ≤ Real.log 3 + (∑ i ∈ G, p i) * Real.log A +
      ((∑ i ∈ H, p i) - ∑ i ∈ G, p i) * Real.log B +
      (1 - ∑ i ∈ H, p i) * Real.log C := by
  classical
  let c : ι → Fin 3 := fun i => if i ∈ G then 0 else if i ∈ H then 1 else 2
  let caps : Fin 3 → ℝ := fun j => if j = 0 then A else if j = 1 then B else C
  have hc0 : ((Finset.univ.filter (fun i : ι => c i = 0)).card : ℝ) ≤ A := by
    apply le_trans _ hGA
    exact_mod_cast Finset.card_le_card (show Finset.univ.filter (fun i => c i = 0) ⊆ G from by
      intro i hi
      have hc := (Finset.mem_filter.mp hi).2
      by_contra hnot
      by_cases hiH : i ∈ H <;> simp [c, hnot, hiH] at hc)
  have hc1 : ((Finset.univ.filter (fun i : ι => c i = 1)).card : ℝ) ≤ B := by
    apply le_trans _ hHB
    exact_mod_cast Finset.card_le_card (show Finset.univ.filter (fun i => c i = 1) ⊆ H from by
      intro i hi
      have hc := (Finset.mem_filter.mp hi).2
      by_contra hnot
      by_cases hiG : i ∈ G <;> simp [c, hnot, hiG] at hc)
  have hc2 : ((Finset.univ.filter (fun i : ι => c i = 2)).card : ℝ) ≤ C := by
    apply le_trans _ hIC
    exact_mod_cast Finset.card_le_univ (Finset.univ.filter (fun i : ι => c i = 2))
  have hcaps (j : Fin 3) : 0 < caps j := by dsimp [caps]; split_ifs <;> assumption
  have hcard (j : Fin 3) : ((Finset.univ.filter (fun i : ι => c i = j)).card : ℝ) ≤ caps j := by
    fin_cases j
    · simpa [caps] using hc0
    · simpa [caps] using hc1
    · simpa [caps] using hc2
  have hentropy := finiteEntropy_le_classification_bound c caps hcaps (by norm_num) hcard hp hsum
  have hpoint (i : ι) : p i * Real.log (caps (c i)) =
      (if i ∈ G then p i else 0) * Real.log A +
      ((if i ∈ H then p i else 0) - (if i ∈ G then p i else 0)) * Real.log B +
      (p i - (if i ∈ H then p i else 0)) * Real.log C := by
    by_cases hiG : i ∈ G
    · have hiH := hGH hiG
      simp [c, caps, hiG, hiH]
    · by_cases hiH : i ∈ H <;> simp [c, caps, hiG, hiH]
  have hGsum : (∑ i : ι, if i ∈ G then p i else 0) = ∑ i ∈ G, p i :=
    Finset.sum_ite_mem_eq G p
  have hHsum : (∑ i : ι, if i ∈ H then p i else 0) = ∑ i ∈ H, p i :=
    Finset.sum_ite_mem_eq H p
  simp only [hpoint, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
    hGsum, hHsum, hsum, Fintype.card_fin] at hentropy
  norm_num only [Nat.cast_ofNat] at hentropy
  exact hentropy.trans_eq (by ring)

end Erdos1148.DukeArithmetic

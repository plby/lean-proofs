import ErdosProblems.Erdos19.BulkForbiddenBounds
import ErdosProblems.Erdos19.OutlierActiveColors

/-! # Prescribed matching packing with an exceptional vertex set

The exceptional vertices are covered only as often as required by their degrees.
Every remaining vertex is covered except for its forbidden colors and at most one
distinct parity correction.
-/

namespace Erdos19

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem eventually_matching_packing_with_outliers (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V], ∀ X : Set V, N ≤ Xᶜ.ncard →
      ∀ G : _root_.SimpleGraph V,
      (∀ v : ↥(Xᶜ), (1 - delta) * Xᶜ.ncard ≤ ((G.induce Xᶜ).degree v : ℝ)) →
      ∀ m : ℕ, m < Fintype.card V → (m : ℝ) ≤ (1 - zeta) * Xᶜ.ncard →
      ∀ C : Fin m → Set V, ∀ U : Set V, ∀ a q : ℕ, 0 < q →
      (∀ i, (C i).ncard ≤ a) →
      m + a + X.ncard ≤ (U \ X).ncard →
      2 * X.ncard + a + (X.ncard * m) / q < Fintype.card V - m - 1 →
      ((a + X.ncard + 1 : ℕ) : ℝ) ≤ delta * Xᶜ.ncard →
      (∀ v : ↥(Xᶜ), (((∑ i : Fin m, if v.1 ∈ C i then 1 else 0) + q + 1 : ℕ) : ℝ) ≤
        delta * Xᶜ.ncard) →
      (∀ v, (G.neighborSet v).ncard + (∑ i : Fin m, if v ∈ C i then 1 else 0) +
        (if v ∈ U then 1 else 0) ≤ Fintype.card V - 1) →
      ∃ M : Fin m → G.Subgraph,
        (∀ i, (M i).IsMatching ∧ (M i).verts ⊆ (C i)ᶜ) ∧
        Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
        (∀ v, (G.neighborSet v).ncard +
          (∑ i : Fin m, if v ∈ (M i).verts then 0 else 1) ≤ Fintype.card V - 1) := by
  classical
  obtain ⟨delta, hd, N, hN⟩ := eventually_prescribed_matching_packing_fintype zeta hzeta
  refine ⟨delta, hd, N, ?_⟩
  intro V _ X hn G hG m hmn hm C U a q hq hclasses hroom hmargin hsmall hinc hbudget
  have hnpos : 0 < Fintype.card V := lt_of_le_of_lt (Nat.zero_le m) hmn
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  obtain ⟨activeAll, hav, _, hdeg, hdegeq⟩ := exists_active_colors_for_residual_degree
    (Fintype.card V) m hmn (fun v ↦ (G.neighborSet v).ncard) C (fun v ↦ by
      have hb := hbudget v
      omega)
  let active : X → Finset (Fin m) := fun u ↦ activeAll u.1
  obtain ⟨partner, hpart, hproper, hquota⟩ := exists_outlier_partners G X m C active
    (Fintype.card V - m - 1) a q hq (fun u ↦ hdegeq u.1) hclasses hmargin
  let F := bulkForbidden X active partner C
  let U' : Set ↥(Xᶜ) := Subtype.val ⁻¹' U
  have hF (i : Fin m) : (F i).ncard ≤ a + X.ncard :=
    (bulkForbidden_ncard_le X active partner C i).trans (Nat.add_le_add_right (hclasses i) _)
  obtain ⟨f, hf, hfmem⟩ := exists_distinct_corrections_avoiding U' F (fun i ↦ by
    have hi := hF i
    rw [Fintype.card_fin, compl_subtype_preimage_ncard]
    omega)
  let A : Fin m → Set ↥(Xᶜ) := fun i ↦ auxiliaryTarget (F i) (f i)
  have heven (i : Fin m) : Even (A i).ncard := auxiliaryTarget_even _ _ (hfmem i).2
  have hsmallA (i : Fin m) : ((A i)ᶜ.ncard : ℝ) ≤ delta * Fintype.card ↥(Xᶜ) := by
    have hi : (A i)ᶜ.ncard ≤ a + X.ncard + 1 :=
      (auxiliaryTarget_compl_ncard_le _ _).trans (Nat.add_le_add_right (hF i) 1)
    rw [Set.fintypeCard_eq_ncard]
    exact (Nat.cast_le.mpr hi).trans hsmall
  have hincA (v : ↥(Xᶜ)) : ((∑ i : Fin m, if v ∈ A i then 0 else 1 : ℕ) : ℝ) ≤
      delta * Fintype.card ↥(Xᶜ) := by
    have ha := auxiliaryTarget_omission_bound F f hf v
    have hb := bulkForbidden_color_count_le X active partner C q hquota v
    have htotal : (∑ i : Fin m, if v ∈ A i then 0 else 1) ≤
        (∑ i : Fin m, if v.1 ∈ C i then 1 else 0) + q + 1 := by
      change (∑ i : Fin m, if v ∈ auxiliaryTarget (F i) (f i) then 0 else 1) ≤ _
      change (∑ i : Fin m, if v ∈ F i then 1 else 0) ≤ _ at hb
      split_ifs at ha <;> omega
    rw [Set.fintypeCard_eq_ncard]
    exact (Nat.cast_le.mpr htotal).trans (hinc v)
  obtain ⟨B, hB, hBd⟩ := hN ↥(Xᶜ) (by simpa only [Set.fintypeCard_eq_ncard] using hn)
    (G.induce Xᶜ) (by
      intro v
      simpa only [Set.fintypeCard_eq_ncard, ← card_neighborSet_eq_degree] using hG v)
    m (by simpa only [Set.fintypeCard_eq_ncard] using hm) A heven hsmallA hincA
  obtain ⟨M, hM, hMd, hcovered, habs⟩ := exists_merged_cross_bulk_matchings X active G partner
    (fun e ↦ (hpart e).1) (fun e ↦ (hpart e).2.1) hproper C (fun u ↦ hav u.1)
    (fun e ↦ (hpart e).2.2) U f hf (fun i ↦ (hfmem i).1) B hB hBd
  refine ⟨M, hM, hMd, ?_⟩
  intro v
  by_cases hv : v ∈ X
  · have hc := hcovered ⟨v, hv⟩
    have hdv := hdeg v
    have hsum : (∑ i : Fin m, if v ∈ (M i).verts then 1 else 0) +
        (∑ i : Fin m, if v ∈ (M i).verts then 0 else 1) = m := by
      rw [← Finset.sum_add_distrib]
      have hper (i : Fin m) : (if v ∈ (M i).verts then 1 else 0) +
          (if v ∈ (M i).verts then 0 else 1) = 1 := by split_ifs <;> rfl
      simp only [hper, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    change (∑ i : Fin m, if v ∈ (M i).verts then 1 else 0) = (activeAll v).card at hc
    omega
  · have ha := habs v hv
    have hb := hbudget v
    omega

#print axioms eventually_matching_packing_with_outliers

end Erdos19

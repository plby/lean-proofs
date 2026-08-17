import ErdosProblems.Erdos632.Basic
import ErdosProblems.Erdos632.Graph

/-!
# The structural obstruction inside the DHS gadget

This file proves that the explicit prescribed lists `L5` admit no two-fold
set-colouring of `g5Graph`.  The proof follows the forced-pair chain in
Dvořák--Hu--Sereni: the odd-cycle obstruction in `G2` forces one `z` block,
the `z` block forces a terminal pair, the three `w` triangles force both
cross-edge terminals, and the resulting restriction to `G1` contradicts the
six-colour incidence count on its five-cycle.
-/

open scoped BigOperators

namespace Erdos632

open G5Vertex

private lemma indicator_pair_le_one (p q : Prop) [Decidable p] [Decidable q]
    (h : ¬ (p ∧ q)) :
    (if p then 1 else 0) + (if q then 1 else 0) ≤ 1 := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

/-- One colour can occur at most twice on a properly set-coloured 5-cycle. -/
private lemma indicator_fiveCycle_le_two
    (p₁ p₂ p₃ p₄ p₅ : Prop)
    [Decidable p₁] [Decidable p₂] [Decidable p₃] [Decidable p₄] [Decidable p₅]
    (h₁₂ : ¬ (p₁ ∧ p₂)) (h₂₃ : ¬ (p₂ ∧ p₃))
    (h₃₄ : ¬ (p₃ ∧ p₄)) (h₄₅ : ¬ (p₄ ∧ p₅))
    (h₅₁ : ¬ (p₅ ∧ p₁)) :
    (if p₁ then 1 else 0) + (if p₂ then 1 else 0) +
        (if p₃ then 1 else 0) + (if p₄ then 1 else 0) +
        (if p₅ then 1 else 0) ≤ 2 := by
  by_cases hp₁ : p₁
  · have hp₂ : ¬ p₂ := fun hp₂ ↦ h₁₂ ⟨hp₁, hp₂⟩
    have hp₅ : ¬ p₅ := fun hp₅ ↦ h₅₁ ⟨hp₅, hp₁⟩
    have h₃₄' := indicator_pair_le_one p₃ p₄ h₃₄
    simp [hp₁, hp₂, hp₅]
    omega
  · have h₂₃' := indicator_pair_le_one p₂ p₃ h₂₃
    have h₄₅' := indicator_pair_le_one p₄ p₅ h₄₅
    simp [hp₁]
    omega

private lemma card_eq_six_indicators {A : Finset ℕ}
    (hA : A ⊆ {1, 2, 3, 4, 5, 6}) :
    A.card = (if 1 ∈ A then 1 else 0) + (if 2 ∈ A then 1 else 0) +
      (if 3 ∈ A then 1 else 0) + (if 4 ∈ A then 1 else 0) +
      (if 5 ∈ A then 1 else 0) + (if 6 ∈ A then 1 else 0) := by
  have hf : ({1, 2, 3, 4, 5, 6} : Finset ℕ).filter (· ∈ A) = A := by
    ext x
    constructor
    · exact fun hx ↦ (Finset.mem_filter.mp hx).2
    · exact fun hx ↦ Finset.mem_filter.mpr ⟨hA hx, hx⟩
  calc
    A.card = (({1, 2, 3, 4, 5, 6} : Finset ℕ).filter (· ∈ A)).card :=
      congrArg Finset.card hf.symm
    _ = (∑ x ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ), if x ∈ A then 1 else 0 : ℕ) := by
      simpa only [Nat.cast_id] using
        (Finset.natCast_card_filter (R := ℕ) (fun x : ℕ ↦ x ∈ A)
          ({1, 2, 3, 4, 5, 6} : Finset ℕ))
    _ = _ := by
      rw [Finset.sum_insert (by decide : (1 : ℕ) ∉ {2, 3, 4, 5, 6})]
      rw [Finset.sum_insert (by decide : (2 : ℕ) ∉ {3, 4, 5, 6})]
      rw [Finset.sum_insert (by decide : (3 : ℕ) ∉ {4, 5, 6})]
      rw [Finset.sum_insert (by decide : (4 : ℕ) ∉ {5, 6})]
      rw [Finset.sum_insert (by decide : (5 : ℕ) ∉ {6})]
      simp only [Finset.sum_singleton]
      simp [Nat.add_assoc]

private lemma not_both_mem_of_disjoint {A B : Finset ℕ}
    (h : Disjoint A B) (c : ℕ) : ¬ (c ∈ A ∧ c ∈ B) := by
  exact fun hc ↦ Finset.disjoint_left.mp h hc.1 hc.2

/-- The asymmetric base-cycle obstruction (DHS Lemma 3), proved by counting
colour incidences.  Colours 1, 2, and 3 occur at most once, while the other
three occur at most twice, giving at most nine incidences instead of ten. -/
lemma no_baseCycle_twoColoring
    (A₁ A₂ A₃ A₄ A₅ : Finset ℕ)
    (hA₁ : A₁ ⊆ {1, 2, 5, 6}) (hA₂ : A₂ ⊆ {1, 4, 5, 6})
    (hA₃ : A₃ ⊆ {3, 4, 5, 6}) (hA₄ : A₄ ⊆ {3, 4, 5, 6})
    (hA₅ : A₅ ⊆ {2, 4, 5, 6})
    (hc₁ : A₁.card = 2) (hc₂ : A₂.card = 2) (hc₃ : A₃.card = 2)
    (hc₄ : A₄.card = 2) (hc₅ : A₅.card = 2)
    (hd₁₂ : Disjoint A₁ A₂) (hd₂₃ : Disjoint A₂ A₃)
    (hd₃₄ : Disjoint A₃ A₄) (hd₄₅ : Disjoint A₄ A₅)
    (hd₅₁ : Disjoint A₅ A₁) : False := by
  have hs₁ : A₁ ⊆ {1, 2, 3, 4, 5, 6} := by
    intro x hx; have hx' := hA₁ hx; simp at hx' ⊢; aesop
  have hs₂ : A₂ ⊆ {1, 2, 3, 4, 5, 6} := by
    intro x hx; have hx' := hA₂ hx; simp at hx' ⊢; aesop
  have hs₃ : A₃ ⊆ {1, 2, 3, 4, 5, 6} := by
    intro x hx; have hx' := hA₃ hx; simp at hx' ⊢; aesop
  have hs₄ : A₄ ⊆ {1, 2, 3, 4, 5, 6} := by
    intro x hx; have hx' := hA₄ hx; simp at hx' ⊢; aesop
  have hs₅ : A₅ ⊆ {1, 2, 3, 4, 5, 6} := by
    intro x hx; have hx' := hA₅ hx; simp at hx' ⊢; aesop
  have he₁ := card_eq_six_indicators hs₁
  have he₂ := card_eq_six_indicators hs₂
  have he₃ := card_eq_six_indicators hs₃
  have he₄ := card_eq_six_indicators hs₄
  have he₅ := card_eq_six_indicators hs₅
  have h₁₃ : 1 ∉ A₃ := by intro h; have := hA₃ h; simp at this
  have h₁₄ : 1 ∉ A₄ := by intro h; have := hA₄ h; simp at this
  have h₁₅ : 1 ∉ A₅ := by intro h; have := hA₅ h; simp at this
  have h₂₂ : 2 ∉ A₂ := by intro h; have := hA₂ h; simp at this
  have h₂₃ : 2 ∉ A₃ := by intro h; have := hA₃ h; simp at this
  have h₂₄ : 2 ∉ A₄ := by intro h; have := hA₄ h; simp at this
  have h₃₁ : 3 ∉ A₁ := by intro h; have := hA₁ h; simp at this
  have h₃₂ : 3 ∉ A₂ := by intro h; have := hA₂ h; simp at this
  have h₃₅ : 3 ∉ A₅ := by intro h; have := hA₅ h; simp at this
  have hcolor₁ :
      (if 1 ∈ A₁ then 1 else 0) + (if 1 ∈ A₂ then 1 else 0) +
        (if 1 ∈ A₃ then 1 else 0) + (if 1 ∈ A₄ then 1 else 0) +
        (if 1 ∈ A₅ then 1 else 0) ≤ 1 := by
    simpa [h₁₃, h₁₄, h₁₅] using
      indicator_pair_le_one (1 ∈ A₁) (1 ∈ A₂)
        (not_both_mem_of_disjoint hd₁₂ 1)
  have hcolor₂ :
      (if 2 ∈ A₁ then 1 else 0) + (if 2 ∈ A₂ then 1 else 0) +
        (if 2 ∈ A₃ then 1 else 0) + (if 2 ∈ A₄ then 1 else 0) +
        (if 2 ∈ A₅ then 1 else 0) ≤ 1 := by
    simpa [h₂₂, h₂₃, h₂₄] using
      indicator_pair_le_one (2 ∈ A₁) (2 ∈ A₅)
        (not_both_mem_of_disjoint hd₅₁.symm 2)
  have hcolor₃ :
      (if 3 ∈ A₁ then 1 else 0) + (if 3 ∈ A₂ then 1 else 0) +
        (if 3 ∈ A₃ then 1 else 0) + (if 3 ∈ A₄ then 1 else 0) +
        (if 3 ∈ A₅ then 1 else 0) ≤ 1 := by
    simpa [h₃₁, h₃₂, h₃₅] using
      indicator_pair_le_one (3 ∈ A₃) (3 ∈ A₄)
        (not_both_mem_of_disjoint hd₃₄ 3)
  have hcolor (c : ℕ) :
      (if c ∈ A₁ then 1 else 0) + (if c ∈ A₂ then 1 else 0) +
        (if c ∈ A₃ then 1 else 0) + (if c ∈ A₄ then 1 else 0) +
        (if c ∈ A₅ then 1 else 0) ≤ 2 := by
    exact indicator_fiveCycle_le_two _ _ _ _ _
      (not_both_mem_of_disjoint hd₁₂ c)
      (not_both_mem_of_disjoint hd₂₃ c)
      (not_both_mem_of_disjoint hd₃₄ c)
      (not_both_mem_of_disjoint hd₄₅ c)
      (not_both_mem_of_disjoint hd₅₁ c)
  have hcolor₄ := hcolor 4
  have hcolor₅ := hcolor 5
  have hcolor₆ := hcolor 6
  omega

private lemma left_eq_of_pair_unions
    {U A B C : Finset ℕ} (hAB : A ∪ B = U) (hBC : B ∪ C = U)
    (hdAB : Disjoint A B) (hdBC : Disjoint B C) : A = C := by
  ext x
  constructor
  · intro hxA
    have hxU : x ∈ U := by rw [← hAB]; exact Finset.mem_union_left _ hxA
    rw [← hBC] at hxU
    rcases Finset.mem_union.mp hxU with hxB | hxC
    · exact (Finset.disjoint_left.mp hdAB hxA hxB).elim
    · exact hxC
  · intro hxC
    have hxU : x ∈ U := by rw [← hBC]; exact Finset.mem_union_right _ hxC
    rw [← hAB] at hxU
    rcases Finset.mem_union.mp hxU with hxA | hxB
    · exact hxA
    · exact (Finset.disjoint_left.mp hdBC hxB hxC).elim

/-- Five two-subsets of a four-set cannot be cyclically disjoint.  This is
the odd-cycle `(4:2)` obstruction used in `G2`. -/
lemma no_twoColoring_fiveCycle
    (U A₁ A₂ A₃ A₄ A₅ : Finset ℕ)
    (hU : U.card = 4)
    (hs₁ : A₁ ⊆ U) (hs₂ : A₂ ⊆ U) (hs₃ : A₃ ⊆ U)
    (hs₄ : A₄ ⊆ U) (hs₅ : A₅ ⊆ U)
    (hc₁ : A₁.card = 2) (hc₂ : A₂.card = 2) (hc₃ : A₃.card = 2)
    (hc₄ : A₄.card = 2) (hc₅ : A₅.card = 2)
    (hd₁₂ : Disjoint A₁ A₂) (hd₂₃ : Disjoint A₂ A₃)
    (hd₃₄ : Disjoint A₃ A₄) (hd₄₅ : Disjoint A₄ A₅)
    (hd₅₁ : Disjoint A₅ A₁) : False := by
  have hu₁₂ := union_eq_of_disjoint_of_card_two_of_subset_four
    hs₁ hs₂ hd₁₂ hc₁ hc₂ hU
  have hu₂₃ := union_eq_of_disjoint_of_card_two_of_subset_four
    hs₂ hs₃ hd₂₃ hc₂ hc₃ hU
  have hu₃₄ := union_eq_of_disjoint_of_card_two_of_subset_four
    hs₃ hs₄ hd₃₄ hc₃ hc₄ hU
  have hu₄₅ := union_eq_of_disjoint_of_card_two_of_subset_four
    hs₄ hs₅ hd₄₅ hc₄ hc₅ hU
  have heq₁₃ : A₁ = A₃ := left_eq_of_pair_unions hu₁₂ hu₂₃ hd₁₂ hd₂₃
  have heq₃₅ : A₃ = A₅ := left_eq_of_pair_unions hu₃₄ hu₄₅ hd₃₄ hd₄₅
  have hdself : Disjoint A₁ A₁ := by simpa [heq₁₃, heq₃₅] using hd₅₁
  have hempty : A₁ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact Finset.disjoint_left.mp hdself hx hx
  simp [hempty] at hc₁

/-- If `A` lies in `U ∪ O`, is disjoint from `U`, and has the same size as
`O`, then it is exactly `O`.  Every forced-pair step below has this form. -/
private lemma subset_right_of_subset_union_of_disjoint_left
    {A U O : Finset ℕ} (hA : A ⊆ U ∪ O) (hdis : Disjoint A U) : A ⊆ O := by
  intro x hxA
  rcases Finset.mem_union.mp (hA hxA) with hxU | hxO
  · exact (Finset.disjoint_left.mp hdis hxA hxU).elim
  · exact hxO

private lemma eq_right_of_subset_union_of_disjoint_left
    {A U O : Finset ℕ} (hA : A ⊆ U ∪ O) (hdis : Disjoint A U)
    (hcA : A.card = O.card) : A = O := by
  apply Finset.eq_of_subset_of_card_le
  · exact subset_right_of_subset_union_of_disjoint_left hA hdis
  · exact hcA.ge

private lemma g5_adj (u v : G5Vertex) (h : s(u, v) ∈ g5Edges) :
    g5Graph.Adj u v := by
  exact g5Graph_adj_iff.mpr h

private lemma g2Edge_mem_g5 {e : Sym2 G5Vertex} (h : e ∈ g2Edges) : e ∈ g5Edges := by
  simp only [g5Edges, g4Edges, g3Edges, Finset.mem_union]
  aesop

private lemma zPieceEdge_mem_g5 (i : Fin 2) {e : Sym2 G5Vertex}
    (h : e ∈ zPieceEdges i) : e ∈ g5Edges := by
  fin_cases i <;> simp only [g5Edges, g4Edges, g3Edges, Finset.mem_union] <;> aesop

private lemma wTriangleEdge_mem_g5 {e : Sym2 G5Vertex}
    (h : e ∈ wTriangleEdges) : e ∈ g5Edges := by
  simp only [g5Edges, g4Edges, Finset.mem_union]
  aesop

private lemma wtTriangleEdge_mem_g5 (i : Fin 2) {e : Sym2 G5Vertex}
    (h : e ∈ wtTriangleEdges i) : e ∈ g5Edges := by
  fin_cases i <;> simp only [g5Edges, g4Edges, Finset.mem_union] <;> aesop

private lemma g4BridgeEdge_mem_g5 {e : Sym2 G5Vertex}
    (h : e ∈ g4BridgeEdges) : e ∈ g5Edges := by
  simp only [g5Edges, g4Edges, Finset.mem_union]
  aesop

private lemma g1Edge_mem_g5 {e : Sym2 G5Vertex} (h : e ∈ g1Edges) : e ∈ g5Edges := by
  simp only [g5Edges, Finset.mem_union]
  aesop

private lemma crossEdge_mem_g5 {e : Sym2 G5Vertex} (h : e ∈ crossEdges) : e ∈ g5Edges := by
  simp only [g5Edges, Finset.mem_union]
  aesop

private lemma three_pairs_partition
    {U A B C : Finset ℕ} (hU : U.card = 6)
    (hA : A ⊆ U) (hB : B ⊆ U) (hC : C ⊆ U)
    (hcA : A.card = 2) (hcB : B.card = 2) (hcC : C.card = 2)
    (hdAB : Disjoint A B) (hdAC : Disjoint A C) (hdBC : Disjoint B C) :
    (A ∪ B) ∪ C = U := by
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.union_subset (Finset.union_subset hA hB) hC
  · rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hdAC, hdBC⟩),
      Finset.card_union_of_disjoint hdAB, hcA, hcB, hcC, hU]

/-- The `G2` obstruction: its terminal `y4` must use 7 or 8. -/
lemma g2_forces_y4
    {phi : G5Vertex → Finset ℕ} (hphi : IsLMulticoloring g5Graph L5 phi 2) :
    7 ∈ phi y4 ∨ 8 ∈ phi y4 := by
  have hsub (v : G5Vertex) : phi v ⊆ L5 v := (hphi.2 v).1
  have hcard (v : G5Vertex) : (phi v).card = 2 := (hphi.2 v).2
  have hdis {u v : G5Vertex} (h : s(u, v) ∈ g5Edges) :
      Disjoint (phi u) (phi v) := hphi.1 (g5_adj u v h)
  have hy4list : phi y4 ⊆ colors4 ∪ colors78 := by
    intro c hc
    have hc' := hsub y4 hc
    simp [L5, L4, L3, L2, colors123478, colors4, colors78] at hc' ⊢
    aesop
  have hy3list : phi y3 ⊆ colors4 := by
    simpa [L5, L4, L3, L2] using hsub y3
  by_contra havoid
  simp only [not_or] at havoid
  have hy4dis78 : Disjoint (phi y4) colors78 := by
    apply Finset.disjoint_left.mpr
    intro c hc hc78
    simp [colors78] at hc78
    rcases hc78 with rfl | rfl
    · exact havoid.1 hc
    · exact havoid.2 hc
  have hy4list4 : phi y4 ⊆ colors4 :=
    subset_right_of_subset_union_of_disjoint_left
      (by simpa [Finset.union_comm] using hy4list) hy4dis78
  have hdy4y3 : Disjoint (phi y4) (phi y3) := by
    apply hdis
    exact g2Edge_mem_g5 (by simp [g2Edges])
  have hy4y3 : phi y4 ∪ phi y3 = colors4 :=
    union_eq_of_disjoint_of_card_two_of_subset_four
      hy4list4 hy3list hdy4y3 (hcard y4) (hcard y3) colors4_card
  have hdy2y4 : Disjoint (phi y2) (phi y4) := by
    apply hdis
    exact g2Edge_mem_g5 (by simp [g2Edges])
  have hdy2y3 : Disjoint (phi y2) (phi y3) := by
    apply hdis
    exact g2Edge_mem_g5 (by simp [g2Edges])
  have hdy2colors4 : Disjoint (phi y2) colors4 := by
    rw [← hy4y3]
    exact Finset.disjoint_union_right.mpr ⟨hdy2y4, hdy2y3⟩
  have hy2list : phi y2 ⊆ colors4 ∪ colors78 := by
    intro c hc
    have hc' := hsub y2 hc
    simp [L5, L4, L3, L2, colors123478, colors4, colors78] at hc' ⊢
    aesop
  have hy2eq : phi y2 = colors78 :=
    eq_right_of_subset_union_of_disjoint_left hy2list hdy2colors4
      (by rw [hcard y2, colors78_card])
  have hdy1y2 : Disjoint (phi y1) (phi y2) := by
    apply hdis
    exact g2Edge_mem_g5 (by simp [g2Edges])
  have hdy1colors78 : Disjoint (phi y1) colors78 := by simpa [hy2eq] using hdy1y2
  have hy1list : phi y1 ⊆ colors78 ∪ colors6 := by
    intro c hc
    have hc' := hsub y1 hc
    simp [L5, L4, L3, L2, colors8, colors6, colors78] at hc' ⊢
    aesop
  have hy1list6 : phi y1 ⊆ colors6 :=
    subset_right_of_subset_union_of_disjoint_left hy1list hdy1colors78
  let U : Finset ℕ := colors6 \ phi y1
  have hUcard : U.card = 4 := by
    rw [show U = colors6 \ phi y1 from rfl,
      card_sdiff_eq_sub_of_subset hy1list6, colors6_card, hcard y1]
  have cycleList (v : G5Vertex)
      (hv : L5 v = colors6) (hedge : s(y1, v) ∈ g5Edges) : phi v ⊆ U := by
    intro c hc
    apply Finset.mem_sdiff.mpr
    constructor
    · exact hv ▸ hsub v hc
    · exact Finset.disjoint_left.mp (hdis hedge).symm hc
  have hv1 : phi v1 ⊆ U := cycleList v1 (by rfl)
    (g2Edge_mem_g5 (by simp [g2Edges]))
  have hu2 : phi u2 ⊆ U := cycleList u2 (by rfl)
    (g2Edge_mem_g5 (by simp [g2Edges]))
  have hv3 : phi v3 ⊆ U := cycleList v3 (by rfl)
    (g2Edge_mem_g5 (by simp [g2Edges]))
  have hu4 : phi u4 ⊆ U := cycleList u4 (by rfl)
    (g2Edge_mem_g5 (by simp [g2Edges]))
  have hu5 : phi u5 ⊆ U := cycleList u5 (by rfl)
    (g2Edge_mem_g5 (by simp [g2Edges]))
  exact no_twoColoring_fiveCycle U (phi v1) (phi u2) (phi v3) (phi u4) (phi u5)
    hUcard hv1 hu2 hv3 hu4 hu5
    (hcard v1) (hcard u2) (hcard v3) (hcard u4) (hcard u5)
    (hdis (g2Edge_mem_g5 (by simp [g2Edges])))
    (hdis (g2Edge_mem_g5 (by simp [g2Edges])))
    (hdis (g2Edge_mem_g5 (by simp [g2Edges])))
    (hdis (g2Edge_mem_g5 (by simp [g2Edges])))
    (hdis (g2Edge_mem_g5 (by simp [g2Edges])))

/-- If the distinguished colour `7 + i` occurs at `y4`, the `i`th `z` block
forces its terminal vertex to receive exactly `{7,8}`. -/
lemma zBlock_forces_terminal
    {phi : G5Vertex → Finset ℕ} (hphi : IsLMulticoloring g5Graph L5 phi 2)
    (i : Fin 2) (hhot : 7 + i.val ∈ phi y4) : phi (z i 6) = colors78 := by
  have hsub (v : G5Vertex) : phi v ⊆ L5 v := (hphi.2 v).1
  have hcard (v : G5Vertex) : (phi v).card = 2 := (hphi.2 v).2
  have hdis {u v : G5Vertex} (h : s(u, v) ∈ g5Edges) :
      Disjoint (phi u) (phi v) := hphi.1 (g5_adj u v h)
  let C123 : Finset ℕ := {1, 2, 3}
  let C456 : Finset ℕ := {4, 5, 6}
  have hy4z0 : Disjoint (phi y4) (phi (z i 0)) :=
    hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))
  have hy4z1 : Disjoint (phi y4) (phi (z i 1)) :=
    hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))
  have hhot0 : 7 + i.val ∉ phi (z i 0) :=
    Finset.disjoint_left.mp hy4z0 hhot
  have hhot1 : 7 + i.val ∉ phi (z i 1) :=
    Finset.disjoint_left.mp hy4z1 hhot
  have hz0sub : phi (z i 0) ⊆ C123 := by
    intro c hc
    have hc' := hsub (z i 0) hc
    simp [L5, L4, L3, C123] at hc' ⊢
    aesop
  have hz1sub : phi (z i 1) ⊆ C456 := by
    intro c hc
    have hc' := hsub (z i 1) hc
    simp [L5, L4, L3, C456] at hc' ⊢
    aesop
  have hz2sub : phi (z i 2) ⊆ colors6 := by
    simpa [L5, L4, L3] using hsub (z i 2)
  have hC123sub : C123 ⊆ colors6 := by
    intro c hc
    simp [C123, colors6] at hc ⊢
    aesop
  have hC456sub : C456 ⊆ colors6 := by
    intro c hc
    simp [C456, colors6] at hc ⊢
    aesop
  have hz0sub6 : phi (z i 0) ⊆ colors6 := hz0sub.trans hC123sub
  have hz1sub6 : phi (z i 1) ⊆ colors6 := hz1sub.trans hC456sub
  have hz0z1 : Disjoint (phi (z i 0)) (phi (z i 1)) := by
    apply Finset.disjoint_left.mpr
    intro c hc0 hc1
    have hc0' := hz0sub hc0
    have hc1' := hz1sub hc1
    simp [C123] at hc0'
    simp [C456] at hc1'
    omega
  have hz0z2 : Disjoint (phi (z i 0)) (phi (z i 2)) :=
    hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))
  have hz1z2 : Disjoint (phi (z i 1)) (phi (z i 2)) :=
    hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))
  have hpartition6 : (phi (z i 0) ∪ phi (z i 1)) ∪ phi (z i 2) = colors6 :=
    three_pairs_partition colors6_card hz0sub6 hz1sub6 hz2sub
      (hcard (z i 0)) (hcard (z i 1)) (hcard (z i 2)) hz0z1 hz0z2 hz1z2
  have hz3z0 : Disjoint (phi (z i 3)) (phi (z i 0)) :=
    (hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))).symm
  have hz3z1 : Disjoint (phi (z i 3)) (phi (z i 1)) :=
    (hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))).symm
  have hz3z2 : Disjoint (phi (z i 3)) (phi (z i 2)) :=
    (hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))).symm
  have hz3colors6 : Disjoint (phi (z i 3)) colors6 := by
    rw [← hpartition6]
    exact Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨hz3z0, hz3z1⟩, hz3z2⟩
  have hz3list : phi (z i 3) ⊆ colors6 ∪ colors78 := by
    intro c hc
    have hc' := hsub (z i 3) hc
    simp [L5, L4, L3, colors8, colors6, colors78] at hc' ⊢
    aesop
  have hz3eq : phi (z i 3) = colors78 :=
    eq_right_of_subset_union_of_disjoint_left hz3list hz3colors6
      (by rw [hcard (z i 3), colors78_card])
  have hz4z3 : Disjoint (phi (z i 4)) (phi (z i 3)) :=
    (hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))).symm
  have hz4colors78 : Disjoint (phi (z i 4)) colors78 := by simpa [hz3eq] using hz4z3
  have hz4list : phi (z i 4) ⊆ colors78 ∪ colors4 := by
    intro c hc
    have hc' := hsub (z i 4) hc
    simp [L5, L4, L3, colors123478, colors4, colors78] at hc' ⊢
    aesop
  have hz4sub4 : phi (z i 4) ⊆ colors4 :=
    subset_right_of_subset_union_of_disjoint_left hz4list hz4colors78
  have hz5sub4 : phi (z i 5) ⊆ colors4 := by
    simpa [L5, L4, L3] using hsub (z i 5)
  have hz4z5 : Disjoint (phi (z i 4)) (phi (z i 5)) :=
    hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))
  have hpartition4 : phi (z i 4) ∪ phi (z i 5) = colors4 :=
    union_eq_of_disjoint_of_card_two_of_subset_four hz4sub4 hz5sub4 hz4z5
      (hcard (z i 4)) (hcard (z i 5)) colors4_card
  have hz6z4 : Disjoint (phi (z i 6)) (phi (z i 4)) :=
    hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))
  have hz6z5 : Disjoint (phi (z i 6)) (phi (z i 5)) :=
    (hdis (zPieceEdge_mem_g5 i (by simp [zPieceEdges]))).symm
  have hz6colors4 : Disjoint (phi (z i 6)) colors4 := by
    rw [← hpartition4]
    exact Finset.disjoint_union_right.mpr ⟨hz6z4, hz6z5⟩
  have hz6list : phi (z i 6) ⊆ colors4 ∪ colors78 := by
    intro c hc
    have hc' := hsub (z i 6) hc
    simp [L5, L4, L3, colors123478, colors4, colors78] at hc' ⊢
    aesop
  exact eq_right_of_subset_union_of_disjoint_left hz6list hz6colors4
    (by rw [hcard (z i 6), colors78_card])

/-- The two `z` blocks together force at least one terminal pair. -/
lemma g3_forces_z_terminal
    {phi : G5Vertex → Finset ℕ} (hphi : IsLMulticoloring g5Graph L5 phi 2) :
    phi (z 0 6) = colors78 ∨ phi (z 1 6) = colors78 := by
  rcases g2_forces_y4 hphi with h7 | h8
  · left
    apply zBlock_forces_terminal hphi 0
    simpa using h7
  · right
    apply zBlock_forces_terminal hphi 1
    simpa using h8

/-- The `G4` forcing chain: both terminal vertices of its two small
triangles receive `{7,8}`. -/
lemma g4_forces_w_terminals
    {phi : G5Vertex → Finset ℕ} (hphi : IsLMulticoloring g5Graph L5 phi 2) :
    phi (wt 0 2) = colors78 ∧ phi (wt 1 2) = colors78 := by
  have hsub (v : G5Vertex) : phi v ⊆ L5 v := (hphi.2 v).1
  have hcard (v : G5Vertex) : (phi v).card = 2 := (hphi.2 v).2
  have hdis {u v : G5Vertex} (h : s(u, v) ∈ g5Edges) :
      Disjoint (phi u) (phi v) := hphi.1 (g5_adj u v h)
  have hw0list : phi (w 0) ⊆ colors78 ∪ colors4 := by
    intro c hc
    have hc' := hsub (w 0) hc
    simp [L5, L4, colors123478, colors4, colors78] at hc' ⊢
    aesop
  have hzforce := g3_forces_z_terminal hphi
  have hw0dis78 : Disjoint (phi (w 0)) colors78 := by
    rcases hzforce with hz0 | hz1
    · have hd : Disjoint (phi (z 0 6)) (phi (w 0)) :=
        hdis (g4BridgeEdge_mem_g5 (by simp [g4BridgeEdges]))
      simpa [hz0] using hd.symm
    · have hd : Disjoint (phi (z 1 6)) (phi (w 0)) :=
        hdis (g4BridgeEdge_mem_g5 (by simp [g4BridgeEdges]))
      simpa [hz1] using hd.symm
  have hw0sub4 : phi (w 0) ⊆ colors4 :=
    subset_right_of_subset_union_of_disjoint_left hw0list hw0dis78
  have hw1sub4 : phi (w 1) ⊆ colors4 := by
    simpa [L5, L4] using hsub (w 1)
  have hw0w1 : Disjoint (phi (w 0)) (phi (w 1)) :=
    hdis (wTriangleEdge_mem_g5 (by simp [wTriangleEdges]))
  have hw01partition : phi (w 0) ∪ phi (w 1) = colors4 :=
    union_eq_of_disjoint_of_card_two_of_subset_four hw0sub4 hw1sub4 hw0w1
      (hcard (w 0)) (hcard (w 1)) colors4_card
  have hw2w0 : Disjoint (phi (w 2)) (phi (w 0)) :=
    hdis (wTriangleEdge_mem_g5 (by simp [wTriangleEdges]))
  have hw2w1 : Disjoint (phi (w 2)) (phi (w 1)) :=
    (hdis (wTriangleEdge_mem_g5 (by simp [wTriangleEdges]))).symm
  have hw2dis4 : Disjoint (phi (w 2)) colors4 := by
    rw [← hw01partition]
    exact Finset.disjoint_union_right.mpr ⟨hw2w0, hw2w1⟩
  have hw2list : phi (w 2) ⊆ colors4 ∪ colors78 := by
    intro c hc
    have hc' := hsub (w 2) hc
    simp [L5, L4, colors123478, colors4, colors78] at hc' ⊢
    aesop
  have hw2eq : phi (w 2) = colors78 :=
    eq_right_of_subset_union_of_disjoint_left hw2list hw2dis4
      (by rw [hcard (w 2), colors78_card])
  have force_small (i : Fin 2) : phi (wt i 2) = colors78 := by
    have hwt0w2 : Disjoint (phi (wt i 0)) (phi (w 2)) :=
      (hdis (g4BridgeEdge_mem_g5 (by fin_cases i <;> simp [g4BridgeEdges]))).symm
    have hwt0dis78 : Disjoint (phi (wt i 0)) colors78 := by
      simpa [hw2eq] using hwt0w2
    have hwt0list : phi (wt i 0) ⊆ colors78 ∪ colors4 := by
      intro c hc
      have hc' := hsub (wt i 0) hc
      simp [L5, L4, colors123478, colors4, colors78] at hc' ⊢
      aesop
    have hwt0sub4 : phi (wt i 0) ⊆ colors4 :=
      subset_right_of_subset_union_of_disjoint_left hwt0list hwt0dis78
    have hwt1sub4 : phi (wt i 1) ⊆ colors4 := by
      simpa [L5, L4] using hsub (wt i 1)
    have hwt0wt1 : Disjoint (phi (wt i 0)) (phi (wt i 1)) :=
      hdis (wtTriangleEdge_mem_g5 i (by simp [wtTriangleEdges]))
    have hwtpartition : phi (wt i 0) ∪ phi (wt i 1) = colors4 :=
      union_eq_of_disjoint_of_card_two_of_subset_four hwt0sub4 hwt1sub4 hwt0wt1
        (hcard (wt i 0)) (hcard (wt i 1)) colors4_card
    have hwt2wt0 : Disjoint (phi (wt i 2)) (phi (wt i 0)) :=
      hdis (wtTriangleEdge_mem_g5 i (by simp [wtTriangleEdges]))
    have hwt2wt1 : Disjoint (phi (wt i 2)) (phi (wt i 1)) :=
      (hdis (wtTriangleEdge_mem_g5 i (by simp [wtTriangleEdges]))).symm
    have hwt2dis4 : Disjoint (phi (wt i 2)) colors4 := by
      rw [← hwtpartition]
      exact Finset.disjoint_union_right.mpr ⟨hwt2wt0, hwt2wt1⟩
    have hwt2list : phi (wt i 2) ⊆ colors4 ∪ colors78 := by
      intro c hc
      have hc' := hsub (wt i 2) hc
      simp [L5, L4, colors123478, colors4, colors78] at hc' ⊢
      aesop
    exact eq_right_of_subset_union_of_disjoint_left hwt2list hwt2dis4
      (by rw [hcard (wt i 2), colors78_card])
  exact ⟨force_small 0, force_small 1⟩

/-- The decisive DHS obstruction: the exact prescribed assignment `L5` has
no two-fold set-colouring of `g5Graph`. -/
theorem g5_no_L5_twoColoring
    (phi : G5Vertex → Finset ℕ) : ¬ IsLMulticoloring g5Graph L5 phi 2 := by
  intro hphi
  have hsub (v : G5Vertex) : phi v ⊆ L5 v := (hphi.2 v).1
  have hcard (v : G5Vertex) : (phi v).card = 2 := (hphi.2 v).2
  have hdis {u v : G5Vertex} (h : s(u, v) ∈ g5Edges) :
      Disjoint (phi u) (phi v) := hphi.1 (g5_adj u v h)
  obtain ⟨hwt0, hwt1⟩ := g4_forces_w_terminals hphi
  have hv2term : Disjoint (phi v2) colors78 := by
    have hd : Disjoint (phi (wt 0 2)) (phi v2) :=
      hdis (crossEdge_mem_g5 (by simp [crossEdges]))
    simpa [hwt0] using hd.symm
  have hv4term : Disjoint (phi v4) colors78 := by
    have hd : Disjoint (phi (wt 0 2)) (phi v4) :=
      hdis (crossEdge_mem_g5 (by simp [crossEdges]))
    simpa [hwt0] using hd.symm
  have hxterm : Disjoint (phi x) colors78 := by
    have hd : Disjoint (phi (wt 1 2)) (phi x) :=
      hdis (crossEdge_mem_g5 (by simp [crossEdges]))
    simpa [hwt1] using hd.symm
  have hyterm : Disjoint (phi y) colors78 := by
    have hd : Disjoint (phi (wt 1 2)) (phi y) :=
      hdis (crossEdge_mem_g5 (by simp [crossEdges]))
    simpa [hwt1] using hd.symm
  have hv2sub : phi v2 ⊆ ({1, 4, 5, 6} : Finset ℕ) := by
    intro c hc
    have hc' := hsub v2 hc
    have hcnot := Finset.disjoint_left.mp hv2term hc
    simp [L5, colors78] at hc' hcnot ⊢
    aesop
  have hv4sub : phi v4 ⊆ ({3, 4, 5, 6} : Finset ℕ) := by
    intro c hc
    have hc' := hsub v4 hc
    have hcnot := Finset.disjoint_left.mp hv4term hc
    simp [L5, colors78] at hc' hcnot ⊢
    aesop
  have hxsub4 : phi x ⊆ colors4 := by
    intro c hc
    have hc' := hsub x hc
    have hcnot := Finset.disjoint_left.mp hxterm hc
    simp [L5, colors123478, colors4, colors78] at hc' hcnot ⊢
    aesop
  have hylist : phi y ⊆ colors78 ∪ ({1, 2} : Finset ℕ) := by
    intro c hc
    have hc' := hsub y hc
    simp [L5, colors78] at hc' ⊢
    aesop
  have hyeq : phi y = ({1, 2} : Finset ℕ) :=
    eq_right_of_subset_union_of_disjoint_left hylist hyterm
      (by rw [hcard y]; decide)
  have hxy : Disjoint (phi x) (phi y) :=
    hdis (g1Edge_mem_g5 (by simp [g1Edges]))
  have hxdis12 : Disjoint (phi x) ({1, 2} : Finset ℕ) := by
    simpa [hyeq] using hxy
  have hxlist : phi x ⊆ ({1, 2} : Finset ℕ) ∪ {3, 4} := by
    intro c hc
    have hc' := hxsub4 hc
    simp [colors4] at hc' ⊢
    aesop
  have hxeq : phi x = ({3, 4} : Finset ℕ) :=
    eq_right_of_subset_union_of_disjoint_left hxlist hxdis12
      (by rw [hcard x]; decide)
  have hv1x : Disjoint (phi v1) (phi x) :=
    hdis (g1Edge_mem_g5 (by simp [g1Edges]))
  have hyv3 : Disjoint (phi y) (phi v3) :=
    hdis (g1Edge_mem_g5 (by simp [g1Edges]))
  have hv1sub : phi v1 ⊆ ({1, 2, 5, 6} : Finset ℕ) := by
    intro c hc
    have hc' := hsub v1 hc
    have hcnot : c ∉ ({3, 4} : Finset ℕ) := by
      rw [← hxeq]
      exact Finset.disjoint_left.mp hv1x hc
    simp [L5, L4, L3, L2, colors6] at hc'
    simp at hcnot ⊢
    aesop
  have hv3sub : phi v3 ⊆ ({3, 4, 5, 6} : Finset ℕ) := by
    intro c hc
    have hc' := hsub v3 hc
    have hcnot : c ∉ ({1, 2} : Finset ℕ) := by
      rw [← hyeq]
      exact Finset.disjoint_left.mp hyv3.symm hc
    simp [L5, L4, L3, L2, colors6] at hc'
    simp at hcnot ⊢
    aesop
  have hv5sub : phi v5 ⊆ ({2, 4, 5, 6} : Finset ℕ) := by
    simpa [L5] using hsub v5
  exact no_baseCycle_twoColoring (phi v1) (phi v2) (phi v3) (phi v4) (phi v5)
    hv1sub hv2sub hv3sub hv4sub hv5sub
    (hcard v1) (hcard v2) (hcard v3) (hcard v4) (hcard v5)
    (hdis (g1Edge_mem_g5 (by simp [g1Edges])))
    (hdis (g1Edge_mem_g5 (by simp [g1Edges])))
    (hdis (g1Edge_mem_g5 (by simp [g1Edges])))
    (hdis (g1Edge_mem_g5 (by simp [g1Edges])))
    (hdis (g1Edge_mem_g5 (by simp [g1Edges])))

/-- Existential form consumed by the uniformization argument. -/
theorem g5_not_twoColorable :
    ¬ ∃ phi : G5Vertex → Finset ℕ, IsLMulticoloring g5Graph L5 phi 2 := by
  rintro ⟨phi, hphi⟩
  exact g5_no_L5_twoColoring phi hphi

end Erdos632

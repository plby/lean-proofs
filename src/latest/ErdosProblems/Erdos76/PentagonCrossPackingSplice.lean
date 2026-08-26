/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PentagonAvoidingPairFamily
import ErdosProblems.Erdos76.PentagonBadPackingAssembly
import ErdosProblems.Erdos76.InducedTransport

/-! # Reserving the old edges of a packing through a new vertex -/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- In a balanced pentagon blow-up, an integral cross-blob packing through
one new vertex can be spliced into a full base fractional packing. -/
theorem pentagonBlowup_splice_crossPacking
    {G : SimpleGraph α} {S : Finset α} {u : α} (hu : u ∉ S)
    {blob : S → Fin 5}
    (hG : IsPentagonBlowup (G.induce (S : Set α)) blob)
    (hsize : ∀ i, 3 ≤ (pentagonBlobFinset blob i).card)
    (hbalance : ∀ i j, (pentagonBlobFinset blob i).card ≤
      (pentagonBlobFinset blob j).card + 1)
    {P : Finset (Finset α)} (hP : IsMonochromaticPacking G P)
    (hthrough : ∀ t ∈ P, ∃ x y : S, blob x ≠ blob y ∧ t = {u, x.1, y.1}) :
    ∃ wR wB : Finset α → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
      fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB =
        3 * ((∑ i : Fin 5, ((pentagonBlobFinset blob i).card.choose 2 : ℝ)) +
          (P.card : ℝ)) := by
  classical
  have hchoice : ∀ p : P, ∃ x y : S,
      blob x ≠ blob y ∧ p.1 = {u, x.1, y.1} := fun p ↦ hthrough p.1 p.2
  choose x y hlabels htri using hchoice
  let oldEdge : P → Sym2 S := fun p ↦ s(x p, y p)
  let M : Finset (Sym2 S) := univ.image oldEdge
  have hmem : ∀ p : P, oldEdge p ∈ M := fun p ↦ mem_image.mpr ⟨p, mem_univ p, rfl⟩
  have hpair : (M : Set (Sym2 S)).PairwiseDisjoint fun e ↦ e.toFinset := by
    intro e he f hf hef
    obtain ⟨p, _, rfl⟩ := mem_image.mp he
    obtain ⟨q, _, rfl⟩ := mem_image.mp hf
    apply Finset.disjoint_left.mpr
    intro z hzP hzQ
    have hpq : p.1 ≠ q.1 := by
      intro h
      exact hef (congrArg oldEdge (Subtype.ext h))
    have hzP' : z.1 ∈ p.1 := by
      rw [htri p]
      have hz : z = x p ∨ z = y p := by simpa [oldEdge] using hzP
      rcases hz with rfl | rfl <;> simp
    have hzQ' : z.1 ∈ q.1 := by
      rw [htri q]
      have hz : z = x q ∨ z = y q := by simpa [oldEdge] using hzQ
      rcases hz with rfl | rfl <;> simp
    have huz : u ≠ z.1 := fun h ↦ hu (h ▸ z.2)
    have hsub : ({u, z.1} : Finset α) ⊆ p.1 ∩ q.1 := by
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact mem_inter.mpr ⟨by rw [htri p]; simp, by rw [htri q]; simp⟩
      · have haz : a = z.1 := mem_singleton.mp ha
        subst a
        exact mem_inter.mpr ⟨hzP', hzQ'⟩
    have htwo := card_le_card hsub
    have hone := hP.2 p.2 q.2 hpq
    have hcard : ({u, z.1} : Finset α).card = 2 := by simp [huz]
    rw [hcard] at htwo
    omega
  have hcross : ∀ a b : S, s(a, b) ∈ M → blob a ≠ blob b := by
    intro a b hab
    obtain ⟨p, _, hp⟩ := mem_image.mp hab
    rcases Sym2.eq_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hlabels p
    · exact (hlabels p).symm
  obtain ⟨vR, vB, hvR, hvB, hbase, hzeroR, hzeroB⟩ :=
    pentagonBlowup_basePacking_avoiding_crossMatching hG hsize hbalance hpair hcross
  have hzero (K : SimpleGraph α) (w : Finset S → ℝ)
      (hw : ∀ e ∈ M, fractionalEdgeLoad (K.induce (S : Set α)) w e = 0)
      (e : Sym2 α) (heK : e ∈ K.edgeSet) (heP : e ∈ packingPairFinset P) :
      fractionalEdgeLoad K (extendInducedWeight S w) e = 0 := by
    obtain ⟨t, ht, het⟩ := mem_packingPairFinset.mp heP
    let p : P := ⟨t, ht⟩
    have htp : t = {u, (x p).1, (y p).1} := htri p
    rw [htp] at het
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : a ≠ b := (show K.Adj a b from heK).ne
      have hends := Finset.mk_mem_sym2_iff.mp het
      by_cases hau : a = u
      · subst a
        exact fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem K S w u b hu
      by_cases hbu : b = u
      · subst b
        rw [Sym2.eq_swap]
        exact fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem K S w u a hu
      have ha : a = (x p).1 ∨ a = (y p).1 := by
        simpa [hau] using hends.1
      have hb : b = (x p).1 ∨ b = (y p).1 := by
        simpa [hbu] using hends.2
      have hold : fractionalEdgeLoad K (extendInducedWeight S w)
          s((x p).1, (y p).1) = 0 := by
        change fractionalEdgeLoad K (extendInducedWeight S w)
          ((inducedEmbedding S).sym2Map (oldEdge p)) = 0
        rw [fractionalEdgeLoad_extendInducedWeight]
        exact hw (oldEdge p) (hmem p)
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hold
      · simpa only [Sym2.eq_swap] using hold
      · exact (hab rfl).elim
  have hExt := extendInduced_pair hvR hvB
  have hzeroB' : ∀ e ∈ M,
      fractionalEdgeLoad (Gᶜ.induce (S : Set α)) vB e = 0 := by
    intro e he
    rw [compl_induce]
    exact hzeroB e he
  obtain ⟨wR, wB, hwR, hwB, htotal⟩ :=
    exists_twoColorPacking_add_monochromaticPacking hP
      (extendInducedWeight S vR) (extendInducedWeight S vB) hExt.1 hExt.2.1
      (fun e he heP ↦ hzero G vR hzeroR e he (by
        obtain ⟨t, ht, het⟩ := mem_packingPairFinset.mp heP
        exact mem_packingPairFinset.mpr ⟨t, (mem_filter.mp ht).1, het⟩))
      (fun e he heP ↦ hzero Gᶜ vB hzeroB' e he (by
        obtain ⟨t, ht, het⟩ := mem_packingPairFinset.mp heP
        exact mem_packingPairFinset.mpr ⟨t, (mem_filter.mp ht).1, het⟩))
  refine ⟨wR, wB, hwR, hwB, ?_⟩
  rw [htotal, hExt.2.2, hbase]
  push_cast
  ring

/-- The smallest blob gives a guaranteed gain over the full fractional base
packing when the old blob sizes are at least three and differ by at most one. -/
theorem pentagonBlowup_extension_coveredSize
    {G : SimpleGraph α} {S : Finset α} {u : α} (hu : u ∉ S)
    {blob : S → Fin 5} {m : ℕ}
    (hG : IsPentagonBlowup (G.induce (S : Set α)) blob)
    (hsize : ∀ i, 3 ≤ (pentagonBlobFinset blob i).card)
    (hbalance : ∀ i j, (pentagonBlobFinset blob i).card ≤
      (pentagonBlobFinset blob j).card + 1)
    (hmin : ∀ i, m ≤ (pentagonBlobFinset blob i).card) :
    ∃ wR wB : Finset α → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
      fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB =
        3 * ((∑ i : Fin 5, ((pentagonBlobFinset blob i).card.choose 2 : ℝ)) +
          (m : ℝ)) := by
  classical
  have hchoice : ∀ i : Fin 5, ∃ f : Fin m ↪ S, ∀ a, blob (f a) = i := by
    intro i
    obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
      (show Fintype.card (Fin m) ≤ (pentagonBlobFinset blob i).card by
        simpa using hmin i)
    exact ⟨f, fun a ↦ mem_pentagonBlobFinset.mp (hf ⟨a, rfl⟩)⟩
  choose f hf using hchoice
  let v : Fin m → Fin 5 → α := fun a i ↦ (f i a).1
  have hv : Function.Injective (fun p : Fin m × Fin 5 ↦ v p.1 p.2) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    have hold : f i a = f j b := Subtype.ext h
    have hij : i = j := (hf i a).symm.trans ((congrArg blob hold).trans (hf j b))
    subst j
    exact Prod.ext ((f i).injective hold) rfl
  have hu' : ∀ a i, u ≠ v a i := by
    intro a i h
    exact hu (h ▸ (f i a).2)
  have hcross : ∀ a i j, i ≠ j →
      (G.Adj (v a i) (v a j) ↔ (SimpleGraph.cycleGraph 5).Adj i j) := by
    intro a i j hij
    have hlabels : blob (f i a) ≠ blob (f j a) := by simpa only [hf] using hij
    simpa only [hf, v, SimpleGraph.induce_adj] using hG.2 hlabels
  obtain ⟨P, hP, hcard, hthrough⟩ :=
    exists_packing_through_disjoint_pentagonTransversals v hv hu' hcross
  have hthrough' : ∀ t ∈ P, ∃ x y : S,
      blob x ≠ blob y ∧ t = {u, x.1, y.1} := by
    intro t ht
    obtain ⟨_, a, i, j, hij, rfl⟩ := hthrough t ht
    exact ⟨f i a, f j a, by simpa only [hf] using hij, rfl⟩
  obtain ⟨wR, wB, hwR, hwB, htotal⟩ :=
    pentagonBlowup_splice_crossPacking hu hG hsize hbalance hP hthrough'
  exact ⟨wR, wB, hwR, hwB, by simpa only [hcard] using htotal⟩

/-- Five blobs of order five cannot extend to a coloring below the order-26
stability threshold: the old base plus five new triangles covers 165 edges. -/
theorem not_upper_of_five_equal_pentagon_blobs
    {G : SimpleGraph α} {S : Finset α} {u : α} (hu : u ∉ S)
    {blob : S → Fin 5}
    (hG : IsPentagonBlowup (G.induce (S : Set α)) blob)
    (hsize : ∀ i, (pentagonBlobFinset blob i).card = 5) :
    ¬FractionalCoveredSizeAtMost G (26 * 25 / 4) := by
  obtain ⟨wR, wB, hwR, hwB, htotal⟩ :=
    pentagonBlowup_extension_coveredSize (m := 5) hu hG
      (by intro i; rw [hsize]; omega)
      (by intro i j; rw [hsize, hsize]; omega)
      (by intro i; rw [hsize])
  norm_num [hsize, Nat.choose] at htotal
  intro hupper
  have hle := hupper wR wB hwR hwB
  unfold twoColorCoveredSize at hle
  linarith

end

end Erdos76

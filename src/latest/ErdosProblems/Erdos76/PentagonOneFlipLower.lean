/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0
-/
import ErdosProblems.Erdos76.PentagonAvoidingPairFamily

/-!
# The constructive lower bound for a one-edge flip

We formalize the construction in Proposition 7.4(b).  In the paper's
orientation, `z`, `y`, and `x` lie in blobs `0`, `1`, and `4`.  The red
adjacent-pair packings reserve `zy` and `xz`; the blue distance-two packing
reserves the flipped pair `xy`.  The red triangle `xyz` is then added with
unit weight.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The two adjacent red pair packings which meet the added triangle reserve
one of its edges. -/
def oneFlipRedAvoid (x y z : α) : Fin 5 → Finset (Sym2 α) :=
  ![{s(z, y)}, ∅, ∅, ∅, {s(x, z)}]

/-- The flipped distance-two pair is absent from the blue graph. -/
def oneFlipBlueMissing (x y : α) : Fin 5 → Finset (Sym2 α) :=
  ![∅, ∅, ∅, ∅, {s(x, y)}]

private lemma singleton_isABCrossMatching
    {A B : Finset α} (hAB : Disjoint A B)
    {a b : α} (ha : a ∈ A) (hb : b ∈ B) :
    IsABCrossMatching A B {s(a, b)} := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he hsame
    have heq : e = s(a, b) := by simpa using he
    subst e
    have hbA : b ∉ A := fun hbA ↦
      Finset.disjoint_left.mp hAB hbA hb
    exact hbA (by simpa [sameSide_mk, ha] using hsame)
  · intro e he f hf hef
    simp at he hf
    exact (hef (he.trans hf.symm)).elim
  · intro e he
    have heq : e = s(a, b) := by simpa using he
    subst e
    intro v hv
    rw [Sym2.toFinset_mk_eq] at hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_union_left B ha
    · have : v = b := by simpa using hv
      subst v
      exact mem_union_right A hb

private lemma empty_isABCrossMatching (A B : Finset α) :
    IsABCrossMatching A B ∅ := by
  simp [IsABCrossMatching, IsCrossMatching]

private lemma sym2_ne_of_label_pair_ne
    {blob : α → Fin 5} {u v x y : α}
    (h : s(blob u, blob v) ≠ s(blob x, blob y)) :
    s(u, v) ≠ s(x, y) := by
  intro huv
  apply h
  rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

lemma oneFlipRedAvoid_isABCrossMatching
    {blob : α → Fin 5} {x y z : α}
    (hx : x ∈ pentagonBlobFinset blob 4)
    (hy : y ∈ pentagonBlobFinset blob 1)
    (hz : z ∈ pentagonBlobFinset blob 0) (i : Fin 5) :
    IsABCrossMatching (pentagonBlobFinset blob i)
      (pentagonBlobFinset blob (pentagonNext i))
      (oneFlipRedAvoid x y z i) := by
  fin_cases i
  · exact singleton_isABCrossMatching
      (pentagonBlobFinset_disjoint blob (by decide : (0 : Fin 5) ≠ 1)) hz hy
  · exact empty_isABCrossMatching _ _
  · exact empty_isABCrossMatching _ _
  · exact empty_isABCrossMatching _ _
  · exact singleton_isABCrossMatching
      (pentagonBlobFinset_disjoint blob (by decide : (4 : Fin 5) ≠ 0)) hx hz

lemma oneFlipBlueMissing_isABCrossMatching
    {blob : α → Fin 5} {x y : α}
    (hx : x ∈ pentagonBlobFinset blob 4)
    (hy : y ∈ pentagonBlobFinset blob 1) (i : Fin 5) :
    IsABCrossMatching (pentagonBlobFinset blob i)
      (pentagonBlobFinset blob (pentagonSkip i))
      (oneFlipBlueMissing x y i) := by
  fin_cases i
  · exact empty_isABCrossMatching _ _
  · exact empty_isABCrossMatching _ _
  · exact empty_isABCrossMatching _ _
  · exact empty_isABCrossMatching _ _
  · exact singleton_isABCrossMatching
      (pentagonBlobFinset_disjoint blob (by decide : (4 : Fin 5) ≠ 1)) hx hy

/-- Every genuine edge of the added triangle is either one of the two edges
reserved by the adjacent-pair construction or lies outside the displayed
adjacent blob pair.  The non-diagonal hypothesis is essential because
`Finset.sym2` also contains the three diagonal pairs. -/
lemma oneFlipRedAvoid_reserves_triangle_edges
    {blob : α → Fin 5} {x y z : α}
    (hx : x ∈ pentagonBlobFinset blob 4)
    (hy : y ∈ pentagonBlobFinset blob 1)
    (hz : z ∈ pentagonBlobFinset blob 0)
    {e : Sym2 α} (he : e ∈ ({x, y, z} : Finset α).sym2)
    (heND : ¬e.IsDiag) (i : Fin 5) :
    e ∈ oneFlipRedAvoid x y z i ∨
      ¬e.toFinset ⊆ pentagonBlobFinset blob i ∪
        pentagonBlobFinset blob (pentagonNext i) := by
  classical
  have hbx : blob x = 4 := mem_pentagonBlobFinset.mp hx
  have hby : blob y = 1 := mem_pentagonBlobFinset.mp hy
  have hbz : blob z = 0 := mem_pentagonBlobFinset.mp hz
  induction e using Sym2.inductionOn with
  | hf u v =>
      have huv : u ≠ v := by
        simpa [Sym2.mk_isDiag_iff] using heND
      have huvMem := Finset.mk_mem_sym2_iff.mp he
      simp only [mem_insert, mem_singleton] at huvMem
      rcases huvMem.1 with rfl | rfl | rfl <;>
        rcases huvMem.2 with rfl | rfl | rfl <;>
        fin_cases i <;>
        simp_all [oneFlipRedAvoid, pentagonNext, Sym2.toFinset_mk_eq,
          subset_iff, mem_pentagonBlobFinset, Sym2.eq_iff]

/-- Assembly form of Proposition 7.4(b)'s lower bound.  The cross-colour
hypotheses are exactly what the oriented single flip supplies; `hreserve`
records the elementary fact that every edge of `xyz` was reserved from all
five red pair packings. -/
theorem twoColorCoveredSize_oneFlip_oriented_ge
    {G : SimpleGraph α} {blob : α → Fin 5} {x y z : α}
    (hsizes : PentagonB2Sizes
      (fun i ↦ (pentagonBlobFinset blob i).card))
    (hx : x ∈ pentagonBlobFinset blob 4)
    (hy : y ∈ pentagonBlobFinset blob 1)
    (hz : z ∈ pentagonBlobFinset blob 0)
    (hRedCross : ∀ i : Fin 5,
      ∀ u : pentagonBlobFinset blob i,
      ∀ v : pentagonBlobFinset blob (pentagonNext i), G.Adj u.1 v.1)
    (hBlueCross : ∀ i : Fin 5,
      ∀ u : pentagonBlobFinset blob i,
      ∀ v : pentagonBlobFinset blob (pentagonSkip i),
        Gᶜ.Adj u.1 v.1 ↔ s(u.1, v.1) ∉ oneFlipBlueMissing x y i)
    (hTriangle : G.IsNClique 3 {x, y, z})
    (hreserve : ∀ e ∈ ({x, y, z} : Finset α).sym2, ¬e.IsDiag → ∀ i : Fin 5,
      e ∈ oneFlipRedAvoid x y z i ∨
        ¬e.toFinset ⊆ pentagonBlobFinset blob i ∪
          pentagonBlobFinset blob (pentagonNext i)) :
    ∃ wR wB : Finset α → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
      fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB =
        3 * ((∑ i : Fin 5,
          ((pentagonBlobFinset blob i).card.choose 2 : ℕ)) + 1) := by
  classical
  have hRedData : ∀ i : Fin 5, Nonempty
      (TwoBlobAvoidingPackingData G
        (pentagonBlobFinset blob i)
        (pentagonBlobFinset blob (pentagonNext i))
        (oneFlipRedAvoid x y z i)) := by
    intro i
    exact exists_twoBlobAvoidingPackingData
      (pentagonBlobFinset_disjoint blob (pentagonNext_ne i).symm)
      (oneFlipRedAvoid_isABCrossMatching hx hy hz i)
      (hRedCross i)
      (pentagonB2Sizes_lower_bound hsizes i)
      (pentagonB2Sizes_lower_bound hsizes (pentagonNext i))
      (pentagonB2Sizes_pair_bound hsizes i (pentagonNext i))
      (pentagonB2Sizes_pair_bound hsizes (pentagonNext i) i)
  let DR : ∀ i : Fin 5, TwoBlobAvoidingPackingData G
      (pentagonBlobFinset blob i)
      (pentagonBlobFinset blob (pentagonNext i))
      (oneFlipRedAvoid x y z i) := fun i ↦ Classical.choice (hRedData i)
  have hBlueData : ∀ i : Fin 5, Nonempty
      (TwoBlobAvoidingPackingData Gᶜ
        (pentagonBlobFinset blob i)
        (pentagonBlobFinset blob (pentagonSkip i))
        (oneFlipBlueMissing x y i)) := by
    intro i
    exact exists_twoBlobMissingMatchingPackingData
      (pentagonBlobFinset_disjoint blob (pentagonSkip_ne i).symm)
      (oneFlipBlueMissing_isABCrossMatching hx hy i)
      (hBlueCross i)
      (pentagonB2Sizes_lower_bound hsizes i)
      (pentagonB2Sizes_lower_bound hsizes (pentagonSkip i))
      (pentagonB2Sizes_pair_bound hsizes i (pentagonSkip i))
      (pentagonB2Sizes_pair_bound hsizes (pentagonSkip i) i)
  let DB : ∀ i : Fin 5, TwoBlobAvoidingPackingData Gᶜ
      (pentagonBlobFinset blob i)
      (pentagonBlobFinset blob (pentagonSkip i))
      (oneFlipBlueMissing x y i) := fun i ↦ Classical.choice (hBlueData i)
  let redBase := pentagonAvoidingPairFamilyWeight
    pentagonNext (oneFlipRedAvoid x y z) DR
  let blue := pentagonAvoidingPairFamilyWeight
    pentagonSkip (oneFlipBlueMissing x y) DB
  let T : Finset α := {x, y, z}
  let red := addTriangleWeight redBase (integralPackingWeight {T})
  have hRedBase : IsFractionalPacking G redBase :=
    isFractionalPacking_pentagonAvoidingNextFamily DR
  have hRedZero : ∀ e ∈ T.sym2,
      ¬e.IsDiag → fractionalEdgeLoad G redBase e = 0 := by
    intro e he heND
    exact fractionalEdgeLoad_pentagonAvoidingPairFamily_eq_zero
      DR (hreserve e he heND)
  have hRed : IsFractionalPacking G red :=
    isFractionalPacking_add_integralSingleton_of_zero_load
      hRedBase hTriangle hRedZero
  have hBlue : IsFractionalPacking Gᶜ blue :=
    isFractionalPacking_pentagonAvoidingSkipFamily DB
  refine ⟨red, blue, hRed, hBlue, ?_⟩
  have hRedBaseSize : fractionalSize G redBase =
      ∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) :=
    fractionalSize_pentagonAvoidingNextFamily DR
  have hRedSize : fractionalSize G red =
      (∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ)) + 1 := by
    rw [show red = addTriangleWeight redBase
      (integralPackingWeight {T}) by rfl,
      fractionalSize_add_integralSingleton redBase hTriangle,
      hRedBaseSize]
  have hBlueSize : fractionalSize Gᶜ blue =
      ∑ i : Fin 5,
        ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ) :=
    fractionalSize_pentagonAvoidingSkipFamily DB
  rw [fractionalCoveredSize, fractionalCoveredSize, hRedSize, hBlueSize]
  push_cast
  calc
    3 * ((∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ)) + 1) +
        3 * (∑ i : Fin 5,
          ((blobPairFinset Gᶜ
            (pentagonBlobFinset blob i)).card : ℝ)) =
      3 * ((∑ i : Fin 5,
        (((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) +
          ((blobPairFinset Gᶜ
            (pentagonBlobFinset blob i)).card : ℝ))) + 1) := by
      rw [sum_add_distrib]
      ring
    _ = 3 * ((∑ i : Fin 5,
          ((pentagonBlobFinset blob i).card.choose 2 : ℝ)) + 1) := by
      congr 2
      apply sum_congr rfl
      intro i _
      exact_mod_cast card_blobPairFinset_add_compl G
        (pentagonBlobFinset blob i)

/-- Constructive lower bound for the paper's oriented one-edge flip.  The
reference blow-up has the flipped pair blue, while `G` is obtained by making
that single pair red. -/
theorem twoColorCoveredSize_oneFlip_oriented_from_blowup_ge
    {G H : SimpleGraph α} {blob : α → Fin 5} {x y z : α}
    (hH : IsPentagonBlowup H blob)
    (hsizes : PentagonB2Sizes
      (fun i ↦ (pentagonBlobFinset blob i).card))
    (hx : x ∈ pentagonBlobFinset blob 4)
    (hy : y ∈ pentagonBlobFinset blob 1)
    (hz : z ∈ pentagonBlobFinset blob 0)
    (hflip : ∀ {u v : α},
      G.Adj u v ↔ H.Adj u v ∨ s(u, v) = s(x, y)) :
    ∃ wR wB : Finset α → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
      fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB =
        3 * ((∑ i : Fin 5,
          ((pentagonBlobFinset blob i).card.choose 2 : ℕ)) + 1) := by
  classical
  have hRedCross : ∀ i : Fin 5,
      ∀ u : pentagonBlobFinset blob i,
      ∀ v : pentagonBlobFinset blob (pentagonNext i), G.Adj u.1 v.1 := by
    intro i u v
    exact hflip.mpr (Or.inl
      (pentagonBlowup_next_cross hH i u.1 u.2 v.1 v.2))
  have hBlueCross : ∀ i : Fin 5,
      ∀ u : pentagonBlobFinset blob i,
      ∀ v : pentagonBlobFinset blob (pentagonSkip i),
        Gᶜ.Adj u.1 v.1 ↔
          s(u.1, v.1) ∉ oneFlipBlueMissing x y i := by
    intro i u v
    have hHc : Hᶜ.Adj u.1 v.1 :=
      pentagonBlowup_skip_cross_compl hH i u.1 u.2 v.1 v.2
    have hmissing :
        s(u.1, v.1) ∉ oneFlipBlueMissing x y i ↔
          s(u.1, v.1) ≠ s(x, y) := by
      have hbx : blob x = 4 := mem_pentagonBlobFinset.mp hx
      have hby : blob y = 1 := mem_pentagonBlobFinset.mp hy
      have hbu : blob u.1 = i := mem_pentagonBlobFinset.mp u.2
      have hbv : blob v.1 = pentagonSkip i :=
        mem_pentagonBlobFinset.mp v.2
      by_cases hi : i = 4
      · subst i
        simp [oneFlipBlueMissing]
      · have hlabelPair :
            s(blob u.1, blob v.1) ≠ s(blob x, blob y) := by
          rw [hbu, hbv, hbx, hby]
          intro heq
          have heq' : s(i, pentagonSkip i) =
              s((4 : Fin 5), pentagonSkip 4) := by
            simpa [pentagonSkip] using heq
          exact hi ((pentagonSkip_pair_unique i 4).mp heq')
        have hpair : s(u.1, v.1) ≠ s(x, y) :=
          sym2_ne_of_label_pair_ne hlabelPair
        have hempty : oneFlipBlueMissing x y i = ∅ := by
          fin_cases i <;> simp_all [oneFlipBlueMissing]
        rw [hempty]
        simp [hpair]
    rw [hmissing, SimpleGraph.compl_adj]
    constructor
    · rintro ⟨_, huvG⟩ huvEq
      exact huvG (hflip.mpr (Or.inr huvEq))
    · intro huvEq
      refine ⟨hHc.1, ?_⟩
      intro huvG
      rcases hflip.mp huvG with huvH | huvFlip
      · exact hHc.2 huvH
      · exact huvEq huvFlip
  have hxyG : G.Adj x y := hflip.mpr (Or.inr rfl)
  have hxzH : H.Adj x z :=
    pentagonBlowup_next_cross hH (4 : Fin 5) x hx z
      (by simpa [pentagonNext] using hz)
  have hzyH : H.Adj z y :=
    pentagonBlowup_next_cross hH (0 : Fin 5) z hz y
      (by simpa [pentagonNext] using hy)
  have hxzG : G.Adj x z := hflip.mpr (Or.inl hxzH)
  have hzyG : G.Adj z y := hflip.mpr (Or.inl hzyH)
  have hTriangle : G.IsNClique 3 ({x, y, z} : Finset α) := by
    constructor
    · rw [SimpleGraph.isClique_iff]
      intro u hu v hv huv
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl | rfl <;>
        rcases hv with rfl | rfl | rfl
      · exact (huv rfl).elim
      · exact hxyG
      · exact hxzG
      · exact hxyG.symm
      · exact (huv rfl).elim
      · exact hzyG.symm
      · exact hxzG.symm
      · exact hzyG
      · exact (huv rfl).elim
    · simp [hxyG.ne, hxzG.ne, hzyG.ne.symm]
  exact twoColorCoveredSize_oneFlip_oriented_ge hsizes hx hy hz
    hRedCross hBlueCross hTriangle
    (fun e he heND i ↦
      oneFlipRedAvoid_reserves_triangle_edges hx hy hz he heND i)

/-- Graph-operation form of the oriented lower bound: adjoining the blue
distance-two edge `xy` to the reference blow-up produces packings attaining
the claimed one-flip objective. -/
theorem twoColorCoveredSize_sup_edge_oriented_ge
    {H : SimpleGraph α} {blob : α → Fin 5} {x y z : α}
    (hH : IsPentagonBlowup H blob)
    (hsizes : PentagonB2Sizes
      (fun i ↦ (pentagonBlobFinset blob i).card))
    (hx : x ∈ pentagonBlobFinset blob 4)
    (hy : y ∈ pentagonBlobFinset blob 1)
    (hz : z ∈ pentagonBlobFinset blob 0) :
    ∃ wR wB : Finset α → ℝ,
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y) wR ∧
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y)ᶜ wB ∧
      fractionalCoveredSize (H ⊔ SimpleGraph.edge x y) wR +
          fractionalCoveredSize (H ⊔ SimpleGraph.edge x y)ᶜ wB =
        3 * ((∑ i : Fin 5,
          ((pentagonBlobFinset blob i).card.choose 2 : ℕ)) + 1) := by
  have hxy : x ≠ y := by
    intro h
    subst y
    exact (by decide : (4 : Fin 5) ≠ 1)
      ((mem_pentagonBlobFinset.mp hx).symm.trans
        (mem_pentagonBlobFinset.mp hy))
  apply twoColorCoveredSize_oneFlip_oriented_from_blowup_ge
    hH hsizes hx hy hz
  intro u v
  rw [SimpleGraph.sup_adj, SimpleGraph.adj_edge]
  constructor
  · rintro (huvH | ⟨huv, _⟩)
    · exact Or.inl huvH
    · exact Or.inr huv.symm
  · rintro (huvH | huv)
    · exact Or.inl huvH
    · right
      refine ⟨huv.symm, ?_⟩
      rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy
      · exact hxy.symm

lemma edgeFlipDistance_sup_edge_eq_one
    (H : SimpleGraph α) {x y : α}
    (hxyH : ¬H.Adj x y) (hxy : x ≠ y) :
    edgeFlipDistance (H ⊔ SimpleGraph.edge x y) H = 1 := by
  classical
  let ef (G : SimpleGraph α) : Finset (Sym2 α) :=
    @SimpleGraph.edgeFinset α G
      (@SimpleGraph.fintypeEdgeSet α G inferInstance
        (fun a b ↦ Classical.propDecidable (G.Adj a b)))
  unfold edgeFlipDistance
  change #(ef (H ⊔ SimpleGraph.edge x y) \ ef H) +
    #(ef H \ ef (H ⊔ SimpleGraph.edge x y)) = 1
  have hnew :
      ef (H ⊔ SimpleGraph.edge x y) \ ef H = {s(x, y)} := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [ef, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, SimpleGraph.sup_adj, SimpleGraph.adj_edge,
          Finset.mem_singleton]
        constructor
        · rintro ⟨huvH | ⟨huv, _⟩, hnH⟩
          · exact (hnH huvH).elim
          · exact huv.symm
        · intro huv
          rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨Or.inr ⟨rfl, hxy⟩, hxyH⟩
          · exact ⟨Or.inr ⟨Sym2.eq_swap, hxy.symm⟩, fun h ↦ hxyH h.symm⟩
  have hold : ef H \ ef (H ⊔ SimpleGraph.edge x y) = ∅ := by
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    intro e he
    simp only [ef, SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono le_sup_left he
  rw [hnew, hold]
  simp

/-- Exact oriented form of Proposition 7.4(b): the displayed construction
attains the dual upper bound for the one-edge extension of a `B₂` pentagon
blow-up. -/
theorem twoColorCoveredSize_sup_edge_oriented_exact
    {H : SimpleGraph α} {blob : α → Fin 5} {x y z : α}
    (hH : IsPentagonBlowup H blob)
    (hsizes : PentagonB2Sizes
      (fun i ↦ (pentagonBlobFinset blob i).card))
    (hx : x ∈ pentagonBlobFinset blob 4)
    (hy : y ∈ pentagonBlobFinset blob 1)
    (hz : z ∈ pentagonBlobFinset blob 0) :
    (∃ wR wB : Finset α → ℝ,
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y) wR ∧
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y)ᶜ wB ∧
      fractionalCoveredSize (H ⊔ SimpleGraph.edge x y) wR +
          fractionalCoveredSize (H ⊔ SimpleGraph.edge x y)ᶜ wB =
        3 * ((∑ i : Fin 5,
          ((pentagonBlobFinset blob i).card.choose 2 : ℕ)) + 1)) ∧
    (∀ wR wB : Finset α → ℝ,
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y) wR →
      IsFractionalPacking (H ⊔ SimpleGraph.edge x y)ᶜ wB →
      fractionalCoveredSize (H ⊔ SimpleGraph.edge x y) wR +
          fractionalCoveredSize (H ⊔ SimpleGraph.edge x y)ᶜ wB ≤
        3 * ((∑ i : Fin 5,
          ((pentagonBlobFinset blob i).card.choose 2 : ℕ)) + 1)) := by
  have hxyHc : Hᶜ.Adj x y :=
    pentagonBlowup_skip_cross_compl hH (4 : Fin 5) x hx y
      (by simpa [pentagonSkip] using hy)
  have hdist : edgeFlipDistance (H ⊔ SimpleGraph.edge x y) H = 1 :=
    edgeFlipDistance_sup_edge_eq_one H hxyHc.2 hxyHc.1
  constructor
  · exact twoColorCoveredSize_sup_edge_oriented_ge hH hsizes hx hy hz
  · intro wR wB hwR hwB
    exact twoColorCoveredSize_oneFlipFromPentagonBlowup_le
      hH hdist hwR hwB

end

end Erdos76

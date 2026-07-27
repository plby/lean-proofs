import Util.Ramsey

/-!
# Optimizing the CGMS upper bound on Ramsey numbers

This directory formalizes Gupta--Ndiaye--Norin--Wei,
*Optimizing the CGMS upper bound on Ramsey numbers* (arXiv:2407.19026).

This file contains the finite graph-theoretic definitions used throughout the
paper.
-/

open Finset

noncomputable section

namespace Arxiv2407_19026

/-- The two-color Ramsey property used in arXiv:2407.19026. -/
abbrev RamseyProperty := Ramsey.RamseyProperty

/-- The off-diagonal Ramsey number `R(k, l)`. -/
abbrev ramseyNumber := Ramsey.ramseyNumber

/-- The indicator of a red edge. A simple graph represents the red edges;
its complement represents the blue edges. -/
def redIndicator {V : Type*} (G : SimpleGraph V) (u v : V) : ℕ :=
  by
    classical
    exact if G.Adj u v then 1 else 0

@[simp]
lemma redIndicator_of_adj {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Adj u v) : redIndicator G u v = 1 := by
  simp [redIndicator, h]

@[simp]
lemma redIndicator_of_not_adj {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : ¬G.Adj u v) : redIndicator G u v = 0 := by
  simp [redIndicator, h]

lemma redIndicator_comm {V : Type*} (G : SimpleGraph V) (u v : V) :
    redIndicator G u v = redIndicator G v u := by
  classical
  unfold redIndicator
  rw [G.adj_comm]

/-- The number `e_R(X,Y)` of red edges with one endpoint in `X` and one in
`Y`.  For disjoint sets each edge is counted exactly once. -/
def redEdgesBetween {V : Type*} (G : SimpleGraph V) (X Y : Finset V) : ℕ :=
  ∑ u ∈ X, ∑ v ∈ Y, redIndicator G u v

lemma redEdgesBetween_comm {V : Type*} (G : SimpleGraph V) (X Y : Finset V) :
    redEdgesBetween G X Y = redEdgesBetween G Y X := by
  simp only [redEdgesBetween]
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  apply sum_congr rfl
  intro u hu
  exact redIndicator_comm G u v

/-- The red neighbors of `v` which lie in `S`. -/
def redNeighborsIn {V : Type*} (G : SimpleGraph V) (v : V) (S : Finset V) :
    Finset V :=
  by
    classical
    exact S.filter (G.Adj v)

@[simp]
lemma mem_redNeighborsIn {V : Type*} (G : SimpleGraph V)
    (v u : V) (S : Finset V) :
    u ∈ redNeighborsIn G v S ↔ u ∈ S ∧ G.Adj v u := by
  classical
  simp [redNeighborsIn]

lemma card_redNeighborsIn {V : Type*} (G : SimpleGraph V) (v : V) (S : Finset V) :
    (redNeighborsIn G v S).card = ∑ u ∈ S, redIndicator G v u := by
  classical
  simp [redNeighborsIn, redIndicator]

lemma redNeighborsIn_subset {V : Type*} (G : SimpleGraph V) (v : V) (S : Finset V) :
    redNeighborsIn G v S ⊆ S := by
  intro u hu
  exact (mem_redNeighborsIn G v u S).1 hu |>.1

/-- The blue neighbors of `v` which lie in `S`. -/
def blueNeighborsIn {V : Type*} (G : SimpleGraph V) (v : V) (S : Finset V) :
    Finset V :=
  redNeighborsIn Gᶜ v S

@[simp]
lemma mem_blueNeighborsIn {V : Type*} (G : SimpleGraph V)
    (v u : V) (S : Finset V) :
    u ∈ blueNeighborsIn G v S ↔ u ∈ S ∧ v ≠ u ∧ ¬G.Adj v u := by
  classical
  simp [blueNeighborsIn, mem_redNeighborsIn]

lemma blueNeighborsIn_subset {V : Type*} (G : SimpleGraph V) (v : V) (S : Finset V) :
    blueNeighborsIn G v S ⊆ S := by
  intro u hu
  exact (mem_blueNeighborsIn G v u S).1 hu |>.1

lemma redEdgesBetween_eq_sum_card {V : Type*} (G : SimpleGraph V)
    (X Y : Finset V) :
    redEdgesBetween G X Y = ∑ v ∈ X, (redNeighborsIn G v Y).card := by
  simp only [redEdgesBetween, card_redNeighborsIn]

/-- The density of red edges between two finite sets. -/
def densityBetween {V : Type*} (G : SimpleGraph V) (X Y : Finset V) : ℝ :=
  (redEdgesBetween G X Y : ℝ) / ((X.card : ℝ) * Y.card)

/-- The excess `f_p(X,Y)` of red edges over density `p`. This is defined even
when one set is empty, as required by the averaging arguments. -/
def excessBetween {V : Type*} (p : ℝ) (G : SimpleGraph V)
    (X Y : Finset V) : ℝ :=
  (redEdgesBetween G X Y : ℝ) - p * X.card * Y.card

lemma left_nonempty_of_excessBetween_pos {V : Type*} {p : ℝ} {G : SimpleGraph V}
    {X Y : Finset V} (h : 0 < excessBetween p G X Y) : X.Nonempty := by
  by_contra hX
  rw [Finset.not_nonempty_iff_eq_empty] at hX
  subst X
  simp [excessBetween, redEdgesBetween] at h

lemma right_nonempty_of_excessBetween_pos {V : Type*} {p : ℝ} {G : SimpleGraph V}
    {X Y : Finset V} (h : 0 < excessBetween p G X Y) : Y.Nonempty := by
  by_contra hY
  rw [Finset.not_nonempty_iff_eq_empty] at hY
  subst Y
  simp [excessBetween, redEdgesBetween] at h

lemma redEdgesBetween_union_left {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {A B : Finset V} (hAB : Disjoint A B) (Y : Finset V) :
    redEdgesBetween G (A ∪ B) Y =
      redEdgesBetween G A Y + redEdgesBetween G B Y := by
  classical
  simp only [redEdgesBetween, sum_union hAB]

lemma redEdgesBetween_union_right {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (X : Finset V) {A B : Finset V} (hAB : Disjoint A B) :
    redEdgesBetween G X (A ∪ B) =
      redEdgesBetween G X A + redEdgesBetween G X B := by
  rw [redEdgesBetween_comm, redEdgesBetween_union_left G hAB,
    redEdgesBetween_comm G A X, redEdgesBetween_comm G B X]

lemma redEdgesBetween_singleton_left {V : Type*} (G : SimpleGraph V)
    (v : V) (S : Finset V) :
    redEdgesBetween G {v} S = (redNeighborsIn G v S).card := by
  classical
  rw [redEdgesBetween_eq_sum_card]
  simp

@[simp]
lemma redEdgesBetween_singleton_self {V : Type*} (G : SimpleGraph V) (v : V) :
    redEdgesBetween G {v} {v} = 0 := by
  classical
  simp [redEdgesBetween, redIndicator]

lemma excessBetween_union_left {V : Type*} [DecidableEq V] (p : ℝ) (G : SimpleGraph V)
    {A B : Finset V} (hAB : Disjoint A B) (Y : Finset V) :
    excessBetween p G (A ∪ B) Y =
      excessBetween p G A Y + excessBetween p G B Y := by
  classical
  rw [excessBetween, excessBetween, excessBetween,
    redEdgesBetween_union_left G hAB, card_union_of_disjoint hAB]
  push_cast
  ring

lemma red_blue_neighbors_union_insert {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {X : Finset V} {v : V} (hv : v ∈ X) :
    (redNeighborsIn G v X ∪ blueNeighborsIn G v X) ∪ {v} = X := by
  classical
  ext u
  by_cases huv : u = v
  · subst u
    simp [redNeighborsIn, blueNeighborsIn, hv]
  · by_cases hred : G.Adj v u
    · simp [redNeighborsIn, blueNeighborsIn, huv, hred]
    · have hvu : v ≠ u := Ne.symm huv
      simp [redNeighborsIn, blueNeighborsIn, huv, hvu, hred]

lemma red_blue_neighbors_disjoint {V : Type*} (G : SimpleGraph V)
    (v : V) (X : Finset V) :
    Disjoint (redNeighborsIn G v X) (blueNeighborsIn G v X) := by
  classical
  rw [Finset.disjoint_left]
  intro u hred hblue
  simp only [mem_redNeighborsIn] at hred
  simp only [mem_blueNeighborsIn] at hblue
  exact hblue.2.2 hred.2

lemma neighbors_union_disjoint_singleton {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (v : V) (X : Finset V) :
    Disjoint (redNeighborsIn G v X ∪ blueNeighborsIn G v X) {v} := by
  classical
  rw [Finset.disjoint_left]
  intro u hu huv
  simp only [mem_singleton] at huv
  subst u
  simp [redNeighborsIn, blueNeighborsIn] at hu

lemma card_redNeighbors_add_card_blueNeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (redNeighborsIn G v univ).card + (blueNeighborsIn G v univ).card + 1 =
      Fintype.card V := by
  classical
  have hpart :=
    red_blue_neighbors_union_insert G (X := (univ : Finset V)) (mem_univ v)
  have hcard := congrArg Finset.card hpart
  rw [card_union_of_disjoint (neighbors_union_disjoint_singleton G v univ),
    card_union_of_disjoint (red_blue_neighbors_disjoint G v univ),
    card_singleton, card_univ] at hcard
  exact hcard

lemma excessBetween_partition_neighbors {V : Type*} (p : ℝ) (G : SimpleGraph V)
    {X : Finset V} {v : V} (hv : v ∈ X) (Y : Finset V) :
    excessBetween p G X Y =
      excessBetween p G (redNeighborsIn G v X) Y +
        excessBetween p G (blueNeighborsIn G v X) Y +
        excessBetween p G {v} Y := by
  classical
  calc
    excessBetween p G X Y =
        excessBetween p G
          ((redNeighborsIn G v X ∪ blueNeighborsIn G v X) ∪ {v}) Y := by
      rw [red_blue_neighbors_union_insert G hv]
    _ = excessBetween p G
          (redNeighborsIn G v X ∪ blueNeighborsIn G v X) Y +
          excessBetween p G {v} Y :=
      excessBetween_union_left p G
        (neighbors_union_disjoint_singleton G v X) Y
    _ = excessBetween p G (redNeighborsIn G v X) Y +
          excessBetween p G (blueNeighborsIn G v X) Y +
          excessBetween p G {v} Y := by
      rw [excessBetween_union_left p G (red_blue_neighbors_disjoint G v X)]

lemma excessBetween_singleton_le_card {V : Type*} (p : ℝ) (hp : 0 ≤ p)
    (G : SimpleGraph V) (v : V) (Y : Finset V) :
    excessBetween p G {v} Y ≤ Y.card := by
  classical
  have hedges : redEdgesBetween G {v} Y ≤ Y.card := by
    rw [redEdgesBetween_eq_sum_card]
    simpa using card_le_card (show redNeighborsIn G v Y ⊆ Y from by
      intro u hu
      exact (mem_redNeighborsIn G v u Y).1 hu |>.1)
  have hedgesR : (redEdgesBetween G {v} Y : ℝ) ≤ Y.card := by
    exact_mod_cast hedges
  rw [excessBetween]
  simp only [card_singleton, Nat.cast_one, mul_one]
  have hnonneg : 0 ≤ p * (Y.card : ℝ) :=
    mul_nonneg hp (Nat.cast_nonneg _)
  linarith

/-- A pair of nonempty disjoint vertex sets, called a candidate in the paper. -/
structure Candidate {V : Type*} (G : SimpleGraph V) where
  X : Finset V
  Y : Finset V
  X_nonempty : X.Nonempty
  Y_nonempty : Y.Nonempty
  disjoint : Disjoint X Y

/-- A finite set of vertices satisfying a Ramsey property contains the
corresponding red clique or blue clique. -/
lemma red_or_blue_of_ramseyProperty {V : Type*} {G : SimpleGraph V}
    (S : Finset V) {k l : ℕ} (hprop : RamseyProperty k l S.card) :
    (∃ K : Finset V, K ⊆ S ∧ G.IsNClique k K) ∨
      ∃ K : Finset V, K ⊆ S ∧ G.IsNIndepSet l K := by
  classical
  let H : SimpleGraph {v // v ∈ S} := G.induce (↑S : Set V)
  have hprop' : RamseyProperty k l (Fintype.card {v // v ∈ S}) := by
    simpa using hprop
  have hram : ¬(H.CliqueFree k ∧ H.IndepSetFree l) :=
    Ramsey.ramseyProperty_of_card rfl hprop' H
  by_cases hcf : H.CliqueFree k
  · have hnif : ¬H.IndepSetFree l := fun hif ↦ hram ⟨hcf, hif⟩
    rw [SimpleGraph.IndepSetFree] at hnif
    push Not at hnif
    obtain ⟨K, hK⟩ := hnif
    let K' : Finset V := K.map ⟨Subtype.val, Subtype.val_injective⟩
    refine Or.inr ⟨K', ?_, ?_⟩
    · intro v hv
      rcases mem_map.mp hv with ⟨w, hw, rfl⟩
      exact w.property
    · have hKtop :
          (((⊤ : SimpleGraph.Subgraph G).induce (↑S : Set V)).coe).IsNIndepSet l K := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact hK
      exact (G.isNIndepSet_induce).1 hKtop
  · rw [SimpleGraph.CliqueFree] at hcf
    push Not at hcf
    obtain ⟨K, hK⟩ := hcf
    let K' : Finset V := K.map ⟨Subtype.val, Subtype.val_injective⟩
    refine Or.inl ⟨K', ?_, ?_⟩
    · intro v hv
      rcases mem_map.mp hv with ⟨w, hw, rfl⟩
      exact w.property
    · exact (G.isNClique_induce_iff (↑S : Set V) K k).1 hK

namespace Candidate

variable {V : Type*} {G : SimpleGraph V}

/-- The density `d(X,Y)` of red edges across a candidate. -/
def density (C : Candidate G) : ℝ :=
  densityBetween G C.X C.Y

/-- The excess `f_p(X,Y)` of red edges over density `p`. -/
def excess (p : ℝ) (C : Candidate G) : ℝ :=
  excessBetween p G C.X C.Y

lemma card_X_pos (C : Candidate G) : 0 < C.X.card :=
  C.X_nonempty.card_pos

lemma card_Y_pos (C : Candidate G) : 0 < C.Y.card :=
  C.Y_nonempty.card_pos

lemma card_X_ne_zero (C : Candidate G) : (C.X.card : ℝ) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt C.card_X_pos

lemma card_Y_ne_zero (C : Candidate G) : (C.Y.card : ℝ) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt C.card_Y_pos

lemma density_mul_card (C : Candidate G) :
    C.density * ((C.X.card : ℝ) * C.Y.card) = redEdgesBetween G C.X C.Y := by
  rw [density, densityBetween, div_mul_cancel₀]
  exact mul_ne_zero C.card_X_ne_zero C.card_Y_ne_zero

lemma excess_eq_card_mul_density_sub (p : ℝ) (C : Candidate G) :
    C.excess p = ((C.X.card : ℝ) * C.Y.card) * (C.density - p) := by
  rw [excess, excessBetween, ← C.density_mul_card]
  ring

/-- A set contains a red clique of order `k`. -/
def ContainsRedClique (S : Finset V) (k : ℕ) : Prop :=
  ∃ K : Finset V, K ⊆ S ∧ G.IsNClique k K

/-- A set contains a blue clique of order `k`, equivalently an independent
set of order `k` in the red graph. -/
def ContainsBlueClique (S : Finset V) (k : ℕ) : Prop :=
  ∃ K : Finset V, K ⊆ S ∧ G.IsNIndepSet k K

/-- The paper's `(k,l,t)`-good predicate. -/
def Good (C : Candidate G) (k l t : ℕ) : Prop :=
  by
    classical
    exact
      ContainsRedClique (G := G) (C.X ∪ C.Y) k ∨
        ContainsBlueClique (G := G) C.X t ∨
        ContainsBlueClique (G := G) C.Y l

lemma containsRedClique_mono {S T : Finset V} {k : ℕ} (hST : S ⊆ T) :
    ContainsRedClique (G := G) S k → ContainsRedClique (G := G) T k := by
  rintro ⟨K, hKS, hK⟩
  exact ⟨K, hKS.trans hST, hK⟩

lemma containsBlueClique_mono {S T : Finset V} {k : ℕ} (hST : S ⊆ T) :
    ContainsBlueClique (G := G) S k → ContainsBlueClique (G := G) T k := by
  rintro ⟨K, hKS, hK⟩
  exact ⟨K, hKS.trans hST, hK⟩

lemma good_of_mono {C D : Candidate G}
    (hX : C.X ⊆ D.X) (hY : C.Y ⊆ D.Y) {k l t : ℕ} :
    C.Good k l t → D.Good k l t := by
  classical
  rintro (h | h | h)
  · exact Or.inl (containsRedClique_mono (union_subset_union hX hY) h)
  · exact Or.inr (Or.inl (containsBlueClique_mono hX h))
  · exact Or.inr (Or.inr (containsBlueClique_mono hY h))

lemma good_of_k_one (C : Candidate G) (l t : ℕ) : C.Good 1 l t := by
  classical
  rcases C.X_nonempty with ⟨v, hv⟩
  exact Or.inl ⟨{v}, by simp [hv], by simp⟩

lemma good_of_t_one (C : Candidate G) (k l : ℕ) : C.Good k l 1 := by
  classical
  rcases C.X_nonempty with ⟨v, hv⟩
  refine Or.inr (Or.inl ⟨{v}, singleton_subset_iff.mpr hv, ?_⟩)
  exact ⟨by simp [SimpleGraph.isIndepSet_iff], by simp⟩

/-- The candidate obtained by taking red neighborhoods on both sides. -/
def redStep (C : Candidate G) (v : V)
    (hX : (redNeighborsIn G v C.X).Nonempty)
    (hY : (redNeighborsIn G v C.Y).Nonempty) : Candidate G where
  X := redNeighborsIn G v C.X
  Y := redNeighborsIn G v C.Y
  X_nonempty := hX
  Y_nonempty := hY
  disjoint := C.disjoint.mono
    (redNeighborsIn_subset G v C.X) (redNeighborsIn_subset G v C.Y)

/-- The candidate used for a blue induction step: a blue neighborhood on the
left and a red neighborhood on the right. -/
def blueStep (C : Candidate G) (v : V)
    (hX : (blueNeighborsIn G v C.X).Nonempty)
    (hY : (redNeighborsIn G v C.Y).Nonempty) : Candidate G where
  X := blueNeighborsIn G v C.X
  Y := redNeighborsIn G v C.Y
  X_nonempty := hX
  Y_nonempty := hY
  disjoint := C.disjoint.mono
    (blueNeighborsIn_subset G v C.X) (redNeighborsIn_subset G v C.Y)

/-- Lift goodness through a red-neighborhood induction step. -/
lemma good_of_redStep_good (C : Candidate G) {v : V} (hv : v ∈ C.X)
    (hX : (redNeighborsIn G v C.X).Nonempty)
    (hY : (redNeighborsIn G v C.Y).Nonempty) {k l t : ℕ}
    (hgood : (C.redStep v hX hY).Good k l t) :
    C.Good (k + 1) l t := by
  classical
  rcases hgood with hred | hblueX | hblueY
  · rcases hred with ⟨K, hKsub, hK⟩
    refine Or.inl ⟨insert v K, ?_, hK.insert ?_⟩
    · intro u hu
      rw [mem_insert] at hu
      rcases hu with rfl | hu
      · exact mem_union_left C.Y hv
      · have hu' := hKsub hu
        simp only [redStep, mem_union] at hu'
        rcases hu' with huX | huY
        · exact mem_union_left C.Y
            (redNeighborsIn_subset G v C.X huX)
        · exact mem_union_right C.X
            (redNeighborsIn_subset G v C.Y huY)
    · intro u hu
      have hu' := hKsub hu
      simp only [redStep, mem_union] at hu'
      rcases hu' with huX | huY
      · exact (mem_redNeighborsIn G v u C.X).1 huX |>.2
      · exact (mem_redNeighborsIn G v u C.Y).1 huY |>.2
  · exact Or.inr (Or.inl
      (containsBlueClique_mono (redNeighborsIn_subset G v C.X) hblueX))
  · exact Or.inr (Or.inr
      (containsBlueClique_mono (redNeighborsIn_subset G v C.Y) hblueY))

/-- Lift goodness through a blue-neighborhood induction step. -/
lemma good_of_blueStep_good (C : Candidate G) {v : V} (hv : v ∈ C.X)
    (hX : (blueNeighborsIn G v C.X).Nonempty)
    (hY : (redNeighborsIn G v C.Y).Nonempty) {k l t : ℕ}
    (hgood : (C.blueStep v hX hY).Good k l t) :
    C.Good k l (t + 1) := by
  classical
  rcases hgood with hred | hblueX | hblueY
  · exact Or.inl (containsRedClique_mono
      (union_subset_union (blueNeighborsIn_subset G v C.X)
        (redNeighborsIn_subset G v C.Y)) hred)
  · rcases hblueX with ⟨K, hKsub, hK⟩
    refine Or.inr (Or.inl ⟨insert v K, ?_, ?_⟩)
    · intro u hu
      rw [mem_insert] at hu
      rcases hu with rfl | hu
      · exact hv
      · exact blueNeighborsIn_subset G v C.X (hKsub hu)
    · have hKcompl : Gᶜ.IsNClique t K := by simpa using hK
      have hins : Gᶜ.IsNClique (t + 1) (insert v K) :=
        hKcompl.insert fun u hu ↦ by
          exact (mem_redNeighborsIn Gᶜ v u C.X).1 (hKsub hu) |>.2
      simpa using hins
  · exact Or.inr (Or.inr
      (containsBlueClique_mono (redNeighborsIn_subset G v C.Y) hblueY))

/-- If the right side of a candidate has at least `R(k,l)` vertices, the
ordinary Ramsey property makes the candidate good. -/
lemma good_of_ramsey_right (C : Candidate G) {k l t : ℕ}
    (hcard : ramseyNumber k l ≤ C.Y.card) : C.Good k l t := by
  classical
  rcases red_or_blue_of_ramseyProperty C.Y
      (Ramsey.ramseyProperty_of_ramseyNumber_le hcard) with hred | hblue
  · exact Or.inl (containsRedClique_mono (subset_union_right) hred)
  · exact Or.inr (Or.inr hblue)

end Candidate

end Arxiv2407_19026

import Arxiv.Arxiv2407_19026.Multicolor

/-!
# The elementary multicolor candidate argument

This file formalizes the multicolor extension in Section 5 of
arXiv:2407.19026.
-/

open Finset

noncomputable section

namespace Arxiv2407_19026

/-- The neighbors of `v` in color `i` that lie in `S`. -/
def multiNeighborsIn {V : Type*} {c : ℕ} (C : MultiColoring V c)
    (v : V) (i : Fin (c + 1)) (S : Finset V) : Finset V := by
  classical
  exact S.filter ((C.graph i).Adj v)

@[simp]
lemma mem_multiNeighborsIn {V : Type*} {c : ℕ}
    (C : MultiColoring V c) (v u : V) (i : Fin (c + 1))
    (S : Finset V) :
    u ∈ multiNeighborsIn C v i S ↔ u ∈ S ∧ (C.graph i).Adj v u := by
  classical
  simp [multiNeighborsIn]

lemma multiNeighborsIn_subset {V : Type*} {c : ℕ}
    (C : MultiColoring V c) (v : V) (i : Fin (c + 1))
    (S : Finset V) :
    multiNeighborsIn C v i S ⊆ S := by
  intro u hu
  exact (mem_multiNeighborsIn C v u i S).1 hu |>.1

@[simp]
lemma multiNeighborsIn_zero {V : Type*} {c : ℕ}
    (C : MultiColoring V c) (v : V) (S : Finset V) :
    multiNeighborsIn C v 0 S = redNeighborsIn (C.graph 0) v S := by
  classical
  ext u
  simp [multiNeighborsIn, redNeighborsIn]

/-- A pair of nonempty disjoint vertex sets in a multicolored complete graph. -/
structure MultiCandidate {V : Type*} {c : ℕ} (C : MultiColoring V c) where
  X : Finset V
  Y : Finset V
  X_nonempty : X.Nonempty
  Y_nonempty : Y.Nonempty
  disjoint : Disjoint X Y

namespace MultiCandidate

variable {V : Type*} {c : ℕ} {C : MultiColoring V c}

/-- The red excess of a multicolor candidate. -/
def excess (D : MultiCandidate C) (p : ℝ) : ℝ :=
  excessBetween p (C.graph 0) D.X D.Y

/-- A set contains a monochromatic clique in color `i`. -/
def ContainsColorClique (S : Finset V) (i : Fin (c + 1))
    (n : ℕ) : Prop :=
  ∃ K : Finset V, K ⊆ S ∧ (C.graph i).IsNClique n K

/-- The paper's multicolor `(k,l,t)`-good predicate. -/
def Good (D : MultiCandidate C) (k : ℕ)
    (l t : Fin c → ℕ) : Prop := by
  classical
  exact
    ContainsColorClique (C := C) (D.X ∪ D.Y) 0 k ∨
      (∃ i : Fin c, ContainsColorClique (C := C) D.X i.succ (t i)) ∨
      ∃ i : Fin c, ContainsColorClique (C := C) D.Y i.succ (l i)

lemma containsColorClique_mono {S T : Finset V} {i : Fin (c + 1)}
    {n : ℕ} (hST : S ⊆ T) :
    ContainsColorClique (C := C) S i n →
      ContainsColorClique (C := C) T i n := by
  rintro ⟨K, hKS, hK⟩
  exact ⟨K, hKS.trans hST, hK⟩

lemma good_of_k_le_one (D : MultiCandidate C) {k : ℕ}
    (hk : k ≤ 1) (l t : Fin c → ℕ) :
    D.Good k l t := by
  classical
  interval_cases k
  · exact Or.inl ⟨∅, by simp, by simp⟩
  · rcases D.X_nonempty with ⟨v, hv⟩
    exact Or.inl ⟨{v}, by simp [hv], by simp⟩

lemma good_of_t_le_one (D : MultiCandidate C) (k : ℕ)
    (l t : Fin c → ℕ) {i : Fin c} (hi : t i ≤ 1) :
    D.Good k l t := by
  classical
  have hval : t i = 0 ∨ t i = 1 := by omega
  rcases hval with hzero | hone
  · exact Or.inr (Or.inl ⟨i, ∅, by simp, by simp [hzero]⟩)
  · rcases D.X_nonempty with ⟨v, hv⟩
    exact Or.inr (Or.inl ⟨i, {v}, by simp [hv], by simp [hone]⟩)

/-- The red-neighborhood induction step. -/
def redStep (D : MultiCandidate C) (v : V)
    (hX : (multiNeighborsIn C v 0 D.X).Nonempty)
    (hY : (multiNeighborsIn C v 0 D.Y).Nonempty) :
    MultiCandidate C where
  X := multiNeighborsIn C v 0 D.X
  Y := multiNeighborsIn C v 0 D.Y
  X_nonempty := hX
  Y_nonempty := hY
  disjoint := D.disjoint.mono
    (multiNeighborsIn_subset C v 0 D.X)
    (multiNeighborsIn_subset C v 0 D.Y)

/-- The induction step in blue color `i`. -/
def blueStep (D : MultiCandidate C) (v : V) (i : Fin c)
    (hX : (multiNeighborsIn C v i.succ D.X).Nonempty)
    (hY : (multiNeighborsIn C v 0 D.Y).Nonempty) :
    MultiCandidate C where
  X := multiNeighborsIn C v i.succ D.X
  Y := multiNeighborsIn C v 0 D.Y
  X_nonempty := hX
  Y_nonempty := hY
  disjoint := D.disjoint.mono
    (multiNeighborsIn_subset C v i.succ D.X)
    (multiNeighborsIn_subset C v 0 D.Y)

lemma good_of_redStep_good (D : MultiCandidate C) {v : V}
    (hv : v ∈ D.X)
    (hX : (multiNeighborsIn C v 0 D.X).Nonempty)
    (hY : (multiNeighborsIn C v 0 D.Y).Nonempty)
    {k : ℕ} {l t : Fin c → ℕ}
    (hgood : (D.redStep v hX hY).Good k l t) :
    D.Good (k + 1) l t := by
  classical
  rcases hgood with hred | hblueX | hblueY
  · rcases hred with ⟨K, hKsub, hK⟩
    refine Or.inl ⟨insert v K, ?_, hK.insert ?_⟩
    · intro u hu
      rw [mem_insert] at hu
      rcases hu with rfl | hu
      · exact mem_union_left D.Y hv
      · have hu' := hKsub hu
        simp only [redStep, mem_union] at hu'
        rcases hu' with huX | huY
        · exact mem_union_left D.Y
            (multiNeighborsIn_subset C v 0 D.X huX)
        · exact mem_union_right D.X
            (multiNeighborsIn_subset C v 0 D.Y huY)
    · intro u hu
      have hu' := hKsub hu
      change u ∈ multiNeighborsIn C v 0 D.X ∪
        multiNeighborsIn C v 0 D.Y at hu'
      rw [mem_union] at hu'
      rcases hu' with huX | huY
      · exact (mem_multiNeighborsIn C v u 0 D.X).1 huX |>.2
      · exact (mem_multiNeighborsIn C v u 0 D.Y).1 huY |>.2
  · rcases hblueX with ⟨i, hclique⟩
    change ContainsColorClique (C := C)
      (multiNeighborsIn C v 0 D.X) i.succ (t i) at hclique
    exact Or.inr (Or.inl ⟨i,
      containsColorClique_mono
        (multiNeighborsIn_subset C v 0 D.X) hclique⟩)
  · rcases hblueY with ⟨i, hclique⟩
    change ContainsColorClique (C := C)
      (multiNeighborsIn C v 0 D.Y) i.succ (l i) at hclique
    exact Or.inr (Or.inr ⟨i,
      containsColorClique_mono
        (multiNeighborsIn_subset C v 0 D.Y) hclique⟩)

lemma good_of_blueStep_good (D : MultiCandidate C) {v : V}
    (hv : v ∈ D.X) (i : Fin c)
    (hX : (multiNeighborsIn C v i.succ D.X).Nonempty)
    (hY : (multiNeighborsIn C v 0 D.Y).Nonempty)
    {k : ℕ} {l t : Fin c → ℕ} (hti : 1 ≤ t i)
    (hgood : (D.blueStep v i hX hY).Good k l (lowerVector t i)) :
    D.Good k l t := by
  classical
  rcases hgood with hred | hblueX | hblueY
  · exact Or.inl (containsColorClique_mono
      (union_subset_union
        (multiNeighborsIn_subset C v i.succ D.X)
        (multiNeighborsIn_subset C v 0 D.Y)) hred)
  · rcases hblueX with ⟨j, K, hKsub, hK⟩
    by_cases hji : j = i
    · subst j
      refine Or.inr (Or.inl ⟨i, insert v K, ?_, ?_⟩)
      · intro u hu
        rw [mem_insert] at hu
        rcases hu with rfl | hu
        · exact hv
        · exact multiNeighborsIn_subset C v i.succ D.X (hKsub hu)
      · have hins := hK.insert fun u hu =>
          (mem_multiNeighborsIn C v u i.succ D.X).1 (hKsub hu) |>.2
        simpa [lowerVector, Nat.sub_add_cancel hti] using hins
    · have hKsub' : K ⊆ multiNeighborsIn C v i.succ D.X := by
        simpa [blueStep] using hKsub
      have hK' : (C.graph j.succ).IsNClique (t j) K := by
        simpa [lowerVector, hji] using hK
      exact Or.inr (Or.inl ⟨j,
        containsColorClique_mono
          (multiNeighborsIn_subset C v i.succ D.X)
          ⟨K, hKsub', hK'⟩⟩)
  · rcases hblueY with ⟨j, hclique⟩
    change ContainsColorClique (C := C)
      (multiNeighborsIn C v 0 D.Y) j.succ (l j) at hclique
    exact Or.inr (Or.inr ⟨j,
      containsColorClique_mono
        (multiNeighborsIn_subset C v 0 D.Y) hclique⟩)

/-- Lemma `l:FpAvg`, packaged for a multicolor candidate. -/
lemma excess_averaging (D : MultiCandidate C) (p : ℝ) :
    p * D.X.card * D.excess p ≤
      ∑ v ∈ D.X,
        excessBetween p (C.graph 0) D.X
          (multiNeighborsIn C v 0 D.Y) := by
  simpa [MultiCandidate.excess, multiNeighborsIn_zero] using
    Arxiv2407_19026.excess_averaging (C.graph 0) D.X D.Y p

/-- A sufficiently large right side makes a multicolor candidate good. -/
lemma good_of_multiRamsey_right {V : Type} {c : ℕ}
    {C : MultiColoring V c} (D : MultiCandidate C) (hc : 1 ≤ c)
    {k : ℕ} {l t : Fin c → ℕ}
    (hcard : multiRamseyRecBound k l ≤ D.Y.card) :
    D.Good k l t := by
  classical
  let W := {v : V // v ∈ D.Y}
  let f : W ↪ V := Function.Embedding.subtype _
  have hWcard : multiRamseyRecBound k l ≤ Fintype.card W := by
    simpa [W] using hcard
  have hgood :
      MultiGood (C.comap f) k l :=
    multiRamseyProperty_recBound hc k l W hWcard (C.comap f)
  rcases hgood with hred | hblue
  · rcases hred with ⟨K, hK⟩
    let K' := K.map f
    have hK' : (C.graph 0).IsNClique k K' :=
      hK.map.mono (SimpleGraph.map_comap_le f (C.graph 0))
    refine Or.inl ⟨K', ?_, hK'⟩
    intro v hv
    rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    exact mem_union_right D.X w.property
  · rcases hblue with ⟨i, K, hK⟩
    let K' := K.map f
    have hK' : (C.graph i.succ).IsNClique (l i) K' :=
      hK.map.mono (SimpleGraph.map_comap_le f (C.graph i.succ))
    refine Or.inr (Or.inr ⟨i, K', ?_, hK'⟩)
    intro v hv
    rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    exact w.property

end MultiCandidate

lemma multiNeighbors_pairwiseDisjoint {V : Type*} {c : ℕ}
    (C : MultiColoring V c) (v : V) (S : Finset V) :
    ((Finset.univ : Finset (Fin (c + 1))) : Set (Fin (c + 1))).PairwiseDisjoint
      (fun i => multiNeighborsIn C v i S) := by
  classical
  intro i _ j _ hij
  change Disjoint (multiNeighborsIn C v i S)
    (multiNeighborsIn C v j S)
  rw [Finset.disjoint_left]
  intro u hui huj
  have hiAdj := (mem_multiNeighborsIn C v u i S).1 hui |>.2
  have hjAdj := (mem_multiNeighborsIn C v u j S).1 huj |>.2
  have hvu : v ≠ u := (C.graph i).ne_of_adj hiAdj
  obtain ⟨q, hq, hqunique⟩ := C.complete v u hvu
  exact hij ((hqunique i hiAdj).trans (hqunique j hjAdj).symm)

lemma biUnion_multiNeighbors_eq_erase {V : Type*}
    [DecidableEq V] {c : ℕ}
    (C : MultiColoring V c) (v : V) (S : Finset V) :
    (Finset.univ : Finset (Fin (c + 1))).biUnion
        (fun i => multiNeighborsIn C v i S) =
      S.erase v := by
  classical
  ext u
  constructor
  · intro hu
    rw [Finset.mem_biUnion] at hu
    obtain ⟨i, _, hui⟩ := hu
    have hmem := (mem_multiNeighborsIn C v u i S).1 hui
    exact Finset.mem_erase.mpr
      ⟨((C.graph i).ne_of_adj hmem.2).symm, hmem.1⟩
  · intro hu
    have hmem := Finset.mem_erase.mp hu
    obtain ⟨i, hi, _⟩ := C.complete v u hmem.1.symm
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, (mem_multiNeighborsIn C v u i S).2
      ⟨hmem.2, hi⟩⟩

/-- The red excess splits over the red cell, all blue color cells, and the
chosen vertex. -/
lemma excessBetween_partition_multiNeighbors {V : Type*} {c : ℕ}
    (C : MultiColoring V c) (p : ℝ) {S : Finset V} {v : V}
    (hv : v ∈ S) (Y : Finset V) :
    excessBetween p (C.graph 0) S Y =
      ∑ i : Fin (c + 1),
          excessBetween p (C.graph 0) (multiNeighborsIn C v i S) Y +
        excessBetween p (C.graph 0) {v} Y := by
  classical
  let cells : Fin (c + 1) → Finset V :=
    fun i => multiNeighborsIn C v i S
  let U : Finset V := Finset.univ.biUnion cells
  have hdisj :
      ((Finset.univ : Finset (Fin (c + 1))) :
        Set (Fin (c + 1))).PairwiseDisjoint cells := by
    simpa [cells] using multiNeighbors_pairwiseDisjoint C v S
  have hU : U = S.erase v := by
    simpa [U, cells] using biUnion_multiNeighbors_eq_erase C v S
  have hUv : Disjoint U {v} := by
    rw [hU, Finset.disjoint_singleton_right]
    simp
  have hUnion : U ∪ {v} = S := by
    rw [hU]
    ext u
    simp [hv]
  have hedge :
      redEdgesBetween (C.graph 0) U Y =
        ∑ i, redEdgesBetween (C.graph 0) (cells i) Y := by
    unfold redEdgesBetween
    simpa [U] using
      (Finset.sum_biUnion hdisj
        (f := fun u => ∑ y ∈ Y, redIndicator (C.graph 0) u y))
  have hcard : U.card = ∑ i, (cells i).card := by
    simpa [U] using Finset.card_biUnion hdisj
  calc
    excessBetween p (C.graph 0) S Y =
        excessBetween p (C.graph 0) (U ∪ {v}) Y := by rw [hUnion]
    _ = excessBetween p (C.graph 0) U Y +
          excessBetween p (C.graph 0) {v} Y :=
      excessBetween_union_left p (C.graph 0) hUv Y
    _ = (∑ i, excessBetween p (C.graph 0) (cells i) Y) +
          excessBetween p (C.graph 0) {v} Y := by
      simp only [excessBetween, hedge, hcard, Nat.cast_sum,
        Finset.sum_sub_distrib]
      rw [mul_sum]
      rw [Finset.sum_mul]
    _ = (∑ i, excessBetween p (C.graph 0)
          (multiNeighborsIn C v i S) Y) +
          excessBetween p (C.graph 0) {v} Y := by
      simp only [cells]

/-- The denominator in the multicolor threshold from Lemma `l:easy2`. -/
def multiEasyDenominator {c : ℕ} (x p : ℝ) (theta : Fin c → ℝ)
    (k : ℕ) (l t : Fin c → ℕ) : ℝ :=
  x ^ (k - 1) *
    (1 - x) ^ ((∑ i, l i) - c) *
    (p - x) ^ ((∑ i, t i) - c) *
    ∏ i, theta i ^ (l i + t i)

/-- The excess threshold in Lemma `l:easy2`. -/
def multiEasyThreshold {c : ℕ} (x p : ℝ) (theta : Fin c → ℝ)
    (k : ℕ) (l t : Fin c → ℕ) : ℝ :=
  (k + ∑ i, t i : ℕ) / multiEasyDenominator x p theta k l t

lemma multiEasyDenominator_pos {c : ℕ} {x p : ℝ}
    {theta : Fin c → ℝ} (hx : 0 < x) (hxp : x < p)
    (hp : p < 1) (htheta : ∀ i, 0 < theta i)
    (k : ℕ) (l t : Fin c → ℕ) :
    0 < multiEasyDenominator x p theta k l t := by
  unfold multiEasyDenominator
  exact mul_pos
    (mul_pos
      (mul_pos (pow_pos hx _)
        (pow_pos (sub_pos.mpr (hxp.trans hp)) _))
      (pow_pos (sub_pos.mpr hxp) _))
    (Finset.prod_pos fun i _ => pow_pos (htheta i) _)

lemma multiEasyThreshold_pos {c : ℕ} {x p : ℝ}
    {theta : Fin c → ℝ} (hx : 0 < x) (hxp : x < p)
    (hp : p < 1) (htheta : ∀ i, 0 < theta i)
    {k : ℕ} (hk : 1 ≤ k) (l t : Fin c → ℕ) :
    0 < multiEasyThreshold x p theta k l t := by
  apply div_pos
  · positivity
  · exact multiEasyDenominator_pos hx hxp hp htheta k l t

lemma sum_lowerVector {c : ℕ} {t : Fin c → ℕ}
    (i : Fin c) (hti : 1 ≤ t i) :
    ∑ j, lowerVector t i j = (∑ j, t j) - 1 := by
  have hi : i ∈ (Finset.univ : Finset (Fin c)) := Finset.mem_univ i
  simp only [lowerVector]
  rw [Finset.sum_update_of_mem hi]
  have hsum := Finset.sum_erase_add
    (Finset.univ : Finset (Fin c)) t hi
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

private lemma prod_theta_lowerVector {c : ℕ}
    (theta : Fin c → ℝ) (l t : Fin c → ℕ)
    (i : Fin c) (hti : 1 ≤ t i) :
    (∏ j, theta j ^ (l j + t j)) =
      theta i * ∏ j, theta j ^ (l j + lowerVector t i j) := by
  classical
  have hi : i ∈ (Finset.univ : Finset (Fin c)) := Finset.mem_univ i
  have hfun :
      (fun j => theta j ^ (l j + lowerVector t i j)) =
        Function.update (fun j => theta j ^ (l j + t j)) i
          (theta i ^ (l i + (t i - 1))) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [lowerVector]
    · simp [lowerVector, hji]
  rw [hfun, Finset.prod_update_of_mem hi]
  have hprod :
      (∏ j ∈ (Finset.univ : Finset (Fin c)) \ {i},
          theta j ^ (l j + t j)) *
          theta i ^ (l i + t i) =
        ∏ j : Fin c, theta j ^ (l j + t j) := by
    simpa only [Finset.sdiff_singleton_eq_erase] using
      Finset.prod_erase_mul (Finset.univ : Finset (Fin c))
        (fun j => theta j ^ (l j + t j)) hi
  rw [← hprod]
  have hexp : l i + t i = (l i + (t i - 1)) + 1 := by omega
  rw [hexp, pow_succ]
  ring

private lemma multiEasyDenominator_red {c : ℕ}
    (x p : ℝ) (theta : Fin c → ℝ)
    {k : ℕ} (hk : 2 ≤ k) (l t : Fin c → ℕ) :
    multiEasyDenominator x p theta k l t =
      x * multiEasyDenominator x p theta (k - 1) l t := by
  unfold multiEasyDenominator
  have hexp : k - 1 = (k - 1 - 1) + 1 := by omega
  have hpow : x ^ (k - 1) = x * x ^ (k - 1 - 1) := by
    calc
      x ^ (k - 1) = x ^ ((k - 1 - 1) + 1) :=
        congrArg (fun n : ℕ => x ^ n) hexp
      _ = x ^ (k - 1 - 1) * x := pow_succ _ _
      _ = x * x ^ (k - 1 - 1) := mul_comm _ _
  rw [hpow]
  ring

private lemma multiEasyDenominator_blue {c : ℕ} (hc : 1 ≤ c)
    (x p : ℝ) (theta : Fin c → ℝ) (k : ℕ)
    (l t : Fin c → ℕ) (ht : ∀ i, 2 ≤ t i) (j : Fin c) :
    multiEasyDenominator x p theta k l t =
      theta j * (p - x) *
        multiEasyDenominator x p theta k l (lowerVector t j) := by
  have htj := ht j
  have hsumLower := sum_lowerVector j (by omega : 1 ≤ t j)
  have hsumGe : 2 * c ≤ ∑ i, t i := by
    calc
      2 * c = ∑ _i : Fin c, 2 := by simp [mul_comm]
      _ ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => ht i
  have hexp :
      (∑ i, t i) - c =
        ((∑ i, lowerVector t j i) - c) + 1 := by
    rw [hsumLower]
    omega
  have hprod :=
    prod_theta_lowerVector theta l t j (by omega : 1 ≤ t j)
  unfold multiEasyDenominator
  rw [hexp, pow_succ, hprod]
  ring

lemma multiEasyThreshold_red_scale {c : ℕ} {x p : ℝ}
    {theta : Fin c → ℝ} (hx : 0 < x) (hxp : x < p)
    (hp : p < 1) (htheta : ∀ i, 0 < theta i)
    {k : ℕ} (hk : 2 ≤ k) (l t : Fin c → ℕ) :
    ((k + ∑ i, t i - 1 : ℕ) : ℝ) /
          (k + ∑ i, t i) * x *
        multiEasyThreshold x p theta k l t =
      multiEasyThreshold x p theta (k - 1) l t := by
  have hDpos :=
    multiEasyDenominator_pos hx hxp hp htheta k l t
  have hDred :=
    multiEasyDenominator_red x p theta hk l t
  have hDpredPos :=
    multiEasyDenominator_pos hx hxp hp htheta (k - 1) l t
  have hnum :
      k + ∑ i, t i - 1 = (k - 1) + ∑ i, t i := by omega
  have hsumPos : 0 < k + ∑ i, t i := by omega
  unfold multiEasyThreshold
  rw [hDred, hnum]
  push_cast
  field_simp [hDpos.ne', hDpredPos.ne']

lemma multiEasyThreshold_blue_scale {c : ℕ} (hc : 1 ≤ c)
    {x p : ℝ} {theta : Fin c → ℝ}
    (hx : 0 < x) (hxp : x < p) (hp : p < 1)
    (htheta : ∀ i, 0 < theta i)
    (k : ℕ) (l t : Fin c → ℕ) (ht : ∀ i, 2 ≤ t i)
    (j : Fin c) :
    ((k + ∑ i, t i - 1 : ℕ) : ℝ) /
          (k + ∑ i, t i) * theta j * (p - x) *
        multiEasyThreshold x p theta k l t =
      multiEasyThreshold x p theta k l (lowerVector t j) := by
  have hDpos :=
    multiEasyDenominator_pos hx hxp hp htheta k l t
  have hDblue :=
    multiEasyDenominator_blue hc x p theta k l t ht j
  have hDpredPos :=
    multiEasyDenominator_pos hx hxp hp htheta k l (lowerVector t j)
  have htj := ht j
  have hsumLower := sum_lowerVector j (by omega : 1 ≤ t j)
  have htjle : t j ≤ ∑ i, t i := Finset.single_le_sum
    (fun i _ => Nat.zero_le (t i)) (Finset.mem_univ j)
  have hsumPos : 0 < k + ∑ i, t i := by
    omega
  have hsumCast : (k : ℝ) + ∑ i, (t i : ℝ) ≠ 0 := by
    have hsumCastPos :
        (0 : ℝ) < (k + ∑ i, t i : ℕ) := by exact_mod_cast hsumPos
    push_cast at hsumCastPos
    exact hsumCastPos.ne'
  have hnum :
      k + ∑ i, t i - 1 = k + ((∑ i, t i) - 1) := by
    omega
  unfold multiEasyThreshold
  rw [hDblue, hsumLower, hnum]
  push_cast
  field_simp [hDpos.ne', hDpredPos.ne',
    (htheta j).ne', (sub_pos.mpr hxp).ne', hsumCast]

private lemma sum_pred_eq_sum_sub_card {c : ℕ}
    {l : Fin c → ℕ} (hl : ∀ i, 1 ≤ l i) :
    ∑ i, (l i - 1) = (∑ i, l i) - c := by
  have hadd :
      (∑ i, (l i - 1)) + c = ∑ i, l i := by
    calc
      (∑ i, (l i - 1)) + c =
          ∑ i : Fin c, ((l i - 1) + 1) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = ∑ i, l i := by
        apply Finset.sum_congr rfl
        intro i _
        exact Nat.sub_add_cancel (hl i)
  omega

private lemma multiEasyDenominator_mul_weight {c : ℕ}
    {x p : ℝ} {theta : Fin c → ℝ}
    (hx : 0 < x) (hxp : x < p) (hp : p < 1)
    (htheta : ∀ i, 0 < theta i)
    (k : ℕ) (l t : Fin c → ℕ) (hl : ∀ i, 1 ≤ l i) :
    multiEasyDenominator x p theta k l t *
        multiRamseyWeight x (fun i => theta i * (1 - x)) k l =
      (p - x) ^ ((∑ i, t i) - c) *
        ∏ i, theta i ^ (t i + 1) := by
  have hsumPred := sum_pred_eq_sum_sub_card hl
  have hyprod :
      (∏ i, (theta i * (1 - x)) ^ (l i - 1)) =
        (1 - x) ^ ((∑ i, l i) - c) *
          ∏ i, theta i ^ (l i - 1) := by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum Finset.univ (fun i => l i - 1) (1 - x),
      hsumPred]
    ring
  have hthetaSplit :
      (∏ i, theta i ^ (l i + t i)) =
        (∏ i, theta i ^ (l i - 1)) *
          ∏ i, theta i ^ (t i + 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_add]
    congr 1
    have hli := hl i
    omega
  have hxpowPos : 0 < x ^ (k - 1) := pow_pos hx _
  have honePowPos :
      0 < (1 - x) ^ ((∑ i, l i) - c) :=
    pow_pos (sub_pos.mpr (hxp.trans hp)) _
  have hthetaPredPos :
      0 < ∏ i, theta i ^ (l i - 1) :=
    Finset.prod_pos fun i _ => pow_pos (htheta i) _
  unfold multiEasyDenominator multiRamseyWeight
  simp_rw [inv_pow]
  rw [Finset.prod_inv_distrib, hyprod, hthetaSplit]
  field_simp [hxpowPos.ne', honePowPos.ne', hthetaPredPos.ne']

private lemma multiEasy_terminal_factor_le_p {c : ℕ} (hc : 1 ≤ c)
    {x p : ℝ} {theta : Fin c → ℝ}
    (hx : 0 < x) (hxp : x < p) (hp : p < 1)
    (htheta : ∀ i, 0 < theta i) (hthetaSum : ∑ i, theta i = 1)
    (t : Fin c → ℕ) (ht : ∀ i, 2 ≤ t i) :
    (p - x) ^ ((∑ i, t i) - c) *
        ∏ i, theta i ^ (t i + 1) ≤ p := by
  have hthetaOne : ∀ i, theta i ≤ 1 := by
    intro i
    have hi : theta i ≤ ∑ j, theta j := Finset.single_le_sum
      (fun j _ => (htheta j).le) (Finset.mem_univ i)
    simpa [hthetaSum] using hi
  have hprod0 :
      0 ≤ ∏ i, theta i ^ (t i + 1) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (htheta i).le _
  have hprod1 :
      ∏ i, theta i ^ (t i + 1) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _
      exact pow_nonneg (htheta i).le _
    · intro i _
      exact pow_le_one₀ (htheta i).le (hthetaOne i)
  have hsumGe : 2 * c ≤ ∑ i, t i := by
    calc
      2 * c = ∑ _i : Fin c, 2 := by simp [mul_comm]
      _ ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => ht i
  have hexp : 1 ≤ (∑ i, t i) - c := by omega
  have hz0 : 0 ≤ p - x := (sub_pos.mpr hxp).le
  have hz1 : p - x ≤ 1 := by linarith
  have hzpow :
      (p - x) ^ ((∑ i, t i) - c) ≤ p - x := by
    simpa using
      (pow_le_pow_of_le_one hz0 hz1
        (m := 1) (n := (∑ i, t i) - c) hexp)
  have hzpow0 :
      0 ≤ (p - x) ^ ((∑ i, t i) - c) :=
    pow_nonneg hz0 _
  calc
    (p - x) ^ ((∑ i, t i) - c) *
          ∏ i, theta i ^ (t i + 1) ≤
        (p - x) ^ ((∑ i, t i) - c) * 1 :=
      mul_le_mul_of_nonneg_left hprod1 hzpow0
    _ ≤ p - x := by simpa using hzpow
    _ ≤ p := by linarith

private lemma multiRamseyWeight_le_terminal_threshold {c : ℕ}
    (hc : 1 ≤ c) {x p : ℝ} {theta : Fin c → ℝ}
    (hx : 0 < x) (hxp : x < p) (hp : p < 1)
    (htheta : ∀ i, 0 < theta i) (hthetaSum : ∑ i, theta i = 1)
    (k : ℕ) (l t : Fin c → ℕ)
    (hl : ∀ i, 1 ≤ l i) (ht : ∀ i, 2 ≤ t i) :
    multiRamseyWeight x (fun i => theta i * (1 - x)) k l ≤
      p * multiEasyThreshold x p theta k l t /
        (k + ∑ i, t i : ℕ) := by
  have hDpos :=
    multiEasyDenominator_pos hx hxp hp htheta k l t
  have hfactor :=
    multiEasy_terminal_factor_le_p hc hx hxp hp htheta hthetaSum t ht
  have hmul :=
    multiEasyDenominator_mul_weight hx hxp hp htheta k l t hl
  have hsumPos : 0 < k + ∑ i, t i := by
    have i0 : Fin c := ⟨0, hc⟩
    have hi := ht i0
    have hile : t i0 ≤ ∑ i, t i := Finset.single_le_sum
      (fun i _ => Nat.zero_le (t i)) (Finset.mem_univ i0)
    omega
  rw [multiEasyThreshold]
  have hsumR : ((k + ∑ i, t i : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hcancel :
      p * (((k + ∑ i, t i : ℕ) : ℝ) /
            multiEasyDenominator x p theta k l t) /
          (k + ∑ i, t i : ℕ) =
        p / multiEasyDenominator x p theta k l t := by
    field_simp [hsumR, hDpos.ne']
  rw [hcancel]
  apply (le_div_iff₀ hDpos).2
  rw [mul_comm, hmul]
  exact hfactor

/-- Lemma `l:easy2`, the multicolor candidate induction. -/
theorem multiCandidate_good_of_excess {V : Type} {c : ℕ}
    (hc : 1 ≤ c) {C : MultiColoring V c}
    {x p : ℝ} (hx : 0 < x) (hxp : x < p) (hp : p < 1)
    {theta : Fin c → ℝ} (htheta : ∀ i, 0 < theta i)
    (hthetaSum : ∑ i, theta i = 1)
    (D : MultiCandidate C) (k : ℕ) (l t : Fin c → ℕ)
    (hk : 1 ≤ k) (hl : ∀ i, 1 ≤ l i) (ht : ∀ i, 1 ≤ t i)
    (hD : multiEasyThreshold x p theta k l t ≤ D.excess p) :
    D.Good k l t := by
  classical
  by_cases hkbase : k ≤ 1
  · exact D.good_of_k_le_one hkbase l t
  by_cases htbase : ∃ i, t i ≤ 1
  · obtain ⟨i, hi⟩ := htbase
    exact D.good_of_t_le_one k l t hi
  have hk2 : 2 ≤ k := by omega
  have ht2 : ∀ i, 2 ≤ t i := by
    intro i
    by_contra hi
    exact htbase ⟨i, by omega⟩
  have hfpos : 0 < D.excess p :=
    (multiEasyThreshold_pos hx hxp hp htheta hk l t).trans_le hD
  have havg := D.excess_averaging p
  have hexists :
      ∃ v ∈ D.X,
        p * D.excess p ≤
          excessBetween p (C.graph 0) D.X
            (multiNeighborsIn C v 0 D.Y) := by
    by_contra hnone
    push Not at hnone
    have hlt := Finset.sum_lt_sum_of_nonempty D.X_nonempty
      (fun v hv => hnone v hv)
    have hlt' :
        (∑ v ∈ D.X,
            excessBetween p (C.graph 0) D.X
              (multiNeighborsIn C v 0 D.Y)) <
          (D.X.card : ℝ) * (p * D.excess p) := by
      simpa [Finset.sum_const, nsmul_eq_mul] using hlt
    nlinarith
  obtain ⟨v, hvX, hvavg⟩ := hexists
  let Y' := multiNeighborsIn C v 0 D.Y
  let XR := multiNeighborsIn C v 0 D.X
  let XB : Fin c → Finset V :=
    fun i => multiNeighborsIn C v i.succ D.X
  have hp0 : 0 < p := hx.trans hxp
  have hYpos : 0 < excessBetween p (C.graph 0) D.X Y' :=
    (mul_pos hp0 hfpos).trans_le hvavg
  have hY' : Y'.Nonempty :=
    right_nonempty_of_excessBetween_pos hYpos
  let q : ℝ :=
    ((k + ∑ i, t i - 1 : ℕ) : ℝ) / (k + ∑ i, t i)
  have hqpos : 0 < q := by
    have hnum : 0 < k + ∑ i, t i - 1 := by omega
    have hden : 0 < k + ∑ i, t i := by omega
    exact div_pos (by exact_mod_cast hnum) (by exact_mod_cast hden)
  by_cases hred :
      q * x * D.excess p ≤
        excessBetween p (C.graph 0) XR Y'
  · have hqxpos : 0 < q * x := by
      exact mul_pos hqpos hx
    have hXRpos : 0 < excessBetween p (C.graph 0) XR Y' :=
      (mul_pos hqxpos hfpos).trans_le hred
    have hXR : XR.Nonempty :=
      left_nonempty_of_excessBetween_pos hXRpos
    let E := D.redStep v hXR hY'
    have hE :
        multiEasyThreshold x p theta (k - 1) l t ≤ E.excess p := by
      calc
        multiEasyThreshold x p theta (k - 1) l t =
            q * x * multiEasyThreshold x p theta k l t := by
          symm
          simpa [q] using
            multiEasyThreshold_red_scale hx hxp hp htheta hk2 l t
        _ ≤ q * x * D.excess p :=
          mul_le_mul_of_nonneg_left hD hqxpos.le
        _ ≤ E.excess p := by
          simpa [E, MultiCandidate.redStep, MultiCandidate.excess,
            XR, Y'] using hred
    have hgoodE :=
      multiCandidate_good_of_excess hc hx hxp hp htheta hthetaSum
        E (k - 1) l t (by omega) hl ht hE
    have hlift := D.good_of_redStep_good hvX hXR hY' hgoodE
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hlift
  · have hnotred :
        excessBetween p (C.graph 0) XR Y' <
          q * x * D.excess p :=
      lt_of_not_ge hred
    by_cases hblue :
        ∃ i : Fin c,
          q * theta i * (p - x) * D.excess p ≤
            excessBetween p (C.graph 0) (XB i) Y'
    · obtain ⟨i, hi⟩ := hblue
      have hqthetapxpos : 0 < q * theta i * (p - x) := by
        exact mul_pos (mul_pos hqpos (htheta i)) (sub_pos.mpr hxp)
      have hXBpos : 0 < excessBetween p (C.graph 0) (XB i) Y' :=
        (mul_pos hqthetapxpos hfpos).trans_le hi
      have hXB : (XB i).Nonempty :=
        left_nonempty_of_excessBetween_pos hXBpos
      let E := D.blueStep v i hXB hY'
      have hE :
          multiEasyThreshold x p theta k l (lowerVector t i) ≤
            E.excess p := by
        calc
          multiEasyThreshold x p theta k l (lowerVector t i) =
              q * theta i * (p - x) *
                multiEasyThreshold x p theta k l t := by
            symm
            simpa [q] using
              multiEasyThreshold_blue_scale hc hx hxp hp htheta
                k l t ht2 i
          _ ≤ q * theta i * (p - x) * D.excess p :=
            mul_le_mul_of_nonneg_left hD hqthetapxpos.le
          _ ≤ E.excess p := by
            simpa [E, MultiCandidate.blueStep, MultiCandidate.excess,
              XB, Y'] using hi
      have htLower : ∀ j, 1 ≤ lowerVector t i j := by
        intro j
        by_cases hji : j = i
        · subst j
          rw [lowerVector, Function.update_self]
          have hti := ht2 i
          omega
        · simp [lowerVector, hji, ht j]
      have hgoodE :=
        multiCandidate_good_of_excess hc hx hxp hp htheta hthetaSum
          E k l (lowerVector t i) hk hl htLower hE
      exact D.good_of_blueStep_good hvX i hXB hY'
        (by have hti := ht2 i; omega) hgoodE
    · have hnotblue : ∀ i : Fin c,
          excessBetween p (C.graph 0) (XB i) Y' <
            q * theta i * (p - x) * D.excess p := by
        intro i
        exact lt_of_not_ge fun hi => hblue ⟨i, hi⟩
      let i0 : Fin c := ⟨0, hc⟩
      have huniv : (Finset.univ : Finset (Fin c)).Nonempty :=
        ⟨i0, Finset.mem_univ i0⟩
      have hsumBlue :
          (∑ i, excessBetween p (C.graph 0) (XB i) Y') <
            ∑ i, q * theta i * (p - x) * D.excess p :=
        Finset.sum_lt_sum_of_nonempty huniv
          (fun i _ => hnotblue i)
      have hsingleton :
          excessBetween p (C.graph 0) {v} Y' ≤ D.Y.card := by
        exact
          (excessBetween_singleton_le_card p hp0.le (C.graph 0) v Y').trans
            (by
              exact_mod_cast Finset.card_le_card
                (multiNeighborsIn_subset C v 0 D.Y))
      have hdecomp :=
        excessBetween_partition_multiNeighbors C p hvX Y'
      have hupper :
          excessBetween p (C.graph 0) D.X Y' <
            q * x * D.excess p +
              (∑ i, q * theta i * (p - x) * D.excess p) +
              D.Y.card := by
        rw [hdecomp, Fin.sum_univ_succ]
        exact add_lt_add_of_lt_of_le
          (add_lt_add hnotred (by simpa [XB] using hsumBlue))
          hsingleton
      have hsumCoeff :
          (∑ i, q * theta i * (p - x) * D.excess p) =
            q * (p - x) * D.excess p := by
        calc
          (∑ i, q * theta i * (p - x) * D.excess p) =
              ∑ i, theta i * (q * (p - x) * D.excess p) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (∑ i, theta i) *
                (q * (p - x) * D.excess p) := by
            rw [Finset.sum_mul]
          _ = q * (p - x) * D.excess p := by
            rw [hthetaSum]
            ring
      have hpf :
          p * D.excess p <
            q * p * D.excess p + D.Y.card := by
        calc
          p * D.excess p ≤
              excessBetween p (C.graph 0) D.X Y' := hvavg
          _ < q * x * D.excess p +
                (∑ i, q * theta i * (p - x) * D.excess p) +
                D.Y.card := hupper
          _ = q * p * D.excess p + D.Y.card := by
            rw [hsumCoeff]
            ring
      have hspos : 0 < ((k + ∑ i, t i : ℕ) : ℝ) := by
        positivity
      have hq :
          q = 1 - 1 / ((k + ∑ i, t i : ℕ) : ℝ) := by
        dsimp [q]
        rw [Nat.cast_sub (by omega : 1 ≤ k + ∑ i, t i)]
        push_cast
        field_simp
      rw [hq] at hpf
      have hterminal :
          p * D.excess p / ((k + ∑ i, t i : ℕ) : ℝ) <
            D.Y.card := by
        have halg :
            p * D.excess p *
                (((k + ∑ i, t i : ℕ) : ℝ))⁻¹ =
              p * D.excess p -
                (1 - (((k + ∑ i, t i : ℕ) : ℝ))⁻¹) *
                  p * D.excess p := by ring
        have hsub :
            p * D.excess p -
                (1 - (((k + ∑ i, t i : ℕ) : ℝ))⁻¹) *
                  p * D.excess p < D.Y.card := by
          apply (sub_lt_iff_lt_add).2
          simpa only [one_div, add_comm] using hpf
        rw [div_eq_mul_inv, halg]
        exact hsub
      have hscaled :
          p * multiEasyThreshold x p theta k l t /
              ((k + ∑ i, t i : ℕ) : ℝ) <
            D.Y.card := by
        exact
          (lt_of_le_of_lt
            ((div_le_div_iff_of_pos_right hspos).2
              (mul_le_mul_of_nonneg_left hD hp0.le))
            hterminal)
      have hWeight :=
        multiRamseyWeight_le_terminal_threshold hc hx hxp hp htheta
          hthetaSum k l t hl ht2
      have hRecWeight :=
        multiRamseyRecBound_le_weight hx
          (fun i => mul_pos (htheta i) (sub_pos.mpr (hxp.trans hp)))
          (by
            have hsum :
                ∑ i, theta i * (1 - x) =
                  (∑ i, theta i) * (1 - x) := by
              rw [Finset.sum_mul]
            rw [hsum, hthetaSum]
            linarith)
          k l hk hl
      have hRecCardR :
          (multiRamseyRecBound k l : ℝ) < D.Y.card :=
        hRecWeight.trans_lt (hWeight.trans_lt hscaled)
      have hRecCard :
          multiRamseyRecBound k l ≤ D.Y.card := by
        exact_mod_cast le_of_lt hRecCardR
      exact D.good_of_multiRamsey_right hc hRecCard
termination_by k + ∑ i, t i
decreasing_by
  · have hsum0 : 0 ≤ ∑ i, t i := Nat.zero_le _
    omega
  · have hsum := sum_lowerVector i (ht i)
    have hile : t i ≤ ∑ j, t j := Finset.single_le_sum
      (fun j _ => Nat.zero_le (t j)) (Finset.mem_univ i)
    have hti := ht i
    rw [hsum]
    omega

end Arxiv2407_19026

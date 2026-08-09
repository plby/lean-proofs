import Arxiv.Arxiv2407_19026.NumericalProfiles

/-!
# Multicolor Ramsey numbers

This file formalizes the multicolor Erdős--Szekeres recurrence and the
weighted bound in Observation `o:easybound2` of arXiv:2407.19026.  The
inequality `0 > x > 1` printed in the paper is impossible; the proofs use its
intended correction `0 < x` (together with `x + ∑ i, y i ≤ 1`).
-/

open Finset

noncomputable section

namespace Arxiv2407_19026

/-- Decrease the `i`th blue clique parameter by one. -/
def lowerVector {c : ℕ} (l : Fin c → ℕ) (i : Fin c) : Fin c → ℕ :=
  Function.update l i (l i - 1)

private def multiRamseyMeasure {c : ℕ} (k : ℕ) (l : Fin c → ℕ) : ℕ :=
  k + ∑ i, l i

/-- The recursive multicolor Erdős--Szekeres bound. -/
noncomputable def multiRamseyRecBound {c : ℕ}
    (k : ℕ) (l : Fin c → ℕ) : ℕ :=
  if k ≤ 1 ∨ ∃ i, l i ≤ 1 then 1
  else
    multiRamseyRecBound (k - 1) l +
      ∑ i, multiRamseyRecBound k (lowerVector l i)
termination_by multiRamseyMeasure k l
decreasing_by
  · dsimp [multiRamseyMeasure]
    omega
  · have hall : ∀ j, 1 < l j := by
      push Not at *
      intro j
      simp_all only
    have hi2 : 2 ≤ l i := by
      have := hall i
      omega
    simp only [multiRamseyMeasure, lowerVector]
    have hi : i ∈ (Finset.univ : Finset (Fin c)) := Finset.mem_univ i
    rw [Finset.sum_update_of_mem hi]
    have hsum := Finset.sum_erase_add
      (Finset.univ : Finset (Fin c)) l hi
    simp only [Finset.sdiff_singleton_eq_erase] at *
    omega

/-- The multiplicative potential in Observation `o:easybound2`. -/
noncomputable def multiRamseyWeight {c : ℕ}
    (x : ℝ) (y : Fin c → ℝ) (k : ℕ) (l : Fin c → ℕ) : ℝ :=
  x⁻¹ ^ (k - 1) * ∏ i, (y i)⁻¹ ^ (l i - 1)

private lemma multiRamseyWeight_red {c : ℕ} {x : ℝ}
    (hx : 0 < x) (y : Fin c → ℝ) {k : ℕ} (hk : 2 ≤ k)
    (l : Fin c → ℕ) :
    multiRamseyWeight x y (k - 1) l =
      x * multiRamseyWeight x y k l := by
  unfold multiRamseyWeight
  have he : k - 1 = (k - 1 - 1) + 1 := by omega
  have hpow : x * x⁻¹ ^ (k - 1) = x⁻¹ ^ (k - 1 - 1) := by
    nth_rw 1 [he]
    rw [pow_succ]
    field_simp [hx.ne']
  rw [← mul_assoc, hpow]

private lemma multiRamseyWeight_blue {c : ℕ} (x : ℝ)
    {y : Fin c → ℝ} (hy : ∀ i, 0 < y i) (k : ℕ)
    {l : Fin c → ℕ} (hl : ∀ i, 2 ≤ l i) (j : Fin c) :
    multiRamseyWeight x y k (lowerVector l j) =
      y j * multiRamseyWeight x y k l := by
  unfold multiRamseyWeight lowerVector
  have hj : j ∈ (Finset.univ : Finset (Fin c)) := Finset.mem_univ j
  have hfun :
      (fun i => (y i)⁻¹ ^ (Function.update l j (l j - 1) i - 1)) =
        Function.update (fun i => (y i)⁻¹ ^ (l i - 1)) j
          ((y j)⁻¹ ^ (l j - 1 - 1)) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij]
  rw [hfun, Finset.prod_update_of_mem hj]
  have hlj := hl j
  have he : l j - 1 = (l j - 1 - 1) + 1 := by omega
  have hypow :
      y j * (y j)⁻¹ ^ (l j - 1) =
        (y j)⁻¹ ^ (l j - 1 - 1) := by
    nth_rw 1 [he]
    rw [pow_succ]
    field_simp [(hy j).ne']
  have hprod :
      (∏ i ∈ (Finset.univ : Finset (Fin c)) \ {j},
          (y i)⁻¹ ^ (l i - 1)) *
          (y j)⁻¹ ^ (l j - 1) =
        ∏ i : Fin c, (y i)⁻¹ ^ (l i - 1) := by
    simpa only [Finset.sdiff_singleton_eq_erase] using
      Finset.prod_erase_mul (Finset.univ : Finset (Fin c))
        (fun i => (y i)⁻¹ ^ (l i - 1)) hj
  rw [← hprod, ← hypow]
  ring

/-- The weighted expression dominates the recursive bound. -/
theorem multiRamseyRecBound_le_weight {c : ℕ}
    {x : ℝ} {y : Fin c → ℝ}
    (hx : 0 < x) (hy : ∀ i, 0 < y i)
    (hsum : x + ∑ i, y i ≤ 1) :
    ∀ k l, 1 ≤ k → (∀ i, 1 ≤ l i) →
      (multiRamseyRecBound k l : ℝ) ≤
        multiRamseyWeight x y k l := by
  intro k l
  induction k, l using multiRamseyRecBound.induct with
  | case1 k l hbase =>
      intro hk hl
      rw [multiRamseyRecBound.eq_def, if_pos hbase]
      have hsum0 : 0 ≤ ∑ i, y i :=
        Finset.sum_nonneg fun i _ => (hy i).le
      have hx1 : x ≤ 1 := by linarith
      have hy1 : ∀ i, y i ≤ 1 := by
        intro i
        have hi : y i ≤ ∑ j, y j := Finset.single_le_sum
          (fun j _ => (hy j).le) (Finset.mem_univ i)
        linarith
      have hxInv : 1 ≤ x⁻¹ := (one_le_inv₀ hx).2 hx1
      have hyInv : ∀ i, 1 ≤ (y i)⁻¹ := fun i =>
        (one_le_inv₀ (hy i)).2 (hy1 i)
      have hprod : 1 ≤ ∏ i, (y i)⁻¹ ^ (l i - 1) := by
        apply Finset.one_le_prod
        intro i _
        exact one_le_pow₀ (hyInv i)
      have hxpow := one_le_pow₀ hxInv (n := k - 1)
      have hmul := mul_nonneg (sub_nonneg.mpr hxpow)
        (sub_nonneg.mpr hprod)
      dsimp [multiRamseyWeight]
      nlinarith
  | case2 k l hactive ihred ihblue =>
      intro hk hl
      have hk2 : 2 ≤ k := by
        by_contra
        apply hactive
        left
        omega
      have hl2 : ∀ i, 2 ≤ l i := by
        intro i
        by_contra
        apply hactive
        right
        exact ⟨i, by omega⟩
      have hred := ihred (by omega) hl
      have hblue : ∀ i,
          (multiRamseyRecBound k (lowerVector l i) : ℝ) ≤
            multiRamseyWeight x y k (lowerVector l i) := by
        intro i
        apply ihblue i hk
        intro j
        by_cases hji : j = i
        · subst j
          rw [lowerVector, Function.update_self]
          have := hl2 i
          omega
        · simp [lowerVector, hji, hl j]
      have hW0 : 0 ≤ multiRamseyWeight x y k l := by
        unfold multiRamseyWeight
        exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hx.le) _)
          (Finset.prod_nonneg fun i _ =>
            pow_nonneg (inv_nonneg.mpr (hy i).le) _)
      calc
        (multiRamseyRecBound k l : ℝ) =
            (multiRamseyRecBound (k - 1) l : ℝ) +
              ∑ i, (multiRamseyRecBound k (lowerVector l i) : ℝ) := by
          rw [multiRamseyRecBound.eq_def, if_neg hactive]
          push_cast
          rfl
        _ ≤ multiRamseyWeight x y (k - 1) l +
              ∑ i, multiRamseyWeight x y k (lowerVector l i) := by
          gcongr with i
          exact hblue i
        _ = x * multiRamseyWeight x y k l +
              ∑ i, y i * multiRamseyWeight x y k l := by
          rw [multiRamseyWeight_red hx y hk2 l]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact multiRamseyWeight_blue x hy k hl2 i
        _ = (x + ∑ i, y i) * multiRamseyWeight x y k l := by
          rw [← Finset.sum_mul]
          ring
        _ ≤ multiRamseyWeight x y k l := by
          nlinarith

/-- A complete edge coloring with one red and `c` blue colors. -/
structure MultiColoring (V : Type*) (c : ℕ) where
  graph : Fin (c + 1) → SimpleGraph V
  complete : ∀ u v : V, u ≠ v → ∃! i, (graph i).Adj u v

/-- Pull a complete edge coloring back along an embedding. -/
def MultiColoring.comap {V W : Type*} {c : ℕ}
    (C : MultiColoring V c) (f : W ↪ V) : MultiColoring W c where
  graph i := (C.graph i).comap f
  complete u v huv := by
    simpa using C.complete (f u) (f v) (f.injective.ne huv)

private lemma isNClique_of_comap {V W : Type*} {G : SimpleGraph V}
    {f : W ↪ V} {n : ℕ} {K : Finset W}
    (hK : (G.comap f).IsNClique n K) :
    G.IsNClique n (K.map f) :=
  hK.map.mono (SimpleGraph.map_comap_le f G)

private lemma exists_isNClique_of_le_one {V : Type*} [Nonempty V]
    (G : SimpleGraph V) {n : ℕ} (hn : n ≤ 1) :
    ∃ K : Finset V, G.IsNClique n K := by
  interval_cases n
  · exact ⟨∅, by simp⟩
  · exact ⟨{Classical.choice (inferInstance : Nonempty V)}, by simp⟩

/-- A monochromatic clique in color `i`. -/
def MultiColorClique {V : Type*} {c : ℕ}
    (C : MultiColoring V c) (i : Fin (c + 1)) (n : ℕ) : Prop :=
  ∃ K : Finset V, (C.graph i).IsNClique n K

/-- The desired red or blue monochromatic clique. -/
def MultiGood {V : Type*} {c : ℕ} (C : MultiColoring V c)
    (k : ℕ) (l : Fin c → ℕ) : Prop :=
  MultiColorClique C 0 k ∨
    ∃ i : Fin c, MultiColorClique C i.succ (l i)

/-- The multicolor Ramsey property at threshold `n`. -/
def MultiRamseyProperty {c : ℕ}
    (k : ℕ) (l : Fin c → ℕ) (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V],
    n ≤ Fintype.card V → ∀ C : MultiColoring V c, MultiGood C k l

private noncomputable def colorCell {V : Type*} [Fintype V]
    {c : ℕ} (C : MultiColoring V c) (v : V)
    (i : Fin (c + 1)) : Finset V := by
  classical
  exact Finset.univ.filter fun u => (C.graph i).Adj v u

@[simp]
private lemma mem_colorCell {V : Type*} [Fintype V]
    {c : ℕ} (C : MultiColoring V c) (v u : V)
    (i : Fin (c + 1)) :
    u ∈ colorCell C v i ↔ (C.graph i).Adj v u := by
  classical
  simp [colorCell]

private lemma colorCells_card {V : Type*} [Fintype V]
    {c : ℕ} (C : MultiColoring V c) (v : V) :
    ∑ i : Fin (c + 1), (colorCell C v i).card =
      Fintype.card V - 1 := by
  classical
  let S : Fin (c + 1) → Finset V := fun i => colorCell C v i
  have hdisj :
      ((Finset.univ : Finset (Fin (c + 1))) : Set (Fin (c + 1))).PairwiseDisjoint S := by
    intro i _ j _ hij
    change Disjoint (S i) (S j)
    rw [Finset.disjoint_left]
    intro u hui huj
    have hiAdj : (C.graph i).Adj v u := by simpa [S] using hui
    have hjAdj : (C.graph j).Adj v u := by simpa [S] using huj
    have hvu : v ≠ u := (C.graph i).ne_of_adj hiAdj
    obtain ⟨q, hq, hqunique⟩ := C.complete v u hvu
    have hiq := hqunique i hiAdj
    have hjq := hqunique j hjAdj
    exact hij (hiq.trans hjq.symm)
  have hunion :
      (Finset.univ : Finset (Fin (c + 1))).biUnion S =
        Finset.univ.erase v := by
    ext u
    constructor
    · intro hu
      rw [Finset.mem_biUnion] at hu
      obtain ⟨i, _, hui⟩ := hu
      have hadj : (C.graph i).Adj v u := by simpa [S] using hui
      rw [Finset.mem_erase]
      exact ⟨((C.graph i).ne_of_adj hadj).symm, Finset.mem_univ u⟩
    · intro hu
      have huv : u ≠ v := by simpa using hu
      obtain ⟨i, hi, _⟩ := C.complete v u huv.symm
      rw [Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, by simpa [S] using hi⟩
  have hcard := Finset.card_biUnion hdisj
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ v)] at hcard
  simpa [S] using hcard.symm

private lemma multiRamseyRecBound_pos {c : ℕ} :
    ∀ k (l : Fin c → ℕ), 0 < multiRamseyRecBound k l := by
  intro k l
  induction k, l using multiRamseyRecBound.induct with
  | case1 k l hbase =>
      simp [multiRamseyRecBound.eq_def, hbase]
  | case2 k l hactive ihred ihblue =>
      rw [multiRamseyRecBound.eq_def, if_neg hactive]
      exact Nat.add_pos_left ihred _

private lemma multiColorClique_comap_lift {V W : Type*} {c : ℕ}
    (C : MultiColoring V c) (f : W ↪ V) (i : Fin (c + 1)) (n : ℕ) :
    MultiColorClique (C.comap f) i n → MultiColorClique C i n := by
  rintro ⟨K, hK⟩
  exact ⟨K.map f, isNClique_of_comap hK⟩

/-- The recursive bound has the multicolor Ramsey property. -/
theorem multiRamseyProperty_recBound {c : ℕ} (hc : 1 ≤ c) :
    ∀ k (l : Fin c → ℕ),
      MultiRamseyProperty k l (multiRamseyRecBound k l) := by
  intro k l
  induction k, l using multiRamseyRecBound.induct with
  | case1 k l hbase =>
      intro V instF instD hcard C
      have hVcard : 1 ≤ Fintype.card V := by
        simpa [multiRamseyRecBound.eq_def, hbase] using hcard
      letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      rcases hbase with hk | ⟨i, hi⟩
      · exact Or.inl (exists_isNClique_of_le_one (C.graph 0) hk)
      · exact Or.inr ⟨i,
          exists_isNClique_of_le_one (C.graph i.succ) hi⟩
  | case2 k l hactive ihred ihblue =>
      intro V instF instD hcard C
      classical
      have hk2 : 2 ≤ k := by
        by_contra
        exact hactive (Or.inl (by omega))
      have hl2 : ∀ i, 2 ≤ l i := by
        intro i
        by_contra
        exact hactive (Or.inr ⟨i, by omega⟩)
      have hboundFormula :
          multiRamseyRecBound k l =
            multiRamseyRecBound (k - 1) l +
              ∑ i, multiRamseyRecBound k (lowerVector l i) := by
        rw [multiRamseyRecBound.eq_def, if_neg hactive]
      have hVpos : 0 < Fintype.card V :=
        (multiRamseyRecBound_pos k l).trans_le hcard
      letI : Nonempty V := Fintype.card_pos_iff.mp hVpos
      let v : V := Classical.choice (inferInstance : Nonempty V)
      let pred : Fin (c + 1) → ℕ :=
        Fin.cases (multiRamseyRecBound (k - 1) l)
          (fun i => multiRamseyRecBound k (lowerVector l i))
      have hpredSum : ∑ q, pred q = multiRamseyRecBound k l := by
        rw [Fin.sum_univ_succ]
        simp only [pred, Fin.cases_zero, Fin.cases_succ]
        exact hboundFormula.symm
      have hlarge : ∃ q : Fin (c + 1),
          pred q ≤ (colorCell C v q).card := by
        by_contra hnone
        push Not at hnone
        have hterm : ∀ q : Fin (c + 1),
            (colorCell C v q).card + 1 ≤ pred q := by
          intro q
          have := hnone q
          omega
        have hsumTerm := Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin (c + 1))))
          (fun q _ => hterm q)
        have hcells := colorCells_card C v
        rw [Finset.sum_add_distrib, hpredSum] at hsumTerm
        simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one] at hsumTerm
        rw [hcells] at hsumTerm
        change Fintype.card V - 1 + (c + 1) ≤
          multiRamseyRecBound k l at hsumTerm
        omega
      obtain ⟨q, hq⟩ := hlarge
      revert hq
      refine Fin.cases ?_ (fun i => ?_) q
      · intro hq
        let S := colorCell C v 0
        let W := {u : V // u ∈ S}
        let f : W ↪ V := Function.Embedding.subtype _
        have hWcardEq : Fintype.card W = S.card := by simp [W]
        have hWcard :
            multiRamseyRecBound (k - 1) l ≤ Fintype.card W := by
          rw [hWcardEq]
          simpa only [pred, Fin.cases_zero, S] using hq
        have hgood := ihred W hWcard (C.comap f)
        rcases hgood with hred | hblue
        · rcases hred with ⟨K, hK⟩
          let K' := K.map f
          have hK' : (C.graph 0).IsNClique (k - 1) K' :=
            isNClique_of_comap hK
          have hadj : ∀ u ∈ K', (C.graph 0).Adj v u := by
            intro u hu
            rcases Finset.mem_map.mp hu with ⟨w, hw, rfl⟩
            exact (mem_colorCell C v w.1 0).1 w.2
          have hins := hK'.insert hadj
          exact Or.inl ⟨insert v K', by
            convert hins using 1
            all_goals omega⟩
        · rcases hblue with ⟨j, hclique⟩
          exact Or.inr ⟨j,
            multiColorClique_comap_lift C f j.succ (l j) hclique⟩
      · intro hq
        let S := colorCell C v i.succ
        let W := {u : V // u ∈ S}
        let f : W ↪ V := Function.Embedding.subtype _
        have hWcardEq : Fintype.card W = S.card := by simp [W]
        have hWcard :
            multiRamseyRecBound k (lowerVector l i) ≤
              Fintype.card W := by
          rw [hWcardEq]
          simpa only [pred, Fin.cases_succ, S] using hq
        have hgood := ihblue i W hWcard (C.comap f)
        rcases hgood with hred | hblue
        · exact Or.inl (multiColorClique_comap_lift C f 0 k hred)
        · rcases hblue with ⟨j, K, hK⟩
          by_cases hji : j = i
          · subst j
            let K' := K.map f
            have hK' : (C.graph i.succ).IsNClique
                (lowerVector l i i) K' := isNClique_of_comap hK
            have hadj : ∀ u ∈ K', (C.graph i.succ).Adj v u := by
              intro u hu
              rcases Finset.mem_map.mp hu with ⟨w, hw, rfl⟩
              exact (mem_colorCell C v w.1 i.succ).1 w.2
            have hins := hK'.insert hadj
            refine Or.inr ⟨i, insert v K', ?_⟩
            have hli2 := hl2 i
            have hli : 1 ≤ l i := by omega
            simpa [lowerVector, Nat.sub_add_cancel hli] using hins
          · refine Or.inr ⟨j, K.map f, ?_⟩
            have hK' := isNClique_of_comap hK
            simpa [lowerVector, hji] using hK'

/-- Existence of a multicolor Ramsey threshold. -/
theorem multiRamseyProperty_exists {c : ℕ} (hc : 1 ≤ c)
    (k : ℕ) (l : Fin c → ℕ) :
    ∃ n, MultiRamseyProperty k l n :=
  ⟨multiRamseyRecBound k l, multiRamseyProperty_recBound hc k l⟩

/-- The least multicolor Ramsey threshold. -/
noncomputable def multiRamseyNumber {c : ℕ} (hc : 1 ≤ c)
    (k : ℕ) (l : Fin c → ℕ) : ℕ := by
  classical
  exact Nat.find (multiRamseyProperty_exists hc k l)

theorem multiRamseyNumber_spec {c : ℕ} (hc : 1 ≤ c)
    (k : ℕ) (l : Fin c → ℕ) :
    MultiRamseyProperty k l (multiRamseyNumber hc k l) := by
  classical
  exact Nat.find_spec (multiRamseyProperty_exists hc k l)

theorem multiRamseyNumber_le_recBound {c : ℕ} (hc : 1 ≤ c)
    (k : ℕ) (l : Fin c → ℕ) :
    multiRamseyNumber hc k l ≤ multiRamseyRecBound k l := by
  classical
  exact Nat.find_min' (multiRamseyProperty_exists hc k l)
    (multiRamseyProperty_recBound hc k l)

/-- Observation `o:easybound2`, with the impossible printed hypothesis
`0 > x > 1` corrected to `0 < x`. -/
theorem multiRamseyNumber_le_weight {c : ℕ} (hc : 1 ≤ c)
    {x : ℝ} {y : Fin c → ℝ}
    (hx : 0 < x) (hy : ∀ i, 0 < y i)
    (hsum : x + ∑ i, y i ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) {l : Fin c → ℕ}
    (hl : ∀ i, 1 ≤ l i) :
    (multiRamseyNumber hc k l : ℝ) ≤
      multiRamseyWeight x y k l := by
  calc
    (multiRamseyNumber hc k l : ℝ) ≤
        (multiRamseyRecBound k l : ℝ) := by
      exact_mod_cast multiRamseyNumber_le_recBound hc k l
    _ ≤ multiRamseyWeight x y k l :=
      multiRamseyRecBound_le_weight hx hy hsum k l hk hl

end Arxiv2407_19026

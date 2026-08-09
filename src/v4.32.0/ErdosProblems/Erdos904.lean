/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 904.
https://www.erdosproblems.com/forum/thread/904

Informal authors:
- Béla Bollobás
- Vladimir Nikiforov

Formal authors:
- Aristotle
- Parcly Taxel

URLs:
- https://www.erdosproblems.com/forum/thread/904#post-5573
- https://gist.githubusercontent.com/Parcly-Taxel/876d4eadd49a0d29db91ed2e790db733/raw/f33e0451100317b6eda0dd48c971e8105ff8ea75/E904.lean
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Set.Finite.List
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

namespace Erdos904

open List Finset

lemma Fin.sum_univ_sub {n : ℕ} (f : Fin (n + 1) → ℕ) (hf : ∀ i : Fin n, f i.succ ≤ f i.castSucc) :
    ∑ i : Fin n, (f i.castSucc - f i.succ) = f 0 - f (Fin.last n) := by
  rw [← Fin.antitone_iff_succ_le] at hf
  induction n with
  | zero => simp
  | succ n ih =>
    specialize ih (f ∘ Fin.succ) (hf.comp_monotone Fin.strictMono_succ.monotone)
    simp only [Function.comp_apply, ← Fin.castSucc_succ] at ih
    rw [Fin.sum_univ_succ, ih, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.succ_last]
    simp only [Nat.succ_eq_add_one]
    have := hf (show 0 ≤ 1 by lia)
    have := hf (show 1 ≤ Fin.last (n + 1) by rw [Fin.le_iff_val_le_val]; simp)
    grind

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (l : List V)

variable (V) in
/-- An abbreviation for the fixed number of vertices `n` in the graph. -/
abbrev n : ℕ := Fintype.card V

/-- `IsGreedyClique G l` means `l` is a possible partial output of Faudree's algorithm `𝔓`. -/
inductive IsGreedyClique (G : SimpleGraph V) [DecidableRel G.Adj] : List V → Prop
  | nil : IsGreedyClique G []
  | append_singleton (l : List V) (gc : IsGreedyClique G l) (v : V)
      (hmax : MaximalFor (∀ w ∈ l, G.Adj w ·) (G.degree ·) v) : IsGreedyClique G (l ++ [v])

/-- `IsPSequence G l` means `l` is a possible final output of Faudree's algorithm `𝔓`
aka `𝔓`-sequence. -/
def IsPSequence : Prop :=
  IsGreedyClique G l ∧ ∀ v, ∃ w ∈ l, ¬G.Adj w v

/-- The smallest 0-index `i` such that `l`'s prefix **up to and including** `i` satisfies
`∑ v ∈ prefix, d(v) ≤ (len(prefix) - 1) * n`. Returns `l.length` if no such `i` exists,
in which case `l` cannot be a `𝔓`-sequence (see `not_isPSequence_of_qIndex_eq_length`).

This number plus one is `q` in the paper. -/
def qIndex : ℕ :=
  (List.range l.length).findIdx fun i ↦ (l.take (i + 1) |>.map (G.degree ·) |>.sum) ≤ i * n V

/-- The 0-index of the first vertex in `l` not adjacent to `v`, capped at `qIndex G l`.
Equivalence classes form the partition `V_i` in section 2 of the paper. -/
def qClass (v : V) : Fin (qIndex G l + 1) :=
  ⟨min (l.findIdx (¬G.Adj · v)) (qIndex G l), by grind⟩

variable {l} in
/-- The 0-index of the first vertex in `l` not adjacent to `v`, capped at `l.length - 1`.
Equivalence classes form the partition `V_i` in section 3 of the paper. -/
def lengthClass (hl : l.length ≠ 0) (v : V) : Fin l.length :=
  ⟨min (l.findIdx (¬G.Adj · v)) (l.length - 1), by grind⟩

variable {G l}

lemma degree_eq_sum (i : V) : G.degree i = ∑ j, if G.Adj i j then 1 else 0 :=
  G.degree_eq_sum_if_adj i

/-- Introduced by Aristotle -/
lemma adj_take_of_qClass {v : V} {c : ℕ} (hc : qClass G l v = c) :
    ∀ w ∈ l.take c, G.Adj w v := by
  grind [mem_iff_getElem, qClass]

omit [Fintype V] in
lemma adj_take_of_lengthClass {v : V} {c : Fin l.length} (hc : lengthClass G c.pos.ne' v = c) :
    ∀ w ∈ l.take c, G.Adj w v := by
  grind [mem_iff_getElem, lengthClass]

/-- Proved by Aristotle -/
lemma card_lengthClass_le {c : Fin l.length} (hl : l.length ≠ 0) (hc : c ≠ ⟨l.length - 1, by lia⟩) :
    #{v | lengthClass G hl v = c} ≤ n V - G.degree l[c] := by
  have : #{v | ¬G.Adj l[c] v} = n V - G.degree l[c] := by
    classical rw [← compl_filter, card_compl, degree_eq_sum, sum_boole, Nat.cast_id]
  rw [← this]
  refine card_le_card fun v mv ↦ ?_
  rw [mem_filter_univ] at mv ⊢
  grind [lengthClass]

namespace IsGreedyClique

variable (gc : IsGreedyClique G l)

include gc

/-- Proved by Aristotle -/
lemma isPrefix {l' : List V} (hl' : l' <+: l) : IsGreedyClique G l' := by
  induction gc generalizing l' with
  | nil =>
    rw [prefix_nil] at hl'
    simp [hl', nil]
  | append_singleton l gc v hmax ih =>
    rw [prefix_concat_iff] at hl'
    obtain rfl | hl' := hl'
    · exact gc.append_singleton l v hmax
    · exact ih hl'

lemma take {r : ℕ} : IsGreedyClique G (l.take r) := gc.isPrefix (take_prefix ..)

lemma pairwise_adj : l.Pairwise G.Adj := by
  induction gc with
  | nil => exact Pairwise.nil
  | append_singleton l gc v hmax ih => simpa [pairwise_append] using ⟨ih, hmax.prop⟩

lemma nodup : l.Nodup := by
  rw [nodup_iff_pairwise_ne]
  exact gc.pairwise_adj.imp fun h ↦ h.ne

/-- Introduced by Aristotle -/
lemma degree_le_of_adj_all {v : V} (hadj : ∀ w ∈ l, G.Adj w v) :
    ∀ w ∈ l, G.degree v ≤ G.degree w := by
  induction gc with
  | nil => simp
  | append_singleton l gc w hmax ih =>
    simp_rw [mem_append, List.mem_singleton, or_imp, forall_and, forall_eq] at hadj ⊢
    exact ⟨ih hadj.1, hmax.le hadj.1⟩

/-- Proved by Aristotle -/
lemma degree_antitone : l.Pairwise (G.degree · ≥ G.degree ·) := by
  induction gc with
  | nil => exact Pairwise.nil
  | append_singleton l gc v hmax ih =>
    refine pairwise_append.mpr ⟨ih, pairwise_singleton .., ?_⟩
    simp_rw [List.mem_singleton, forall_eq]
    exact gc.degree_le_of_adj_all hmax.prop

/-- Introduced by Aristotle -/
lemma qClass_getElem_eq {c : ℕ} (hc : c < l.length) (hcq : c ≤ qIndex G l) :
    qClass G l l[c] = ⟨c, by lia⟩ := by
  suffices l.findIdx (¬G.Adj · l[c]) = c by
    rw [qClass, Fin.mk.injEq, this]
    exact min_eq_left hcq
  simp_rw [findIdx_eq hc, decide_eq_true_eq, _root_.SimpleGraph.irrefl, not_false_eq_true, true_and]
  intro i hi
  rw [decide_not, Bool.not_eq_false_eq_eq_true, decide_eq_true_eq]
  exact (pairwise_iff_get.mp gc.pairwise_adj) _ _ hi

/-- Introduced by Aristotle -/
lemma maximalFor_take {c : ℕ} (hc : c < l.length) :
    MaximalFor (∀ w ∈ l.take c, G.Adj w ·) (G.degree ·) l[c] := by
  induction gc generalizing c with
  | nil => tauto
  | append_singleton l gc v hmax ih =>
    rw [length_append, length_singleton, Nat.lt_add_one_iff] at hc
    obtain rfl | h := hc.eq_or_lt
    · simpa using hmax
    · rw [getElem_append_left h, take_append_of_le_length hc]
      exact ih h

variable {c : Fin l.length}

lemma lengthClass_getElem_eq : lengthClass G c.pos.ne' l[c] = c := by
  suffices l.findIdx (¬G.Adj · l[c]) = c by
    rw [lengthClass, Fin.mk.injEq, this]
    exact min_eq_left (by lia)
  simp_rw [findIdx_eq c.2, Fin.getElem_fin, _root_.SimpleGraph.irrefl, not_false_eq_true,
    decide_true, true_and, decide_not, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq]
  exact fun i hi ↦ (pairwise_iff_get.mp gc.pairwise_adj) _ _ hi

lemma maximalFor_lengthClass_self :
    MaximalFor (lengthClass G c.pos.ne' · = c) (G.degree ·) l[c] :=
  ⟨gc.lengthClass_getElem_eq, fun _ hv _ ↦ (gc.maximalFor_take c.2).le (adj_take_of_lengthClass hv)⟩

variable (hl : l.length ≠ 0)

lemma equation_15half :
    let z : Fin l.length := ⟨l.length - 1, by grind⟩
    let s := ∑ c : Fin l.length, (G.degree l[c] : ℤ)
    2 * #G.edgeFinset ≤ n V * s - ∑ c : Fin l.length, (G.degree l[c] ^ 2 : ℤ) +
      G.degree l[z] * (s - n V * (l.length - 1)) := by
  extract_lets z s
  calc
    _ ≤ ∑ c, #{v | lengthClass G hl v = c} * (G.degree l[c] : ℤ) := by
      norm_cast
      rw [← _root_.SimpleGraph.sum_degrees_eq_twice_card_edges,
        ← sum_fiberwise _ (lengthClass G hl ·)]
      refine Finset.sum_le_sum fun c _ ↦ ?_
      rw [← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun v cv ↦ ?_
      rw [mem_filter_univ] at cv
      exact gc.maximalFor_lengthClass_self.le cv
    _ ≤ n V * G.degree l[z] +
        ∑ c ∈ {z}ᶜ, (n V - G.degree l[c]) * (G.degree l[c] - G.degree l[z] : ℤ) := by
      conv_lhs =>
        enter [2, c]
        rw [← sub_add_cancel (G.degree l[c] : ℤ) (G.degree l[z]), mul_add]
      rw [sum_add_distrib, Fintype.sum_eq_add_sum_compl z, sub_self, mul_zero, zero_add, add_comm]
      have n_eq : n V = ∑ c, #{v | lengthClass G hl v = c} := by
        rw [n, Fintype.card_eq_sum_ones, ← sum_fiberwise _ (lengthClass G hl ·)]
        simp
      nth_rw 1 [n_eq, Nat.cast_sum, sum_mul]
      refine add_le_add_right (Finset.sum_le_sum fun c hc ↦ ?_) _
      rw [mem_compl, Finset.mem_singleton] at hc
      replace hc : c < z := by grind
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · rw [← Nat.cast_sub (G.degree_lt_card_verts _).le, Nat.cast_le]
        exact card_lengthClass_le hl hc.ne
      · rw [sub_nonneg, Nat.cast_le]
        have := gc.degree_antitone
        rw [pairwise_iff_get] at this
        exact this _ _ hc
    _ = _ := by
      conv_lhs =>
        simp only [mul_sub, sub_mul (n V : ℤ), ← sq, sum_sub_distrib]
      rw [sub_sub, ← add_sub_assoc,
        ← Fintype.sum_eq_add_sum_compl (f := fun c ↦ (n V : ℤ) * G.degree l[c]), ← mul_sum,
        sum_const]
      have cc : #{z}ᶜ = l.length - 1 := by rw [card_compl, card_singleton, Fintype.card_fin]
      rw [cc, Int.nsmul_eq_mul, Nat.cast_pred (Nat.zero_lt_of_ne_zero hl),
        ← add_sub_cancel_right (∑ c ∈ {z}ᶜ, _ ^ 2) (G.degree l[z] ^ 2 : ℤ),
        ← Fintype.sum_eq_sum_compl_add (f := fun c ↦ (G.degree l[c] ^ 2 : ℤ)), sub_sub,
        add_sub_left_comm, ← sub_sub, sub_eq_add_neg, neg_sub]
      congr
      rw [sq, ← sum_mul, ← add_mul, ← mul_assoc, ← sub_mul, mul_comm _ (n V : ℤ),
        ← Fintype.sum_eq_add_sum_compl (f := fun c ↦ (G.degree l[c] : ℤ)), mul_comm]

theorem equation_16 (h : n V * (l.length - 1) ≤ ∑ c : Fin l.length, G.degree l[c]) :
    2 * #G.edgeFinset * l.length ≤ n V * ∑ c : Fin l.length, G.degree l[c] := by
  obtain hl | hl := eq_or_ne l.length 0
  · simp [hl]
  zify
  let z : Fin l.length := ⟨l.length - 1, by grind⟩
  let s := ∑ c : Fin l.length, (G.degree l[c] : ℤ)
  calc
    _ ≤ (n V * s - ∑ c : Fin l.length, (G.degree l[c] ^ 2 : ℤ) +
        G.degree l[z] * (s - n V * (l.length - 1))) * l.length :=
      mul_le_mul_of_nonneg_right (gc.equation_15half hl) (by simp)
    _ ≤ n V * s * l.length - s ^ 2 + s * (s - n V * (l.length - 1)) := by
      rw [add_mul, sub_mul, mul_right_comm (G.degree l[z] : ℤ)]
      gcongr <;> unfold s
      · rw [mul_comm]
        conv_rhs =>
          enter [1]
          rw [← Fintype.card_fin l.length]
        exact sq_sum_le_card_mul_sum_sq
      · rwa [sub_nonneg, ← Nat.cast_pred (Nat.zero_lt_of_ne_zero hl), ← Nat.cast_mul,
          ← Nat.cast_sum, Nat.cast_le]
      · have rearr : ∑ c : Fin l.length, (G.degree l[z] : ℤ) = G.degree l[z] * l.length := by
          simp [mul_comm]
        rw [← rearr]
        norm_cast
        refine Finset.sum_le_sum fun c _ ↦ ?_
        have : Std.Refl (G.degree · ≥ G.degree ·) := ⟨fun _ ↦ le_rfl⟩
        exact gc.degree_antitone.rel_get_of_le (by grind)
    _ = _ := by ring

end IsGreedyClique

section

variable [Nonempty V]

lemma nil_not_isPSequence : ¬IsPSequence G [] := by simp [IsPSequence]

lemma not_isPSequence_of_qIndex_eq_length (hl : qIndex G l = l.length) : ¬IsPSequence G l := by
  obtain rfl | nl := eq_or_ne l []
  · exact nil_not_isPSequence
  rw [← length_pos_iff] at nl
  rw [← length_range (n := l.length), qIndex, findIdx_eq_length] at hl
  simp only [List.mem_range, decide_eq_false_iff_not, not_le] at hl
  specialize hl (l.length - 1) (by lia)
  rw [Nat.sub_one_add_one nl.ne', take_length, ← Fin.sum_univ_fun_getElem] at hl
  contrapose! hl
  replace hl := hl.2
  simp_rw [degree_eq_sum]
  rw [sum_comm]
  simp_rw [sum_boole, Nat.cast_id,
    show (l.length - 1) * n V = ∑ v : V, (l.length - 1) by simp [mul_comm]]
  refine sum_le_sum fun v _ ↦ ?_
  suffices 1 ≤ Fintype.card (Fin l.length) - #{i : Fin l.length | G.Adj l[i] v} by
    rw [Fintype.card_fin] at this
    have hlt : #{i : Fin l.length | G.Adj l[i] v} < l.length :=
      Nat.lt_of_sub_pos (zero_lt_one.trans_le this)
    simpa [Fin.getElem_fin] using Nat.le_sub_one_of_lt hlt
  rw [← card_compl, compl_filter, one_le_card]
  obtain ⟨w, mw, hw⟩ := hl v
  rw [mem_iff_getElem] at mw
  obtain ⟨i, li, rfl⟩ := mw
  exact ⟨⟨i, li⟩, by simp [hw]⟩

namespace IsPSequence

variable (pl : IsPSequence G l)

include pl

lemma qIndex_lt_length : qIndex G l < l.length := by
  contrapose! pl
  refine not_isPSequence_of_qIndex_eq_length (le_antisymm ?_ pl)
  rw [← length_range (n := l.length)]
  exact findIdx_le_length

/-- Get the `c`-th vertex of a `𝔓`-sequence, up to index `q`.
This is a shorthand to avoid having to provide the in-bounds proof every time. -/
def get (c : Fin (qIndex G l + 1)) : V :=
  l[c]'(by grind [pl.qIndex_lt_length])

lemma sum_degree_get_le_mul : ∑ i, G.degree (pl.get i) ≤ qIndex G l * n V := by
  have key := pl.qIndex_lt_length
  conv_rhs at key => rw [← length_range (n := l.length)]
  replace key := findIdx_getElem (w := key)
  simp only [getElem_range, decide_eq_true_eq] at key
  change ((l.take (qIndex G l + 1)).map (G.degree ·)).sum ≤ qIndex G l * n V at key
  convert key
  rw [Fin.sum_univ_def]
  congr 1
  refine ext_get (by simp [pl.qIndex_lt_length]) fun i _ _ ↦ ?_
  simp only [get, Fin.getElem_fin, get_eq_getElem, getElem_map, map_take, getElem_take]
  congr!
  simp

lemma mul_lt_sum_degree_get {s : ℕ} (hs : s < qIndex G l) :
    s * n V < ∑ i : Fin (s + 1), G.degree (pl.get (i.castLE (by lia))) := by
  have key := not_of_lt_findIdx hs
  simp_rw [getElem_range, decide_eq_false_iff_not, not_le] at key
  convert key <;> try rfl
  rw [Fin.sum_univ_def]
  congr 1
  refine ext_get (by grind [pl.qIndex_lt_length]) fun i _ _ ↦ ?_
  simp only [get, Fin.getElem_fin, get_eq_getElem, getElem_map, map_take, getElem_take]
  congr!
  simp

lemma pred_mul_lt_sum_degree_get {r : ℕ} (hr : r ∈ Set.Icc 1 (qIndex G l)) :
    (r - 1) * n V < ∑ i : Fin r, G.degree (pl.get (i.castLE (by grind))) := by
  rw [Set.mem_Icc] at hr
  convert pl.mul_lt_sum_degree_get (show r - 1 < qIndex G l by lia) <;> lia

/-- Proved by Aristotle -/
lemma maximalFor_qClass_self {c : Fin (qIndex G l + 1)} :
    MaximalFor (qClass G l · = c) (G.degree ·) (pl.get c) := by
  unfold get
  generalize_proofs bc
  exact ⟨pl.1.qClass_getElem_eq bc (by lia),
    fun v hv _ ↦ (pl.1.maximalFor_take bc).le (adj_take_of_qClass (Fin.val_eq_of_eq hv))⟩

/-- The finset of **c**ommon **n**eighbours of the `𝔓`-sequence's vertices
in the **r**ange `[0,c)`. $\widehat{Γ}([c])$ in the paper. -/
def cnr (c : Fin (qIndex G l + 1)) : Finset V :=
  {v | ∀ j < c, G.Adj (pl.get j) v}

lemma cnr_succ_subset_cnr_castSucc {i : Fin (qIndex G l)} :
    pl.cnr i.succ ⊆ pl.cnr i.castSucc := fun v mv ↦ by
  simp only [cnr, mem_filter_univ] at mv ⊢
  exact fun j mj ↦ mv j (mj.trans Fin.castSucc_lt_succ)

lemma card_qClass_eq_cast {i : Fin (qIndex G l)} :
    #{v | qClass G l v = i.castSucc} = #(pl.cnr i.castSucc) - #(pl.cnr i.succ) := by
  classical rw [← card_sdiff_of_subset pl.cnr_succ_subset_cnr_castSucc]
  congr
  ext v
  simp_rw [mem_filter_univ, qClass, Fin.ext_iff, Fin.val_castSucc]
  have meq : min (findIdx (¬G.Adj · v) l) (qIndex G l) = i ↔ findIdx (¬G.Adj · v) l = i := by grind
  rw [meq, findIdx_eq (by grind [pl.qIndex_lt_length])]
  simp_rw [decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Bool.not_false, decide_eq_true_eq, mem_sdiff, cnr, mem_filter_univ, get]
  conv_rhs =>
    enter [2, 1, j]
    rw [← Fin.le_castSucc_iff, le_iff_lt_or_eq, or_imp]
  rw [forall_and, forall_eq, not_and_or, and_or_left, and_not_self_iff, false_or, and_comm]
  exact Iff.and ⟨fun h j ↦ h j.1, fun h j hj ↦ h ⟨j, by lia⟩ (by simp [Fin.lt_def, hj])⟩ Iff.rfl

lemma card_qClass_eq_last : #{v | qClass G l v = Fin.last _} = #(pl.cnr (Fin.last _)) := by
  have key : n V = ∑ c, ∑ v with qClass G l v = c, 1 := by
    rw [sum_fiberwise, ← Fintype.card_eq_sum_ones]
  simp_rw [sum_const, smul_eq_mul, mul_one, Fin.sum_univ_castSucc, pl.card_qClass_eq_cast] at key
  have hf (i : Fin (qIndex G l)) : #(pl.cnr i.succ) ≤ #(pl.cnr i.castSucc) :=
    card_le_card pl.cnr_succ_subset_cnr_castSucc
  rw [Fin.sum_univ_sub (fun i ↦ #(pl.cnr i)) hf, show #(pl.cnr 0) = n V by simp [cnr]] at key
  suffices #(pl.cnr (Fin.last (qIndex G l))) ≤ n V by lia
  exact card_le_univ _

lemma equation_8 :
    2 * #G.edgeFinset ≤ n V * G.degree (pl.get 0) + ∑ i : Fin (qIndex G l),
      #(pl.cnr i.succ) * (G.degree (pl.get i.succ) - G.degree (pl.get i.castSucc) : ℤ) := by
  let d (c : Fin (qIndex G l + 1)) : ℕ := G.degree (pl.get c)
  change _ ≤ n V * d 0 + ∑ i : Fin (qIndex G l), #(pl.cnr i.succ) * (d i.succ - d i.castSucc : ℤ)
  calc
    _ ≤ (∑ c, #{v | qClass G l v = c} * d c : ℤ) := by
      norm_cast
      rw [← _root_.SimpleGraph.sum_degrees_eq_twice_card_edges, ← sum_fiberwise _ (qClass G l ·)]
      refine Finset.sum_le_sum fun c _ ↦ ?_
      rw [← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun v cv ↦ ?_
      rw [mem_filter_univ] at cv
      exact pl.maximalFor_qClass_self.le cv
    _ = ∑ i : Fin (qIndex G l), #(pl.cnr i.castSucc) * (d i.castSucc : ℤ) +
        #(pl.cnr (Fin.last (qIndex G l))) * d (Fin.last (qIndex G l)) -
        ∑ i : Fin (qIndex G l), #(pl.cnr i.succ) * (d i.castSucc : ℤ) := by
      have n_anti {i : Fin (qIndex G l)} : #(pl.cnr i.succ) ≤ #(pl.cnr i.castSucc) :=
        card_le_card pl.cnr_succ_subset_cnr_castSucc
      simp_rw [Fin.sum_univ_castSucc, card_qClass_eq_cast pl, card_qClass_eq_last pl,
        Nat.cast_sub n_anti, sub_mul, sum_sub_distrib]
      exact sub_add_eq_add_sub ..
    _ = n V * d 0 + ∑ i : Fin (qIndex G l), #(pl.cnr i.succ) * (d i.succ : ℤ) -
        ∑ i : Fin (qIndex G l), #(pl.cnr i.succ) * (d i.castSucc : ℤ) := by
      rw [← Fin.sum_univ_castSucc fun i ↦ #(pl.cnr i) * (d i : ℤ), Fin.sum_univ_succ]
      simp [cnr]
    _ = _ := by
      rw [add_sub_assoc, ← sum_sub_distrib]
      congr! 2 with i
      rw [mul_sub]

/-- The number of vertices not adjacent to the vertex with index `c` if `c < q`,
and the number of remaining vertices if `c = q`. $k_c$ in the paper. -/
def adeg (c : Fin (qIndex G l + 1)) : ℕ :=
  c.lastCases (n V - ∑ i : Fin (qIndex G l), (n V - G.degree (pl.get i.castSucc)))
    fun i ↦ n V - G.degree (pl.get i.castSucc)

/-- Proved by Aristotle -/
lemma adeg_pos {c : Fin (qIndex G l + 1)} : 0 < pl.adeg c := by
  unfold adeg
  cases c using Fin.lastCases with
  | cast i => simp [_root_.SimpleGraph.degree_lt_card_verts]
  | last =>
    rw [Fin.lastCases_last, tsub_pos_iff_lt]
    rcases eq_or_ne (qIndex G l) 0 with h | h
    · simp_rw [sum_fin_eq_sum_range, h]
      exact Fintype.card_pos
    · have e :
          ∑ i : Fin (qIndex G l), (n V - G.degree (pl.get i.castSucc)) +
          ∑ i : Fin (qIndex G l), G.degree (pl.get i.castSucc) = qIndex G l * n V := by
        simp_rw [← sum_add_distrib, Nat.sub_add_cancel (G.degree_lt_card_verts _).le, sum_const,
          card_fin, smul_eq_mul]
      conv_rhs at e => rw [← Nat.sub_one_add_one h, add_one_mul]
      suffices (qIndex G l - 1) * n V < ∑ i : Fin (qIndex G l), G.degree (pl.get i.castSucc) by lia
      have key := not_of_lt_findIdx (Nat.sub_one_lt h)
      simp_rw [getElem_range, decide_eq_false_iff_not, not_le] at key
      change (qIndex G l - 1) * n V < ((l.take (qIndex G l - 1 + 1)).map (G.degree ·)).sum at key
      rw [Nat.sub_one_add_one h] at key
      convert key
      rw [Fin.sum_univ_def]
      congr 1
      exact ext_get (by simp [pl.qIndex_lt_length.le]) fun _ _ _ ↦ by
        simp [get, finRange]
        congr

/-- Proved by Aristotle -/
lemma sum_adeg : ∑ i, pl.adeg i = n V := by
  simp_rw [Fin.sum_univ_castSucc, adeg, Fin.lastCases_castSucc, Fin.lastCases_last]
  apply Nat.add_sub_of_le
  have := pl.adeg_pos (c := Fin.last _)
  rw [adeg, Fin.lastCases_last, tsub_pos_iff_lt] at this
  exact this.le

lemma sub_adeg_last_eq :
    n V - pl.adeg (Fin.last _) = ∑ i : Fin (qIndex G l), pl.adeg i.castSucc := by
  rw [← pl.sum_adeg, Fin.sum_univ_castSucc, add_tsub_cancel_right]

/-- Proved by Aristotle -/
lemma equation_9 {i : Fin (qIndex G l)} : n V - ∑ j ≤ i, pl.adeg j.castSucc ≤ #(pl.cnr i.succ) := by
  apply Nat.sub_le_of_le_add
  have key : n V ≤ ∑ v, ((if ∀ j ≤ i, G.Adj (pl.get j.castSucc) v then 1 else 0) +
      ∑ j ≤ i, if ¬G.Adj (pl.get j.castSucc) v then 1 else 0) := by
    simp only [Fintype.card_eq_sum_ones]
    refine Finset.sum_le_sum fun v _ ↦ ?_
    split_ifs with h
    · lia
    · simp only [not_forall] at h
      rw [zero_add, sum_ite, sum_const_zero, ← card_eq_sum_ones, add_zero, one_le_card]
      obtain ⟨j, hj, jj⟩ := h
      exact ⟨j, mem_filter.mpr ⟨mem_Iic.mpr hj, jj⟩⟩
  simp_rw [ite_not, sum_add_distrib, sum_boole, Nat.cast_id] at key
  refine key.trans (add_le_add (card_le_card fun v hv ↦ ?_) ?_)
  · simp_rw [cnr, mem_filter_univ] at hv ⊢
    exact fun j hj ↦ hv ⟨j.1, by lia⟩ (Nat.le_of_lt_succ hj)
  · classical
    rw [sum_comm]
    exact sum_le_sum fun v _ ↦ by rw [sum_ite, sum_const_zero, zero_add, ← card_eq_sum_ones, adeg,
      Fin.lastCases_castSucc, degree_eq_sum, ← card_filter, ← card_compl, compl_filter]

/-- Proved by Aristotle -/
lemma equation_10 :
    G.degree (pl.get (Fin.last _)) ≤ ∑ i : Fin (qIndex G l), pl.adeg i.castSucc := by
  have key := pl.sum_degree_get_le_mul
  simp only [adeg, Fin.sum_univ_castSucc, Fin.lastCases_castSucc] at key ⊢
  have e : ∑ i : Fin (qIndex G l), (n V - G.degree (pl.get i.castSucc)) =
      qIndex G l * n V - ∑ i : Fin (qIndex G l), G.degree (pl.get i.castSucc) := by
    rw [sum_tsub_distrib _ fun _ _ ↦ (G.degree_lt_card_verts _).le, sum_const, card_fin,
      smul_eq_mul, mul_comm]
  lia

lemma equation_11a : 2 * #G.edgeFinset ≤
    ∑ i : Fin (qIndex G l), (pl.adeg i.castSucc : ℤ) * G.degree (pl.get i.castSucc) +
      G.degree (pl.get (Fin.last _)) * pl.adeg (Fin.last _) := by
  calc
    _ ≤ _ := pl.equation_8
    _ ≤ n V * G.degree (pl.get 0) +
        ∑ i : Fin (qIndex G l), (n V - ∑ j ≤ i, (pl.adeg j.castSucc : ℤ)) *
          (G.degree (pl.get i.succ) - G.degree (pl.get i.castSucc)) := by
      refine add_le_add_right (Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonpos_right ?_ ?_) _
      · have sl : ∑ j ≤ i, pl.adeg j.castSucc ≤ n V := by
          rw [← pl.sum_adeg, Fin.sum_univ_castSucc]
          exact Nat.le_add_right_of_le (sum_le_univ_sum_of_nonneg (by lia))
        rw [← Nat.cast_sum, ← Nat.cast_sub sl, Nat.cast_le]
        exact pl.equation_9
      · rw [sub_nonpos, Nat.cast_le]
        have := pl.1.degree_antitone
        rw [pairwise_iff_get] at this
        exact this _ _ (Nat.lt_succ_self _)
    _ = ∑ i : Fin (qIndex G l), (pl.adeg i.castSucc : ℤ) * G.degree (pl.get i.castSucc) +
        G.degree (pl.get (Fin.last _)) * pl.adeg (Fin.last _) := by
      simp_rw [sub_mul, mul_sub, sum_sub_distrib, ← add_sub_assoc]
      rw [← Fin.sum_univ_succ fun i ↦ (n V * G.degree (pl.get i) : ℤ), Fin.sum_univ_castSucc,
        add_sub_cancel_left, sub_sub_eq_add_sub, add_comm, ← pl.sum_adeg, Nat.cast_sum]
      have e₁ (i : Fin (qIndex G l)) := sum_map (Iic i) Fin.castSuccEmb fun j ↦ (pl.adeg j : ℤ)
      simp_rw [Fin.map_castSuccEmb_Iic, Fin.coe_castSuccEmb] at e₁
      simp_rw [← e₁]
      have s : Iic (Fin.last (qIndex G l)) = univ := by simp [eq_univ_iff_forall, Fin.le_last]
      rw [← s, ← Fin.sum_univ_castSucc fun i ↦ (∑ x ∈ Iic i, (pl.adeg x : ℤ)) * G.degree (pl.get i),
        Fin.sum_univ_succ, add_sub_assoc, ← sum_sub_distrib]
      simp_rw [← sub_mul]
      have s₁ (i : Fin (qIndex G l)) : Iic i.castSucc ⊆ Iic i.succ := by
        rw [Iic_subset_Iic]
        exact Fin.castSucc_le_succ _
      have e₃ (i : Fin (qIndex G l)) : Iic i.succ \ Iic i.castSucc = {i.succ} := by
        ext j
        simp_rw [mem_sdiff, mem_Iic, not_le, Finset.mem_singleton, Fin.castSucc_lt_iff_succ_le,
          le_antisymm_iff]
      conv_lhs =>
        enter [2, 2, i]
        rw [← sum_sdiff (s₁ i), e₃, Finset.sum_singleton, add_sub_cancel_right]
      rw [show Iic (0 : Fin (qIndex G l + 1)) = {0} by ext; simp, Finset.sum_singleton,
        ← Fin.sum_univ_succ fun i ↦ (pl.adeg i : ℤ) * G.degree (pl.get i), Fin.sum_univ_castSucc,
        mul_comm]

/-- We break the proof of equation 11 here so we can later substitute a strict version
to prove the lower bound on the degree sum. -/
lemma equation_11b :
    ∑ i : Fin (qIndex G l), (pl.adeg i.castSucc : ℤ) * G.degree (pl.get i.castSucc) +
      G.degree (pl.get (Fin.last _)) * pl.adeg (Fin.last _) ≤
    ∑ i : Fin (qIndex G l), (pl.adeg i.castSucc : ℤ) * G.degree (pl.get i.castSucc) +
      (∑ i : Fin (qIndex G l), (pl.adeg i.castSucc : ℤ)) * pl.adeg (Fin.last _) := by
  gcongr
  rw [← Nat.cast_sum, Nat.cast_le]
  exact pl.equation_10

lemma equation_11c :
    ∑ i : Fin (qIndex G l), (pl.adeg i.castSucc : ℤ) * G.degree (pl.get i.castSucc) +
      (∑ i : Fin (qIndex G l), (pl.adeg i.castSucc : ℤ)) * pl.adeg (Fin.last _) =
    ∑ i, ∑ j with i ≠ j, (pl.adeg i * pl.adeg j : ℤ) := by
  have {i : Fin (qIndex G l)} : (n V - pl.adeg i.castSucc : ℤ) = G.degree (pl.get i.castSucc) := by
    rw [adeg, Fin.lastCases_castSucc, Nat.cast_sub (G.degree_lt_card_verts _).le, sub_sub_cancel]
  simp_rw [← this, mul_sub, ← sq, sum_sub_distrib]
  have e : (∑ i : Fin (qIndex G l), pl.adeg i.castSucc : ℤ) = n V - pl.adeg (Fin.last _) := by
    rw [eq_sub_iff_add_eq, ← Nat.cast_sum, ← Nat.cast_add, ← pl.sum_adeg, Fin.sum_univ_castSucc]
  rw [e, sub_mul, ← sq, sub_add_sub_comm, ← Fin.sum_univ_castSucc fun i ↦ (pl.adeg i ^ 2 : ℤ),
    ← sum_mul, mul_comm, ← mul_add, ← Fin.sum_univ_castSucc fun i ↦ (pl.adeg i : ℤ),
    sub_eq_iff_eq_add]
  have e₂ : ∑ i, (pl.adeg i ^ 2 : ℤ) = ∑ i, ∑ j with i = j, (pl.adeg i * pl.adeg j : ℤ) := by
    simp only [sum_filter, sum_ite_eq, mem_univ, ↓reduceIte, sq]
  rw [e₂, add_comm (Finset.sum ..), ← sum_add_distrib]
  simp_rw [sum_filter_add_sum_filter_not, ← pl.sum_adeg, Nat.cast_sum, sum_mul, mul_sum]

theorem equation_11 : 2 * #G.edgeFinset ≤ ∑ i, ∑ j with i ≠ j, pl.adeg i * pl.adeg j :=
  mod_cast pl.equation_11a |>.trans pl.equation_11b |>.trans_eq pl.equation_11c

end IsPSequence

end

section TuranNumber

/-- The number of edges in the `r`-chromatic Turán graph on `n` vertices aka `t_r(n)`. -/
abbrev turanNumber (n r : ℕ) : ℕ := #(_root_.SimpleGraph.turanGraph n r).edgeFinset

/-- Proved by Aristotle -/
lemma pair_sum_mul_le_turanNumber {n : ℕ} {f : Fin n → ℕ} :
    ∑ i, ∑ j with i ≠ j, f i * f j ≤ 2 * turanNumber (∑ i, f i) n := by
  let H : SimpleGraph (Σ i, Fin (f i)) := ⟨fun x y ↦ x.1 ≠ y.1, by tauto, by tauto⟩
  have cfH : H.CliqueFree (n + 1) := fun s ⟨hs₁, hs₂⟩ ↦ by
    have c := (s.image (·.1)).card_le_univ
    rw [Fintype.card_fin] at c
    apply absurd c
    have ic : (SetLike.coe s).InjOn (·.1) := fun v mv w mw e ↦ not_imp_not.mp (hs₁ mv mw) e
    rw [not_le, card_image_of_injOn ic]
    lia
  replace cfH := cfH.card_edgeFinset_le
  simp_rw [← _root_.SimpleGraph.card_edgeFinset_turanGraph] at cfH
  rw [show Fintype.card (Σ i, Fin (f i)) = ∑ i, f i by simp] at cfH
  have eH : ∑ i, ∑ j with i ≠ j, f i * f j = 2 * #H.edgeFinset := by
    simp_rw [← _root_.SimpleGraph.sum_degrees_eq_twice_card_edges, degree_eq_sum,
      Fintype.sum_sigma, H]
    have rsum (c₁ c₂ : Fin n) :
        (∑ x : Fin (f c₁), ∑ y : Fin (f c₂), if c₁ ≠ c₂ then 1 else 0) =
        if c₁ ≠ c₂ then f c₁ * f c₂ else 0 := by simp
    conv_rhs =>
      enter [2, c₁]
      rw [sum_comm]
      enter [2, c₂]
      rw [rsum]
    simp_rw [sum_filter]
  rwa [eH, mul_le_mul_iff_right₀ zero_lt_two]

/-- Proved by Aristotle -/
lemma strictMonoOn_turanNumber {n : ℕ} : StrictMonoOn (turanNumber n) (Set.Icc 1 n) := by
  rintro a ⟨lba, -⟩ b ⟨lbb, ubb⟩ hab
  by_contra! ht
  have itm : (_root_.SimpleGraph.turanGraph n a).IsTuranMaximal b := by
    constructor
    · exact (_root_.SimpleGraph.turanGraph_cliqueFree lba).mono (by lia)
    · exact fun G' _ hG' ↦
        ((_root_.SimpleGraph.isTuranMaximal_turanGraph lbb).2 hG').trans ht
  replace itm :
      Nonempty (_root_.SimpleGraph.turanGraph n a ≃g _root_.SimpleGraph.turanGraph n b) := by
    obtain ⟨g⟩ := itm.nonempty_iso_turanGraph
    rw [Fintype.card_fin] at g
    exact ⟨g⟩
  obtain ⟨f⟩ := itm
  apply absurd ((_root_.SimpleGraph.turanGraph_cliqueFree lba).comap f.symm.toEmbedding.isContained)
  have key := _root_.SimpleGraph.not_cliqueFree_of_isTuranMaximal (by simp [ubb])
    (@_root_.SimpleGraph.isTuranMaximal_turanGraph n _ lbb)
  contrapose key
  exact key.mono hab

end TuranNumber

variable (pl : IsPSequence G l)
  {r : ℕ} (hr : r ∈ Set.Icc 1 (n V)) (hm : turanNumber (n V) r ≤ #G.edgeFinset)

include hr in
lemma nonempty_of_params : Nonempty V := by
  rw [← Fintype.card_pos_iff]
  grind

namespace IsPSequence

include pl hr hm in
theorem equation_12 : r ≤ qIndex G l + 1 := by
  let _ := nonempty_of_params hr
  rw [← mul_le_mul_iff_right₀ zero_lt_two] at hm
  have key := hm.trans (pl.equation_11.trans pair_sum_mul_le_turanNumber)
  have bq : qIndex G l + 1 ∈ Set.Icc 1 (n V) :=
    ⟨by lia, pl.qIndex_lt_length.trans_le pl.1.nodup.length_le_card⟩
  rwa [pl.sum_adeg, mul_le_mul_iff_right₀ zero_lt_two,
    strictMonoOn_turanNumber.le_iff_le hr bq] at key

lemma equation_10_strict (_ := nonempty_of_params hr) :
    ∑ i, G.degree (pl.get i) < qIndex G l * n V →
    G.degree (pl.get (Fin.last _)) < ∑ i : Fin (qIndex G l), pl.adeg i.castSucc := by
  simp only [IsPSequence.adeg, Fin.sum_univ_castSucc, Fin.lastCases_castSucc]
  have e : ∑ i : Fin (qIndex G l), (n V - G.degree (pl.get i.castSucc)) =
      qIndex G l * n V - ∑ i : Fin (qIndex G l), G.degree (pl.get i.castSucc) := by
    rw [sum_tsub_distrib _ fun _ _ ↦ (G.degree_lt_card_verts _).le, sum_const, card_fin,
      smul_eq_mul, mul_comm]
  lia

lemma equation_11b_strict (_ := nonempty_of_params hr) :
    ∑ i, G.degree (pl.get i) < qIndex G l * n V →
    ∑ i : Fin (qIndex G l), (pl.adeg i.castSucc : ℤ) * G.degree (pl.get i.castSucc) +
      G.degree (pl.get (Fin.last _)) * pl.adeg (Fin.last _) <
    ∑ i : Fin (qIndex G l), (pl.adeg i.castSucc : ℤ) * G.degree (pl.get i.castSucc) +
      (∑ i : Fin (qIndex G l), (pl.adeg i.castSucc : ℤ)) * pl.adeg (Fin.last _) := by
  intro h
  gcongr <;> norm_cast
  · exact pl.adeg_pos
  · exact pl.equation_10_strict hr _ h

lemma equation_11_strict (_ := nonempty_of_params hr) :
    ∑ i, G.degree (pl.get i) < qIndex G l * n V →
    2 * #G.edgeFinset < ∑ i, ∑ j with i ≠ j, pl.adeg i * pl.adeg j := by
  intro h
  exact_mod_cast pl.equation_11a |>.trans_lt (pl.equation_11b_strict hr _ h)
    |>.trans_eq pl.equation_11c

include hm in
theorem equation_12_strict (_ := nonempty_of_params hr) :
    ∑ i, G.degree (pl.get i) < qIndex G l * n V → r ≤ qIndex G l := by
  intro h
  rw [← mul_le_mul_iff_right₀ zero_lt_two] at hm
  have key := hm.trans_lt ((pl.equation_11_strict hr _ h).trans_le pair_sum_mul_le_turanNumber)
  have bq : qIndex G l + 1 ∈ Set.Icc 1 (n V) :=
    ⟨by lia, pl.qIndex_lt_length.trans_le pl.1.nodup.length_le_card⟩
  rwa [pl.sum_adeg, mul_lt_mul_iff_right₀ zero_lt_two,
    strictMonoOn_turanNumber.lt_iff_lt hr bq, Nat.lt_add_one_iff] at key

theorem sum_degree_lower_bound (_ := nonempty_of_params hr) :
    (r - 1) * n V ≤ ∑ i : Fin r, G.degree (pl.get (i.castLE (pl.equation_12 hr hm))) := by
  generalize_proofs e12
  by_contra! h
  obtain rfl | hrq := e12.eq_or_lt
  · simp_rw [add_tsub_cancel_right, Fin.castLE_refl] at h
    grind [pl.equation_12_strict hr hm _ h]
  · exact lt_asymm h (pl.pred_mul_lt_sum_degree_get ⟨hr.1, by lia⟩)

include pl hr hm in
theorem mul_length_sub_one_le_sum_take :
    let l' := l.take r
    n V * (l'.length - 1) ≤ ∑ c : Fin l'.length, G.degree l'[c] := by
  extract_lets l'
  let _ := nonempty_of_params hr
  have len_take : l'.length = r :=
    length_take_of_le (by grind [pl.equation_12 hr hm, pl.qIndex_lt_length])
  simp_rw [len_take, mul_comm (n V)]
  convert pl.sum_degree_lower_bound hr hm using 1
  simp_rw [Fin.sum_univ_def]
  congr 1
  refine ext_get (by simp [len_take]) fun i _ _ ↦ ?_
  simp only [Fin.getElem_fin, get_eq_getElem, getElem_map]
  congr!
  simp only [getElem_finRange, Fin.cast_mk, get, Fin.castLE_mk, Fin.getElem_fin]
  exact getElem_take

end IsPSequence

/-- Proved by Aristotle -/
theorem exists_isPSequence : ∃ l, IsPSequence G l := by
  classical
  have fgc : {l | IsGreedyClique G l}.Finite := by
    refine (finite_length_le V (n V)).subset fun l gc ↦ ?_
    have := card_le_univ l.toFinset
    rwa [toFinset_card_of_nodup gc.nodup] at this
  obtain ⟨l, gc, maxl⟩ := fgc.exists_maximalFor length _ ⟨_, .nil⟩
  refine ⟨l, gc, fun v ↦ ?_⟩
  contrapose! maxl
  obtain ⟨u, hu⟩ := {u | ∀ w ∈ l, G.Adj w u}.toFinite.exists_maximalFor (G.degree ·) _ ⟨_, maxl⟩
  exact ⟨_, gc.append_singleton _ _ hu, by simp⟩

include hr hm in
/-- Erdős Problem 904. -/
theorem erdos904 : ∃ s, G.IsNClique r s ∧ 2 * r * #G.edgeFinset ≤ n V * ∑ v ∈ s, G.degree v := by
  let _ := nonempty_of_params hr
  obtain ⟨l, pl⟩ : ∃ l, IsPSequence G l := exists_isPSequence
  have key := pl.1.take.equation_16 (pl.mul_length_sub_one_le_sum_take hr hm)
  have nodup_take : (l.take r).Nodup := pl.1.take.nodup
  have len_take : (l.take r).length = r :=
    length_take_of_le (by grind [pl.equation_12 hr hm, pl.qIndex_lt_length])
  classical
  refine ⟨(l.take r).toFinset, ?_, ?_⟩
  · constructor
    · haveI : Std.Symm G.Adj := ⟨fun _ _ h ↦ h.symm⟩
      rw [_root_.SimpleGraph.IsClique, pairwise_iff_coe_toFinset_pairwise nodup_take]
      exact pl.1.pairwise_adj.take
    · rwa [toFinset_card_of_nodup nodup_take]
  · nth_rw 1 [len_take, mul_right_comm, Fin.sum_univ_def] at key
    rw [sum_toFinset _ nodup_take]
    convert key
    refine ext_get (by simp) fun i _ _ ↦ ?_
    simp only [get_eq_getElem, map_take, getElem_take, getElem_map, Fin.getElem_fin]
    grind

#print axioms erdos904
-- 'Erdos904.SimpleGraph.erdos904' depends on axioms: [propext, Classical.choice, Quot.sound]

end SimpleGraph

end Erdos904

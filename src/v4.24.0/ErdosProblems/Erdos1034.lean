/-

This is a Lean formalization of a solution to Erdős Problem 1034.
https://www.erdosproblems.com/1034

The original human proof was found by: Jie Ma and Quanyu Tang

Jie Ma; Quanyu Tang. Erdős Problem 1034. Unpublished note, University
of Science and Technology of China, Hefei, China, 2025


Namrata Anand worked with Aristotle to formalize this proof.


ChatGPT from OpenAI explained the proof.  The LaTeX file output from
the previous step was auto-formalized into Lean by Aristotle from
Harmonic.  The final theorem statement was written by hand by Boris
Alexeev.

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

namespace Erdos1034


set_option maxHeartbeats 0

noncomputable section

def Y_set {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : Finset V :=
  Finset.univ.filter (fun v => 2 ≤ (G.neighborFinset v ∩ T).card)

def MaTangGraph (n : ℕ) (α : ℝ) (s : ℕ) : SimpleGraph (Fin n) where
  Adj u v :=
    let b := ⌊α * n⌋₊
    let uB := (u : ℕ) < b
    let vB := (v : ℕ) < b
    (uB ≠ vB) ∨ (uB ∧ vB ∧ (u : ℕ) / s = (v : ℕ) / s ∧ u ≠ v)
  symm := by
    tauto
  loopless := by
    aesop_cat

instance instDecidableRel_MaTangGraphAdj (n : ℕ) (α : ℝ) (s : ℕ) :
    DecidableRel (MaTangGraph n α s).Adj := by
  intro u v
  dsimp [MaTangGraph]
  exact instDecidableOr

noncomputable def alpha_star : ℝ := 1 - 1 / Real.sqrt 10

noncomputable def c1 (α : ℝ) : ℝ := 2 * α - Real.sqrt (2 - 4 * (α - 1)^2)

noncomputable def s_func (n : ℕ) (α : ℝ) : ℕ := Nat.ceil (c1 α * n)

def B_set (n : ℕ) (α : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (v : ℕ) < ⌊α * n⌋₊)

def S_set (n : ℕ) (α : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ⌊α * n⌋₊ ≤ (v : ℕ))

section AristotleLemmas

lemma card_B_set (n : ℕ) (α : ℝ) (h : ⌊α * n⌋₊ ≤ n) : (B_set n α).card = ⌊α * n⌋₊ := by
  -- The set B_set is exactly the set of elements from 0 to floor(α*n) - 1, so its cardinality is floor(α*n).
  have hB_card : (B_set n α).card = Finset.card (Finset.filter (fun v : Fin n => v.val < Nat.floor (α * n)) Finset.univ) := by
    congr! 2;
  rw [ hB_card ];
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => ⟨ i, by linarith ⟩;
  · -- For any element a in the set {v : Fin n | v.val < Nat.floor (α * n)}, we can take i to be a.val, which satisfies i < Nat.floor (α * n) and ⟨i, by linarith⟩ = a.
    intro a ha
    use a.val
    aesop;
  · aesop;
  · aesop

lemma card_S_set (n : ℕ) (α : ℝ) (h : ⌊α * n⌋₊ ≤ n) : (S_set n α).card = n - ⌊α * n⌋₊ := by
  unfold S_set;
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => ⟨ i + ⌊α * n⌋₊, by linarith [ Nat.sub_add_cancel h ] ⟩;
  · aesop;
    exact ⟨ a - ⌊α * n⌋₊, by rw [ tsub_lt_tsub_iff_right a_1 ] ; exact a.2, by rw [ Fin.ext_iff ] ; simp +decide [ Nat.sub_add_cancel a_1 ] ⟩;
  · aesop;
  · aesop

def edges_BS_set (n : ℕ) (α : ℝ) : Finset (Sym2 (Fin n)) :=
  (B_set n α ×ˢ S_set n α).image (fun x => Sym2.mk x)

def edges_B_set (n : ℕ) (α : ℝ) (s : ℕ) : Finset (Sym2 (Fin n)) :=
  ((B_set n α).offDiag.filter (fun x => (x.1 : ℕ) / s = (x.2 : ℕ) / s)).image (fun x => Sym2.mk x)

lemma edges_disjoint (n : ℕ) (α : ℝ) (s : ℕ) : Disjoint (edges_BS_set n α) (edges_B_set n α s) := by
  -- If an edge is in edges_BS_set, then one endpoint is in B and the other is in S. Since B and S are disjoint, this edge can't be in edges_B_set, which requires both endpoints to be in B. Hence, the intersection of the two sets is empty.
  have h_disjoint : ∀ e ∈ edges_BS_set n α, e ∉ edges_B_set n α s := by
    unfold edges_BS_set edges_B_set; aesop;
    · unfold B_set S_set at * ; aesop;
      grind;
    · unfold B_set S_set at *; aesop;
      -- Since $x \in B$ and $x_1 \in S$, we have $x < \lfloor \alpha n \rfloor$ and $x_1 \geq \lfloor \alpha n \rfloor$. But we also have $x_1 < \lfloor \alpha n \rfloor$, which contradicts $x_1 \in S$.
      exfalso; exact lt_irrefl (⌊α * n⌋₊) (by linarith);
  exact Finset.disjoint_left.mpr h_disjoint

lemma edges_decomposition (n : ℕ) (α : ℝ) (s : ℕ) :
  (MaTangGraph n α s).edgeFinset = edges_BS_set n α ∪ edges_B_set n α s := by
    ext ⟨ u, v ⟩;
    unfold edges_BS_set edges_B_set;
    -- By definition of MaTangGraph, u and v are adjacent if they are in different parts (B and S) or if they are in the same part (B) and their indices are in the same clique.
    simp [MaTangGraph, B_set, S_set];
    grind

lemma card_edges_BS (n : ℕ) (α : ℝ) :
  (edges_BS_set n α).card = (B_set n α).card * (S_set n α).card := by
    unfold edges_BS_set B_set S_set; erw [ Finset.card_image_of_injOn ] ; aesop_cat;
    -- Since $B$ and $S$ are disjoint, the only way for $\{u, v\} = \{u', v'\}$ is if $u = u'$ and $v = v'$.
    intros p hp q hq h_eq
    have h_eq_elements : p.1 = q.1 ∧ p.2 = q.2 ∨ p.1 = q.2 ∧ p.2 = q.1 := by
      cases p ; cases q ; aesop;
    aesop;
    · exact False.elim <| left_1.not_le right;
    · exact False.elim <| left_1.not_le right

def clique_i (n : ℕ) (α : ℝ) (s : ℕ) (i : ℕ) : Finset (Fin n) :=
  (B_set n α).filter (fun v => (v : ℕ) / s = i)

lemma card_clique_i_lt (n : ℕ) (α : ℝ) (s : ℕ) (i : ℕ)
  (h_b : ⌊α * n⌋₊ ≤ n) (hs : s > 0) (hi : i < ⌊α * n⌋₊ / s) :
  (clique_i n α s i).card = s := by
    unfold clique_i;
    rw [ Finset.card_eq_of_bijective ];
    use fun j hj => ⟨ i * s + j, by nlinarith [ Nat.div_mul_le_self ( ⌊α * n⌋₊ ) s ] ⟩;
    · aesop;
      exact ⟨ a % s, Nat.mod_lt _ hs, by simpa [ Nat.div_add_mod' ] ⟩;
    · unfold B_set; aesop;
      · nlinarith [ Nat.div_mul_le_self ( ⌊α * n⌋₊ ) s ];
      · rw [ Nat.add_div ] <;> aesop;
        linarith [ Nat.mod_lt i_1 hs ];
    · aesop

lemma card_clique_i_eq (n : ℕ) (α : ℝ) (s : ℕ)
  (h_b : ⌊α * n⌋₊ ≤ n) (hs : s > 0) :
  (clique_i n α s (⌊α * n⌋₊ / s)).card = ⌊α * n⌋₊ % s := by
    unfold clique_i;
    -- Let's simplify the set {v ∈ B_set n α | (v : ℕ) / s = ⌊α * n⌋₊ / s}.
    have h_last_group_card : (Finset.filter (fun v : ℕ => v / s = ⌊α * n⌋₊ / s) (Finset.range ⌊α * n⌋₊)).card = ⌊α * n⌋₊ % s := by
      -- The set {v ∈ Finset.range ⌊α * n⌋₊ | v / s = ⌊α * n⌋₊ / s} consists of numbers that are congruent to ⌊α * n⌋₊ % s modulo s.
      have h_cong : Finset.filter (fun v : ℕ => v / s = ⌊α * n⌋₊ / s) (Finset.range ⌊α * n⌋₊) = Finset.Ico (⌊α * n⌋₊ / s * s) (⌊α * n⌋₊ / s * s + ⌊α * n⌋₊ % s) := by
        ext ; aesop;
        · nlinarith [ Nat.div_mul_le_self a s, Nat.div_mul_le_self ⌊α * n⌋₊ s ];
        · linarith [ Nat.mod_add_div ⌊α * n⌋₊ s ];
        · linarith [ Nat.mod_add_div ⌊α * n⌋₊ s ];
        · exact Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith [ Nat.div_add_mod ⌊α * n⌋₊ s, Nat.mod_lt ⌊α * n⌋₊ hs ] ) ( Nat.le_div_iff_mul_le hs |>.2 <| by linarith [ Nat.div_add_mod ⌊α * n⌋₊ s, Nat.mod_lt ⌊α * n⌋₊ hs ] );
      aesop;
    convert h_last_group_card using 1;
    refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> aesop;
    · unfold B_set at left; aesop;
    · exact ⟨ ⟨ b, by linarith ⟩, ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by linarith ⟩, right ⟩, rfl ⟩

def edges_clique_i (n : ℕ) (α : ℝ) (s : ℕ) (i : ℕ) : Finset (Sym2 (Fin n)) :=
  ((clique_i n α s i).offDiag).image (fun x => Sym2.mk x)

lemma card_edges_clique_i (n : ℕ) (α : ℝ) (s : ℕ) (i : ℕ) :
  (edges_clique_i n α s i).card = (clique_i n α s i).card * ((clique_i n α s i).card - 1) / 2 := by
    -- The cardinality of the off-diagonal pairs of a set S is |S|*(|S|-1).
    have h_off_diag : (clique_i n α s i).offDiag.card = (clique_i n α s i).card * ((clique_i n α s i).card - 1) := by
      simp +decide [ mul_tsub, Finset.offDiag_card ];
    rw [ ← h_off_diag ];
    -- Since Sym2.mk is 2-to-1 on the off-diagonal elements, the cardinality of the image is half the cardinality of the off-diagonal elements. This follows from the fact that each unordered pair is counted twice in the off-diagonal elements.
    have h_card_image : ∀ x ∈ (clique_i n α s i).offDiag, Finset.card (Finset.filter (fun y => Sym2.mk y = Sym2.mk x) (clique_i n α s i).offDiag) = 2 := by
      -- Since $x$ is in the off-diagonal, it means that $a \neq b$. Therefore, the only pairs $y$ that satisfy $Sym2.mk y = Sym2.mk x$ are $(a, b)$ and $(b, a)$.
      intros x hx
      have h_pairs : {y ∈ (clique_i n α s i).offDiag | Sym2.mk y = Sym2.mk x} = {(x.1, x.2), (x.2, x.1)} := by
        ext y; aesop;
      aesop;
    have h_card_image : ∑ x ∈ edges_clique_i n α s i, (Finset.filter (fun y => Sym2.mk y = x) (clique_i n α s i).offDiag).card = (clique_i n α s i).offDiag.card := by
      rw [ ← Finset.card_eq_sum_card_fiberwise ];
      exact fun x hx => Finset.mem_image_of_mem _ hx;
    rw [ ← h_card_image, Finset.sum_congr rfl fun x hx => show Finset.card ( Finset.filter ( fun y => Sym2.mk y = x ) ( clique_i n α s i |> Finset.offDiag ) ) = 2 from ?_ ] ; aesop;
    unfold edges_clique_i at hx; aesop;

lemma edges_B_decomposition (n : ℕ) (α : ℝ) (s : ℕ) (hs : s > 0) :
  let b := ⌊α * n⌋₊
  let q := b / s
  edges_B_set n α s = Finset.biUnion (Finset.range (q + 1)) (fun i => edges_clique_i n α s i) := by
    -- To prove equality of finite sets, we show each set is a subset of the other.
    apply Finset.ext
    intro e
    simp [edges_B_set, edges_clique_i];
    -- To prove the forward direction, assume there exists a pair (a, b) in edges_B_set. Then a and b are in B, distinct, and their division by s is the same. This means they are in the same clique_i for some i, hence in edges_clique_i.
    apply Iff.intro
    intro h
    obtain ⟨a, b, h_pair, h_eq⟩ := h
    use (a.val / s)
    aesop;
    · exact Nat.lt_succ_of_le ( Nat.div_le_div_right <| Finset.mem_filter.mp left_1 |>.2.le );
    · unfold clique_i at *; aesop;
    · -- If there exists an i in the range up to q+1 and a pair (a, b) in clique_i n α s i such that a ≠ b, then a and b are in B_set n α and a/s = b/s.
      intro h
      obtain ⟨i, hi, a, b, h_clique, h_eq⟩ := h;
      unfold clique_i at h_clique; aesop;

lemma edges_clique_disjoint (n : ℕ) (α : ℝ) (s : ℕ) (i j : ℕ) (hij : i ≠ j) :
  Disjoint (edges_clique_i n α s i) (edges_clique_i n α s j) := by
    unfold edges_clique_i;
    rw [ Finset.disjoint_left ] ; aesop;
    · unfold clique_i at *; aesop;
    · unfold clique_i at * ; aesop

lemma card_edges_B_sum (n : ℕ) (α : ℝ) (s : ℕ) (hs : s > 0) :
  (edges_B_set n α s).card = ∑ i ∈ Finset.range (⌊α * n⌋₊ / s + 1), (edges_clique_i n α s i).card := by
    -- To prove the equality of cardinalities, we first show that the edges_clique_i are pairwise disjoint.
    have h_disjoint : ∀ i j : ℕ, i ≠ j → Disjoint (edges_clique_i n α s i) (edges_clique_i n α s j) := by
      unfold edges_clique_i;
      intro i j hij; rw [ Finset.disjoint_left ] ; aesop;
      · unfold clique_i at *; contrapose! hij; aesop;
      · unfold clique_i at *; aesop;
    -- Since the edges_clique_i sets are pairwise disjoint, the cardinality of their union is the sum of their cardinalities.
    have h_card_union : (Finset.biUnion (Finset.range (⌊α * n⌋₊ / s + 1)) (fun i => edges_clique_i n α s i)).card = ∑ i ∈ Finset.range (⌊α * n⌋₊ / s + 1), (edges_clique_i n α s i).card := by
      -- Apply the fact that the cardinality of a union of pairwise disjoint sets is the sum of their cardinalities.
      apply Finset.card_biUnion;
      exact fun i hi j hj hij => h_disjoint i j hij;
    exact h_card_union.symm ▸ congr_arg _ ( edges_B_decomposition n α s hs )

lemma sum_edges_clique_lt (n : ℕ) (α : ℝ) (s : ℕ) (hs : s > 0) (h_b : ⌊α * n⌋₊ ≤ n) :
  ∑ i ∈ Finset.range (⌊α * n⌋₊ / s), (edges_clique_i n α s i).card = (⌊α * n⌋₊ / s) * (s * (s - 1) / 2) := by
    rw [ Finset.sum_congr rfl fun i hi => card_edges_clique_i _ _ _ _ ];
    rw [ Finset.sum_congr rfl fun i hi => by rw [ card_clique_i_lt _ _ _ _ ] <;> aesop ] ; aesop

lemma card_edges_B_exact (n : ℕ) (α : ℝ) (s : ℕ) (hs : s > 0) (h_b : ⌊α * n⌋₊ ≤ n) :
  let b := ⌊α * n⌋₊
  let q := b / s
  let r := b % s
  (edges_B_set n α s).card = q * (s * (s - 1) / 2) + r * (r - 1) / 2 := by
    -- Using the previous lemma, we can split the sum into the sum over `range q` and the term at `q`.
    have h_split_sum : ∑ i ∈ Finset.range (⌊α * n⌋₊ / s + 1), (edges_clique_i n α s i).card = (∑ i ∈ Finset.range (⌊α * n⌋₊ / s), (edges_clique_i n α s i).card) + (edges_clique_i n α s (⌊α * n⌋₊ / s)).card := by
      rw [Finset.sum_range_succ];
    rw [ card_edges_B_sum n α s hs, h_split_sum, sum_edges_clique_lt n α s hs h_b ];
    rw [ card_edges_clique_i, card_clique_i_eq n α s h_b hs ]

lemma card_edges_MaTangGraph (n : ℕ) (α : ℝ) (s : ℕ) (hs : s > 0) (h_b : ⌊α * n⌋₊ ≤ n) :
  let b := ⌊α * n⌋₊
  let q := b / s
  let r := b % s
  (MaTangGraph n α s).edgeFinset.card = b * (n - b) + q * (s * (s - 1) / 2) + r * (r - 1) / 2 := by
    -- The edge set is the disjoint union of edges_BS_set and edges_B_set.
    have edges_union : (MaTangGraph n α s).edgeFinset = edges_BS_set n α ∪ edges_B_set n α s := by
      exact?;
    rw [ edges_union, Finset.card_union_of_disjoint ];
    · rw [ card_edges_BS, card_edges_B_exact ];
      · rw [ card_B_set, card_S_set ] <;> linarith;
      · -- Since $s > 0$ is given by the hypothesis $hs$, we can directly use it.
        exact hs;
      · assumption;
    · -- Since $B$ and $S$ are disjoint, their images under the Sym2.mk function are also disjoint.
      apply edges_disjoint

lemma eB_eq_real (n : ℕ) (α : ℝ) (s : ℕ) (hs : s > 0) (h_b : ⌊α * n⌋₊ ≤ n) :
  let b := ⌊α * n⌋₊
  let r := b % s
  ((edges_B_set n α s).card : ℝ) = (b * (s - 1) - r * (s - r)) / 2 := by
    bound;
    -- We know card = q * s(s-1)/2 + r(r-1)/2.
    have h_card : (edges_B_set n α s).card = (b / s) * (s * (s - 1) / 2) + r * (r - 1) / 2 := by
      exact?;
    -- Substitute $b = q * s + r$ into the equation.
    have h_sub : (b : ℝ) = (b / s : ℕ) * s + r := by
      exact mod_cast Eq.symm ( Nat.div_add_mod' _ _ );
    norm_num [ h_card, h_sub ];
    cases s <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] ; ring;
    · contradiction;
    · cases r <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] ; ring;
      ring

lemma r_s_minus_r_le (s r : ℝ) : r * (s - r) ≤ s^2 / 4 := by
  linarith [ sq_nonneg ( s - 2 * r ) ]

lemma lower_bound_eB (n : ℕ) (α : ℝ) (s : ℕ) (hs : s > 0) (h_b : ⌊α * n⌋₊ ≤ n) :
  let b := ⌊α * n⌋₊
  ((edges_B_set n α s).card : ℝ) ≥ (b * (s - 1)) / 2 - s^2 / 8 := by
    bound;
    -- Let's express the cardinality of the edges in $B$ using the provided formula.
    have h_card_edges_B : (edges_B_set n α s).card = (b / s) * (s * (s - 1) / 2) + (b % s) * ((b % s) - 1) / 2 := by
      exact?;
    rcases s with ( _ | _ | s ) <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
    · norm_num [ Nat.mod_one ];
    · -- Substitute $b = q(s + 2) + r$ into the inequality.
      set q := b / (s + 2)
      set r := b % (s + 2)
      have hb : b = q * (s + 2) + r := by
        rw [ Nat.div_add_mod' ];
      rcases r with ( _ | r ) <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] at *;
      · rw [ hb ] ; push_cast ; nlinarith [ sq ( s : ℝ ) ];
      · rw [ hb ] ; push_cast ; ring_nf ; norm_num;
        nlinarith only [ sq_nonneg ( s - 2 * r : ℝ ) ]

lemma lower_bound_BS (n : ℕ) (α : ℝ) (hα : 1/2 ≤ α) (hα1 : α ≤ 1) :
  let b := ⌊α * n⌋₊
  ((b * (n - b)) : ℝ) ≥ α * (1 - α) * n^2 - 1 := by
    -- Let $b = \lfloor \alpha n \rfloor$. Then $b \leq \alpha n < b + 1$.
    set b := ⌊α * n⌋₊
    have hb : (b : ℝ) ≤ α * n ∧ α * n < b + 1 := by
      -- By definition of the floor function, we know that ⌊α * n⌋ ≤ α * n and α * n < ⌊α * n⌋ + 1.
      apply And.intro; exact Nat.floor_le (by positivity); exact Nat.lt_floor_add_one (α * n);
    nlinarith [ mul_le_mul_of_nonneg_right hα ( Nat.cast_nonneg n ) ]

lemma alpha_star_val : alpha_star = 1 - 1 / Real.sqrt 10 := rfl

lemma c1_val (α : ℝ) : c1 α = 2 * α - Real.sqrt (2 - 4 * (α - 1)^2) := rfl

lemma algebraic_inequality :
  let α := alpha_star
  let c := c1 α
  α * (1 - α) + α * c / 2 - c^2 / 8 = 1 / 4 := by
    unfold alpha_star c1; norm_num; ring_nf;
    bound

lemma S_independent (n : ℕ) (α : ℝ) (s : ℕ) :
  (MaTangGraph n α s).IsIndepSet (S_set n α : Set (Fin n)) := by
    -- To prove that $S$ is independent, we need to show that no two vertices in $S$ are adjacent.
    intro u hu v hv huv;
    -- Since $u$ and $v$ are in $S_set$, they are not in $B_set$, so the first part of the adjacency condition (uB ≠ vB) is false.
    have h_not_B : ¬(u.val < ⌊α * n⌋₊) ∧ ¬(v.val < ⌊α * n⌋₊) := by
      unfold S_set at hu hv; aesop;
    -- Since u and v are in S_set, their uB and vB are both false. So the first part of the adjacency condition (uB ≠ vB) is false. The second part requires uB and vB to be true, which they aren't. Therefore, the adjacency condition can't hold, so u and v aren't adjacent.
    simp [MaTangGraph, h_not_B]

lemma B_clique_structure (n : ℕ) (α : ℝ) (s : ℕ) (u v : Fin n) (hu : u ∈ B_set n α) (hv : v ∈ B_set n α) (h_adj : (MaTangGraph n α s).Adj u v) :
  (u : ℕ) / s = (v : ℕ) / s := by
    unfold B_set at hu hv; unfold MaTangGraph at h_adj; aesop;

lemma B_complete_S (n : ℕ) (α : ℝ) (s : ℕ) (u v : Fin n) (hu : u ∈ B_set n α) (hv : v ∈ S_set n α) :
  (MaTangGraph n α s).Adj u v := by
    unfold MaTangGraph;
    unfold B_set S_set at * ; aesop

lemma c1_pos : c1 alpha_star > 0 := by
  -- Substitute the value of `alpha_star` into the expression for `c1`.
  have h_c1_pos : c1 alpha_star = 2 * (1 - 1 / Real.sqrt 10) - Real.sqrt (2 - 4 * (1 - 1 / Real.sqrt 10 - 1)^2) := by
    exact?;
  norm_num [ h_c1_pos ];
  rw [ ← Real.sqrt_div ( by norm_num ) ];
  rw [ Real.sqrt_lt ] <;> ring <;> nlinarith [ Real.sqrt_nonneg 10, Real.sq_sqrt <| show 0 ≤ 10 by norm_num, inv_mul_cancel₀ <| ne_of_gt <| Real.sqrt_pos.2 <| show 0 < 10 by norm_num ]

noncomputable def gamma_const : ℝ := alpha_star / c1 alpha_star

lemma gamma_not_half_integer : ∀ k : ℤ, gamma_const ≠ k + 1/2 := by
  -- By simplifying, we can see that gamma_const is approximately 6.6667, which is not equal to any integer plus 1/2.
  have h_approx : gamma_const > 6 ∧ gamma_const < 7 := by
    -- Let's compute the numerical value of gamma_const.
    have h_gamma_approx : gamma_const = (Real.sqrt 10 - 1) / (2 * Real.sqrt 10 - 6) := by
      -- Substitute the definitions of `alpha_star` and `c1` into the expression for `gamma_const`.
      have h_gamma_const : gamma_const = (1 - 1 / Real.sqrt 10) / (2 * (1 - 1 / Real.sqrt 10) - Real.sqrt (2 - 4 * (1 - 1 / Real.sqrt 10 - 1)^2)) := by
        -- Substitute the definitions of `alpha_star` and `c1` into the expression for `gamma_const` and simplify.
        rw [show gamma_const = alpha_star / c1 alpha_star from rfl]
        rw [alpha_star_val, c1_val];
      rw [ h_gamma_const, div_eq_div_iff ] <;> ring <;> norm_num;
      · rw [ show ( 10 : ℝ ) = 2 * 5 by norm_num, Real.sqrt_mul ] <;> ring <;> norm_num;
        rw [ show ( 8 : ℝ ) = 4 * 2 by norm_num, Real.sqrt_mul ] <;> ring <;> norm_num;
        rw [ ← Real.sqrt_div_self ] ; ring;
      · grind;
      · -- By simplifying, we can see that the expression is not zero.
        by_contra h_contra
        have : Real.sqrt 10 = 3 := by
          linarith
        norm_num at this
    exact ⟨ by rw [ h_gamma_approx, gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 10, Real.sq_sqrt ( show 0 ≤ 10 by norm_num ) ], by rw [ h_gamma_approx, div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 10, Real.sq_sqrt ( show 0 ≤ 10 by norm_num ) ] ⟩;
  -- Since gamma_const is strictly between 6 and 7, it cannot be equal to any integer plus 1/2.
  intros k hk
  have h_bounds : 6 < gamma_const ∧ gamma_const < 7 := by
    grind +ring;
  -- If gamma_const were equal to k + 1/2 for some integer k, then k would have to be 6 because 6 + 1/2 = 6.5, which is between 6 and 7.
  have h_k : k = 6 := by
    exact Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith );
  norm_num [ h_k, gamma_const ] at hk;
  rw [ div_eq_iff ] at hk <;> norm_num [ alpha_star, c1 ] at *;
  · rw [ show ( 8 : ℝ ) = 4 * 2 by norm_num, show ( 5 : ℝ ) = 5 * 1 by norm_num, Real.sqrt_mul ( by norm_num ), Real.sqrt_mul ( by norm_num ) ] at hk ; ring_nf at hk;
    rw [ show ( 10 : ℝ ) = 2 * 5 by norm_num, Real.sqrt_mul ] at hk <;> ring_nf at * <;> norm_num at *;
    nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), inv_pos.2 ( Real.sqrt_pos.2 ( show 0 < 2 by norm_num ) ), inv_pos.2 ( Real.sqrt_pos.2 ( show 0 < 5 by norm_num ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.2 ( show 0 < 2 by norm_num ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.2 ( show 0 < 5 by norm_num ) ) ) ];
  · intro h; rw [ h ] at hk; norm_num at hk;

lemma density_gap :
  let α := alpha_star
  let c := c1 α
  let γ := α / c
  let frac_γ := γ - ⌊γ⌋
  α * (1 - α) + α * c / 2 - c^2 / 2 * (frac_γ * (1 - frac_γ)) > 1 / 4 := by
    have h_gamma_frac : let α := alpha_star;
        let c := c1 α;
        let γ := α / c;
        let frac_γ := γ - ⌊γ⌋;
        frac_γ * (1 - frac_γ) < 1 / 4 := by
          have h_frac_γ : ¬(gamma_const = ⌊gamma_const⌋ + 1 / 2) := by
            exact fun h => gamma_not_half_integer ( ⌊gamma_const⌋ ) ( by linear_combination h );
          -- Since $\frac{1}{2}$ is not equal to $\gamma - \lfloor \gamma \rfloor$, we have $(\gamma - \lfloor \gamma \rfloor) * (1 - (\gamma - \lfloor \gamma \rfloor)) < \frac{1}{4}$.
          have h_frac_γ_lt : (gamma_const - ⌊gamma_const⌋) * (1 - (gamma_const - ⌊gamma_const⌋)) < 1 / 4 := by
            nlinarith [ mul_self_pos.mpr ( sub_ne_zero.mpr h_frac_γ ), Int.floor_le gamma_const, Int.lt_floor_add_one gamma_const ];
          exact h_frac_γ_lt;
    -- Substitute the inequality from h_gamma_frac into the expression.
    have h_subst : let α := alpha_star;
        let c := c1 α;
        let γ := α / c;
        let frac_γ := γ - ⌊γ⌋;
        α * (1 - α) + α * c / 2 - c ^ 2 / 2 * (frac_γ * (1 - frac_γ)) > α * (1 - α) + α * c / 2 - c ^ 2 / 8 := by
          norm_num at *;
          nlinarith [ show 0 < c1 alpha_star ^ 2 by exact sq_pos_of_pos ( c1_pos ) ];
    exact h_subst.trans_le' ( by rw [ algebraic_inequality ] )

lemma S_is_independent (n : ℕ) (α : ℝ) (s : ℕ) :
  (MaTangGraph n α s).IsIndepSet (S_set n α : Set (Fin n)) := by
    exact?

lemma B_clique_prop (n : ℕ) (α : ℝ) (s : ℕ) (u v : Fin n) (hu : u ∈ B_set n α) (hv : v ∈ B_set n α) (h_adj : (MaTangGraph n α s).Adj u v) :
  (u : ℕ) / s = (v : ℕ) / s := by
    have := B_clique_structure n α s u v hu hv h_adj; aesop;

lemma B_S_complete (n : ℕ) (α : ℝ) (s : ℕ) (u v : Fin n) (hu : u ∈ B_set n α) (hv : v ∈ S_set n α) :
  (MaTangGraph n α s).Adj u v := by
    unfold B_set S_set at *; aesop;
    exact Or.inl <| by aesop;

lemma triangle_has_large_intersection_B (n : ℕ) (α : ℝ) (s : ℕ) (T : Finset (Fin n)) (hT : T ∈ (MaTangGraph n α s).cliqueFinset 3) :
  2 ≤ (T ∩ B_set n α).card := by
    -- Since T is a clique of size 3, it must have at least two vertices in B_set.
    have h_two_in_B : (T ∩ S_set n α).card ≤ 1 := by
      have h_indep_S : (MaTangGraph n α s).IsIndepSet (S_set n α : Set (Fin n)) := by
        exact?;
      -- Since $T$ is a clique of size 3, any two vertices in $T$ are adjacent. However, $S_set n α$ is an independent set, so no two vertices in $S_set n α$ can be adjacent. Therefore, $T$ can have at most one vertex in $S_set n α$.
      have h_adj_in_T : ∀ u v : Fin n, u ∈ T → v ∈ T → u ≠ v → (MaTangGraph n α s).Adj u v := by
        norm_num +zetaDelta at *;
        exact fun u v hu hv huv => hT.1 hu hv huv;
      contrapose! h_indep_S;
      obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp h_indep_S; exact fun h => by have := h ( by aesop : u ∈ S_set n α ) ( by aesop : v ∈ S_set n α ) ; aesop;
    norm_num +zetaDelta at *;
    -- Since $T$ is a subset of $B_set \cup S_set$, we have $|T| = |T \cap B_set| + |T \cap S_set|$.
    have h_card_union : T.card = (T ∩ B_set n α).card + (T ∩ S_set n α).card := by
      rw [ ← Finset.card_union_of_disjoint ];
      · congr with x ; by_cases hx : x ∈ B_set n α <;> aesop;
        exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_of_not_lt fun h => hx <| Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h ⟩ ⟩;
      · simp +contextual [ Finset.disjoint_left, B_set, S_set ];
    linarith [ hT.card_eq ]

lemma triangle_in_clique (n : ℕ) (α : ℝ) (s : ℕ) (T : Finset (Fin n)) (hT : T ∈ (MaTangGraph n α s).cliqueFinset 3) :
  ∃ i, (T ∩ B_set n α) ⊆ clique_i n α s i := by
    unfold MaTangGraph at hT;
    -- Since T is a clique, every pair of vertices in T must be adjacent.
    have h_adj : ∀ u v : Fin n, u ∈ T → v ∈ T → u ≠ v → (u : ℕ) < ⌊α * n⌋₊ → (v : ℕ) < ⌊α * n⌋₊ → (u : ℕ) / s = (v : ℕ) / s := by
      aesop;
      have := hT.1 a a_1; aesop;
    by_cases h : ∃ u : Fin n, u ∈ T ∧ ( u : ℕ ) < ⌊α * n⌋₊ <;> aesop;
    · use w / s;
      intro u hu; specialize h_adj u w; aesop;
      unfold clique_i; aesop;
      unfold B_set at right_1; aesop;
      by_cases huw : u = w <;> aesop;
    · use 0; intro x hx; aesop;
      exact absurd ( h x left ) ( not_le_of_gt ( Finset.mem_filter.mp right |>.2 ) )

lemma S_is_indep_set (n : ℕ) (α : ℝ) (s : ℕ) :
  (MaTangGraph n α s).IsIndepSet (S_set n α : Set (Fin n)) := by
    exact?

lemma B_clique_struct_prop (n : ℕ) (α : ℝ) (s : ℕ) (u v : Fin n) (hu : u ∈ B_set n α) (hv : v ∈ B_set n α) (h_adj : (MaTangGraph n α s).Adj u v) :
  (u : ℕ) / s = (v : ℕ) / s := by
    exact?

lemma B_S_adj_prop (n : ℕ) (α : ℝ) (s : ℕ) (u v : Fin n) (hu : u ∈ B_set n α) (hv : v ∈ S_set n α) :
  (MaTangGraph n α s).Adj u v := by
    -- By definition of $B_set$ and $S_set$, we know that $u < \lfloor \alpha n \rfloor$ and $v \geq \lfloor \alpha n \rfloor$.
    have huv : u.val < ⌊α * n⌋₊ ∧ v.val ≥ ⌊α * n⌋₊ := by
      unfold B_set S_set at *; aesop;
    unfold MaTangGraph; aesop;

lemma S_is_indep_v2 (n : ℕ) (α : ℝ) (s : ℕ) :
  (MaTangGraph n α s).IsIndepSet (S_set n α : Set (Fin n)) := by
    exact?

lemma B_clique_struct_v2 (n : ℕ) (α : ℝ) (s : ℕ) (u v : Fin n) (hu : u ∈ B_set n α) (hv : v ∈ B_set n α) (h_adj : (MaTangGraph n α s).Adj u v) :
  (u : ℕ) / s = (v : ℕ) / s := by
    exact B_clique_prop n α s u v hu hv h_adj

lemma B_S_adj_v2 (n : ℕ) (α : ℝ) (s : ℕ) (u v : Fin n) (hu : u ∈ B_set n α) (hv : v ∈ S_set n α) :
  (MaTangGraph n α s).Adj u v := by
    exact?

lemma S_subset_Y (n : ℕ) (α : ℝ) (s : ℕ) (T : Finset (Fin n)) (hT : T ∈ (MaTangGraph n α s).cliqueFinset 3) :
  S_set n α ⊆ Y_set (MaTangGraph n α s) T := by
    -- Let's take any vertex $v$ in $S_set n α$.
    intro v hv
    -- Since $v$ is in $S_set n α$, it is adjacent to all vertices in $B_set n α$.
    have h_adj_B : ∀ u ∈ B_set n α, (MaTangGraph n α s).Adj v u := by
      exact?;
    -- Since $T$ is a triangle, it has at least two vertices in $B_set n α$.
    have h_T_B : 2 ≤ (T ∩ B_set n α).card := by
      exact?;
    exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_trans h_T_B <| Finset.card_le_card <| fun x hx => by aesop ⟩

lemma clique_subset_Y (n : ℕ) (α : ℝ) (s : ℕ) (T : Finset (Fin n)) (hT : T ∈ (MaTangGraph n α s).cliqueFinset 3)
  (i : ℕ) (h_subset : T ∩ B_set n α ⊆ clique_i n α s i) :
  clique_i n α s i ⊆ Y_set (MaTangGraph n α s) T := by
    -- Let $v$ be a vertex in $clique_i n α s i$. Since $clique_i n α s i$ is a clique, $v$ is adjacent to all other vertices in $clique_i n α s i$.
    intro v hv
    have hv_adj : ∀ u ∈ clique_i n α s i, u ≠ v → (MaTangGraph n α s).Adj v u := by
      unfold clique_i at hv; aesop;
      unfold clique_i at a; aesop;
      unfold B_set at *; aesop;
      unfold MaTangGraph; aesop;
    -- Since $T \cap B_set n α \subseteq clique_i n α s i$, we have $|T \cap B_set n α| \geq 2$.
    have h_card_inter : 2 ≤ (T ∩ B_set n α).card := by
      exact?;
    -- If $v \in T$, then $v$ is adjacent to the other two vertices of $T$, which are also in $clique_i n α s i$.
    by_cases hvT : v ∈ T;
    · have h_adj_T : (Finset.filter (fun u => (MaTangGraph n α s).Adj v u) T).card ≥ 2 := by
        have h_adj_T : (Finset.filter (fun u => (MaTangGraph n α s).Adj v u) T).card ≥ (T \ {v}).card := by
          refine Finset.card_le_card ?_;
          intro u hu; aesop;
          have := hT.1; aesop;
        simp_all +decide [ Finset.card_sdiff ];
        linarith [ hT.card_eq ];
      unfold Y_set; aesop;
      convert h_adj_T using 2 ; ext ; aesop;
    · -- Since $v \notin T$, we need to show that $v$ is adjacent to at least two vertices in $T$.
      have h_adj_T : 2 ≤ (Finset.filter (fun u => (MaTangGraph n α s).Adj v u) T).card := by
        refine' le_trans h_card_inter ( Finset.card_mono _ );
        intro u hu; aesop;
      unfold Y_set; aesop;
      convert h_adj_T using 2 ; ext ; aesop

lemma Y_subset_S_union_clique (n : ℕ) (α : ℝ) (s : ℕ) (T : Finset (Fin n)) (hT : T ∈ (MaTangGraph n α s).cliqueFinset 3)
  (i : ℕ) (h_subset : T ∩ B_set n α ⊆ clique_i n α s i) :
  Y_set (MaTangGraph n α s) T ⊆ S_set n α ∪ clique_i n α s i := by
    intro v hv
    unfold Y_set at hv;
    by_cases hvB : v ∈ B_set n α <;> simp_all +decide [ Finset.subset_iff ];
    · contrapose! hv; aesop;
      -- Since $v \in B_set n α$ and $v \notin clique_i n α s i$, $v$ is not adjacent to any vertex in $T \cap B_set n α$.
      have h_not_adj_B : ∀ u ∈ T ∩ B_set n α, ¬(MaTangGraph n α s).Adj v u := by
        intros u hu; specialize h_subset ( Finset.mem_of_mem_inter_left hu ) ( Finset.mem_of_mem_inter_right hu ) ; unfold clique_i at *; aesop;
        unfold MaTangGraph at a; aesop;
        unfold B_set at *; aesop;
      -- Since $v$ is not adjacent to any vertex in $T \cap B_set n α$, the only vertices in $T$ that $v$ can be adjacent to are in $S_set n α$.
      have h_adj_S : (MaTangGraph n α s).neighborFinset v ∩ T ⊆ S_set n α := by
        intro u hu; specialize h_not_adj_B u; aesop;
        unfold B_set at *; unfold S_set at *; aesop;
      have h_adj_S_card : (S_set n α ∩ T).card ≤ 1 := by
        have h_adj_S_card : ∀ u v : Fin n, u ∈ S_set n α → v ∈ S_set n α → u ≠ v → ¬(MaTangGraph n α s).Adj u v := by
          unfold MaTangGraph; aesop;
          · exact absurd a_3 ( not_lt_of_ge ( Finset.mem_filter.mp a |>.2 ) );
          · exact absurd a_3 ( not_lt_of_ge ( Finset.mem_filter.mp a_1 |>.2 ) );
          · exact a_3.not_le ( Finset.mem_filter.mp a |>.2 );
        exact Finset.card_le_one.mpr fun x hx y hy => Classical.not_not.1 fun hxy => h_adj_S_card x y ( Finset.mem_of_mem_inter_left hx ) ( Finset.mem_of_mem_inter_left hy ) hxy <| hT.1 ( Finset.mem_of_mem_inter_right hx ) ( Finset.mem_of_mem_inter_right hy ) hxy;
      exact lt_of_le_of_lt ( Finset.card_le_card fun x hx => by aesop ) ( lt_of_le_of_lt h_adj_S_card ( by norm_num ) );
    · exact Or.inl <| Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_of_not_lt fun h => hvB <| Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h ⟩ ⟩

lemma card_clique_i_le_s (n : ℕ) (α : ℝ) (s : ℕ) (i : ℕ) (hs : s > 0) :
  (clique_i n α s i).card ≤ s := by
    -- The set of vertices in clique_i is a subset of the vertices in B_set that are between i*s and i*s + s-1.
    have h_subset : clique_i n α s i ⊆ Finset.filter (fun v : Fin n => i * s ≤ v.val ∧ v.val < (i + 1) * s) (B_set n α) := by
      -- By definition of clique_i, if v is in clique_i, then v.val / s = i, which implies i * s ≤ v.val < (i + 1) * s.
      intros v hv
      simp [clique_i] at hv
      aesop;
      · exact Nat.div_mul_le_self _ _;
      · linarith [ Nat.div_add_mod v s, Nat.mod_lt v hs ];
    -- The set {v ∈ B_set n α | i * s ≤ v.val ∧ v.val < (i + 1) * s} has exactly s elements.
    have h_card_superset : (Finset.filter (fun v : Fin n => i * s ≤ v.val ∧ v.val < (i + 1) * s) (B_set n α)).card ≤ s := by
      have h_card_superset : (Finset.filter (fun v : Fin n => i * s ≤ v.val ∧ v.val < (i + 1) * s) Finset.univ).card ≤ s := by
        have h_card_superset : Finset.card (Finset.filter (fun v : ℕ => i * s ≤ v ∧ v < (i + 1) * s) (Finset.range n)) ≤ s := by
          exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun v => i * s ≤ v ∧ v < ( i + 1 ) * s ) ( Finset.range n ) ⊆ Finset.Ico ( i * s ) ( ( i + 1 ) * s ) from fun x hx => Finset.mem_Ico.mpr <| Finset.mem_filter.mp hx |>.2 ) ) ( by simp +arith +decide [ add_mul ] );
        convert h_card_superset using 1;
        rw [ Finset.card_filter, Finset.card_filter ];
        rw [ Finset.sum_range ];
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_card_superset;
    exact le_trans ( Finset.card_le_card h_subset ) h_card_superset

lemma Y_structure (n : ℕ) (α : ℝ) (s : ℕ) (T : Finset (Fin n)) (hT : T ∈ (MaTangGraph n α s).cliqueFinset 3) :
  ∃ i, Y_set (MaTangGraph n α s) T = S_set n α ∪ clique_i n α s i := by
    -- Use triangle_in_clique to get such an i.
    obtain ⟨i, hi⟩ := triangle_in_clique n α s T hT;
    -- Since $S \subseteq Y(T)$ and $clique_i \subseteq Y(T)$, and $Y(T) \subseteq S \cup clique_i$, we have $Y(T) = S \cup clique_i$.
    use i
    apply Finset.Subset.antisymm;
    · exact?;
    · exact Finset.union_subset ( S_subset_Y n α s T hT ) ( clique_subset_Y n α s T hT i hi )

lemma S_subset_Y_lemma (n : ℕ) (α : ℝ) (s : ℕ) (T : Finset (Fin n)) (hT : T ∈ (MaTangGraph n α s).cliqueFinset 3) :
  S_set n α ⊆ Y_set (MaTangGraph n α s) T := by
    exact?

lemma clique_subset_Y_lemma (n : ℕ) (α : ℝ) (s : ℕ) (T : Finset (Fin n)) (hT : T ∈ (MaTangGraph n α s).cliqueFinset 3)
  (i : ℕ) (h_subset : T ∩ B_set n α ⊆ clique_i n α s i) :
  clique_i n α s i ⊆ Y_set (MaTangGraph n α s) T := by
    apply clique_subset_Y;
    · bound;
    · -- Apply the hypothesis `h_subset` directly to conclude the proof.
      apply h_subset

lemma Y_subset_S_union_clique_lemma (n : ℕ) (α : ℝ) (s : ℕ) (T : Finset (Fin n)) (hT : T ∈ (MaTangGraph n α s).cliqueFinset 3)
  (i : ℕ) (h_subset : T ∩ B_set n α ⊆ clique_i n α s i) :
  Y_set (MaTangGraph n α s) T ⊆ S_set n α ∪ clique_i n α s i := by
    exact?

lemma Y_card_bound (n : ℕ) (α : ℝ) (s : ℕ) (hs : s > 0) (T : Finset (Fin n)) (hT : T ∈ (MaTangGraph n α s).cliqueFinset 3) :
  (Y_set (MaTangGraph n α s) T).card ≤ (S_set n α).card + s := by
    -- By Y_structure, Y(T) = S \cup clique_i for some i.
    obtain ⟨i, hi⟩ : ∃ i, Y_set (MaTangGraph n α s) T = S_set n α ∪ clique_i n α s i := Y_structure n α s T hT;
    -- Substitute hi into the goal.
    rw [hi];
    -- The cardinality of the union of two sets is less than or equal to the sum of their cardinalities.
    have h_union_card : (S_set n α ∪ clique_i n α s i).card ≤ (S_set n α).card + (clique_i n α s i).card := by
      exact Finset.card_union_le _ _;
    exact h_union_card.trans ( add_le_add_left ( card_clique_i_le_s n α s i hs ) _ )

lemma Phi_val : 1 - alpha_star + c1 alpha_star = 2 - Real.sqrt (5 / 2) := by
  unfold alpha_star c1; ring;
  -- Combine like terms and simplify the expression.
  field_simp
  ring;
  norm_num [ ← Real.sqrt_mul ];
  -- Combine like terms and simplify the expression.
  field_simp
  ring;
  rw [ show ( 10 : ℝ ) = 2 * 5 by norm_num, show ( 8 : ℝ ) = 4 * 2 by norm_num, Real.sqrt_mul, Real.sqrt_mul ] <;> ring <;> norm_num;
  -- Combine like terms and simplify the expression on the left-hand side.
  simp [pow_three]
  ring

lemma Y_asymptotic_bound (ε : ℝ) (hε : ε > 0) :
  ∀ᶠ n in Filter.atTop, ∀ T ∈ (MaTangGraph n alpha_star (s_func n alpha_star)).cliqueFinset 3,
  ((Y_set (MaTangGraph n alpha_star (s_func n alpha_star)) T).card : ℝ) ≤ (2 - Real.sqrt (5/2) + ε) * n := by
    -- We'll use the fact that |Y(T)| ≤ |S| + |clique_i| and the bounds on |S| and |clique_i|.
    have h_bound : ∀ n : ℕ, ∀ T ∈ (MaTangGraph n alpha_star (s_func n alpha_star)).cliqueFinset 3, (Y_set (MaTangGraph n alpha_star (s_func n alpha_star)) T).card ≤ (1 - alpha_star) * n + 1 + (c1 alpha_star) * n + 1 := by
      -- Let's choose any $n$ and $T$.
      intro n T hT
      have h_Y_card : (Y_set (MaTangGraph n alpha_star (s_func n alpha_star)) T).card ≤ (S_set n alpha_star).card + (s_func n alpha_star) := by
        apply Y_card_bound;
        · -- Since $c1 \alpha_star$ is positive and $n$ is a natural number, $c1 \alpha_star * n$ is positive. The ceiling of a positive number is also positive.
          have h_pos : 0 < c1 alpha_star * n := by
            -- Since $n$ is a natural number and $c1 \alpha_star$ is positive, their product is positive.
            have h_n_pos : 0 < n := by
              cases n <;> aesop;
              fin_cases T ; simp_all +decide [ SimpleGraph.isNClique_iff ];
            exact mul_pos ( c1_pos ) ( Nat.cast_pos.mpr h_n_pos );
          exact Nat.ceil_pos.mpr h_pos;
        · -- By definition of $hT$, we know that $T$ is in the cliqueFinset 3 of the MaTangGraph.
          exact hT;
      -- We'll use the fact that $|S| = n - \lfloor \alpha n \rfloor$ and $|clique_i| \leq s$.
      have h_S_card : (S_set n alpha_star).card ≤ (1 - alpha_star) * n + 1 := by
        rw [ card_S_set ];
        · rw [ Nat.cast_sub ];
          · linarith [ Nat.lt_floor_add_one ( alpha_star * n ) ];
          · exact Nat.floor_le_of_le ( mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( by rw [ show alpha_star = 1 - 1 / Real.sqrt 10 by rfl ] ; nlinarith [ Real.sqrt_nonneg 10, Real.sq_sqrt ( show 0 ≤ 10 by norm_num ), one_div_mul_cancel ( show Real.sqrt 10 ≠ 0 by norm_num ) ] ) );
        · exact Nat.floor_le_of_le ( mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( by rw [ show alpha_star = 1 - 1 / Real.sqrt 10 by rfl ] ; nlinarith [ Real.sqrt_nonneg 10, Real.sq_sqrt ( show 0 ≤ 10 by norm_num ), one_div_mul_cancel ( show Real.sqrt 10 ≠ 0 by norm_num ) ] ) );
      refine le_trans ( Nat.cast_le.mpr h_Y_card ) ?_;
      norm_num +zetaDelta at *;
      linarith [ show ( s_func n alpha_star : ℝ ) ≤ c1 alpha_star * n + 1 by exact_mod_cast Nat.ceil_lt_add_one ( show 0 ≤ c1 alpha_star * n by exact mul_nonneg ( show 0 ≤ c1 alpha_star by exact ( show 0 ≤ c1 alpha_star by exact le_of_lt ( c1_pos ) ) ) ( Nat.cast_nonneg _ ) ) |> le_of_lt ];
    -- We can choose N such that for all n ≥ N, 2 ≤ ε * n.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, 2 ≤ ε * n := by
      exact ⟨ ⌈2 / ε⌉₊ + 1, fun n hn => by nlinarith [ Nat.le_ceil ( 2 / ε ), mul_div_cancel₀ 2 hε.ne', show ( n : ℝ ) ≥ ⌈2 / ε⌉₊ + 1 by exact_mod_cast hn ] ⟩;
    filter_upwards [ Filter.eventually_ge_atTop N ] with n hn T hT using le_trans ( h_bound n T hT ) ( by nlinarith [ hN n hn, show ( 1 - alpha_star ) + c1 alpha_star = 2 - Real.sqrt ( 5 / 2 ) by exact? ] )

lemma c1_irrational : Irrational (c1 alpha_star) := by
  -- Substitute the value of `alpha_star` into the expression for `c1`.
  have h_c1_val : c1 alpha_star = 2 - 2 / Real.sqrt 10 - 2 * Real.sqrt 10 / 5 := by
    unfold c1;
    rw [ show alpha_star = 1 - 1 / Real.sqrt 10 by rfl ] ; ring ; norm_num;
    -- Combine like terms and simplify the expression.
    field_simp
    ring;
    -- Combine like terms and simplify the expression further.
    norm_num [ ← Real.sqrt_mul ] at *;
    rw [ show ( 80 : ℝ ) = 16 * 5 by norm_num, Real.sqrt_mul ] <;> ring ; norm_num
  rw [ h_c1_val ];
  -- Combine the terms involving $\sqrt{10}$.
  have h_combined : 2 - 2 / Real.sqrt 10 - 2 * Real.sqrt 10 / 5 = 2 - (3 * Real.sqrt 10) / 5 := by
    rw [ sub_sub ] ; ring;
    nlinarith [ Real.sqrt_nonneg 10, Real.sq_sqrt ( show 0 ≤ 10 by norm_num ), inv_mul_cancel₀ ( show Real.sqrt 10 ≠ 0 by norm_num ) ];
  have h_irrational : Irrational (Real.sqrt 10) := by
    exact fun ⟨ a, ha ⟩ => by have := congr_arg ( · ^ 2 ) ha; norm_num at this; norm_cast at this; exact absurd ( congr_arg ( ·.num ) this ) ( by norm_num [ sq, Rat.mul_self_num ] ; intros h; nlinarith [ show a.num ≤ 3 by nlinarith, show a.num ≥ -3 by nlinarith ] ) ;
  exact h_combined.symm ▸ fun ⟨ a, ha ⟩ => h_irrational ⟨ ( 2 - a ) * 5 / 3, by push_cast; linarith ⟩

lemma s_over_n_gt_c1 (n : ℕ) (hn : n > 0) :
  (s_func n alpha_star : ℝ) / n > c1 alpha_star := by
    -- Since $c1 \alpha_star$ is irrational, $c1 \alpha_star * n$ is also irrational. The ceiling of an irrational number is strictly greater than the number itself.
    have h_ceil : (s_func n alpha_star : ℝ) > c1 alpha_star * n := by
      -- By definition of ceiling, we know that ceiling(x) ≥ x for any real number x. However, if x is not an integer, then ceiling(x) > x.
      have h_ceil_gt : ∀ x : ℝ, ¬(∃ k : ℤ, x = k) → (Nat.ceil x : ℝ) > x := by
        aesop;
        exact lt_of_le_of_ne ( Nat.le_ceil _ ) ( by tauto );
      apply h_ceil_gt;
      -- Since $c1 \alpha_star$ is irrational, multiplying it by $n$ (a positive integer) results in an irrational number.
      have h_irrational : Irrational (c1 alpha_star) := by
        exact?;
      exact fun ⟨ k, hk ⟩ => h_irrational ⟨ k / n, by push_cast; rw [ ← hk, mul_div_cancel_right₀ _ ( by positivity ) ] ⟩
    rwa [ gt_iff_lt, lt_div_iff₀ ( by positivity ) ]

lemma edge_density_quad_neg (c : ℝ) (hc1 : c > c1 alpha_star) (hc2 : c < c1 alpha_star + 0.1) :
  c^2 - 4 * alpha_star * c + 8 * (alpha_star - 1/2)^2 < 0 := by
    unfold c1 at * ; norm_num at * ; aesop;
    unfold alpha_star at * ; norm_num at *;
    -- Substitute the values of $c1$ and $c2$ into the quadratic expression.
    have h_quad_neg : (c - (2 * (1 - 1 / Real.sqrt 10) - Real.sqrt 8 / Real.sqrt 5)) * (c - (2 * (1 - 1 / Real.sqrt 10) + Real.sqrt 8 / Real.sqrt 5)) < 0 := by
      -- Since $c$ is between the roots $r1$ and $r2$, we have $r1 < c < r2$.
      have h_roots : 2 * (1 - 1 / Real.sqrt 10) - Real.sqrt 8 / Real.sqrt 5 < c ∧ c < 2 * (1 - 1 / Real.sqrt 10) + Real.sqrt 8 / Real.sqrt 5 := by
        norm_num +zetaDelta at *;
        exact ⟨ hc1, hc2.trans_le <| by nlinarith [ show Real.sqrt 8 / Real.sqrt 5 ≥ 1 by rw [ ge_iff_le ] ; rw [ one_le_div ] <;> norm_num ] ⟩;
      exact mul_neg_of_pos_of_neg ( by linarith ) ( by linarith );
    convert h_quad_neg using 1 ; ring ; norm_num ; ring;

noncomputable def density_limit (α c : ℝ) : ℝ := α * (1 - α) + α * c / 2 - c^2 / 8

lemma density_limit_c1 : density_limit alpha_star (c1 alpha_star) = 1 / 4 := by
  unfold density_limit
  exact algebraic_inequality

lemma density_limit_gt (c : ℝ) (hc1 : c > c1 alpha_star) (hc2 : c < c1 alpha_star + 0.1) :
  density_limit alpha_star c > 1 / 4 := by
    -- By rearranging the inequality from `edge_density_quad_neg`, we can show that the density limit is greater than 1/4.
    have h_density_limit : 8 * alpha_star * (1 - alpha_star) + 4 * alpha_star * c - c^2 > 2 := by
      have := edge_density_quad_neg c hc1 hc2;
      linarith;
    unfold density_limit; linarith;

lemma gamma_const_eq : gamma_const = 7 / 2 + Real.sqrt 10 := by
  -- Substitute the values of alpha_star and c1 into the expression for gamma_const.
  have h_gamma_const : gamma_const = (1 - 1 / Real.sqrt 10) / (2 - 6 / Real.sqrt 10) := by
    have h_alpha_star : alpha_star = 1 - 1 / Real.sqrt 10 := by
      exact?
    have h_c1 : c1 alpha_star = 2 - 6 / Real.sqrt 10 := by
      -- Substitute α_star into the expression for c1.
      rw [show c1 alpha_star = 2 * alpha_star - Real.sqrt (2 - 4 * (alpha_star - 1)^2) from rfl];
      -- Let's simplify the expression inside the square root.
      have h_sqrt : Real.sqrt (2 - 4 * (alpha_star - 1)^2) = 4 / Real.sqrt 10 := by
        -- Substitute α_star into the expression and simplify.
        rw [h_alpha_star]
        field_simp
        ring;
        norm_num;
        rw [ ← sq_eq_sq₀ ] <;> ring_nf <;> norm_num [ ← Real.sqrt_mul ];
      rw [ h_sqrt ] ; ring_nf ; norm_num [ h_alpha_star ] ; ring_nf;
    rw [ ← h_alpha_star, ← h_c1, show gamma_const = alpha_star / c1 alpha_star from rfl ];
  rw [ h_gamma_const, div_eq_iff ] <;> ring_nf <;> nlinarith [ Real.sqrt_nonneg 10, Real.sq_sqrt ( show 0 ≤ 10 by norm_num ), mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( show 0 < 10 by norm_num ) ) ) ]

noncomputable def s_func_final (n : ℕ) (α : ℝ) : ℕ := Nat.ceil (c1 α * n) + 20

noncomputable def s_func_robust (n : ℕ) (α : ℝ) : ℕ := Nat.ceil (c1 α * n) + 100

lemma gamma_const_eq_proof : gamma_const = 7 / 2 + Real.sqrt 10 := by
  exact?

lemma gamma_not_half_integer_proven : ∀ k : ℤ, gamma_const ≠ k + 1/2 := by
  -- Since $\sqrt{10}$ is irrational, $3 + \sqrt{10}$ cannot be an integer.
  have h_irr : Irrational (Real.sqrt 10) := by
    have h_not_sq : ¬IsSquare 10 := by
      apply Aesop.BuiltinRules.not_intro
      intro a
      obtain ⟨k, hk⟩ := a;
      cases le_or_gt k 3 <;> nlinarith
    exact irrational_sqrt_ofNat_iff.mpr h_not_sq
  -- Since $\sqrt{10}$ is irrational, $3 + \sqrt{10}$ cannot be an integer. Therefore, $\gamma \neq k + 1/2$ for any integer $k$.
  intros k hk
  have h_contra : 3 + Real.sqrt 10 = k := by
    rw [gamma_const_eq] at hk;
    linarith;
  exact h_irr ⟨ k - 3, by push_cast; linarith ⟩

lemma b_div_s_tendsto_gamma : Filter.Tendsto (fun n : ℕ => (⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ)) Filter.atTop (nhds gamma_const) := by
  -- We'll use the fact that if the denominator grows faster than the numerator, the limit will tend to zero.
  -- By definition of $s_func_robust$, we know that $s_func_robust n alpha_star \approx c1 alpha_star * n$ for large $n$.
  have h_s_func_robust_approx : Filter.Tendsto (fun n : ℕ => (s_func_robust n alpha_star : ℝ) / n) Filter.atTop (nhds (c1 alpha_star)) := by
    unfold s_func_robust;
    -- The term $\frac{100}{n}$ tends to $0$ as $n$ tends to infinity.
    have h_zero : Filter.Tendsto (fun n : ℕ => (100 : ℝ) / n) Filter.atTop (nhds 0) := by
      exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop;
    -- The term $\frac{\lceil c1 \alpha_star n \rceil}{n}$ tends to $c1 \alpha_star$ as $n$ tends to infinity.
    have h_ceil : Filter.Tendsto (fun n : ℕ => (Nat.ceil (c1 alpha_star * n) : ℝ) / n) Filter.atTop (nhds (c1 alpha_star)) := by
      -- By the properties of the ceiling function and the fact that $1/n \to 0$ as $n \to \infty$, we can apply the squeeze theorem.
      have h_squeeze : ∀ n : ℕ, n > 0 → abs ((Nat.ceil (c1 alpha_star * n) : ℝ) / n - c1 alpha_star) ≤ 1 / (n : ℝ) := by
        intro n hn; rw [ abs_le ] ; constructor <;> nlinarith [ Nat.le_ceil ( c1 alpha_star * n ), Nat.ceil_lt_add_one ( show 0 ≤ c1 alpha_star * n by exact mul_nonneg ( show 0 ≤ c1 alpha_star by exact le_of_lt c1_pos ) ( Nat.cast_nonneg n ) ), show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr hn, div_mul_cancel₀ ( Nat.ceil ( c1 alpha_star * n ) : ℝ ) ( show ( n : ℝ ) ≠ 0 by positivity ), div_mul_cancel₀ ( 1 : ℝ ) ( show ( n : ℝ ) ≠ 0 by positivity ) ] ;
      exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero_norm' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; simpa using h_squeeze n hn ) <| tendsto_one_div_atTop_nhds_zero_nat;
    convert h_ceil.add h_zero using 2 <;> push_cast <;> ring;
  have h_gamma_const_approx : Filter.Tendsto (fun n : ℕ => (⌊alpha_star * (n : ℝ)⌋₊ : ℝ) / (n : ℝ)) Filter.atTop (nhds alpha_star) := by
    -- By the properties of the floor function, we have $\alpha_star * n - 1 < \lfloor \alpha_star * n \rfloor \leq \alpha_star * n$.
    have h_floor : ∀ n : ℕ, n > 0 → (alpha_star * (n : ℝ) - 1) < ⌊alpha_star * (n : ℝ)⌋₊ ∧ ⌊alpha_star * (n : ℝ)⌋₊ ≤ alpha_star * (n : ℝ) := by
      exact fun n hn => ⟨ Nat.sub_one_lt_floor _, Nat.floor_le <| by exact mul_nonneg ( show 0 ≤ alpha_star by exact sub_nonneg.mpr <| div_le_one_of_le₀ ( Real.le_sqrt_of_sq_le <| by norm_num ) <| Real.sqrt_nonneg _ ) <| Nat.cast_nonneg _ ⟩;
    rw [ Metric.tendsto_nhds ] ; aesop;
    refine' ⟨ ⌈ε⁻¹⌉₊ + 1, fun n hn => abs_lt.mpr ⟨ _, _ ⟩ ⟩ <;> nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ( ne_of_gt a ), h_floor n ( by linarith ), show ( n : ℝ ) ≥ ⌈ε⁻¹⌉₊ + 1 by exact_mod_cast hn, div_mul_cancel₀ ( ⌊alpha_star * ( n : ℝ ) ⌋₊ : ℝ ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ];
  have := h_gamma_const_approx.div h_s_func_robust_approx;
  exact this ( by exact ne_of_gt <| c1_pos ) |> fun h => h.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Pi.div_apply, div_div_div_cancel_right₀ <| by positivity ] ;

lemma fract_gamma_ne_half : Int.fract gamma_const ≠ 1/2 := by
  -- By contradiction, assume that `Int.fract gamma_const = 1/2`.
  by_contra h_contra
  -- Then `gamma_const = ⌊gamma_const⌋ + 1/2`.
  have h_gamma_eq : gamma_const = ⌊gamma_const⌋ + 1 / 2 := by
    linarith [ Int.fract_add_floor gamma_const ];
  exact absurd ( gamma_not_half_integer_proven ⌊gamma_const⌋ ) ( by norm_num [ h_gamma_eq.symm ] )

noncomputable def limit_density_val : ℝ :=
  let α := alpha_star
  let c := c1 α
  let γ := gamma_const
  let x := Int.fract γ
  α * (1 - α) + α * c / 2 - c^2 / 2 * x * (1 - x)

lemma limit_density_gt_quarter : limit_density_val > 1 / 4 := by
  unfold limit_density_val;
  -- Since $x = \text{Int.fract}(\gamma)$ and $\gamma$ is not half-integer, we have $x(1-x) < 1/4$.
  have hx_lt : Int.fract gamma_const * (1 - Int.fract gamma_const) < 1 / 4 := by
    -- Since $Int.fract \gamma_const \neq 1/2$, we have $Int.fract \gamma_const * (1 - Int.fract \gamma_const) < 1/4$ by the properties of the fractional part function.
    have h_frac_lt : Int.fract gamma_const ≠ 1 / 2 := by
      exact?;
    cases lt_or_gt_of_ne h_frac_lt <;> nlinarith [ Int.fract_nonneg gamma_const, Int.fract_lt_one gamma_const ] ;
  have := algebraic_inequality ; nlinarith [ show 0 < c1 alpha_star ^ 2 by exact sq_pos_of_pos ( c1_pos ) ]

lemma gamma_not_integer : ∀ k : ℤ, gamma_const ≠ k := by
  bound;
  -- From the assumption that `gamma_const = k`, we can derive that `Real.sqrt 10 = k - 7 / 2`.
  have h_sqrt : Real.sqrt 10 = k - 7 / 2 := by
    exact a.symm ▸ gamma_const_eq.symm ▸ by ring;
  -- Since $\sqrt{10}$ is irrational, it cannot be equal to any rational number, including $k - 7/2$.
  have h_irr : Irrational (Real.sqrt 10) := by
    have h_not_sq : ¬IsSquare 10 := by
      apply Aesop.BuiltinRules.not_intro
      intro a
      obtain ⟨k, hk⟩ := a;
      cases le_or_gt k 3 <;> nlinarith
    exact irrational_sqrt_ofNat_iff.mpr h_not_sq
  exact h_irr ⟨ k - 7 / 2, by push_cast; linarith ⟩

lemma fract_b_div_s_tendsto_fract_gamma : Filter.Tendsto (fun n : ℕ => Int.fract ((⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ))) Filter.atTop (nhds (Int.fract gamma_const)) := by
  -- Since $\gamma$ is not an integer, the fractional part function is continuous at $\gamma$.
  have h_cont : ContinuousAt Int.fract gamma_const := by
    -- Since $\gamma$ is not an integer, the floor function $\lfloor x \rfloor$ is constant in a neighborhood of $\gamma$.
    have h_floor_const : ∃ δ > 0, ∀ x, abs (x - gamma_const) < δ → ⌊x⌋ = ⌊gamma_const⌋ := by
      norm_num [ Int.floor_eq_iff ];
      exact ⟨ Min.min ( gamma_const - ⌊gamma_const⌋ ) ( ⌊gamma_const⌋ + 1 - gamma_const ), lt_min ( sub_pos.mpr <| lt_of_le_of_ne ( Int.floor_le _ ) fun h => by exact gamma_not_integer _ h.symm ) ( sub_pos.mpr <| Int.lt_floor_add_one _ ), fun x hx => ⟨ by linarith [ abs_lt.mp hx, min_le_left ( gamma_const - ⌊gamma_const⌋ ) ( ⌊gamma_const⌋ + 1 - gamma_const ) ], by linarith [ abs_lt.mp hx, min_le_right ( gamma_const - ⌊gamma_const⌋ ) ( ⌊gamma_const⌋ + 1 - gamma_const ) ] ⟩ ⟩;
    -- Since the floor function is constant in a neighborhood of gamma_const, the fractional part function is continuous there.
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x, abs (x - gamma_const) < δ → ⌊x⌋ = ⌊gamma_const⌋ := h_floor_const;
    exact ContinuousAt.congr ( show ContinuousAt ( fun x : ℝ => x - ⌊gamma_const⌋ ) gamma_const from continuousAt_id.sub continuousAt_const ) ( Filter.eventuallyEq_of_mem ( Metric.ball_mem_nhds _ hδ_pos ) fun x hx => by simp +decide [ Int.fract, hδ x hx ] );
  refine' h_cont.tendsto.comp _;
  convert b_div_s_tendsto_gamma using 1

theorem MaTang_edge_density_limit :
  Filter.Tendsto (fun n : ℕ => ((MaTangGraph n alpha_star (s_func_robust n alpha_star)).edgeFinset.card : ℝ) / n^2) Filter.atTop (nhds limit_density_val) := by
    -- We express the edge count in terms of $b, s, r$ using the provided formula.
    have h_edges_formula : ∀ n : ℕ, (n > 0) → ((MaTangGraph n alpha_star (s_func_robust n alpha_star)).edgeFinset.card : ℝ) = ((⌊alpha_star * n⌋₊ : ℝ) * (n - ⌊alpha_star * n⌋₊)) + (1 / 2 : ℝ) * ((⌊alpha_star * n⌋₊ : ℝ) * (s_func_robust n alpha_star : ℝ) - ⌊alpha_star * n⌋₊ - (s_func_robust n alpha_star : ℝ) ^ 2 * Int.fract ((⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ)) * (1 - Int.fract ((⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ)))) := by
      intro n hn_pos
      have h_edges_formula : ((MaTangGraph n alpha_star (s_func_robust n alpha_star)).edgeFinset.card : ℝ) = ((⌊alpha_star * n⌋₊ : ℝ) * (n - ⌊alpha_star * n⌋₊)) + (1 / 2 : ℝ) * ((⌊alpha_star * n⌋₊ : ℝ) * (s_func_robust n alpha_star : ℝ) - ⌊alpha_star * n⌋₊ - (s_func_robust n alpha_star : ℝ) ^ 2 * Int.fract ((⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ)) * (1 - Int.fract ((⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ)))) := by
        have h_card_edges_B_real : ((edges_B_set n alpha_star (s_func_robust n alpha_star)).card : ℝ) = ((⌊alpha_star * n⌋₊ : ℝ) * (s_func_robust n alpha_star - 1) - (s_func_robust n alpha_star : ℝ) ^ 2 * Int.fract ((⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ)) * (1 - Int.fract ((⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ)))) / 2 := by
          rw [ eB_eq_real, Int.fract ];
          · rw [ Nat.mod_def ];
            -- Since ⌊alpha_star * n⌋₊ is an integer and s_func_robust n alpha_star is also an integer, the division ⌊alpha_star * n⌋₊ / s_func_robust n alpha_star is an integer. Therefore, the floor of this division is just the integer itself.
            have h_floor : ⌊(⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ)⌋ = ⌊alpha_star * n⌋₊ / s_func_robust n alpha_star := by
              exact Int.floor_eq_iff.mpr ⟨ by rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by unfold s_func_robust; aesop ) ] ; norm_cast; linarith [ Nat.div_mul_le_self ( ⌊alpha_star * n⌋₊ ) ( s_func_robust n alpha_star ) ], by rw [ div_lt_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by unfold s_func_robust; aesop ) ] ; norm_cast; linarith [ Nat.div_add_mod ( ⌊alpha_star * n⌋₊ ) ( s_func_robust n alpha_star ), Nat.mod_lt ( ⌊alpha_star * n⌋₊ ) ( Nat.pos_of_ne_zero <| show s_func_robust n alpha_star ≠ 0 from by unfold s_func_robust; aesop ) ] ⟩;
            rw [ Nat.cast_sub ] <;> norm_num [ h_floor ] ; ring;
            · by_cases h : s_func_robust n alpha_star = 0 <;> simp_all +decide [ sq, mul_assoc ] ; ring;
              · unfold s_func_robust at h; aesop;
              · norm_cast ; ring;
                push_cast ; ring;
            · exact Nat.mul_div_le _ _;
          · exact Nat.succ_pos _;
          · -- Since $\alpha^* < 1$, we have $\alpha^* n < n$, and thus $\lfloor \alpha^* n \rfloor \leq n$.
            have h_alpha_star_lt_1 : alpha_star < 1 := by
              exact sub_lt_self _ ( by positivity );
            exact Nat.floor_le_of_le ( by nlinarith )
        -- The edge count is the sum of the edges in the B set and the edges between B and S.
        have h_edge_count : ((MaTangGraph n alpha_star (s_func_robust n alpha_star)).edgeFinset.card : ℝ) = ((edges_B_set n alpha_star (s_func_robust n alpha_star)).card : ℝ) + ((edges_BS_set n alpha_star).card : ℝ) := by
          rw [ add_comm, ← Nat.cast_add ];
          rw [ ← Finset.card_union_of_disjoint ];
          · rw [ edges_decomposition ];
          · exact?;
        rw [ h_edge_count, h_card_edges_B_real ];
        rw [ card_edges_BS ] ; ring;
        rw [ card_B_set, card_S_set ] <;> norm_num ; ring;
        · rw [ Nat.cast_sub ( show ⌊alpha_star * n⌋₊ ≤ n from Nat.floor_le_of_le ( mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( show alpha_star ≤ 1 by rw [ show alpha_star = 1 - 1 / Real.sqrt 10 by rfl ] ; exact sub_le_self _ <| by positivity ) ) ) ] ; ring;
        · exact Nat.floor_le_of_le ( mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( show alpha_star ≤ 1 by exact sub_le_self _ <| by positivity ) );
        · exact Nat.floor_le_of_le ( mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( show alpha_star ≤ 1 by exact sub_le_self _ <| by positivity ) );
      convert h_edges_formula using 1;
    -- We know the following limits:
    have h_lims : Filter.Tendsto (fun n : ℕ => (⌊alpha_star * n⌋₊ : ℝ) / n) Filter.atTop (nhds alpha_star) ∧ Filter.Tendsto (fun n : ℕ => (s_func_robust n alpha_star : ℝ) / n) Filter.atTop (nhds (c1 alpha_star)) ∧ Filter.Tendsto (fun n : ℕ => (⌊alpha_star * n⌋₊ : ℝ) / n^2) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun n : ℕ => Int.fract ((⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ))) Filter.atTop (nhds (Int.fract gamma_const)) := by
      -- We'll use the fact that the floor function and the ceiling function's effects become negligible as $n$ grows.
      have h_floor_ceil : Filter.Tendsto (fun n : ℕ => (⌊alpha_star * n⌋₊ : ℝ) / n) Filter.atTop (nhds alpha_star) ∧ Filter.Tendsto (fun n : ℕ => (Nat.ceil (c1 alpha_star * n) : ℝ) / n) Filter.atTop (nhds (c1 alpha_star)) := by
        constructor <;> refine' Metric.tendsto_nhds.mpr _ <;> aesop;
        · refine' ⟨ ⌈ε⁻¹⌉₊ + 1, fun n hn => abs_lt.mpr ⟨ _, _ ⟩ ⟩ <;> nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ( ne_of_gt a ), Nat.lt_of_ceil_lt hn, Nat.floor_le ( show 0 ≤ alpha_star * ( n : ℝ ) by exact mul_nonneg ( show 0 ≤ alpha_star by exact sub_nonneg.mpr <| div_le_one_of_le₀ ( Real.le_sqrt_of_sq_le <| by norm_num ) <| Real.sqrt_nonneg _ ) <| Nat.cast_nonneg _ ), Nat.lt_floor_add_one ( alpha_star * ( n : ℝ ) ), div_mul_cancel₀ ( ⌊alpha_star * ( n : ℝ ) ⌋₊ : ℝ ) <| show ( n : ℝ ) ≠ 0 by norm_cast; linarith ];
        · refine' ⟨ ⌈ε⁻¹⌉₊ + 1, fun n hn => abs_lt.mpr ⟨ _, _ ⟩ ⟩ <;> nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ( ne_of_gt a ), Nat.lt_of_ceil_lt hn, Nat.le_ceil ( c1 alpha_star * n ), Nat.ceil_lt_add_one ( show 0 ≤ c1 alpha_star * n by exact mul_nonneg ( le_of_lt ( c1_pos ) ) ( Nat.cast_nonneg _ ) ), div_mul_cancel₀ ( ⌈c1 alpha_star * n⌉₊ : ℝ ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ];
      aesop;
      · convert right.add ( show Filter.Tendsto ( fun n : ℕ => ( 100 : ℝ ) / n ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) using 2 <;> ring;
        unfold s_func_robust; norm_num ; ring;
      · convert left.div_atTop tendsto_natCast_atTop_atTop using 2 ; ring;
      · convert fract_b_div_s_tendsto_fract_gamma using 1;
    -- We can rewrite the expression using the limits obtained.
    have h_rewrite : Filter.Tendsto (fun n : ℕ => ((⌊alpha_star * n⌋₊ : ℝ) / n) * (1 - (⌊alpha_star * n⌋₊ : ℝ) / n) + (1 / 2 : ℝ) * (((⌊alpha_star * n⌋₊ : ℝ) / n) * ((s_func_robust n alpha_star : ℝ) / n) - (⌊alpha_star * n⌋₊ : ℝ) / n^2 - ((s_func_robust n alpha_star : ℝ) / n)^2 * Int.fract ((⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ)) * (1 - Int.fract ((⌊alpha_star * n⌋₊ : ℝ) / (s_func_robust n alpha_star : ℝ))))) Filter.atTop (nhds (limit_density_val)) := by
      convert Filter.Tendsto.add ( Filter.Tendsto.mul h_lims.1 ( tendsto_const_nhds.sub h_lims.1 ) ) ( Filter.Tendsto.mul tendsto_const_nhds ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( Filter.Tendsto.mul h_lims.1 h_lims.2.1 ) h_lims.2.2.1 ) ( Filter.Tendsto.mul ( Filter.Tendsto.mul ( h_lims.2.1.pow 2 ) h_lims.2.2.2 ) ( tendsto_const_nhds.sub h_lims.2.2.2 ) ) ) ) using 2 ; norm_num [ limit_density_val ];
      ring;
    -- By definition of edge density, we can rewrite the limit expression using the formula from h_edges_formula.
    have h_edge_density : ∀ n : ℕ, n > 0 → ((MaTangGraph n alpha_star (s_func_robust n alpha_star)).edgeFinset.card : ℝ) / n^2 = ((Nat.floor (alpha_star * n) : ℝ) / n) * (1 - (Nat.floor (alpha_star * n) : ℝ) / n) + (1 / 2) * ((Nat.floor (alpha_star * n) : ℝ) / n * (s_func_robust n alpha_star : ℝ) / n - (Nat.floor (alpha_star * n) : ℝ) / n^2 - ((s_func_robust n alpha_star : ℝ) / n)^2 * Int.fract ((Nat.floor (alpha_star * n) : ℝ) / (s_func_robust n alpha_star : ℝ)) * (1 - Int.fract ((Nat.floor (alpha_star * n) : ℝ) / (s_func_robust n alpha_star : ℝ)))) := by
      -- By dividing both sides of the equation from h_edges_formula by n squared, we can rewrite the left-hand side as the edge density.
      intro n hn_pos
      rw [h_edges_formula n hn_pos]
      field_simp;
    exact h_rewrite.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ h_edge_density n hn ] ; ring )

theorem MaTang_edge_density_lower_bound : ∃ N : ℕ, ∀ n ≥ N, ((MaTangGraph n alpha_star (s_func_robust n alpha_star)).edgeFinset.card : ℝ) > (n^2 : ℝ) / 4 := by
  -- Let's choose any $n$ greater than $N$.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ((MaTangGraph n alpha_star (s_func_robust n alpha_star)).edgeFinset.card : ℝ) / n^2 > 1 / 4 := by
    -- By definition of convergence, for any ε > 0, there exists an N such that for all n ≥ N, the edge density is within ε of limit_density_val.
    have h_conv : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (((MaTangGraph n alpha_star (s_func_robust n alpha_star)).edgeFinset.card : ℝ) / n^2 - limit_density_val) < ε := by
      exact Metric.tendsto_atTop.mp MaTang_edge_density_limit;
    exact Exists.elim ( h_conv ( limit_density_val - 1 / 4 ) ( sub_pos.mpr <| by exact? ) ) fun N hN => ⟨ N, fun n hn => by linarith [ abs_lt.mp ( hN n hn ) ] ⟩;
  exact ⟨ N + 1, fun n hn => by have := hN n ( by linarith ) ; rw [ gt_iff_lt ] at *; rw [ lt_div_iff₀ ] at * <;> nlinarith [ show ( n : ℝ ) ≥ N + 1 by norm_cast ] ⟩

theorem MaTang_Y_upper_bound (ε : ℝ) (hε : 0 < ε) :
  ∃ N, ∀ n ≥ N, ∀ T ∈ (MaTangGraph n alpha_star (s_func_robust n alpha_star)).cliqueFinset 3,
  ((Y_set (MaTangGraph n alpha_star (s_func_robust n alpha_star)) T).card : ℝ) ≤ (2 - Real.sqrt (5/2) + ε) * n := by
    -- Apply the lemma Y_card_bound to bound |Y(T)|.
    have h_bound : ∀ n ≥ 1, ∀ T ∈ (MaTangGraph n alpha_star (s_func_robust n alpha_star)).cliqueFinset 3, ((Y_set (MaTangGraph n alpha_star (s_func_robust n alpha_star)) T).card : ℝ) ≤ (n - ⌊alpha_star * n⌋₊) + (Nat.ceil (c1 alpha_star * n) + 100) := by
      intros n hn T hT
      have h_bound_Y : (Y_set (MaTangGraph n alpha_star (s_func_robust n alpha_star)) T).card ≤ (S_set n alpha_star).card + (s_func_robust n alpha_star : ℕ) := by
        have := Y_card_bound n alpha_star ( s_func_robust n alpha_star ) ?_ T hT <;> aesop;
        exact Nat.succ_pos _;
      refine' le_trans ( Nat.cast_le.mpr h_bound_Y ) _;
      rw [ card_S_set ] <;> norm_num;
      · rw [ Nat.cast_sub ( Nat.floor_le_of_le ( by nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast, show ( alpha_star : ℝ ) ≤ 1 by rw [ alpha_star_val ] ; exact sub_le_self _ <| by positivity ] ) ) ] ; norm_cast;
      · exact Nat.floor_le_of_le ( mul_le_of_le_one_left ( by positivity ) ( by rw [ alpha_star ] ; exact sub_le_self _ ( by positivity ) ) );
    -- We need to show that the right-hand side of the inequality tends to $2 - \sqrt{5/2}$ as $n$ tends to infinity.
    have h_rhs_tendsto : Filter.Tendsto (fun n : ℕ => ((n - ⌊alpha_star * n⌋₊) + (Nat.ceil (c1 alpha_star * n) + 100) : ℝ) / n) Filter.atTop (nhds (1 - alpha_star + c1 alpha_star)) := by
      -- We can split the fraction into three parts and show that each part tends to its respective limit.
      have h_split : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - (⌊alpha_star * n⌋₊ : ℝ) / n + (⌈c1 alpha_star * n⌉₊ : ℝ) / n + 100 / n) Filter.atTop (nhds (1 - alpha_star + c1 alpha_star)) := by
        have h_floor : Filter.Tendsto (fun n : ℕ => (⌊alpha_star * n⌋₊ : ℝ) / n) Filter.atTop (nhds alpha_star) := by
          -- By the properties of the floor function, we know that for any real number $x$, $\lfloor x \rfloor \leq x < \lfloor x \rfloor + 1$.
          have h_floor : ∀ n : ℕ, (⌊alpha_star * n⌋₊ : ℝ) ≤ alpha_star * n ∧ alpha_star * n < (⌊alpha_star * n⌋₊ + 1 : ℝ) := by
            exact fun n => ⟨ Nat.floor_le <| mul_nonneg ( show 0 ≤ alpha_star by exact sub_nonneg.2 <| div_le_one_of_le₀ ( Real.le_sqrt_of_sq_le <| by norm_num ) <| Real.sqrt_nonneg _ ) <| Nat.cast_nonneg _, Nat.lt_floor_add_one _ ⟩;
          rw [ Metric.tendsto_nhds ] ; aesop;
          exact ⟨ ⌈ε_1⁻¹⌉₊ + 1, fun n hn => abs_lt.mpr ⟨ by rw [ lt_sub_iff_add_lt ] ; rw [ lt_div_iff₀ ] <;> nlinarith [ Nat.le_ceil ( ε_1⁻¹ ), mul_inv_cancel₀ ( ne_of_gt a ), h_floor n, show ( n : ℝ ) ≥ ⌈ε_1⁻¹⌉₊ + 1 by exact_mod_cast hn ], by rw [ sub_lt_iff_lt_add' ] ; rw [ div_lt_iff₀ ] <;> nlinarith [ Nat.le_ceil ( ε_1⁻¹ ), mul_inv_cancel₀ ( ne_of_gt a ), h_floor n, show ( n : ℝ ) ≥ ⌈ε_1⁻¹⌉₊ + 1 by exact_mod_cast hn ] ⟩ ⟩
        have h_ceil : Filter.Tendsto (fun n : ℕ => (⌈c1 alpha_star * n⌉₊ : ℝ) / n) Filter.atTop (nhds (c1 alpha_star)) := by
          rw [ Metric.tendsto_nhds ] ; aesop;
          refine' ⟨ ⌈ε_1⁻¹⌉₊ + 1, fun n hn => abs_lt.mpr ⟨ _, _ ⟩ ⟩ <;> nlinarith [ Nat.le_ceil ( ε_1⁻¹ ), mul_inv_cancel₀ ( ne_of_gt a ), Nat.lt_of_ceil_lt hn, Nat.le_ceil ( c1 alpha_star * n ), Nat.ceil_lt_add_one ( show 0 ≤ c1 alpha_star * n by exact mul_nonneg ( show 0 ≤ c1 alpha_star by exact le_of_lt ( c1_pos ) ) ( Nat.cast_nonneg _ ) ), div_mul_cancel₀ ( ⌈c1 alpha_star * n⌉₊ : ℝ ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ];
        simpa using Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.sub h_floor ) h_ceil ) ( tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat );
      -- Since the two expressions are equal, their limits are the same.
      have h_eq : ∀ n : ℕ, n ≥ 1 → ((n : ℝ) - ⌊alpha_star * n⌋₊ + (Nat.ceil (c1 alpha_star * n) + 100)) / n = 1 - (⌊alpha_star * n⌋₊ : ℝ) / n + (Nat.ceil (c1 alpha_star * n) : ℝ) / n + 100 / n := by
        -- By simplifying the left-hand side, we can see that it matches the right-hand side.
        intro n hn
        field_simp [hn]
        ring;
      -- Since the two functions are equal for all $n \geq 1$, their limits are the same.
      apply Filter.Tendsto.congr' (by filter_upwards [Filter.eventually_ge_atTop 1] with n hn; rw [h_eq n hn]) h_split
    -- We know that $1 - \alpha + c1 \alpha = 2 - \sqrt{5/2}$.
    have h_rhs_eq : 1 - alpha_star + c1 alpha_star = 2 - Real.sqrt (5 / 2) := by
      have := Phi_val; norm_num [ show alpha_star = 1 - 1 / Real.sqrt 10 by rfl, show c1 alpha_star = 2 * alpha_star - Real.sqrt ( 2 - 4 * ( alpha_star - 1 ) ^ 2 ) by rfl ] at *; nlinarith [ Real.sq_sqrt ( show 0 ≤ 10 by norm_num ), Real.sq_sqrt ( show 0 ≤ 5 / 2 by norm_num ), Real.sqrt_nonneg 10, Real.sqrt_nonneg ( 5 / 2 ), mul_div_cancel₀ 1 ( ne_of_gt ( Real.sqrt_pos.mpr ( show 0 < 10 by norm_num ) ) ) ] ;
    have := h_rhs_tendsto.eventually ( gt_mem_nhds <| show 1 - alpha_star + c1 alpha_star < 2 - Real.sqrt ( 5 / 2 ) + ε by linarith ) ; aesop;
    exact ⟨ w + 1, fun n hn T hT => le_trans ( h_bound n ( by linarith ) T hT ) ( by have := h n ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ) ⟩

end AristotleLemmas

theorem MaTang_main (ε : ℝ) (hε : 0 < ε) :
  ∃ N : ℕ, ∀ n ≥ N,
    let G : SimpleGraph (Fin n) := MaTangGraph n alpha_star (s_func_robust n alpha_star)
    (G.edgeFinset.card : ℝ) > (n^2 : ℝ) / 4 ∧
    ∀ T ∈ G.cliqueFinset 3,
      ((Y_set G T).card : ℝ) ≤ (2 - Real.sqrt (5/2) + ε) * n := by
  obtain ⟨ N1, hN1 ⟩ := MaTang_edge_density_lower_bound;
  obtain ⟨ N2, hN2 ⟩ := MaTang_Y_upper_bound ε hε ; exact ⟨ Max.max N1 N2, fun n hn => ⟨ hN1 n ( le_trans ( le_max_left _ _ ) hn ), fun T hT => hN2 n ( le_trans ( le_max_right _ _ ) hn ) T hT ⟩ ⟩ ;

/--
If a graph on `n` vertices has more than `n^2 / 4` edges, then for large enough `n`
(depending on `ε`), there is a triangle `T` in the graph such that more than
`(1/2 - ε) * n` vertices have at least two neighbors in `T`.
-/
def erdos_1034 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n0 : ℕ,
      ∀ n ≥ n0,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (G.edgeFinset.card : ℝ) > ((n : ℝ)^2 / 4) →
          ∃ T ∈ G.cliqueFinset 3,
            ((Y_set G T).card : ℝ) > (((1 : ℝ) / 2) - ε) * (n : ℝ)

theorem not_erdos_1034 : ¬ erdos_1034 := by
  intro h;
  -- Apply the MaTang graph's properties to derive a contradiction with h.
  have := h (1 / 100) (by norm_num);
  contrapose! this;
  intro x;
  -- By the properties of the MaTang graph, we can choose n large enough such that the edge count exceeds n²/4 and the Y-set condition holds.
  obtain ⟨n, hn⟩ : ∃ n ≥ x, (MaTangGraph n alpha_star (s_func_robust n alpha_star)).edgeFinset.card > (n^2 : ℝ) / 4 ∧ ∀ T ∈ (MaTangGraph n alpha_star (s_func_robust n alpha_star)).cliqueFinset 3, ((Y_set (MaTangGraph n alpha_star (s_func_robust n alpha_star)) T).card : ℝ) ≤ (2 - Real.sqrt (5/2) + 1/100) * n := by
    have := MaTang_main ( 1 / 100 ) ( by norm_num );
    exact ⟨ _, le_max_left _ _, this.choose_spec _ ( le_max_right _ _ ) ⟩;
  refine' ⟨ n, hn.1, _, _, hn.2.1, fun T hT => _ ⟩;
  exact le_trans ( hn.2.2 T hT ) ( by nlinarith only [ Real.sqrt_nonneg ( 5 / 2 ), Real.sq_sqrt ( show 0 ≤ 5 / 2 by norm_num ) ] )

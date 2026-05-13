/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 914.
https://www.erdosproblems.com/forum/thread/914

Informal authors:
- H. A. Kierstead
- A. V. Kostochka

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/914#post-5403
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem914.lean
-/
/-
The Hajnal-Szemerédi theorem states that any graph with maximum degree Δ has an equitable colouring with Δ + 1 colours. Equivalently, every graph with $rm$ vertices and minimum degree at least $m(r-1)$ contains $m$ vertex disjoint copies of $K_r$.

Hajnal, A. and Szemerédi, E., Proof of a conjecture of P. Erdős. In Combinatorial Theory and Its Applications, Vol. 2 (1970), 601--623.

On Bloom's website this is recorded as Erdős Problem #914; https://www.erdosproblems.com/914.

In 2008, an alternative proof was given by H. A. Kierstead and A. V. Kostochka.

Kierstead, H. A. and Kostochka, A. V., A Short Proof of the Hajnal–Szemerédi Theorem on Equitable Colouring. Combinatorics, Probability and Computing, Vol. 17 (2008), 265--270.

It is the latter proof Aristotle from Harmonic (aristotle-harmonic@harmonic.fun)
managed to formalize, the result of which you can find below.

-/

import Mathlib

namespace Erdos914

set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.style.induction false
set_option linter.style.refine false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.flexible false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false

open Classical

/-! ## Terminal vertex construction

A vertex W in a directed graph is "terminal" (with respect to a root r) if every
other vertex that can reach r can also reach r without passing through W.
This section proves that such a terminal vertex always exists when there are ≥ 2
vertices reaching r. -/

namespace TerminalVertex

variable {α : Type*} [Fintype α] [DecidableEq α]

/-
Extract a nodup chain witnessing ReflTransGen.
-/
omit [Fintype α] in
lemma exists_nodup_chain'
    {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) (hab : a ≠ b) :
    ∃ l : List α, l.Nodup ∧ l.IsChain R ∧ l.head? = some a ∧
    l.getLast? = some b ∧ 2 ≤ l.length := by
  obtain ⟨l, hl⟩ : ∃ l : List α, List.IsChain R l ∧ l.head? = some a ∧ l.getLast? = some b := by
    have h_contradiction : ∀ {x y : α}, Relation.ReflTransGen R x y → ∃ l : List α, List.IsChain R l ∧ l.head? = some x ∧ l.getLast? = some y := by
      intro x y hxy
      induction' hxy with x y hxy ih;
      · exact ⟨ [ x ], List.isChain_singleton _, rfl, rfl ⟩;
      · rename_i h;
        obtain ⟨ l, hl₁, hl₂, hl₃ ⟩ := h; use l ++ [ y ] ; simp_all +decide ;
        exact List.isChain_append.mpr ⟨ hl₁, by aesop ⟩;
    exact h_contradiction h;
  -- Let's take the shortest such chain.
  obtain ⟨l, hl_min⟩ : ∃ l : List α, List.IsChain R l ∧ l.head? = some a ∧ l.getLast? = some b ∧ ∀ l' : List α, List.IsChain R l' → l'.head? = some a → l'.getLast? = some b → l.length ≤ l'.length := by
    have h_well_founded : WellFounded fun l l' : { l : List α // List.IsChain R l ∧ l.head? = some a ∧ l.getLast? = some b } => l.val.length < l'.val.length := by
      rw [ WellFounded.wellFounded_iff_has_min ];
      intro s hs;
      have h_well_founded : WellFounded fun l l' : ℕ => l < l' := by
        exact wellFounded_lt;
      have := h_well_founded.has_min ( Set.image ( fun x : { l : List α // List.IsChain R l ∧ l.head? = some a ∧ l.getLast? = some b } => x.val.length ) s ) ⟨ _, Set.mem_image_of_mem _ hs.choose_spec ⟩ ; aesop;
    have := h_well_founded.has_min { l : { l : List α // List.IsChain R l ∧ l.head? = some a ∧ l.getLast? = some b } | True } ⟨ ⟨ l, hl ⟩, trivial ⟩ ; aesop;
  -- If $l$ has duplicates, we can remove them to obtain a shorter chain.
  by_cases h_dup : ∃ i j : Fin l.length, i < j ∧ l.get i = l.get j;
  · obtain ⟨ i, j, hij, h_eq ⟩ := h_dup;
    have h_shorter : ∃ l' : List α, List.IsChain R l' ∧ l'.head? = some a ∧ l'.getLast? = some b ∧ l'.length < l.length := by
      refine' ⟨ l.take i.val ++ l.drop j.val, _, _, _, _ ⟩ <;> simp_all +decide;
      · refine' List.isChain_append.mpr ⟨ _, _, _ ⟩;
        · have := hl_min.1;
          exact List.IsChain.take this ↑i;
        · have := hl_min.1;
          exact List.IsChain.drop this ↑j;
        · rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> simp_all +decide [ List.getLast?_take, List.head?_drop ];
          have := List.isChain_iff_getElem.mp hl_min.1;
          convert this i (by omega) using 1;
          · rw [ List.getElem?_eq_getElem ] ; aesop;
          · exact h_eq.symm;
      · rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> simp_all +decide [ List.take ];
        · cases l <;> aesop;
        · cases l <;> aesop;
      · rw [ List.getLast?_drop ] ; aesop;
      · linarith [ show ( i : ℕ ) < j from hij, Nat.sub_add_cancel ( show ( j : ℕ ) ≤ l.length from j.2.le ) ];
    grind;
  · refine' ⟨ l, _, hl_min.1, hl_min.2.1, hl_min.2.2.1, _ ⟩;
    · exact List.nodup_iff_injective_get.mpr fun i j hij => le_antisymm ( not_lt.mp fun hi => h_dup ⟨ j, i, hi, hij.symm ⟩ ) ( not_lt.mp fun hj => h_dup ⟨ i, j, hj, hij ⟩ );
    · rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide;
      grind

/-
A nodup chain from a to b gives ReflTransGen of the base relation.
-/
omit [Fintype α] [DecidableEq α] in
lemma chain_to_reflTransGen
    {R : α → α → Prop} {l : List α} {a b : α}
    (hchain : l.IsChain R) (hhead : l.head? = some a)
    (hlast : l.getLast? = some b) :
    Relation.ReflTransGen R a b := by
  induction' l with x l ih generalizing a b;
  · cases hhead;
  · cases l with
    | nil => simp_all +decide; rfl
    | cons y l =>
      simp at hhead; subst hhead
      exact Relation.ReflTransGen.head (List.isChain_cons_cons.mp hchain |>.1)
        (ih (List.isChain_cons_cons.mp hchain |>.2) rfl hlast)

/-
If every element of a chain (except possibly the last) is ≠ w,
    then we get ReflTransGen of the restricted relation.
-/
omit [Fintype α] [DecidableEq α] in
lemma chain_to_restricted_reflTransGen
    {R : α → α → Prop} {l : List α} {a b w : α}
    (hchain : l.IsChain R) (hhead : l.head? = some a)
    (hlast : l.getLast? = some b)
    (hw : w ∉ l ∨ w = b) :
    Relation.ReflTransGen (fun x y => R x y ∧ x ≠ w) a b := by
      induction' l with x xs hx generalizing a b w <;> simp_all +decide;
      cases xs <;> simp_all +decide;
      · rfl;
      · grind +suggestions

/-
If l is a nodup chain from a to b, and w ∈ l with w ≠ a,
    then the suffix starting from w is a chain from w to b that
    is strictly shorter and doesn't contain a.
-/
omit [Fintype α] [DecidableEq α] in
lemma nodup_chain_suffix
    {R : α → α → Prop} {l : List α} {a b w : α}
    (hchain : l.IsChain R) (hnodup : l.Nodup)
    (hhead : l.head? = some a) (hlast : l.getLast? = some b)
    (hw_mem : w ∈ l) (hw_ne_a : w ≠ a) (_hw_ne_b : w ≠ b) :
    ∃ l' : List α, l'.IsChain R ∧ l'.Nodup ∧ l'.head? = some w ∧
      l'.getLast? = some b ∧ l'.length < l.length ∧ a ∉ l' := by
  obtain ⟨l₁, l₂, hl₁, hl₂⟩ : ∃ l₁ l₂ : List α, l = l₁ ++ w :: l₂ := by
    exact List.mem_iff_append.mp hw_mem;
  refine' ⟨ w :: l₂, _, _, _, _, _, _ ⟩ <;> simp_all +decide;
  · exact List.IsChain.suffix hchain ( List.suffix_append _ _ );
  · grind;
  · cases l₁ <;> aesop;
  · cases l₁ <;> aesop

/-
In a finite directed graph, if there exists a vertex W₀ ≠ r that can reach r,
    then there exists a "terminal" vertex W ≠ r that can reach r, such that every
    other vertex that can reach r can also reach r without passing through W.
-/
set_option maxHeartbeats 800000 in
theorem exists_terminal_vertex
    (R : α → α → Prop) (r : α)
    (W₀ : α) (hW₀ : Relation.ReflTransGen R W₀ r) (hW₀_ne : W₀ ≠ r) :
    ∃ W : α, Relation.ReflTransGen R W r ∧ W ≠ r ∧
      ∀ C : α, Relation.ReflTransGen R C r → C ≠ W →
        Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W) C r := by
  by_contra! h_contra;
  -- By finiteness, the set of vertices that can reach r is nonempty and finite, so it must have a minimal element with respect to some well-ordering.
  obtain ⟨W_star, hW_star⟩ : ∃ W_star : α, Relation.ReflTransGen R W_star r ∧ W_star ≠ r ∧ ∀ W' : α, Relation.ReflTransGen R W' r → W' ≠ r → (Nat.card {C : α | Relation.ReflTransGen R C r ∧ C ≠ W' ∧ ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W') C r}) ≥ (Nat.card {C : α | Relation.ReflTransGen R C r ∧ C ≠ W_star ∧ ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star) C r}) := by
    have h_finite : Set.Finite {W : α | Relation.ReflTransGen R W r ∧ W ≠ r} := by
      exact Set.toFinite _;
    have := h_finite.toFinset.exists_min_image ( fun W => Nat.card { C : α | Relation.ReflTransGen R C r ∧ C ≠ W ∧ ¬Relation.ReflTransGen ( fun a b => R a b ∧ a ≠ W ) C r } ) ⟨ W₀, by aesop ⟩ ; aesop;
  obtain ⟨C, hC⟩ : ∃ C : α, Relation.ReflTransGen R C r ∧ C ≠ W_star ∧ ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star) C r := h_contra W_star hW_star.left hW_star.right.left;
  -- By definition of $block$, we know that $block(C) \subset block(W_star)$.
  have h_block_subset : ∀ D : α, Relation.ReflTransGen R D r → D ≠ C → ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ C) D r → D ≠ W_star ∧ ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star) D r := by
    intro D hD hD_ne_C hD_not_reach_C
    constructor;
    · rintro rfl;
      obtain ⟨l, hl_nodup, hl_chain, hl_head, hl_last, hl_length⟩ : ∃ l : List α, l.Nodup ∧ l.IsChain R ∧ l.head? = some D ∧ l.getLast? = some r ∧ 2 ≤ l.length := by
        apply exists_nodup_chain' hD hW_star.2.1;
      by_cases hC_in_l : C ∈ l;
      · obtain ⟨l', hl'_chain, hl'_nodup, hl'_head, hl'_last, hl'_length, hl'_not_D⟩ : ∃ l' : List α, l'.IsChain R ∧ l'.Nodup ∧ l'.head? = some C ∧ l'.getLast? = some r ∧ l'.length < l.length ∧ D ∉ l' := by
          apply nodup_chain_suffix hl_chain hl_nodup hl_head hl_last hC_in_l;
          · grobner;
          · rintro rfl; simp_all +decide [ Relation.ReflTransGen.refl ] ;
        have := chain_to_restricted_reflTransGen hl'_chain hl'_head hl'_last ( Or.inl hl'_not_D ) ; simp_all +decide ;
      · exact hD_not_reach_C ( chain_to_restricted_reflTransGen hl_chain hl_head hl_last ( Or.inl hC_in_l ) );
    · intro hD_reach_W_star;
      obtain ⟨l, hl_nodup, hl_chain, hl_head, hl_last, hl_length⟩ : ∃ l : List α, l.Nodup ∧ l.IsChain (fun a b => R a b ∧ a ≠ W_star) ∧ l.head? = some D ∧ l.getLast? = some r ∧ 2 ≤ l.length := by
        apply exists_nodup_chain' hD_reach_W_star;
        grind +suggestions;
      by_cases hC_in_l : C ∈ l;
      · obtain ⟨l', hl'_chain, hl'_nodup, hl'_head, hl'_last, hl'_length, hl'_not_in_l⟩ : ∃ l' : List α, l'.IsChain (fun a b => R a b ∧ a ≠ W_star) ∧ l'.Nodup ∧ l'.head? = some C ∧ l'.getLast? = some r ∧ l'.length < l.length ∧ D ∉ l' := by
          apply_rules [ nodup_chain_suffix ];
          grind;
        have hC_reach_r : Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star) C r := by
          exact chain_to_reflTransGen hl'_chain hl'_head hl'_last;
        exact hC.2.2 hC_reach_r;
      · refine' hD_not_reach_C _;
        have h_chain_to_restricted_reflTransGen : Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star ∧ a ≠ C) D r := by
          have h_chain_to_restricted_reflTransGen : ∀ {l : List α}, l.Nodup → l.IsChain (fun a b => R a b ∧ a ≠ W_star) → l.head? = some D → l.getLast? = some r → C ∉ l → Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star ∧ a ≠ C) D r := by
            intros l hl_nodup hl_chain hl_head hl_last hC_in_l;
            convert chain_to_restricted_reflTransGen hl_chain hl_head hl_last _ using 1;
            rotate_left;
            exact C;
            · exact Or.inl hC_in_l;
            · simp +decide only [and_assoc];
          exact h_chain_to_restricted_reflTransGen hl_nodup hl_chain hl_head hl_last hC_in_l;
        exact h_chain_to_restricted_reflTransGen.mono fun a b hab => ⟨ hab.1, hab.2.2 ⟩;
  have h_block_card_lt : Nat.card {D : α | Relation.ReflTransGen R D r ∧ D ≠ C ∧ ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ C) D r} < Nat.card {D : α | Relation.ReflTransGen R D r ∧ D ≠ W_star ∧ ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star) D r} := by
    apply_rules [ Set.ncard_lt_ncard ];
    · simp_all +decide [ Set.ssubset_def, Set.subset_def ];
      exact ⟨ C, hC.1, by tauto, hC.2.2, by tauto ⟩;
    · exact Set.toFinite _;
  grind

end TerminalVertex

/-! ## Weight function helpers

Combinatorial and rational inequalities used in the weight function
argument of Lemma 2.3 (Kierstead-Kostochka). -/

open Finset

/-! ## Rational weight function lower bound -/

lemma weight_sum_lower_bound {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (s : ι → ℕ) (q t c_max : ℕ)
    (hq : 1 ≤ q) (ht : q < t)
    (hF_card : F.card ≥ t - q + c_max)
    (hc_max_le : c_max ≤ q)
    (hc_max_pos : 1 ≤ c_max)
    (hs_pos : ∀ i ∈ F, 1 ≤ s i)
    (hs_le : ∀ i ∈ F, s i ≤ c_max) :
    ∑ i ∈ F, (q : ℚ) / (s i : ℚ) ≥ (t : ℚ) := by
  -- By assumption, $s_i \leq c_max$ for all $i \in F$, so $\frac{q}{s_i} \geq \frac{q}{c_max}$.
  have h_term_bound : ∀ i ∈ F, (q : ℚ) / s i ≥ q / c_max := by
    field_simp;
    exact fun i hi => by rw [ le_div_iff₀ ] <;> norm_cast <;> linarith [ hs_pos i hi, hs_le i hi ] ;
  refine' le_trans _ ( Finset.sum_le_sum h_term_bound );
  simp +zetaDelta at *;
  rw [ mul_div, le_div_iff₀ ] <;> norm_cast;
  nlinarith [ Nat.sub_add_cancel ht.le ]

/-! ## Double counting for the weight function -/

lemma weight_function_contradiction
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β)
    (Solo : α → Finset β)
    (q t s : ℕ)
    (hq : 1 ≤ q) (ht : q < t) (_hs : 1 ≤ s)
    (hA_card_le : A.card ≤ t * s)
    (hB_card : B.card = q * s + 1)
    (hS_sub : ∀ a ∈ A, Solo a ⊆ B)
    (_hS_pos : ∀ a ∈ A, (Solo a).Nonempty → 1 ≤ (Solo a).card)
    (_hS_le : ∀ a ∈ A, (Solo a).card ≤ q)
    (h_lower : ∀ y ∈ B,
      let Sy := A.filter (fun z => y ∈ Solo z)
      ∃ c_max : ℕ, 1 ≤ c_max ∧ c_max ≤ q ∧
        Sy.card ≥ t - q + c_max ∧
        (∀ z ∈ Sy, (Solo z).card ≤ c_max) ∧
        (∀ z ∈ Sy, 1 ≤ (Solo z).card)) :
    False := by
  -- Define the weight function total computed by the "z-side".
  set μ := ∑ a ∈ A, ∑ b ∈ Solo a, (q : ℚ) / ((Solo a).card : ℚ)
  have mu_upper : μ ≤ q * (t * s) := by
    refine' le_trans ( Finset.sum_le_sum _ ) _;
    use fun a => q;
    · intro a ha; by_cases ha' : Solo a = ∅ <;> simp_all +decide ;
      rw [ mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr ( Finset.card_ne_zero_of_mem ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ha' ) ) ) ) ];
    · simp +zetaDelta at *;
      norm_cast ; nlinarith;
  have mu_lower : ∑ y ∈ B, ∑ z ∈ A, (if y ∈ Solo z then (q : ℚ) / ((Solo z).card : ℚ) else 0) ≥ t * (q * s + 1) := by
    have mu_lower : ∀ y ∈ B, ∑ z ∈ A, (if y ∈ Solo z then (q : ℚ) / ((Solo z).card : ℚ) else 0) ≥ t := by
      intro y hy
      obtain ⟨c_max, hc1, hcq, hcard, hle, hpos⟩ := h_lower y hy
      have h_lower_bound : ∑ z ∈ A.filter (fun z => y ∈ Solo z), (q : ℚ) / ((Solo z).card : ℚ) ≥ t := by
        convert weight_sum_lower_bound _ _ q t c_max hq ht hcard hcq hc1 hpos hle;
      simpa [ Finset.sum_ite ] using h_lower_bound;
    exact le_trans ( by simp [ mul_comm, hB_card ] ) ( Finset.sum_le_sum mu_lower );
  -- By Fubini's theorem, we can interchange the order of summation.
  have mu_fubini : ∑ y ∈ B, ∑ z ∈ A, (if y ∈ Solo z then (q : ℚ) / ((Solo z).card : ℚ) else 0) = ∑ z ∈ A, ∑ y ∈ B, (if y ∈ Solo z then (q : ℚ) / ((Solo z).card : ℚ) else 0) := by
    exact Finset.sum_comm;
  -- Simplify the expression inside the sum.
  have mu_simplified : ∑ z ∈ A, ∑ y ∈ B, (if y ∈ Solo z then (q : ℚ) / ((Solo z).card : ℚ) else 0) = ∑ z ∈ A, ∑ y ∈ Solo z, (q : ℚ) / ((Solo z).card : ℚ) := by
    simp +contextual [Finset.inter_eq_right.mpr (hS_sub _ _)];
  nlinarith [ ( by norm_cast : ( 1 : ℚ ) ≤ q ), ( by norm_cast : ( q : ℚ ) < t ), ( by norm_cast : ( 1 : ℚ ) ≤ s ) ]

namespace HajnalSzemeredi

open Finset Function SimpleGraph

/-! ## Section 1: Basic definitions -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Terminal set construction

Constructs the proper terminal set A' from the paper's proof, where A'
consists of accessible color classes that are all "terminal" (meaning
every other accessible class can reach the small class without them). -/

/-
In a finite digraph, if W can't reach target without U,
    and C can't reach target without W, and C ≠ U,
    then C can't reach target without U.
-/
lemma cannot_reach_transitive {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (target U W C : α)
    (hW : ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) W target)
    (hC : ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W) C target)
    (_hCU : C ≠ U) :
    ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) C target := by
  contrapose! hC;
  induction hC;
  · rfl;
  · grind +locals

/-
Mutual dependency is impossible: if W needs U to reach target,
    and U needs W to reach target, we get a contradiction.
-/
lemma mutual_dependency_impossible {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R] (target U W : α)
    (hUW : U ≠ W)
    (hU_acc : Relation.ReflTransGen R U target)
    (hW_acc : Relation.ReflTransGen R W target)
    (hU_needs_W : ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W) U target)
    (hW_needs_U : ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) W target) :
    False := by
  -- Consider a nodup chain from U to target: U = c₀, c₁, ..., cₖ = target.
  obtain ⟨l, hl_nodup, hl_chain, hl_head, hl_last⟩ : ∃ l : List α, l.Nodup ∧ l.IsChain R ∧ l.head? = some U ∧ l.getLast? = some target ∧ 2 ≤ l.length := by
    by_cases h : U = target <;> simp_all +decide [Relation.ReflTransGen.refl];
    exact TerminalVertex.exists_nodup_chain' hU_acc h;
  -- Since U ≠ W, W must be in the list l.
  have hW_in_l : W ∈ l := by
    grind +suggestions;
  obtain ⟨l', hl'_chain, hl'_nodup, hl'_head, hl'_last, hl'_length, hl'_not_U⟩ : ∃ l' : List α, l'.IsChain R ∧ l'.Nodup ∧ l'.head? = some W ∧ l'.getLast? = some target ∧ l'.length < l.length ∧ U ∉ l' := by
    apply TerminalVertex.nodup_chain_suffix hl_chain hl_nodup hl_head hl_last.left hW_in_l hUW.symm;
    contrapose! hW_needs_U; aesop;
  contrapose! hW_needs_U;
  grind +suggestions

/-
Every member of the minimal T_U is terminal.
-/
lemma terminal_set_members_are_terminal {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R] (target : α)
    (acc : Finset α)
    (hacc : ∀ c ∈ acc, Relation.ReflTransGen R c target)
    (U : α) (hU_acc : U ∈ acc)
    (hU_nonterm : ∃ C ∈ acc, C ≠ U ∧
      ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) C target)
    (T_U : Finset α)
    (hT_U_def : T_U = acc.filter (fun c => c ≠ U ∧
      ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) c target))
    (hT_U_min : ∀ V ∈ acc,
      (∃ C ∈ acc, C ≠ V ∧ ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ V) C target) →
      T_U.card ≤ (acc.filter (fun c => c ≠ V ∧
        ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ V) c target)).card)
    (W : α) (hW : W ∈ T_U) :
    ∀ C ∈ acc, C ≠ W →
      Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W) C target := by
  intro C hC hCW; contrapose! hT_U_min; simp_all +decide ;
  refine' ⟨ W, hW.1, ⟨ C, hC, hCW, hT_U_min ⟩, _ ⟩;
  refine' Finset.card_lt_card _;
  constructor;
  · intro c hc; simp_all +decide ;
    refine' ⟨ _, _ ⟩;
    · grind +suggestions;
    · intro h;
      apply cannot_reach_transitive R target U W c;
      · exact hW.2.2;
      · exact hc.2.2;
      · grind;
      · exact h;
  · rw [ Finset.not_subset ] ; use W ; aesop;

/-- The finset of vertices assigned color `c` by function `f`. -/
noncomputable def cClass (f : V → Fin k) (c : Fin k) : Finset V :=
  Finset.univ.filter (fun v => f v = c)

omit [DecidableEq V] in
@[simp]
lemma mem_cClass (f : V → Fin k) (c : Fin k) (v : V) :
    v ∈ cClass f c ↔ f v = c := by simp [cClass]

/-- A coloring is proper if adjacent vertices get different colors. -/
def IsProper (G : SimpleGraph V) (f : V → α) : Prop :=
  ∀ v w : V, G.Adj v w → f v ≠ f w

/-- A k-coloring is equitable if all color classes differ by at most 1. -/
def IsEquitable (f : V → Fin k) : Prop :=
  ∀ c₁ c₂ : Fin k, (cClass f c₁).card ≤ (cClass f c₂).card + 1

/-- A graph has an equitable k-coloring. -/
def HasEquitableColoring (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, IsProper G f ∧ IsEquitable f

lemma hasEquitableColoring_of_iso {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}
    (e : H ≃g G) :
    HasEquitableColoring H k → HasEquitableColoring G k := by
  rintro ⟨f, hf_proper, hf_equitable⟩
  refine ⟨fun v => f (e.symm v), ?_, ?_⟩
  · intro v w hvw h_eq
    exact hf_proper (e.symm v) (e.symm w) (e.symm.map_adj_iff.mpr hvw) h_eq
  · have h_card : ∀ c : Fin k,
        (cClass (fun v : V => f (e.symm v)) c).card = (cClass f c).card := by
      intro c
      refine Finset.card_bij
        (s := cClass (fun v : V => f (e.symm v)) c) (t := cClass f c)
        (fun v _ => e.symm v) ?_ ?_ ?_
      · intro v hv
        simpa [cClass] using hv
      · intro a _ b _ h
        exact e.symm.injective h
      · intro w hw
        refine ⟨e w, ?_, by simp⟩
        simpa [cClass] using hw
    intro c₁ c₂
    rw [h_card c₁, h_card c₂]
    exact hf_equitable c₁ c₂

/-- Vertex v is movable to color c: v is not colored c and has no neighbor of
    color c. -/
def IsMovable (G : SimpleGraph V) (f : V → Fin k) (v : V) (c : Fin k) : Prop :=
  f v ≠ c ∧ ∀ w : V, f w = c → ¬G.Adj v w

/-- Recolor vertex v with color c. -/
def recolor (f : V → Fin k) (v : V) (c : Fin k) : V → Fin k :=
  Function.update f v c

/-! ## Section 2: Basic lemmas about color classes -/

omit [DecidableEq V] in
lemma cClass_card_sum (f : V → Fin k) :
    ∑ c : Fin k, (cClass f c).card = Fintype.card V := by
  have h_insert : ∑ c : Fin k, Finset.card (Finset.filter (fun v => f v = c) Finset.univ) = Finset.card (Finset.univ : Finset V) := by
    simp +decide only [card_filter]
    rw [Finset.sum_comm]; aesop
  exact h_insert

omit [Fintype V] in
lemma recolor_preserves_proper {G : SimpleGraph V} [DecidableRel G.Adj]
    {f : V → Fin k} (hf : IsProper G f) {v : V} {c : Fin k}
    (hm : IsMovable G f v c) :
    IsProper G (recolor f v c) := by
  intro w x; by_cases hvw : w = v <;> by_cases hvx : x = v <;> simp_all +decide [recolor]
  · intro hx; have := hm.2 x; simp_all +decide; aesop
  · rintro h; have := hm.2 w; simp_all +decide [SimpleGraph.adj_comm]; aesop
  · exact hf w x

/-! ## Section 2b: Effect of recoloring on class sizes -/

lemma cClass_recolor_old {f : V → Fin k} {v : V} {c : Fin k}
    (hvc : f v ≠ c) :
    cClass (recolor f v c) (f v) = (cClass f (f v)).erase v := by
  ext w; by_cases hw : w = v <;> simp +decide [ *, recolor ] ;
  exact Ne.symm hvc

lemma cClass_recolor_new {f : V → Fin k} {v : V} {c : Fin k}
    (hvc : f v ≠ c) :
    cClass (recolor f v c) c = insert v (cClass f c) := by
  ext w; by_cases hw : w = v <;> simp +decide [ *, recolor ] ;

lemma cClass_recolor_other {f : V → Fin k} {v : V} {c d : Fin k}
    (hd1 : d ≠ f v) (hd2 : d ≠ c) :
    cClass (recolor f v c) d = cClass f d := by
  ext w; by_cases hw : w = v <;> simp +decide [ *, recolor ] ;
  aesop

lemma cClass_recolor_old_card {f : V → Fin k} {v : V} {c : Fin k}
    (hvc : f v ≠ c) :
    (cClass (recolor f v c) (f v)).card = (cClass f (f v)).card - 1 := by
  rw [ cClass_recolor_old hvc, Finset.card_erase_of_mem ] ; aesop

lemma cClass_recolor_new_card {f : V → Fin k} {v : V} {c : Fin k}
    (hvc : f v ≠ c) :
    (cClass (recolor f v c) c).card = (cClass f c).card + 1 := by
  rw [ cClass_recolor_new hvc, Finset.card_insert_of_notMem ] ; aesop

lemma cClass_recolor_other_card {f : V → Fin k} {v : V} {c d : Fin k}
    (hd1 : d ≠ f v) (hd2 : d ≠ c) :
    (cClass (recolor f v c) d).card = (cClass f d).card := by
  rw [ cClass_recolor_other hd1 hd2 ]

/-! ## Section 3: Graph edge operations -/

instance deleteEdges_decidable (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set (Sym2 V)) [DecidablePred (· ∈ s)] :
    DecidableRel (G.deleteEdges s).Adj := by
  intro v w; simp only [deleteEdges_adj]; infer_instance

omit [DecidableEq V] in
lemma maxDegree_deleteEdges_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set (Sym2 V)) [DecidablePred (· ∈ s)] :
    (G.deleteEdges s).maxDegree ≤ G.maxDegree := by
  apply_rules [SimpleGraph.maxDegree_le_of_forall_degree_le]
  intro v
  have h_deg_le : (G.deleteEdges s).degree v ≤ G.degree v := by
    exact Finset.card_mono fun x hx => by aesop
  linarith [h_deg_le, G.degree_le_maxDegree v]

/-! ## Section 4: Base case -/

lemma equitable_coloring_of_edgeless (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hG : G.edgeSet = ∅) :
    HasEquitableColoring G (r + 1) := by
  simp +decide [Set.ext_iff] at hG ⊢
  have h_eq : ∃ f : V → Fin (r + 1), ∀ c₁ c₂ : Fin (r + 1), ((cClass f c₁).card ≤ (cClass f c₂).card + 1) := by
    have h_card : ∀ n : ℕ, ∃ f : Fin n → Fin (r + 1), ∀ c₁ c₂ : Fin (r + 1), ((Finset.filter (fun v => f v = c₁) (Finset.univ)).card ≤ (Finset.filter (fun v => f v = c₂) (Finset.univ)).card + 1) := by
      intro n
      use fun i => ⟨i.val % (r + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
      intro c₁ c₂
      simp [Finset.card] at *
      have h_card_classes : ∀ c : Fin (r + 1), (Finset.filter (fun v : Fin n => v.val % (r + 1) = c.val) Finset.univ).card = n / (r + 1) + if c.val < n % (r + 1) then 1 else 0 := by
        intro c
        have h_card_classes : (Finset.filter (fun v : Fin n => v.val % (r + 1) = c.val) Finset.univ).card = Finset.card (Finset.filter (fun v : ℕ => v % (r + 1) = c.val) (Finset.range n)) := by
          refine' Finset.card_bij (fun x hx => x) _ _ _ <;> simp +decide [Fin.ext_iff]
          exact fun b hb hb' => ⟨⟨b, hb⟩, hb', rfl⟩
        simp [h_card_classes] at *
        have h_set_eq : {v ∈ Finset.range n | v % (r + 1) = c.val} = Finset.image (fun k => k * (r + 1) + c.val) (Finset.range (n / (r + 1) + if c.val < n % (r + 1) then 1 else 0)) := by
          ext v; simp [Finset.mem_image] at *
          constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> simp_all +decide
          · exact ⟨v / (r + 1), by split_ifs <;> nlinarith [Nat.mod_add_div v (r + 1), Nat.mod_lt v (Nat.succ_pos r), Nat.mod_add_div n (r + 1), Nat.mod_lt n (Nat.succ_pos r)], by linarith [Nat.mod_add_div v (r + 1)]⟩
          · split_ifs at h₂ <;> exact ⟨by nlinarith [Nat.div_mul_le_self n (r + 1), Nat.mod_add_div n (r + 1), Fin.is_lt c], by simp +decide [← h₂.2, Nat.add_mod, Nat.mod_eq_of_lt (Fin.is_lt c)]⟩
        generalize_proofs at *
        rw [h_set_eq, Finset.card_image_of_injective] <;> simp +decide [Function.Injective, *]
      simp_all +decide [Fin.ext_iff, Finset.card]
      split_ifs <;> simp +arith +decide [*] at *
    obtain ⟨f, hf⟩ := h_card (Fintype.card V)
    obtain ⟨e, he⟩ : ∃ e : V ≃ Fin (Fintype.card V), True := ⟨Fintype.equivFin V, trivial⟩
    use fun v => f (e v)
    intro c₁ c₂; convert hf c₁ c₂ using 1; simp +decide [cClass]
    · rw [Finset.card_filter, Finset.card_filter]; conv_rhs => rw [← Equiv.sum_comp e]
    · rw [show cClass (fun v => f (e v)) c₂ = Finset.image (fun v => e.symm v) (Finset.filter (fun v => f v = c₂) Finset.univ) from ?_, Finset.card_image_of_injective _ e.symm.injective]; aesop
  refine ⟨h_eq.choose, ?_, h_eq.choose_spec⟩
  intro v w hvw
  have h_edge : s(v, w) ∈ G.edgeSet := by
    simpa [SimpleGraph.mem_edgeSet] using hvw
  simpa [hG] using h_edge

/-! ## Section 5: Auxiliary digraph and accessibility -/

/-- The auxiliary digraph: directed edge from color i to color j iff
    some vertex of color i has no neighbor of color j. -/
def AuxAdj (G : SimpleGraph V) (f : V → Fin k) (i j : Fin k) : Prop :=
  ∃ v, f v = i ∧ ∀ w, f w = j → ¬G.Adj v w

/-- Color j is accessible from i_minus if there's a directed path
    from j to i_minus in the auxiliary digraph. -/
def IsAccessible (G : SimpleGraph V) (f : V → Fin k)
    (i_minus j : Fin k) : Prop :=
  Relation.ReflTransGen (AuxAdj G f) j i_minus

/-! ## Section 6: Nearly equitable colorings -/

/-- A nearly equitable k-coloring on k*s vertices:
    all classes have size s, except the small class (s-1) and large class (s+1). -/
structure NearlyEquitable (G : SimpleGraph V) (k s : ℕ) where
  f : V → Fin k
  proper : IsProper G f
  small : Fin k
  large : Fin k
  ne_small_large : small ≠ large
  card_small : (cClass f small).card = s - 1
  card_large : (cClass f large).card = s + 1
  card_other : ∀ c, c ≠ small → c ≠ large → (cClass f c).card = s
  card_total : Fintype.card V = k * s

/-! ## Section 7: Lemma 2.1 — One-step and general cases -/

lemma one_step_equitable
    (G : SimpleGraph V) [DecidableRel G.Adj] (k s : ℕ) (hs : 1 ≤ s)
    (ne : NearlyEquitable G k s)
    (hdirect : AuxAdj G ne.f ne.large ne.small) :
    HasEquitableColoring G k := by
  obtain ⟨ v, hv ⟩ := hdirect;
  refine' ⟨ recolor ne.f v ne.small, _, _ ⟩ <;> simp_all +decide [ IsProper, IsEquitable ];
  · intro u w huw; by_cases hu : u = v <;> by_cases hw : w = v <;> simp_all +decide [ recolor, SimpleGraph.adj_comm ] ;
    · grind +splitIndPred;
    · contrapose! hv; aesop;
    · exact ne.proper u w huw;
  · -- By definition of recoloring, we know that the sizes of the color classes change as follows:
    have h_rec : ∀ c, (cClass (recolor ne.f v ne.small) c).card = if c = ne.large then (cClass ne.f ne.large).card - 1 else if c = ne.small then (cClass ne.f ne.small).card + 1 else (cClass ne.f c).card := by
      intro c; split_ifs <;> simp_all +decide [cClass_recolor_other_card] ;
      · convert cClass_recolor_old_card _ ; aesop;
        · rw [ hv.1 ];
        · infer_instance;
        · exact hv.1.symm ▸ ne.ne_small_large.symm;
      · rw [ cClass_recolor_new_card ] ; aesop;
    intro c₁ c₂; by_cases hc₁ : c₁ = ne.large <;> by_cases hc₂ : c₂ = ne.large <;> simp +decide [ * ] ;
    · split_ifs <;> simp_all +decide [NearlyEquitable.card_large, NearlyEquitable.card_small, NearlyEquitable.card_other];
    · split_ifs <;> simp_all +decide [ ne.card_small, ne.card_large, ne.card_other ];
    · by_cases hc₃ : c₁ = ne.small <;> by_cases hc₄ : c₂ = ne.small <;> simp_all +decide [ ne.card_small, ne.card_large, ne.card_other ]

omit [Fintype V] in
lemma auxAdj_preserved_by_recolor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {f : V → Fin k} {v : V} {c : Fin k}
    {i j : Fin k} (hvc : f v ≠ c)
    (hij : AuxAdj G f i j)
    (hi_ne : i ≠ f v) (hj_ne : j ≠ c) :
    AuxAdj G (recolor f v c) i j := by
  obtain ⟨ u, hu ⟩ := hij;
  refine' ⟨ u, _, _ ⟩ <;> simp_all +decide [ recolor ];
  · rw [ Function.update_apply ] ; aesop;
  · intro w hw; by_cases hw' : w = v <;> simp_all +decide [ update_apply ] ;

/-! ### Simple path extraction from ReflTransGen -/

lemma exists_nodup_chain {α : Type*} [Fintype α] [DecidableEq α]
    {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) (hab : a ≠ b) :
    ∃ l : List α, l.Nodup ∧ l.IsChain R ∧ l.head? = some a ∧
    l.getLast? = some b ∧ 2 ≤ l.length := by
  -- Let's take the shortest path from `a` to `b` in the reflexive transitive closure.
  obtain ⟨l, hl⟩ : ∃ l : List α, l.head? = some a ∧ l.getLast? = some b ∧ List.IsChain R l ∧ ¬∃ l' : List α, l'.head? = some a ∧ l'.getLast? = some b ∧ List.IsChain R l' ∧ l'.length < l.length := by
    have h_shortest : ∃ l : List α, l.head? = some a ∧ l.getLast? = some b ∧ List.IsChain R l := by
      have h_path : ∀ {a b : α}, Relation.ReflTransGen R a b → ∃ l : List α, l.head? = some a ∧ l.getLast? = some b ∧ List.IsChain R l := by
        intro a b h
        induction' h with a b h ih;
        · exact ⟨ [ a ], rfl, rfl, List.isChain_singleton _ ⟩;
        · obtain ⟨ l, hl₁, hl₂, hl₃ ⟩ := ‹_›; use l ++ [ b ] ; simp_all +decide ;
          exact List.isChain_append.mpr ⟨ hl₃, by aesop ⟩;
      exact h_path h;
    have h_well_founded : WellFounded fun l l' : List α => l.length < l'.length := by
      refine' ⟨ fun l => _ ⟩;
      induction' n : l.length using Nat.strong_induction_on with n ih generalizing l;
      exact ⟨ _, fun l' hl' => ih _ ( by linarith ) _ rfl ⟩;
    have := h_well_founded.has_min { l : List α | l.head? = some a ∧ l.getLast? = some b ∧ List.IsChain R l } ⟨ _, h_shortest.choose_spec ⟩ ; aesop;
  refine' ⟨ l, _, hl.2.2.1, hl.1, hl.2.1, _ ⟩;
  · -- If the list had duplicates, we could remove the cycle between the duplicates and create a shorter path, contradicting the assumption that l is the shortest.
    by_contra h_dup
    obtain ⟨i, j, hij, h_dup⟩ : ∃ i j, i < j ∧ l.get i = l.get j := by
      rw [ List.nodup_iff_injective_get ] at h_dup;
      obtain ⟨ i, j, hij ⟩ := Function.not_injective_iff.mp h_dup;
      grind;
    -- Let's remove the cycle between the duplicates and create a shorter path.
    set l' : List α := l.take i.val ++ l.drop j.val;
    refine' hl.2.2.2 ⟨ l', _, _, _, _ ⟩;
    · rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> simp_all +decide;
      · cases l <;> aesop;
      · cases l <;> aesop;
    · grind +suggestions;
    · refine' List.isChain_append.mpr ⟨ _, _, _ ⟩;
      · have := hl.2.2.1;
        exact List.IsChain.take this _;
      · have := hl.2.2.1;
        exact List.IsChain.drop this _;
      · have := List.isChain_iff_getElem.mp hl.2.2.1;
        rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> simp_all +decide [ List.getLast?_take, List.head?_drop ];
        convert this i (by omega) using 1;
        · rw [ List.getElem?_eq_getElem ] ; aesop;
        · exact h_dup.symm;
    · grind;
  · rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide;
    grind

omit [Fintype V] in
lemma chain_preserved_after_recolor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {f : V → Fin k} {v : V} {c : Fin k}
    (hvc : f v ≠ c)
    {path : List (Fin k)}
    (hchain : path.IsChain (AuxAdj G f))
    (hi_avoid : ∀ x ∈ path, x ≠ f v)
    (hj_avoid : ∀ x ∈ path.tail, x ≠ c) :
    path.IsChain (AuxAdj G (recolor f v c)) := by
      induction' path with x path ih;
      · exact List.isChain_nil;
      · rcases path <;> simp_all +decide;
        exact auxAdj_preserved_by_recolor G hvc hchain.1 hi_avoid.1 hj_avoid.1

lemma step_with_chain_preservation
    (G : SimpleGraph V) [DecidableRel G.Adj] (k s : ℕ) (_hs : 1 ≤ s)
    (ne : NearlyEquitable G k s)
    (mid : Fin k) (hmid_ne_small : mid ≠ ne.small)
    (hmid_ne_large : mid ≠ ne.large)
    (hedge : AuxAdj G ne.f ne.large mid)
    {tail : List (Fin k)}
    (hchain_tail : (mid :: tail).IsChain (AuxAdj G ne.f))
    (hnodup_full : (ne.large :: mid :: tail).Nodup)
    (hlast : (mid :: tail).getLast? = some ne.small) :
    ∃ ne' : NearlyEquitable G k s,
      ne'.small = ne.small ∧ ne'.large = mid ∧
      (mid :: tail).Nodup ∧
      (mid :: tail).IsChain (AuxAdj G ne'.f) ∧
      (mid :: tail).head? = some ne'.large ∧
      (mid :: tail).getLast? = some ne'.small := by
  obtain ⟨ v, hv1, hv2 ⟩ := hedge; use ⟨ recolor ne.f v mid, ?_, ne.small, mid, ?_, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide ;
  any_goals tauto;
  any_goals exact ne.card_total;
  · apply chain_preserved_after_recolor;
    · grind;
    · exact hchain_tail;
    · grind +ring;
    · grind +ring;
  · exact recolor_preserves_proper ne.proper ⟨ by aesop, hv2 ⟩;
  · rw [ ← ne.card_small, cClass_recolor_other_card ] <;> simp_all +decide;
    · grind;
    · tauto;
  · convert cClass_recolor_new_card ( show ne.f v ≠ mid from by aesop ) using 1;
    rw [ ne.card_other mid ( by tauto ) ( by tauto ) ];
  · intro c hc1 hc2; by_cases hc3 : c = ne.large <;> simp_all +decide [ cClass_recolor_other_card ] ;
    · convert cClass_recolor_old_card ( show ne.f v ≠ mid from by aesop ) using 1;
      · rw [ hv1 ];
      · have := ne.card_large; aesop;
    · exact ne.card_other c hc1 hc3

lemma equitable_from_nodup_chain
    (G : SimpleGraph V) [DecidableRel G.Adj] (k s : ℕ)
    (ne : NearlyEquitable G k s)
    (path : List (Fin k))
    (hnodup : path.Nodup)
    (hchain : path.IsChain (AuxAdj G ne.f))
    (hhead : path.head? = some ne.large)
    (hlast : path.getLast? = some ne.small) :
    HasEquitableColoring G k := by
      by_cases hs : 1 ≤ s;
      · induction' n : path.length using Nat.strong_induction_on with n ih generalizing path ne;
        by_cases hpath : path.length ≤ 2;
        · rcases path with ( _ | ⟨ x, _ | ⟨ y, _ | path ⟩ ⟩ ) <;> simp_all +decide;
          · exact absurd hlast ne.ne_small_large.symm;
          · exact one_step_equitable G k s hs ne hchain;
          · linarith;
        · obtain ⟨mid, tail, htail⟩ : ∃ mid tail, path = ne.large :: mid :: tail := by
            rcases path with ( _ | ⟨ x, _ | ⟨ y, path ⟩ ⟩ ) <;> simp_all +decide;
            linarith;
          by_cases hmid : mid = ne.small;
          · simp_all +decide [ List.isChain_cons_cons ];
            exact one_step_equitable G k s hs ne hchain.1;
          · obtain ⟨ne', hne'⟩ : ∃ ne' : NearlyEquitable G k s, ne'.small = ne.small ∧ ne'.large = mid ∧ (mid :: tail).Nodup ∧ (mid :: tail).IsChain (AuxAdj G ne'.f) ∧ (mid :: tail).head? = some ne'.large ∧ (mid :: tail).getLast? = some ne'.small := by
              apply step_with_chain_preservation;
              all_goals simp_all +decide [ List.isChain_cons_cons ];
              tauto;
            grind;
      · have := ne.card_small; have := ne.card_large; simp_all +decide ;
        have := ne.card_total; simp_all +decide [ cClass ] ;
        rw [ Fintype.card_eq_zero_iff ] at this ; aesop

lemma accessible_large_gives_equitable
    (G : SimpleGraph V) [DecidableRel G.Adj] (k s : ℕ)
    (ne : NearlyEquitable G k s)
    (hacc : IsAccessible G ne.f ne.small ne.large) :
    HasEquitableColoring G k := by
  -- Use the hypothesis `hacc` to obtain a nodup chain from the large class to the small class in the auxiliary digraph.
  obtain ⟨l, hl⟩ : ∃ l : List (Fin k), l.Nodup ∧ l.IsChain (AuxAdj G ne.f) ∧ l.head? = some ne.large ∧ l.getLast? = some ne.small ∧ 2 ≤ l.length := by
    apply exists_nodup_chain; assumption; exact ne.ne_small_large.symm;
  -- Apply Lemma 2.1 to the chain l.
  apply equitable_from_nodup_chain G k s ne l hl.left hl.right.left hl.right.right.left hl.right.right.right.left

/-! ## Section 8: Creating a nearly equitable coloring -/

omit [DecidableEq V] in
lemma equitable_all_same_size {k s : ℕ}
    {f : V → Fin k} (hf : IsEquitable f)
    (htotal : Fintype.card V = k * s) :
    ∀ c : Fin k, (cClass f c).card = s := by
  intro c
  have h_sum : ∑ c, (cClass f c).card = k * s := by
    rw [ ← htotal, cClass_card_sum ];
  by_contra h_contra;
  -- Since there's a class with size less than s, let's denote this class as d. Then (cClass f d).card < s.
  obtain ⟨d, hd⟩ : ∃ d, (cClass f d).card < s := by
    by_cases h_all_ge_s : ∀ c, (cClass f c).card ≥ s;
    · exact absurd ( h_sum ▸ Finset.sum_lt_sum ( fun a _ => h_all_ge_s a ) ⟨ c, Finset.mem_univ c, lt_of_le_of_ne ( h_all_ge_s c ) ( Ne.symm h_contra ) ⟩ ) ( by simp +decide );
    · aesop;
  have h_all_le : ∀ c, (cClass f c).card ≤ s := by
    exact fun c => by linarith [ hf c d, hf d c ] ;
  exact absurd h_sum ( ne_of_lt ( lt_of_lt_of_le ( Finset.sum_lt_sum ( fun x _ => h_all_le x ) ⟨ d, Finset.mem_univ d, hd ⟩ ) ( by simp +decide ) ) )

omit [DecidableEq V] in
lemma exists_movable_class
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hd : G.maxDegree ≤ r)
    (f : V → Fin (r + 1)) (x : V)
    (hx_neighbor : ∃ w, f w = f x ∧ G.Adj x w) :
    ∃ c : Fin (r + 1), c ≠ f x ∧ ∀ w, f w = c → ¬G.Adj x w := by
  -- The set of colors used by neighbors of x is S = {f w | G.Adj x w}. Since |neighbors of x| = degree(x) ≤ maxDegree ≤ r, |S| ≤ r.
  set S := (G.neighborFinset x).image f with hS_def
  have hS_card : S.card ≤ r := by
    exact le_trans ( Finset.card_image_le ) ( by simpa using G.degree_le_maxDegree x |> le_trans <| hd );
  -- Since S contains f x and has size ≤ r, the complement Finset.univ \ S has size ≥ r+1 - r = 1.
  have h_compl_card : (Finset.univ \ S).card ≥ 1 := by
    simp +decide [ Finset.card_sdiff, * ];
    exact Nat.sub_pos_of_lt ( lt_of_le_of_lt hS_card ( Nat.lt_succ_self _ ) );
  obtain ⟨ c, hc ⟩ := Finset.card_pos.mp h_compl_card; use c; aesop;

/-! ## Section 9: Induction step -/

set_option maxHeartbeats 800000 in
/-- Variant of `induction_step` that takes a callback for converting
    nearly equitable colorings, rather than calling `nearly_equitable_to_equitable`
    directly. This allows the master theorem to provide the primary IH. -/
lemma induction_step_with_callback
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hs_card : (r + 1) ∣ Fintype.card V)
    (hd : G.maxDegree ≤ r)
    (e : Sym2 V) (he : e ∈ G.edgeSet)
    (hIH : HasEquitableColoring (G.deleteEdges {e}) (r + 1))
    (h_ne : ∀ (s : ℕ), Fintype.card V = (r + 1) * s → 0 < s →
      NearlyEquitable G (r + 1) s → HasEquitableColoring G (r + 1)) :
    HasEquitableColoring G (r + 1) := by
  cases' hIH with f hf
  rcases e with ⟨x, y⟩
  by_cases hxy : f x = f y
  · obtain ⟨c, hc_ne, hc_movable⟩ : ∃ c : Fin (r + 1), c ≠ f x ∧ ∀ w, f w = c → ¬G.Adj x w := by
      apply exists_movable_class G hd f x ⟨y, by aesop⟩
    set f' : V → Fin (r + 1) := recolor f x c
    have hf'_proper : IsProper G f' := by
      intro u v huv; by_cases hu : u = x <;> by_cases hv : v = x <;> simp_all +decide
      · simp +zetaDelta at *; unfold recolor; aesop
      · simp +zetaDelta at *; simp +decide [*, recolor]
        exact fun h => hc_movable u h (by simpa [SimpleGraph.adj_comm] using huv)
      · simp +zetaDelta at *; unfold recolor; aesop
    obtain ⟨s, hs⟩ : ∃ s : ℕ, Fintype.card V = (r + 1) * s := hs_card
    have h_card_f' : ∀ c' : Fin (r + 1), (cClass f' c').card =
        if c' = f x then s - 1 else if c' = c then s + 1 else s := by
      have h1 : ∀ c' : Fin (r + 1), (cClass f' c').card =
          if c' = f x then (cClass f (f x)).card - 1
          else if c' = c then (cClass f c).card + 1
          else (cClass f c').card := by
        intro c'
        by_cases hc'_eq_fx : c' = f x
        · rw [hc'_eq_fx, cClass_recolor_old_card]; aesop; exact Ne.symm hc_ne
        · by_cases hc'_eq_c : c' = c <;>
            simp_all +decide
          · rw [cClass_recolor_new_card]; aesop
          · convert cClass_recolor_other_card (show c' ≠ f x from by aesop) (show c' ≠ c from by aesop) using 1
      have h_card_f : ∀ c' : Fin (r + 1), (cClass f c').card = s := by
        apply equitable_all_same_size hf.2 hs
      aesop
    refine' h_ne s hs (Nat.pos_of_ne_zero _) ⟨f', hf'_proper, f x, c, _, _, _, _, _⟩ <;>
      simp_all +decide
    · rintro rfl; simp_all +decide [Fintype.card_eq_zero_iff]; exact hs.elim x
    · exact Ne.symm hc_ne
  · refine' ⟨f, _, hf.2⟩
    intro v w hvw; by_cases h : v = x ∧ w = y ∨ v = y ∧ w = x <;>
      simp_all +decide [SimpleGraph.deleteEdges]
    · grind +ring
    · exact hf.1 v w (by aesop)

lemma edgeFinset_card_deleteEdges_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (G.deleteEdges {↑e}).edgeFinset.card < G.edgeFinset.card := by
  refine' Finset.card_lt_card _;
  simp +decide [SimpleGraph.deleteEdges];
  rw [ lt_iff_le_and_ne ] ; aesop

/-! ## Non-accessible case helpers -/

omit [DecidableEq V] in
lemma non_acc_has_acc_neighbor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {f : V → Fin k} {i_minus : Fin k}
    {y : V} {c : Fin k}
    (hacc_c : IsAccessible G f i_minus c)
    (hnacc_y : ¬IsAccessible G f i_minus (f y)) :
    ∃ w, f w = c ∧ G.Adj y w := by
  by_contra h_contra; push Not at h_contra; (
  -- By contraposition, if y has no neighbor of color c, then y's color is accessible to i_minus by the definition of AuxAdj.
  have h_aux_adj_y : AuxAdj G f (f y) c := by
    exact ⟨ y, rfl, h_contra ⟩;
  exact hnacc_y ( Relation.ReflTransGen.head h_aux_adj_y hacc_c ));

/-! ### Helper lemmas for Lemma 2.3 -/

/-- There exists a second accessible color besides ne.small. -/
lemma acc_has_second_color
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    ∃ W : Fin (r + 1), W ≠ ne.small ∧ W ≠ ne.large ∧ IsAccessible G ne.f ne.small W := by
  by_contra h_contra;
  -- If there are no vertices of color ne.small that are not adjacent to any vertex of color ne.large, then every vertex of color ne.small is adjacent to at least one vertex of color ne.large.
  have h_adj_small_large : ∀ y : V, ne.f y ≠ ne.small → ∃ w : V, ne.f w = ne.small ∧ G.Adj y w := by
    intro y hy_ne_small
    generalize_proofs at *; (
    apply non_acc_has_acc_neighbor G (Relation.ReflTransGen.refl) (by
    by_cases hy_large : ne.f y = ne.large <;> simp_all +decide [ IsAccessible ]))
  generalize_proofs at *; (
  have h_edges : (Finset.card (Finset.filter (fun v => ne.f v ≠ ne.small) Finset.univ)) ≤ r * (Finset.card (Finset.filter (fun v => ne.f v = ne.small) Finset.univ)) := by
    have h_edges : (Finset.card (Finset.filter (fun v => ne.f v ≠ ne.small) Finset.univ)) ≤ Finset.sum (Finset.filter (fun v => ne.f v = ne.small) Finset.univ) (fun v => Finset.card (Finset.filter (fun w => ne.f w ≠ ne.small ∧ G.Adj v w) Finset.univ)) := by
      have h_edges : Finset.filter (fun v => ne.f v ≠ ne.small) Finset.univ ⊆ Finset.biUnion (Finset.filter (fun v => ne.f v = ne.small) Finset.univ) (fun v => Finset.filter (fun w => ne.f w ≠ ne.small ∧ G.Adj v w) Finset.univ) := by
        intro v hv; specialize h_adj_small_large v; simp_all +decide ;
        exact ⟨ h_adj_small_large.choose, h_adj_small_large.choose_spec.1, h_adj_small_large.choose_spec.2.symm ⟩
      generalize_proofs at *; (
      exact le_trans ( Finset.card_le_card h_edges ) ( Finset.card_biUnion_le ) |> le_trans <| by simp +decide [ Finset.sum_filter ] ;)
    generalize_proofs at *; (
    have h_edges : ∀ v ∈ Finset.filter (fun v => ne.f v = ne.small) Finset.univ, Finset.card (Finset.filter (fun w => ne.f w ≠ ne.small ∧ G.Adj v w) Finset.univ) ≤ r := by
      intro v hv
      have h_deg_v : Finset.card (Finset.filter (fun w => G.Adj v w) Finset.univ) ≤ r := by
        convert (SimpleGraph.degree_le_maxDegree G v).trans hd using 1
        rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
      generalize_proofs at *; (
      exact le_trans ( Finset.card_le_card fun w hw => by aesop ) h_deg_v)
    generalize_proofs at *; (
    exact le_trans ‹_› ( by simpa [ mul_comm ] using Finset.sum_le_sum h_edges )))
  generalize_proofs at *; (
  have h_card_small : (Finset.card (Finset.filter (fun v => ne.f v = ne.small) Finset.univ)) = s - 1 := by
    exact ne.card_small ▸ rfl
  generalize_proofs at *; (
  simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
  nlinarith only [ h_edges, hs0, Nat.sub_add_cancel hs0 ])))

/-- In a finite directed graph, if there exists a vertex W₀ ≠ r that can reach r,
    then there exists a "terminal" vertex W ≠ r that can reach r, such that every
    other vertex that can reach r can also reach r without passing through W. -/
lemma exists_terminal_vertex {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (r : α)
    (W₀ : α) (hW₀ : Relation.ReflTransGen R W₀ r) (hW₀_ne : W₀ ≠ r) :
    ∃ W : α, Relation.ReflTransGen R W r ∧ W ≠ r ∧
      ∀ C : α, Relation.ReflTransGen R C r → C ≠ W →
        Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W) C r :=
  TerminalVertex.exists_terminal_vertex R r W₀ hW₀ hW₀_ne

omit [Fintype V] [DecidableEq V] in
/-- Specialization of exists_terminal_vertex to the auxiliary digraph. -/
lemma exists_terminal_color
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (f : V → Fin k) (small : Fin k)
    (W₀ : Fin k) (hW₀ : IsAccessible G f small W₀) (hW₀_ne : W₀ ≠ small) :
    ∃ W : Fin k, IsAccessible G f small W ∧ W ≠ small ∧
      ∀ C : Fin k, IsAccessible G f small C → C ≠ W →
        Relation.ReflTransGen (fun c d => AuxAdj G f c d ∧ c ≠ W) C small :=
  exists_terminal_vertex (AuxAdj G f) small W₀ hW₀ hW₀_ne

set_option maxHeartbeats 1600000 in
/-- Under negation of the good solo vertex conclusion (all solo vertices are "bad"),
    derive False. "Bad" means: every solo z in accessible W is not movable to any
    other accessible class AND all special neighbors of z form a clique. -/
lemma solo_weight_contradiction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (h_all_bad : ∀ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W → W ≠ ne.small → W ≠ ne.large →
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      -- z has a neighbor in every accessible class ≠ W (not movable)
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      -- all special neighbors of z are pairwise adjacent
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂)) :
    False := by
  -- Step 1: Get an accessible color W₀ ≠ small, ≠ large
  obtain ⟨W₀, hW₀_ne_small, hW₀_ne_large, hW₀_acc⟩ :=
    acc_has_second_color G r s hs hd hs0 ne hacc
  -- Step 2: Define key finsets
  -- B_verts = non-accessible vertices
  let B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
  let W₀_class := cClass ne.f W₀
  -- m+1 = number of accessible colors, q = r - m
  let acc_colors := Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)
  -- Step 3: Key cardinality facts
  have hW₀_card : W₀_class.card = s := ne.card_other W₀ hW₀_ne_small hW₀_ne_large
  have hW₀_mem : W₀ ∈ acc_colors := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW₀_acc⟩
  have hsmall_mem : ne.small ∈ acc_colors := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  have hlarge_nmem : ne.large ∉ acc_colors := by simp [acc_colors, Finset.mem_filter]; exact hacc
  have hacc_ge_2 : 2 ≤ acc_colors.card := by
    have : {ne.small, W₀} ⊆ acc_colors := by
      simp [Finset.subset_iff]; exact ⟨hsmall_mem, hW₀_mem⟩
    exact le_trans (by simp [Finset.card_pair hW₀_ne_small.symm]) (Finset.card_le_card this)
  -- Every y ∈ B has ≥ 1 neighbor in each accessible class (by non_acc_has_acc_neighbor)
  have hB_has_nbr : ∀ y : V, ¬IsAccessible G ne.f ne.small (ne.f y) →
      ∀ c, IsAccessible G ne.f ne.small c → ∃ w, ne.f w = c ∧ G.Adj y w := by
    intro y hy c hc; exact non_acc_has_acc_neighbor G hc hy
  -- Step 4: For solo z in W₀, z has neighbor in every accessible class ≠ W₀
  -- Hence z has ≥ acc_colors.card - 1 accessible neighbors, so ≤ r - (acc_colors.card - 1) non-acc neighbors
  -- This is the key degree bound from h_all_bad
  have h_solo_deg_bound : ∀ z : V, ne.f z = W₀ →
      (∃ y₁ : V, ¬IsAccessible G ne.f ne.small (ne.f y₁) ∧
        G.Adj y₁ z ∧ (∀ w, ne.f w = W₀ → w ≠ z → ¬G.Adj y₁ w)) →
      (Finset.univ.filter (fun w => G.Adj z w ∧ ¬IsAccessible G ne.f ne.small (ne.f w))).card
        ≤ r + 1 - acc_colors.card := by
    intro z hz ⟨y₁, hy₁_nacc, hy₁_adj, hy₁_uniq⟩
    have h_bad := h_all_bad W₀ z y₁ hW₀_acc hW₀_ne_small hW₀_ne_large hz hy₁_nacc hy₁_adj hy₁_uniq
    -- z has a neighbor in every accessible class ≠ W₀
    -- So z has ≥ acc_colors.card - 1 neighbors with accessible colors
    -- Total degree ≤ r, so non-accessible neighbors ≤ r - (acc_colors.card - 1) = r + 1 - acc_colors.card
    have h_deg_bound : Finset.card (Finset.filter (fun w => G.Adj z w ∧ IsAccessible G ne.f ne.small (ne.f w)) (Finset.univ : Finset V)) ≥ acc_colors.card - 1 := by
      have hN_acc_ge : Finset.card (acc_colors.erase W₀) ≤ Finset.card (Finset.image (fun w => ne.f w) (Finset.filter (fun w => G.Adj z w ∧ IsAccessible G ne.f ne.small (ne.f w)) (Finset.univ : Finset V))) := by
        refine Finset.card_le_card ?_;
        grind;
      exact le_trans ( by rw [ Finset.card_erase_of_mem hW₀_mem ] ) ( hN_acc_ge.trans ( Finset.card_image_le ) );
    have h_deg_bound : Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ : Finset V)) ≤ r := by
      convert (SimpleGraph.degree_le_maxDegree G z).trans hd using 1
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    have h_deg_bound : Finset.card (Finset.filter (fun w => G.Adj z w ∧ IsAccessible G ne.f ne.small (ne.f w)) (Finset.univ : Finset V)) + Finset.card (Finset.filter (fun w => G.Adj z w ∧ ¬IsAccessible G ne.f ne.small (ne.f w)) (Finset.univ : Finset V)) = Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ : Finset V)) := by
      rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext w ; by_cases hw : IsAccessible G ne.f ne.small ( ne.f w ) <;> simp +decide [ hw ] ;
    omega
  -- Step 5: Compute |B_verts|
  -- |V| = (r+1)*s. Accessible vertices: ne.small (s-1) + (acc_colors.card - 1) other acc classes (s each).
  -- |acc vertices| = (s-1) + (acc_colors.card - 1)*s = acc_colors.card * s - 1.
  -- |B_verts| = (r+1)*s - (acc_colors.card * s - 1) = (r+1-acc_colors.card)*s + 1.
  set q := r + 1 - acc_colors.card with hq_def
  -- Step 5a: acc_colors.card ≤ r + 1
  have hacc_le : acc_colors.card ≤ r + 1 := by
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  -- Step 5b: Compute B_verts.card = q * s + 1
  have hB_card : B_verts.card = q * s + 1 := by
    have hB_card : B_verts.card = Fintype.card V - ∑ c ∈ acc_colors, (cClass ne.f c).card := by
      rw [ ← Finset.card_biUnion ];
      · rw [ ← Finset.card_compl ];
        congr with v ; simp +decide [ B_verts, acc_colors, cClass ];
      · exact fun x hx y hy hxy => Finset.disjoint_filter.2 fun z => by simp +contextual [ hxy ] ;
    have hB_card : ∑ c ∈ acc_colors, (cClass ne.f c).card = (acc_colors.card - 1) * s + (s - 1) := by
      have hB_card : ∑ c ∈ acc_colors, (cClass ne.f c).card = ∑ c ∈ acc_colors.erase ne.small, (cClass ne.f c).card + (cClass ne.f ne.small).card := by
        rw [ Finset.sum_erase_add _ _ hsmall_mem ];
      rw [ hB_card, Finset.sum_congr rfl fun x hx => ne.card_other x ?_ ?_ ] <;> simp +decide [ *, Finset.card_erase_of_mem hsmall_mem ];
      · exact ne.card_small;
      · exact Finset.ne_of_mem_erase hx;
      · exact fun h => hlarge_nmem <| h ▸ Finset.mem_of_mem_erase hx;
    rw [ ‹#B_verts = Fintype.card V - ∑ c ∈ acc_colors, #(cClass ne.f c)›, hs, hB_card ];
    exact Nat.sub_eq_of_eq_add <| by nlinarith only [ Nat.sub_add_cancel hacc_le, Nat.sub_add_cancel ( show 1 ≤ s from hs0 ), Nat.sub_add_cancel ( show 1 ≤ Finset.card acc_colors from by linarith ) ] ;
  -- Step 5c: Degree bound for non-accessible vertices
  have hB_deg : ∀ y : V, y ∈ B_verts →
      (B_verts.filter (fun w => G.Adj y w)).card ≤ q - 1 := by
    intro y hy; specialize hB_has_nbr y; simp_all +decide ;
    -- Since $y$ is in $B_verts$, $y$ is not accessible. Therefore, $y$ has at least $acc_colors.card$ neighbors with accessible colors.
    have h_y_acc_nbr : (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)).card ≥ acc_colors.card := by
      have h_y_acc_nbr : (Finset.image (fun w => ne.f w) (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y))).card ≥ acc_colors.card := by
        refine Finset.card_le_card ?_;
        intro c hc; specialize hB_has_nbr ( Finset.mem_filter.mp hy |>.2 ) c ( Finset.mem_filter.mp hc |>.2 ) ; aesop;
      exact h_y_acc_nbr.trans ( Finset.card_image_le );
    have h_y_total_nbr : (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)).card + (Finset.filter (fun w => ¬IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)).card ≤ r := by
      rw [ Finset.card_filter_add_card_filter_not ] ; exact le_trans ( SimpleGraph.degree_le_maxDegree _ _ ) hd;
    rw [ show { w ∈ B_verts | G.Adj y w } = { w ∈ G.neighborFinset y | ¬IsAccessible G ne.f ne.small ( ne.f w ) } from ?_ ];
    · omega;
    · ext; simp [B_verts];
      tauto
  -- Case split: t ≤ q vs t > q (where t = acc_colors.card - 1)
  by_cases h_case : acc_colors.card * 2 ≤ r + 2
  · -- Case 1: t ≤ q (equivalently acc_colors.card - 1 ≤ r + 1 - acc_colors.card)
    -- Edge counting between W₀_class and B_verts gives contradiction
    -- The edge count between W₀_class and B_verts contradicts the degree bounds.
    have h_edge_count : 2 * (q * s + 1) - q * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) ≤ q * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) + r * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ¬∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) := by
      have h_edge_count : ∑ z ∈ W₀_class, (B_verts.filter (fun w => G.Adj z w)).card = ∑ y ∈ B_verts, (W₀_class.filter (fun w => G.Adj y w)).card := by
        simp +decide only [card_filter];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp +decide [ SimpleGraph.adj_comm ] );
      have h_edge_count : ∑ y ∈ B_verts, (W₀_class.filter (fun w => G.Adj y w)).card ≥ 2 * (q * s + 1) - q * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) := by
        have h_edge_count : ∀ y ∈ B_verts, (W₀_class.filter (fun w => G.Adj y w)).card ≥ if ∃ z ∈ W₀_class, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w then 1 else 2 := by
          intro y hy
          by_cases h_exists_z : ∃ z ∈ W₀_class, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w;
          · simp +zetaDelta at *;
            rw [ if_pos h_exists_z ] ; exact Finset.card_pos.mpr ⟨ h_exists_z.choose, Finset.mem_filter.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_exists_z.choose_spec.1 ⟩, h_exists_z.choose_spec.2.1 ⟩ ⟩ ;
          · obtain ⟨z₁, hz₁⟩ : ∃ z₁ ∈ W₀_class, G.Adj y z₁ := by
              simp +zetaDelta at *;
              exact Exists.elim ( hB_has_nbr y hy W₀ hW₀_mem ) fun z hz => ⟨ z, hz.1, hz.2 ⟩;
            obtain ⟨z₂, hz₂⟩ : ∃ z₂ ∈ W₀_class, G.Adj y z₂ ∧ z₂ ≠ z₁ := by
              grind;
            simp [h_exists_z];
            refine' Finset.one_lt_card.mpr ⟨ z₁, _, z₂, _, _ ⟩ <;> simp +decide [ hz₁, hz₂ ];
            exact Ne.symm hz₂.2.2;
        have h_edge_count : ∑ y ∈ B_verts, (if ∃ z ∈ W₀_class, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w then 1 else 2) ≥ 2 * (q * s + 1) - q * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) := by
          have h_edge_count : Finset.card (Finset.filter (fun y => ∃ z ∈ W₀_class, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) B_verts) ≤ q * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) := by
            have h_edge_count : ∀ z ∈ W₀_class, (Finset.filter (fun y => G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) B_verts).card ≤ q := by
              intros z hz
              by_cases hz_solo : ∃ y₁, y₁ ∈ B_verts ∧ G.Adj y₁ z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y₁ w;
              · refine' le_trans _ ( h_solo_deg_bound z _ _ );
                · refine' Finset.card_le_card _;
                  simp +contextual [ Finset.subset_iff, SimpleGraph.adj_comm ];
                  exact fun x hx hx' hx'' => Finset.mem_filter.mp hx |>.2;
                · exact Finset.mem_filter.mp hz |>.2;
                · exact ⟨ hz_solo.choose, Finset.mem_filter.mp hz_solo.choose_spec.1 |>.2, hz_solo.choose_spec.2.1, fun w hw hw' => hz_solo.choose_spec.2.2 w ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hw ⟩ ) hw' ⟩;
              · rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
                grind;
            have h_edge_count : Finset.card (Finset.filter (fun y => ∃ z ∈ W₀_class, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) B_verts) ≤ ∑ z ∈ Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y ∈ B_verts, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class, (Finset.filter (fun y => G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) B_verts).card := by
              have h_edge_count : Finset.filter (fun y => ∃ z ∈ W₀_class, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) B_verts ⊆ Finset.biUnion (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y ∈ B_verts, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) (fun z => Finset.filter (fun y => G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) B_verts) := by
                simp +contextual [ Finset.subset_iff ];
                exact fun x hx y hy hxy hyx => ⟨ y, ⟨ hy, x, hx, hxy, hyx ⟩, hxy, hyx ⟩;
              exact le_trans ( Finset.card_le_card h_edge_count ) ( Finset.card_biUnion_le );
            exact h_edge_count.trans ( by simpa [ mul_comm ] using Finset.sum_le_sum fun x hx => ‹∀ z ∈ W₀_class, #({y ∈ B_verts | G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w}) ≤ q› x <| Finset.mem_filter.mp hx |>.1 );
          simp +decide [Finset.sum_ite, *] at *;
          rw [ show ( Finset.filter ( fun x => ∀ x_1 ∈ W₀_class, G.Adj x x_1 → ∃ x_2 ∈ W₀_class, ¬x_2 = x_1 ∧ G.Adj x x_2 ) B_verts ) = B_verts \ ( Finset.filter ( fun x => ∃ z ∈ W₀_class, G.Adj x z ∧ ∀ w ∈ W₀_class, ¬w = z → ¬G.Adj x w ) B_verts ) from ?_ ];
          · grind;
          · grind;
        exact h_edge_count.trans ( Finset.sum_le_sum ‹_› );
      have h_edge_count : ∑ z ∈ W₀_class, (B_verts.filter (fun w => G.Adj z w)).card ≤ q * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) + r * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ¬∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) := by
        have h_edge_count : ∀ z ∈ W₀_class, (B_verts.filter (fun w => G.Adj z w)).card ≤ if ∃ y ∈ B_verts, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w then q else r := by
          intro z hz;
          split_ifs with h;
          · convert h_solo_deg_bound z ( Finset.mem_filter.mp hz |>.2 ) _ using 1;
            · congr 1 with w ; simp +decide;
              exact ⟨ fun h => ⟨ h.2, Finset.mem_filter.mp h.1 |>.2 ⟩, fun h => ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h.2 ⟩, h.1 ⟩ ⟩;
            · exact ⟨ h.choose, Finset.mem_filter.mp h.choose_spec.1 |>.2, h.choose_spec.2.1, fun w hw hw' => h.choose_spec.2.2 w ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hw ⟩ ) hw' ⟩;
          · have h_deg_z : (B_verts.filter (fun w => G.Adj z w)).card ≤ G.degree z := by
              exact Finset.card_le_card fun x hx => by simpa [ SimpleGraph.adj_comm ] using Finset.mem_filter.mp hx |>.2;
            exact le_trans h_deg_z ( le_trans ( SimpleGraph.degree_le_maxDegree _ _ ) hd );
        convert Finset.sum_le_sum h_edge_count using 1;
        simp +decide [ Finset.sum_ite, Finset.filter_and ];
        simp +decide [ mul_comm, Finset.filter_mem_eq_inter ];
        simp +decide [ Finset.inter_filter ];
      linarith;
    -- Since $|S₀| + |D₀| = s$, we have $|S₀| = s - |D₀|$.
    have hS₀_card : Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) + Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ¬∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) = s := by
      rw [ ← hW₀_card, ← Finset.card_union_of_disjoint ];
      · congr with z ; by_cases h : ∃ y ∈ B_verts, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w <;> simp +decide [ h ];
        grind;
      · simp +contextual [ Finset.disjoint_left ];
    rw [ tsub_le_iff_right ] at h_edge_count ; nlinarith only [ h_case, hS₀_card, h_edge_count, Nat.sub_add_cancel hacc_le ] ;
  · -- Case 2: t > q, weight function contradiction
    push Not at h_case
    -- Sub-case: q = 0 is impossible
    -- (would mean all r+1 colors accessible, but ne.large is not)
    by_cases hq0 : q = 0
    · -- q = 0 means acc_colors.card = r + 1, all colors accessible
      -- But ne.large ∉ acc_colors, contradiction
      have : acc_colors.card = r + 1 := by omega
      have hacc_full : acc_colors.card = Fintype.card (Fin (r+1)) := by simp; omega
      have := Finset.eq_univ_of_card acc_colors hacc_full
      exact hlarge_nmem (this ▸ Finset.mem_univ _)
    · -- q ≥ 1
      -- Set up parameters for weight_function_contradiction
      set t_val := acc_colors.card - 1 with ht_def
      have ht_gt_q : q < t_val := by omega
      -- A'_colors = accessible colors except ne.small
      set A'_colors := acc_colors.erase ne.small with hA'_def
      have hA'_card : A'_colors.card = t_val := by
        rw [show A'_colors = acc_colors.erase ne.small from rfl, Finset.card_erase_of_mem hsmall_mem]
      -- A'_verts = vertices whose color is in A'_colors
      set A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ A'_colors) with hA'_verts_def
      -- Solo(z) = B vertices y where z is y's unique class-neighbor
      set Solo : V → Finset V := fun z =>
        B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
      -- Apply weight_function_contradiction
      exact weight_function_contradiction A'_verts B_verts Solo q t_val s
        (by omega) ht_gt_q hs0
        -- A'_verts.card ≤ t_val * s
        (by
          have : A'_verts.card = ∑ c ∈ A'_colors, (cClass ne.f c).card := by
            rw [← Finset.card_biUnion]
            · congr 1; ext v; simp [A'_verts, A'_colors, cClass]
            · intro x hx y hy hxy; exact Finset.disjoint_filter.2 fun z => by simp +contextual [hxy]
          rw [this, ← hA'_card]
          apply Finset.sum_le_card_nsmul
          intro c hc
          have hc_ne_small : c ≠ ne.small := Finset.ne_of_mem_erase hc
          have hc_ne_large : c ≠ ne.large := by
            intro h; exact hlarge_nmem (h ▸ Finset.mem_of_mem_erase hc)
          exact le_of_eq (ne.card_other c hc_ne_small hc_ne_large))
        hB_card
        -- Solo z ⊆ B_verts
        (fun z _ => Finset.filter_subset _ _)
        -- nonempty → card ≥ 1
        (fun z _ h => Finset.card_pos.mpr h)
        -- |Solo z| ≤ q
        (by
          intro z hz
          by_cases hSz : (Solo z).card = 0
          · omega
          · -- Solo z is nonempty, get witness y₁
            obtain ⟨y₁, hy₁⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hSz)
            have hy₁_mem := Finset.mem_filter.mp hy₁
            -- z is in A'_verts, so ne.f z ∈ A'_colors
            have hz_mem := Finset.mem_filter.mp hz
            have hz_acc : IsAccessible G ne.f ne.small (ne.f z) :=
              (Finset.mem_filter.mp (Finset.mem_of_mem_erase (hA'_def ▸ hz_mem.2))).2
            have hz_ne_small : ne.f z ≠ ne.small :=
              Finset.ne_of_mem_erase (hA'_def ▸ hz_mem.2)
            have hz_ne_large : ne.f z ≠ ne.large := by
              intro h; exact hlarge_nmem (h ▸ Finset.mem_of_mem_erase (hA'_def ▸ hz_mem.2))
            -- y₁ ∈ B_verts: non-accessible, adj to z, unique in class
            have hy₁_B := (Finset.mem_filter.mp hy₁_mem.1).2
            -- From h_all_bad: Solo z is a clique
            -- If |Solo z| ≥ q+1, then y₁ has ≥ q B-neighbors (the others in Solo z)
            -- But hB_deg says y₁ has ≤ q-1 B-neighbors. Contradiction.
            by_contra h_gt
            push Not at h_gt
            -- y₁ has at least |Solo z| - 1 ≥ q neighbors in B_verts
            have : (B_verts.filter (fun w => G.Adj y₁ w)).card ≥ q := by
              have h_clique : ∀ y₂ ∈ Solo z, y₂ ≠ y₁ → G.Adj y₁ y₂ := by
                intro y₂ hy₂ hne
                have hy₂_mem := Finset.mem_filter.mp hy₂
                exact (h_all_bad (ne.f z) z y₁ hz_acc hz_ne_small hz_ne_large rfl
                  hy₁_B hy₁_mem.2.1 hy₁_mem.2.2).2
                  y₂ hne (Finset.mem_filter.mp hy₂_mem.1).2
                  hy₂_mem.2.1 hy₂_mem.2.2
              have h_sub : (Solo z).erase y₁ ⊆ B_verts.filter (fun w => G.Adj y₁ w) := by
                intro w hw
                have hw_ne := Finset.ne_of_mem_erase hw
                have hw_solo := Finset.mem_of_mem_erase hw
                exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw_solo).1,
                  h_clique w hw_solo hw_ne⟩
              calc (B_verts.filter (fun w => G.Adj y₁ w)).card
                  ≥ ((Solo z).erase y₁).card := Finset.card_le_card h_sub
                _ = (Solo z).card - 1 := Finset.card_erase_of_mem hy₁
                _ ≥ q := by omega
            have := hB_deg y₁ hy₁_mem.1
            omega)
        -- h_lower: for each y ∈ B, the |S^y| lower bound
        (by
          intro y hy
          -- y ∈ B_verts means ¬IsAccessible (ne.f y)
          have hy_nacc : ¬IsAccessible G ne.f ne.small (ne.f y) :=
            (Finset.mem_filter.mp hy).2
          -- For each c ∈ A'_colors, y has ≥ 1 neighbor of color c
          have h_has_nbr_A' : ∀ c ∈ A'_colors, ∃ w, ne.f w = c ∧ G.Adj y w :=
            fun c hc => hB_has_nbr y hy_nacc c (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)).2
          -- Degree of y
          have h_deg_y : G.degree y ≤ r := le_trans (G.degree_le_maxDegree y) hd
          -- d_B(y)
          set dB := (B_verts.filter (fun w => G.Adj y w)).card
          have hdB_le : dB ≤ q - 1 := hB_deg y hy
          -- Use c_max = dB + 1
          refine ⟨dB + 1, by omega, by omega, ?_, ?_, ?_⟩
          · -- |Sy| ≥ t_val - q + dB + 1
            -- Let's count the number of A' colors where y has ≥ 2 neighbors.
            have h_multi_count : (Finset.filter (fun c => (Finset.filter (fun w => ne.f w = c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card ≥ 2) A'_colors).card ≤ (G.degree y - 1 - dB) - t_val := by
              have h_multi_count : (Finset.sum A'_colors (fun c => (Finset.filter (fun w => ne.f w = c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card)) + 1 + dB ≤ G.degree y := by
                have h_multi_count : (Finset.sum A'_colors (fun c => (Finset.filter (fun w => ne.f w = c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card)) + (Finset.filter (fun w => ne.f w = ne.small) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card + dB ≤ G.degree y := by
                  rw [ ← Finset.card_biUnion, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
                  · refine' le_trans ( Finset.card_le_card _ ) _;
                    any_goals exact Finset.filter ( fun w => G.Adj y w ) Finset.univ;
                    · grind;
                    · exact Finset.card_le_card fun x hx => by simpa using hx;
                  · simp +contextual [ Finset.disjoint_left ];
                    grind +ring;
                  · simp +contextual [ Finset.disjoint_left ];
                    exact fun v hv₁ hv₂ => Finset.ne_of_mem_erase hv₁ |> fun h => by simp [ h ];
                  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by simp +contextual [ hxy ] ;
                generalize_proofs at *; (
                refine' le_trans _ h_multi_count
                generalize_proofs at *; (
                simp +zetaDelta at *;
                exact Exists.elim ( hB_has_nbr y hy ne.small hsmall_mem ) fun w hw => ⟨ w, by aesop ⟩))
              generalize_proofs at *; (
              have h_multi_count : ∑ c ∈ A'_colors, (Finset.filter (fun w => ne.f w = c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card ≥ ∑ c ∈ A'_colors, 1 + ∑ c ∈ Finset.filter (fun c => (Finset.filter (fun w => ne.f w = c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card ≥ 2) A'_colors, 1 := by
                rw [ Finset.sum_filter ];
                rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_le_sum fun x hx => by split_ifs <;> linarith [ show Finset.card ( Finset.filter ( fun w => ne.f w = x ) ( Finset.filter ( fun w => G.Adj y w ) Finset.univ ) ) ≥ 1 from Finset.card_pos.mpr <| by obtain ⟨ w, hw₁, hw₂ ⟩ := h_has_nbr_A' x hx; exact ⟨ w, Finset.mem_filter.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hw₂ ⟩, hw₁ ⟩ ⟩ ] ;
              generalize_proofs at *; (
              simp +zetaDelta at *; omega;));
            -- The set of solo vertices in A'_verts for y is exactly the set of vertices z in A'_verts such that y is a solo neighbor of z.
            have h_solo_set : {z ∈ A'_verts | y ∈ Solo z} = Finset.biUnion (Finset.filter (fun c => (Finset.filter (fun w => ne.f w = c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card = 1) A'_colors) (fun c => Finset.filter (fun z => ne.f z = c ∧ G.Adj y z ∧ ∀ w, ne.f w = c → w ≠ z → ¬G.Adj y w) A'_verts) := by
              ext z; simp [Solo, hA'_verts_def];
              simp +decide [ Finset.card_eq_one, Finset.filter_filter ];
              simp +decide [ Finset.eq_singleton_iff_unique_mem ];
              grind;
            rw [ h_solo_set, Finset.card_biUnion ];
            · refine' le_trans _ ( Finset.sum_le_sum fun c hc => Finset.card_pos.mpr _ );
              · simp +zetaDelta at *;
                rw [ show ( Finset.filter ( fun c => Finset.card ( Finset.filter ( fun w => ne.f w = c ) ( Finset.filter ( fun w => G.Adj y w ) Finset.univ ) ) = 1 ) ( Finset.erase ( Finset.filter ( fun c => IsAccessible G ne.f ne.small c ) Finset.univ ) ne.small ) ) = Finset.erase ( Finset.filter ( fun c => IsAccessible G ne.f ne.small c ) Finset.univ ) ne.small \ ( Finset.filter ( fun c => 2 ≤ Finset.card ( Finset.filter ( fun w => ne.f w = c ) ( Finset.filter ( fun w => G.Adj y w ) Finset.univ ) ) ) ( Finset.erase ( Finset.filter ( fun c => IsAccessible G ne.f ne.small c ) Finset.univ ) ne.small ) ) from ?_ ];
                · grind;
                · ext; simp [Finset.mem_sdiff, Finset.mem_filter];
                  exact fun _ _ => ⟨ fun h => fun _ _ => by linarith, fun h => by linarith [ h ‹_› ‹_›, show # ( Finset.filter ( fun w => ne.f w = ‹_› ) ( Finset.filter ( fun w => G.Adj y w ) Finset.univ ) ) ≥ 1 from Finset.card_pos.mpr ( by obtain ⟨ w, hw₁, hw₂ ⟩ := h_has_nbr_A' _ ‹_› ‹_›; exact ⟨ w, by aesop ⟩ ) ] ⟩;
              · obtain ⟨ z, hz ⟩ := Finset.card_eq_one.mp ( Finset.mem_filter.mp hc |>.2 );
                use z;
                simp +decide [ Finset.eq_singleton_iff_unique_mem ] at hz ⊢;
                grind;
            · intros c hc d hd hcd; simp +contextual [ Finset.disjoint_left, hcd ] ;
          · -- ∀ z ∈ Sy, (Solo z).card ≤ dB + 1
            intro z hz
            -- Extract membership info
            have hz_mem := Finset.mem_filter.mp hz
            have hy_in_solo : y ∈ Solo z := hz_mem.2
            have hz_in_A' : z ∈ A'_verts := hz_mem.1
            have hz_A'_color : ne.f z ∈ A'_colors := (Finset.mem_filter.mp hz_in_A').2
            -- z's color is accessible, ≠ small, ≠ large
            have hz_acc : IsAccessible G ne.f ne.small (ne.f z) :=
              (Finset.mem_filter.mp (Finset.mem_of_mem_erase hz_A'_color)).2
            have hz_ne_small : ne.f z ≠ ne.small := Finset.ne_of_mem_erase hz_A'_color
            have hz_ne_large : ne.f z ≠ ne.large := by
              intro h; exact hlarge_nmem (h ▸ Finset.mem_of_mem_erase hz_A'_color)
            -- y ∈ Solo z gives us: y ∈ B_verts, G.Adj y z, unique
            have hy_solo := Finset.mem_filter.mp hy_in_solo
            -- Apply h_all_bad with y₁ = y
            have h_bad := h_all_bad (ne.f z) z y hz_acc hz_ne_small hz_ne_large rfl
              hy_nacc hy_solo.2.1 hy_solo.2.2
            -- Show (Solo z).erase y ⊆ B_verts.filter (G.Adj y)
            have h_sub : (Solo z).erase y ⊆ B_verts.filter (fun w => G.Adj y w) := by
              intro w hw
              have hw_ne := Finset.ne_of_mem_erase hw
              have hw_solo := Finset.mem_of_mem_erase hw
              have hw_mem := Finset.mem_filter.mp hw_solo
              exact Finset.mem_filter.mpr ⟨hw_mem.1,
                h_bad.2 w hw_ne (Finset.mem_filter.mp hw_mem.1).2 hw_mem.2.1 hw_mem.2.2⟩
            -- (Solo z).card = |(Solo z).erase y| + 1 ≤ dB + 1
            have h_erase_card := Finset.card_erase_of_mem hy_in_solo
            -- (Solo z).erase y).card = (Solo z).card - 1
            have h_card_le := Finset.card_le_card h_sub
            have h_pos := Finset.card_pos.mpr ⟨y, hy_in_solo⟩
            omega
          · -- ∀ z ∈ Sy, 1 ≤ (Solo z).card
            intro z hz
            exact Finset.card_pos.mpr ⟨y, (Finset.mem_filter.mp hz).2⟩)

/-- Lemma 2.3 from Kierstead-Kostochka: Given a nearly equitable coloring where
    the large class is not accessible, there exists a "good solo vertex"
    configuration that enables progress. -/
lemma good_solo_vertex_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    ∃ (W : Fin (r + 1)) (z y₁ : V),
      -- W is accessible, distinct from small and large
      IsAccessible G ne.f ne.small W ∧
      W ≠ ne.small ∧ W ≠ ne.large ∧
      -- z has color W
      ne.f z = W ∧
      -- y₁ has non-accessible color
      ¬IsAccessible G ne.f ne.small (ne.f y₁) ∧
      -- z is y₁'s unique neighbor in class W
      G.Adj y₁ z ∧
      (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) ∧
      -- Either Case 1 (z movable to another accessible class) or Case 2
      ((∃ X : Fin (r+1), X ≠ W ∧ IsAccessible G ne.f ne.small X ∧
        ∀ w, ne.f w = X → ¬G.Adj z w) ∨
       -- Case 2: z is not movable and has two nonadjacent solo neighbors
       (∃ y₂ : V, y₂ ≠ y₁ ∧ ¬IsAccessible G ne.f ne.small (ne.f y₂) ∧
        G.Adj y₂ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) ∧
        ¬G.Adj y₁ y₂ ∧
        (∀ X : Fin (r+1), IsAccessible G ne.f ne.small X → X ≠ W →
          ∃ w, ne.f w = X ∧ G.Adj z w))) := by
  by_contra h_neg
  -- h_neg : ¬∃ W z y₁, ... ∧ (Case1 ∨ Case2)
  apply solo_weight_contradiction G r s hs hd hs0 ne hacc
  intro W z y₁ hW_acc hW_ne_small hW_ne_large hz_color hy₁_nacc hadj huniq
  -- First prove z is not movable to any accessible class ≠ W
  have h_not_movable : ∀ X, X ≠ W → IsAccessible G ne.f ne.small X →
      ∃ w, ne.f w = X ∧ G.Adj z w := by
    intro X hXW hXacc
    by_contra h_no
    exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc, hadj, huniq,
      Or.inl ⟨X, hXW, hXacc, fun w hw => by
        intro hadj_zw; exact h_no ⟨w, hw, hadj_zw⟩⟩⟩
  refine ⟨h_not_movable, fun y₂ hy₂_ne hy₂_nacc hy₂_adj hy₂_uniq => ?_⟩
  by_contra h_not_adj
  -- With ¬G.Adj y₁ y₂, we construct Case 2 directly, contradicting h_neg.
  exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc, hadj, huniq,
    Or.inr ⟨y₂, hy₂_ne, hy₂_nacc, hy₂_adj, hy₂_uniq, h_not_adj,
      fun X hXacc hXW => h_not_movable X hXW hXacc⟩⟩

/-! ### Helper: T-vertex degree bound in B -/

set_option maxHeartbeats 1600000 in
/-- Any vertex in a T-class has at most q + t neighbors in B, where q = r+1-|acc_colors|, t = |T|.
    This follows from h_not_mov_outside: such a vertex has a neighbor in every accessible
    class outside T ∪ {U}. -/
lemma T_vertex_B_degree_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (_hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (_hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (_hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (U : Fin (r + 1))
    (_hU_acc : IsAccessible G ne.f ne.small U)
    (hU_not_T : U ∉ T)
    (h_not_mov_outside : ∀ W ∈ T, ∀ x : V, ne.f x = W →
      ∀ V_out : Fin (r + 1), IsAccessible G ne.f ne.small V_out →
      V_out ∉ T → V_out ≠ U →
      ∃ w, ne.f w = V_out ∧ G.Adj x w)
    (x : V) (W : Fin (r + 1)) (hW_T : W ∈ T) (hx : ne.f x = W) :
    (Finset.univ.filter (fun w => G.Adj x w ∧ ¬IsAccessible G ne.f ne.small (ne.f w))).card
      ≤ r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card + T.card := by
  -- The number of accessible neighbors of x is at least acc_colors.card - T.card - 1.
  have h_acc_neighbors : (Finset.filter (fun w => G.Adj x w ∧ IsAccessible G ne.f ne.small (ne.f w)) Finset.univ).card ≥ (Finset.filter (fun c => IsAccessible G ne.f ne.small c) Finset.univ).card - T.card - 1 := by
    have h_acc_neighbors : (Finset.image (fun w => ne.f w) (Finset.filter (fun w => G.Adj x w ∧ IsAccessible G ne.f ne.small (ne.f w)) Finset.univ)).card ≥ (Finset.filter (fun c => IsAccessible G ne.f ne.small c) Finset.univ \ (T ∪ {U})).card := by
      refine Finset.card_le_card ?_;
      grind;
    grind +splitImp;
  -- The total number of neighbors of x is at most r.
  have h_total_neighbors : (Finset.filter (fun w => G.Adj x w) Finset.univ).card ≤ r := by
    convert (SimpleGraph.degree_le_maxDegree G x).trans hd using 1
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  rw [ show ( Finset.filter ( fun w => G.Adj x w ∧ ¬IsAccessible G ne.f ne.small ( ne.f w ) ) Finset.univ ) = Finset.filter ( fun w => G.Adj x w ) Finset.univ \ Finset.filter ( fun w => G.Adj x w ∧ IsAccessible G ne.f ne.small ( ne.f w ) ) Finset.univ by ext; aesop ] ; rw [ Finset.card_sdiff ] ; simp_all +decide ;
  rw [ show ( Finset.filter ( fun w => G.Adj x w ∧ IsAccessible G ne.f ne.small ( ne.f w ) ) Finset.univ ∩ Finset.filter ( fun w => G.Adj x w ) Finset.univ ) = Finset.filter ( fun w => G.Adj x w ∧ IsAccessible G ne.f ne.small ( ne.f w ) ) Finset.univ by ext; aesop ] ; omega;

set_option maxHeartbeats 1600000 in
/-- Solo vertex in T-class has at most q non-accessible neighbors.
    From h_bad: z has a neighbor in every accessible class ≠ (ne.f z). -/
lemma T_solo_vertex_B_degree_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (_hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (_hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (z y₁ : V) (W : Fin (r + 1))
    (hz : ne.f z = W) (_hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (_hadj : G.Adj y₁ z) (huniq : ∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w)
    (h_nbr_all : ∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) :
    (Finset.univ.filter (fun w => G.Adj z w ∧ ¬IsAccessible G ne.f ne.small (ne.f w))).card
      ≤ r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card := by
  have h_image : Finset.card (Finset.image (fun w => ne.f w) (Finset.univ.filter (fun w => G.Adj z w ∧ IsAccessible G ne.f ne.small (ne.f w)))) ≥ Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) - 1 := by
    refine' le_trans _ ( Finset.card_mono <| show Finset.image ( fun w => ne.f w ) ( Finset.filter ( fun w => G.Adj z w ∧ IsAccessible G ne.f ne.small ( ne.f w ) ) Finset.univ ) ≥ Finset.univ.filter ( fun c => IsAccessible G ne.f ne.small c ) \ { W } from _ );
    · grind;
    · intro c hc; specialize h_nbr_all c; aesop;
  have h_card_le_image : Finset.card (Finset.univ.filter (fun w => G.Adj z w ∧ IsAccessible G ne.f ne.small (ne.f w))) ≥ Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) - 1 := by
    exact h_image.trans ( Finset.card_image_le );
  have h_card_le_image : Finset.card (Finset.univ.filter (fun w => G.Adj z w ∧ ¬IsAccessible G ne.f ne.small (ne.f w))) + Finset.card (Finset.univ.filter (fun w => G.Adj z w ∧ IsAccessible G ne.f ne.small (ne.f w))) ≤ G.degree z := by
    rw [ ← Finset.card_union_of_disjoint ];
    · exact Finset.card_le_card fun x hx => by aesop;
    · exact Finset.disjoint_filter.mpr ( by aesop );
  have h_card_le_image : G.degree z ≤ r := by
    exact le_trans ( SimpleGraph.degree_le_maxDegree _ _ ) hd;
  omega

/-
B_card computation: number of non-accessible vertices = q*s + 1.
-/
lemma B_card_eq_aux
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    (Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))).card =
    (r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card) * s + 1 := by
  -- The number of vertices in the union of all accessible color classes is equal to the sum of their sizes.
  have h_union_accessible_size : ∑ c ∈ Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c), (cClass ne.f c).card = (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)).sum (fun c => if c = ne.small then s - 1 else s) := by
    refine' Finset.sum_congr rfl fun c hc => _;
    split_ifs <;> simp_all +decide [ NearlyEquitable.card_small ];
    exact ne.card_other c ‹_› ( by rintro rfl; exact hacc hc );
  -- The total number of vertices is the sum of the sizes of all color classes.
  have h_total_vertices : (Finset.univ.filter (fun v => ¬IsAccessible G ne.f ne.small (ne.f v))).card + (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)).sum (fun c => (cClass ne.f c).card) = Fintype.card V := by
    rw [ ← Finset.card_biUnion ];
    · rw [ ← Finset.card_union_of_disjoint ];
      · convert Finset.card_univ using 2 ; ext v ; by_cases hv : IsAccessible G ne.f ne.small ( ne.f v ) <;> simp +decide [ hv ];
      · simp +contextual [ Finset.disjoint_left ];
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz hz' => hxy <| by aesop;
  simp_all +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq' ];
  split_ifs at * <;> simp_all +decide [ Finset.card_erase_of_mem ];
  · zify at *;
    rw [ Nat.cast_sub ] at * <;> push_cast at *;
    · rw [ Nat.cast_sub ] at * <;> push_cast at *;
      · grind +revert;
      · exact Finset.card_pos.mpr ⟨ ne.small, by aesop ⟩;
      · exact Finset.card_pos.mpr ⟨ ne.small, by aesop ⟩;
    · linarith;
    · linarith;
    · exact le_trans ( Finset.card_le_univ _ ) ( by simp +decide );
  · exact False.elim ( ‹¬IsAccessible G ne.f ne.small ne.small› ( Relation.ReflTransGen.refl ) )

/-- Solo vertex bound: for z with a solo B-neighbor y₁, the number of B-neighbors of z that
    are solo (unique in W₀-class) is at most q. -/
lemma solo_card_le_q_aux
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (W₀ : Fin (r + 1)) (hW₀ : W₀ ∈ T)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂))
    (z : V) (hz : ne.f z = W₀)
    (y₁ : V) (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (hy₁_adj : G.Adj y₁ z) (hy₁_uniq : ∀ w, ne.f w = W₀ → w ≠ z → ¬G.Adj y₁ w) :
    (Finset.univ.filter (fun w => G.Adj z w ∧ ¬IsAccessible G ne.f ne.small (ne.f w))).card ≤
    r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card := by
  exact T_solo_vertex_B_degree_bound G r s hs hd hs0 ne hacc z y₁ W₀ hz hy₁_nacc hy₁_adj hy₁_uniq
    ((h_bad W₀ hW₀ z y₁ hz hy₁_nacc hy₁_adj hy₁_uniq).1)

set_option maxHeartbeats 3200000 in
lemma restricted_T_card_gt_q
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (hT_ne_small : ∀ c ∈ T, c ≠ ne.small)
    (hT_ne_large : ∀ c ∈ T, c ≠ ne.large)
    (hT_nonempty : T.Nonempty)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂))
    (U : Fin (r + 1))
    (hU_acc : IsAccessible G ne.f ne.small U)
    (hU_not_T : U ∉ T)
    (h_not_mov_outside : ∀ W ∈ T, ∀ x : V, ne.f x = W →
      ∀ V_out : Fin (r + 1), IsAccessible G ne.f ne.small V_out →
      V_out ∉ T → V_out ≠ U →
      ∃ w, ne.f w = V_out ∧ G.Adj x w) :
    (r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card) < T.card := by
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ ∈ T, True := by
    exact ⟨ hT_nonempty.choose, hT_nonempty.choose_spec, trivial ⟩;
  -- Let $B$ be the set of non-accessible vertices, and $W₀_class$ be the class of $W₀$.
  set B := Finset.univ.filter (fun v => ¬IsAccessible G ne.f ne.small (ne.f v))
  set W₀_class := cClass ne.f W₀;
  -- Let $p$ be the number of vertices in $W₀_class$ that have at least one non-accessible neighbor.
  set p := (W₀_class.filter (fun z => ∃ y ∈ B, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w)).card;
  -- Upper bound: $\sum_{z \in W₀_class} |B \cap N(z)| \leq p \cdot q + (s - p) \cdot (q + T.card)$.
  have h_upper_bound : ∑ z ∈ W₀_class, (B.filter (fun y => G.Adj y z)).card ≤ p * (r + 1 - Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c))) + (s - p) * (r + 1 - Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) + T.card) := by
    have h_upper_bound : ∀ z ∈ W₀_class, (B.filter (fun y => G.Adj y z)).card ≤ if ∃ y ∈ B, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w then r + 1 - Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) else r + 1 - Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) + T.card := by
      intro z hz
      by_cases h_solo : ∃ y ∈ B, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w;
      · rw [ if_pos h_solo ];
        obtain ⟨ y, hyB, hyz, hy ⟩ := h_solo;
        have := solo_card_le_q_aux G r s hs hd hs0 ne hacc T W₀ hW₀.1 h_bad z (by
        exact Finset.mem_filter.mp hz |>.2) y (by
        exact Finset.mem_filter.mp hyB |>.2) hyz (by
        exact fun w hw hwz => hy w ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hw ⟩ ) hwz);
        convert this using 1;
        simp +decide [ SimpleGraph.adj_comm ];
        exact congr_arg Finset.card ( by ext; aesop );
      · rw [ if_neg h_solo ];
        convert T_vertex_B_degree_bound G r s hs hd hs0 ne hacc T hT_sub U hU_acc hU_not_T h_not_mov_outside z W₀ hW₀.1 ( by aesop ) using 1;
        simp +decide [ SimpleGraph.adj_comm ];
        exact congr_arg Finset.card ( by ext; aesop );
    refine' le_trans ( Finset.sum_le_sum h_upper_bound ) _;
    simp +zetaDelta at *;
    simp +decide [ Finset.sum_ite ];
    rw [ show ( Finset.filter ( fun x => ∀ x_1 : V, ¬IsAccessible G ne.f ne.small ( ne.f x_1 ) → G.Adj x_1 x → ∃ x_2 : V, ne.f x_2 = W₀ ∧ ¬x_2 = x ∧ G.Adj x_1 x_2 ) ( cClass ne.f W₀ ) ) = cClass ne.f W₀ \ ( Finset.filter ( fun x => ∃ y : V, ¬IsAccessible G ne.f ne.small ( ne.f y ) ∧ G.Adj y x ∧ ∀ w : V, ne.f w = W₀ → ¬w = x → ¬G.Adj y w ) ( cClass ne.f W₀ ) ) from ?_ ];
    · rw [ Finset.card_sdiff ] ; norm_num [ ne.card_other W₀ ( by aesop ) ( by aesop ) ];
      simp +decide [ Finset.filter_inter ];
    · grind;
  -- Lower bound: $\sum_{y \in B} |W₀_class \cap N(y)| \geq 2|B| - pq$.
  have h_lower_bound : ∑ y ∈ B, (W₀_class.filter (fun z => G.Adj y z)).card ≥ 2 * B.card - p * (r + 1 - Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c))) := by
    -- Each vertex in $B$ has at least one neighbor in $W₀_class$.
    have h_B_neighbor : ∀ y ∈ B, ∃ z ∈ W₀_class, G.Adj y z := by
      intro y hy;
      have := non_acc_has_acc_neighbor G ( hT_sub W₀ hW₀.1 ) ( Finset.mem_filter.mp hy |>.2 );
      exact ⟨ this.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, this.choose_spec.1 ⟩, this.choose_spec.2 ⟩;
    -- Each vertex in $B$ that has exactly one neighbor in $W₀_class$ contributes exactly 1 to the sum.
    have h_B_one_neighbor : ∑ y ∈ B, (if (W₀_class.filter (fun z => G.Adj y z)).card = 1 then 1 else 0) ≤ p * (r + 1 - Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c))) := by
      have h_B_one_neighbor : ∀ z ∈ W₀_class.filter (fun z => ∃ y ∈ B, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w), (B.filter (fun y => G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w)).card ≤ r + 1 - Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) := by
        intros z hz
        have hz_degree : (B.filter (fun y => G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w)).card ≤ r + 1 - Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) := by
          have := T_solo_vertex_B_degree_bound G r s hs hd hs0 ne hacc z (Classical.choose (Finset.mem_filter.mp hz).right) W₀ (by
          exact Finset.mem_filter.mp ( Finset.mem_filter.mp hz |>.1 ) |>.2) (by
          grind) (by
          exact Classical.choose_spec ( Finset.mem_filter.mp hz |>.2 ) |>.2.1) (by
          have := Classical.choose_spec ( Finset.mem_filter.mp hz |>.2 );
          exact fun w hw hwz => this.2.2 w ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hw ⟩ ) hwz)
          refine' le_trans _ ( this _ );
          · refine' Finset.card_le_card _;
            simp +contextual [ Finset.subset_iff, SimpleGraph.adj_comm ];
            exact fun x hx hx' hx'' => Finset.mem_filter.mp hx |>.2;
          · exact fun X hX₁ hX₂ => h_bad W₀ hW₀.1 z ( Classical.choose ( Finset.mem_filter.mp hz |>.2 ) ) ( by
              exact Finset.mem_filter.mp ( Finset.mem_filter.mp hz |>.1 ) |>.2 ) ( by
              exact Classical.choose_spec ( Finset.mem_filter.mp hz |>.2 ) |>.1 |> Finset.mem_filter.mp |>.2 ) ( by
              exact Classical.choose_spec ( Finset.mem_filter.mp hz |>.2 ) |>.2.1 ) ( by
              exact fun w hw₁ hw₂ => Classical.choose_spec ( Finset.mem_filter.mp hz |>.2 ) |>.2.2 w ( by aesop ) hw₂ ) |>.1 X hX₁ hX₂;
        exact hz_degree;
      have h_B_one_neighbor : ∑ y ∈ B, (if (W₀_class.filter (fun z => G.Adj y z)).card = 1 then 1 else 0) ≤ ∑ z ∈ W₀_class.filter (fun z => ∃ y ∈ B, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w), (B.filter (fun y => G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w)).card := by
        have h_B_one_neighbor : ∀ y ∈ B, (if (W₀_class.filter (fun z => G.Adj y z)).card = 1 then 1 else 0) ≤ ∑ z ∈ W₀_class.filter (fun z => ∃ y ∈ B, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w), (if G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w then 1 else 0) := by
          intro y hy
          by_cases h : (W₀_class.filter (fun z => G.Adj y z)).card = 1;
          · obtain ⟨ z, hz ⟩ := Finset.card_eq_one.mp h;
            rw [ Finset.eq_singleton_iff_unique_mem ] at hz;
            simp +zetaDelta at *;
            rw [ if_pos h ];
            refine' Finset.card_pos.mpr ⟨ z, _ ⟩ ; simp +decide [ hz ];
            exact ⟨ ⟨ y, hy, hz.1.2, fun w hw hw' hw'' => hw' <| hz.2 w hw hw'' ⟩, fun w hw hw' hw'' => hw' <| hz.2 w hw hw'' ⟩;
          · lia;
        refine' le_trans ( Finset.sum_le_sum h_B_one_neighbor ) _;
        rw [ Finset.sum_comm ];
        simp +decide ;
      exact h_B_one_neighbor.trans ( Finset.sum_le_card_nsmul _ _ _ fun x hx => by solve_by_elim );
    -- Each vertex in $B$ that has exactly one neighbor in $W₀_class$ contributes exactly 1 to the sum, and each vertex in $B$ that has more than one neighbor in $W₀_class$ contributes at least 2 to the sum.
    have h_B_contribution : ∑ y ∈ B, (W₀_class.filter (fun z => G.Adj y z)).card ≥ ∑ y ∈ B, (if (W₀_class.filter (fun z => G.Adj y z)).card = 1 then 1 else 2) := by
      gcongr;
      split_ifs <;> norm_num;
      · exact Exists.elim ( h_B_neighbor _ ‹_› ) fun x hx => ⟨ x, by aesop ⟩;
      · exact Nat.lt_of_le_of_ne ( Finset.card_pos.mpr ⟨ Classical.choose ( h_B_neighbor _ ‹_› ), Finset.mem_filter.mpr ⟨ Classical.choose_spec ( h_B_neighbor _ ‹_› ) |>.1, Classical.choose_spec ( h_B_neighbor _ ‹_› ) |>.2 ⟩ ⟩ ) ( Ne.symm ‹_› );
    simp_all +decide [ Finset.sum_ite ];
    rw [ show #B = # ( { x ∈ B | # ( { z ∈ W₀_class | G.Adj x z } ) = 1 } ) + # ( { x ∈ B | ¬# ( { z ∈ W₀_class | G.Adj x z } ) = 1 } ) by rw [ Finset.card_filter_add_card_filter_not ] ] ; linarith;
  -- By Fubini's theorem, we have $\sum_{z \in W₀_class} |B \cap N(z)| = \sum_{y \in B} |W₀_class \cap N(y)|$.
  have h_fubini : ∑ z ∈ W₀_class, (B.filter (fun y => G.Adj y z)).card = ∑ y ∈ B, (W₀_class.filter (fun z => G.Adj y z)).card := by
    simp +decide only [card_filter];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp +decide );
  -- By definition of $B$, we know that $|B| = (r + 1 - \text{acc\_colors.card}) * s + 1$.
  have hB_card : B.card = (r + 1 - Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c))) * s + 1 := by
    convert B_card_eq_aux G r s hs hs0 ne hacc using 1;
  contrapose! h_lower_bound;
  rw [ Nat.lt_sub_iff_add_lt ];
  rw [ ← h_fubini ];
  refine' lt_of_le_of_lt ( Nat.add_le_add_right h_upper_bound _ ) _;
  rw [ hB_card ];
  have hp_le_s : p ≤ s := by
    have hp_le_s : W₀_class.card = s := by
      exact ne.card_other W₀ ( hT_ne_small W₀ hW₀.1 ) ( hT_ne_large W₀ hW₀.1 );
    exact le_trans ( Finset.card_filter_le _ _ ) hp_le_s.le;
  nlinarith only [ Nat.sub_add_cancel hp_le_s, h_lower_bound, hp_le_s, hs0, Nat.sub_add_cancel ( show Finset.card ( Finset.filter ( fun c => IsAccessible G ne.f ne.small c ) Finset.univ ) ≤ r + 1 from le_trans ( Finset.card_le_univ _ ) ( by simp +decide ) ) ]

-- Helper lemma: |Solo z| ≤ q for z in T-class
set_option maxHeartbeats 1600000 in
lemma restricted_Solo_card_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (_hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (_hT_ne_small : ∀ c ∈ T, c ≠ ne.small)
    (_hT_ne_large : ∀ c ∈ T, c ≠ ne.large)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂)) :
    let B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
    let Solo : V → Finset V := fun z =>
      B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
    let A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ T)
    let q := r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card
    ∀ z ∈ A'_verts, (Solo z).card ≤ q := by
  intro B_verts Solo A'_verts q z hz
  by_cases h_empty : (Solo z).card = 0
  · omega
  · obtain ⟨y₁, hy₁⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h_empty)
    have hy₁_B : y₁ ∈ B_verts := (Finset.mem_filter.mp hy₁).1
    have hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁) := (Finset.mem_filter.mp hy₁_B).2
    have hy₁_adj : G.Adj y₁ z := (Finset.mem_filter.mp hy₁).2.1
    have hy₁_uniq : ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y₁ w := (Finset.mem_filter.mp hy₁).2.2
    have hz_T : ne.f z ∈ T := (Finset.mem_filter.mp hz).2
    have h_nbr_all := (h_bad (ne.f z) hz_T z y₁ rfl hy₁_nacc hy₁_adj hy₁_uniq).1
    have h_deg := T_solo_vertex_B_degree_bound G r s hs hd hs0 ne hacc z y₁ (ne.f z) rfl
      hy₁_nacc hy₁_adj hy₁_uniq h_nbr_all
    exact le_trans (Finset.card_le_card (fun x hx => by
      have hx_mem := Finset.mem_filter.mp hx
      have hx_B := Finset.mem_filter.mp hx_mem.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (SimpleGraph.adj_comm G _ _).mp hx_mem.2.1, hx_B.2⟩)) h_deg

/-! ### Helper lemmas for restricted_Solo_lower_bound -/

set_option maxHeartbeats 1600000 in
/-- Solo(z) has at most dB+1 elements, where dB is the B-degree of y. -/
lemma solo_card_le_dB_plus_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (_hd : G.maxDegree ≤ r) (_hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (_hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (_hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂))
    (y : V) (hy : y ∈ Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))) :
    let B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
    let Solo : V → Finset V := fun z =>
      B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
    let A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ T)
    let dB := (B_verts.filter (fun w => G.Adj y w)).card
    ∀ z ∈ A'_verts.filter (fun z => y ∈ Solo z), (Solo z).card ≤ dB + 1 := by
  intro B_verts Solo A'_verts dB z hz;
  have h_erase : Solo z ⊆ insert y (B_verts.filter (fun w => G.Adj y w)) := by
    grind;
  exact le_trans ( Finset.card_le_card h_erase ) ( Finset.card_insert_le _ _ )

set_option maxHeartbeats 1600000 in
/-- Lower bound on |S^y| (number of solo vertices in T-classes for y). -/
lemma sy_card_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (_hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (hT_card_gt_q : (r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card) < T.card)
    (_h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂))
    (y : V) (hy : y ∈ Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))) :
    let B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
    let Solo : V → Finset V := fun z =>
      B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
    let A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ T)
    let dB := (B_verts.filter (fun w => G.Adj y w)).card
    let q := r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card
    (A'_verts.filter (fun z => y ∈ Solo z)).card ≥ T.card - q + (dB + 1) := by
  intro B_verts Solo A'_verts dB q
  have hy_nacc : ¬IsAccessible G ne.f ne.small (ne.f y) := (Finset.mem_filter.mp hy).2
  set acc_colors := Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)
  have hT_gt_q : q < T.card := hT_card_gt_q
  -- For each W ∈ T, y has ≥ 1 neighbor in class W
  have h_has_nbr : ∀ W ∈ T, ∃ w, ne.f w = W ∧ G.Adj y w :=
    fun W hW => non_acc_has_acc_neighbor G (hT_sub W hW) hy_nacc
  -- S^y maps: for each W ∈ T where y has exactly 1 neighbor z, z ∈ S_y
  -- Define solo_colors = T-colors where y has unique neighbor
  set S_y := A'_verts.filter (fun z => y ∈ Solo z)
  -- For W ∈ T, the neighbors of y in class W
  set nbrs_of_y_in := fun W : Fin (r + 1) => Finset.univ.filter (fun w : V => ne.f w = W ∧ G.Adj y w)
  set solo_colors := T.filter (fun W => (nbrs_of_y_in W).card = 1)
  set multi_colors := T.filter (fun W => (nbrs_of_y_in W).card ≥ 2)
  -- Step 1: solo_colors injects into S_y, so |S_y| ≥ |solo_colors|
  have h_solo_inj : solo_colors.card ≤ S_y.card := by
    -- For each $W \in \text{solo\_colors}$, there exists a unique $z \in S_y$ such that $z$ is the only neighbor of $y$ in class $W$.
    have h_inj : ∀ W ∈ solo_colors, ∃! z, z ∈ S_y ∧ ne.f z = W := by
      intro W hW;
      obtain ⟨ z, hz ⟩ := Finset.card_eq_one.mp ( Finset.mem_filter.mp hW |>.2 );
      use z;
      simp_all +decide [ Finset.ext_iff ];
      simp +zetaDelta at *;
      grind;
    choose! f hf₁ hf₂ using h_inj;
    have h_inj : Function.Injective (fun W : solo_colors => f W W.2) := by
      intro W₁ W₂ h_eq;
      grind;
    have := Finset.card_le_card ( show Finset.image ( fun W : solo_colors => f W W.2 ) Finset.univ ⊆ S_y from Finset.image_subset_iff.mpr fun W _ => hf₁ _ _ |>.1 ) ; simp +decide [ Finset.card_image_of_injective _ h_inj ] at this ⊢; linarith;
  -- Step 2: multi_colors.card + dB ≤ q - 1
  have h_multi_dB_bound : multi_colors.card + dB ≤ q - 1 := by
    have h_multi_colors_card : ∑ c ∈ acc_colors, (nbrs_of_y_in c).card ≤ r - dB := by
      have h_multi_colors_card : (∑ c ∈ acc_colors, (nbrs_of_y_in c).card) + dB ≤ (SimpleGraph.neighborFinset G y).card := by
        -- The sum of the neighbor counts for each accessible color is the total number of accessible neighbors of y.
        have h_accessible_neighbors : ∑ c ∈ acc_colors, (nbrs_of_y_in c).card = (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)).card := by
          rw [ ← Finset.card_biUnion ] ; congr ; ext ; aesop;
          exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
        rw [ h_accessible_neighbors, ← Finset.card_union_of_disjoint ];
        · exact Finset.card_le_card fun x hx => by aesop;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop;
      exact le_tsub_of_add_le_right ( h_multi_colors_card.trans ( by simpa using hd.trans' ( G.degree_le_maxDegree y ) ) );
    have h_multi_colors_card : ∑ c ∈ acc_colors, (nbrs_of_y_in c).card ≥ acc_colors.card + multi_colors.card := by
      have h_multi_colors_card : ∀ c ∈ acc_colors, (nbrs_of_y_in c).card ≥ 1 + (if c ∈ multi_colors then 1 else 0) := by
        intro c hc; split_ifs <;> simp_all +decide ;
        · grind;
        · simp +zetaDelta at *;
          exact non_acc_has_acc_neighbor G hc hy_nacc |> fun ⟨ w, hw₁, hw₂ ⟩ => ⟨ w, by aesop ⟩;
      refine' le_trans _ ( Finset.sum_le_sum h_multi_colors_card );
      simp +decide [ Finset.sum_add_distrib ];
      exact Finset.card_le_card fun x hx => Finset.mem_inter.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by aesop ⟩, hx ⟩;
    rw [ Nat.le_sub_iff_add_le ] at *;
    · grind;
    · have := G.degree_le_maxDegree y;
      exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun w => G.Adj y w ) B_verts ⊆ G.neighborFinset y from fun x hx => by aesop ) ) ( by simpa using this.trans hd );
    · grind
  -- Step 3: solo_colors + multi_colors = T
  have h_partition : solo_colors.card + multi_colors.card = T.card := by
    rw [ ← Finset.card_union_of_disjoint, Finset.filter_union_right ];
    · refine' congr_arg Finset.card ( Finset.filter_true_of_mem fun x hx => _ );
      exact Classical.or_iff_not_imp_left.2 fun h => Nat.lt_of_le_of_ne ( Finset.card_pos.2 <| by obtain ⟨ w, hw₁, hw₂ ⟩ := h_has_nbr x hx; exact ⟨ w, by aesop ⟩ ) ( Ne.symm h );
    · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
  -- Conclude
  have hq_pos : q ≥ 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (Finset.card_lt_card
    (Finset.filter_ssubset.mpr ⟨ne.large, Finset.mem_univ _, hacc⟩)) (by simp))
  have : q ≤ T.card := le_of_lt hT_gt_q
  have : multi_colors.card + dB + 1 ≤ q := by omega
  have : solo_colors.card ≥ T.card - q + dB + 1 := by omega
  omega

/-
Helper lemma: lower bound on |S^y| for y ∈ B
-/
set_option maxHeartbeats 1600000 in
lemma restricted_Solo_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (hT_card_gt_q : (r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card) < T.card)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂)) :
    let B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
    let Solo : V → Finset V := fun z =>
      B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
    let A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ T)
    let q := r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card
    ∀ y ∈ B_verts,
      ∃ c_max : ℕ, 1 ≤ c_max ∧ c_max ≤ q ∧
        (A'_verts.filter (fun z => y ∈ Solo z)).card ≥ T.card - q + c_max ∧
        (∀ z ∈ A'_verts.filter (fun z => y ∈ Solo z), (Solo z).card ≤ c_max) ∧
        (∀ z ∈ A'_verts.filter (fun z => y ∈ Solo z), 1 ≤ (Solo z).card) := by
  intro B_verts Solo A'_verts q y hy
  have hy_nacc : ¬IsAccessible G ne.f ne.small (ne.f y) := (Finset.mem_filter.mp hy).2
  set acc_colors := Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)
  -- y has a neighbor in each accessible color class
  have h_has_nbr : ∀ c, IsAccessible G ne.f ne.small c → ∃ w, ne.f w = c ∧ G.Adj y w :=
    fun c hc => non_acc_has_acc_neighbor G hc hy_nacc
  -- Degree of y
  have h_deg_y : G.degree y ≤ r := le_trans (G.degree_le_maxDegree y) hd
  -- dB = non-accessible degree of y
  set dB := (B_verts.filter (fun w => G.Adj y w)).card
  have hq_pos : 1 ≤ q := Nat.sub_pos_of_lt (lt_of_lt_of_le (Finset.card_lt_card
    (Finset.filter_ssubset.mpr ⟨ne.large, Finset.mem_univ _, hacc⟩)) (by simp))
  -- dB ≤ q - 1
  have hdB_le : dB ≤ q - 1 := by
    have h_deg_y_acc : Finset.card (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)) ≥ Finset.card acc_colors := by
      have h_deg_y_acc : Finset.card (Finset.image (fun w => ne.f w) (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y))) ≥ Finset.card acc_colors := by
        refine' Finset.card_le_card _;
        intro c hc; obtain ⟨ w, rfl, hw ⟩ := h_has_nbr c ( Finset.mem_filter.mp hc |>.2 ) ; aesop;
      exact h_deg_y_acc.trans ( Finset.card_image_le );
    have h_deg_y_nonacc : Finset.card (Finset.filter (fun w => ¬IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)) ≥ dB := by
      exact Finset.card_mono fun x hx => by aesop;
    have h_deg_y_total : Finset.card (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)) + Finset.card (Finset.filter (fun w => ¬IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)) = G.degree y := by
      rw [ Finset.card_filter_add_card_filter_not, SimpleGraph.degree ];
    grind
  exact ⟨dB + 1, by omega, by omega,
    sy_card_lower_bound G r s hs hd hs0 ne hacc T hT_sub hT_card_gt_q h_bad y hy,
    solo_card_le_dB_plus_one G r s hs hd hs0 ne hacc T hT_sub h_bad y hy,
    fun z hz => Finset.card_pos.mpr ⟨y, (Finset.mem_filter.mp hz).2⟩⟩

/-- The non-accessible vertices have cardinality q*s + 1, expressed in terms of q -/
lemma non_acc_verts_card_q
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    (Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))).card =
    (r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card) * s + 1 := by
  have := ne.card_total;
  rw [ tsub_mul, mul_comm ];
  rw [ mul_comm, this.symm ];
  rw [ tsub_add_eq_add_tsub ];
  · rw [ Fintype.card_eq_sum_ones ];
    rw [ Finset.sum_const, Finset.card_eq_sum_ones ];
    rw [ show ( Finset.univ.filter fun v => ¬IsAccessible G ne.f ne.small ( ne.f v ) ) = Finset.biUnion ( Finset.univ.filter fun c => ¬IsAccessible G ne.f ne.small c ) ( fun c => Finset.filter ( fun v => ne.f v = c ) Finset.univ ) from ?_, Finset.sum_biUnion ];
    · have h_card : ∀ c : Fin (r + 1), (Finset.univ.filter (fun v => ne.f v = c)).card = if c = ne.small then s - 1 else if c = ne.large then s + 1 else s := by
        have := ne.card_small; have := ne.card_large; have := ne.card_other; aesop;
      simp_all +decide [ Finset.sum_ite ];
      simp +decide [ Finset.filter_eq', Finset.filter_ne' ];
      split_ifs <;> simp_all +decide
      · rw [ show ( Finset.univ.filter fun c => ¬IsAccessible G ne.f ne.small c ) = Finset.univ \ ( Finset.univ.filter fun c => IsAccessible G ne.f ne.small c ) by ext; simp +decide, Finset.card_sdiff ] ; simp +decide [ Finset.card_univ ];
        rw [ tsub_tsub, add_comm ];
        exact eq_tsub_of_add_eq ( by nlinarith only [ Nat.sub_add_cancel ( show ( Finset.card ( Finset.filter ( fun c => IsAccessible G ne.f ne.small c ) Finset.univ ) + 1 ) ≤ r + 1 from Nat.succ_le_of_lt ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.filter_ssubset.mpr ⟨ ne.large, by aesop ⟩ ) ) ( by simp +decide ) ) ) ] );
      · exact False.elim ( ‹¬IsAccessible G ne.f ne.small ne.small› ( Relation.ReflTransGen.refl ) );
      · exact absurd ‹_› ( ne.ne_small_large.symm );
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun v hvx hvy => hxy <| by aesop;
    · ext; aesop;
  · rw [ this ];
    exact Nat.mul_le_mul_right _ ( le_trans ( Finset.card_le_univ _ ) ( by simp +decide ) )

set_option maxHeartbeats 3200000 in
/-- Restricted weight argument: the weight function argument applied to a subset T
    of accessible classes (the terminal set). If every W ∈ T has the "bad property"
    (solo z has neighbor in every accessible class, special neighbors form clique),
    then the weight function on T-vertices vs B-vertices gives a contradiction.
    This is the core of Lemma 2.3 restricted to terminal classes. -/
lemma restricted_solo_weight_contradiction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (hT_ne_small : ∀ c ∈ T, c ≠ ne.small)
    (hT_ne_large : ∀ c ∈ T, c ≠ ne.large)
    (hT_nonempty : T.Nonempty)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂))
    (U : Fin (r + 1))
    (hU_acc : IsAccessible G ne.f ne.small U)
    (hU_not_T : U ∉ T)
    (h_not_mov_outside : ∀ W ∈ T, ∀ x : V, ne.f x = W →
      ∀ V_out : Fin (r + 1), IsAccessible G ne.f ne.small V_out →
      V_out ∉ T → V_out ≠ U →
      ∃ w, ne.f w = V_out ∧ G.Adj x w) :
    False := by
  -- Step 1: Setup
  set acc_colors := Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)
  set q := r + 1 - acc_colors.card
  set B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
  set Solo : V → Finset V := fun z =>
    B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
  set A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ T)
  -- Step 2: q ≥ 1
  have hq_ge_1 : 1 ≤ q := by
    exact Nat.sub_pos_of_lt (lt_of_lt_of_le (Finset.card_lt_card
      (Finset.filter_ssubset.mpr ⟨ne.large, Finset.mem_univ _, hacc⟩)) (by simp))
  -- Step 3: q < T.card
  have ht : q < T.card :=
    restricted_T_card_gt_q G r s hs hd hs0 ne hacc T hT_sub hT_ne_small hT_ne_large
      hT_nonempty h_bad U hU_acc hU_not_T h_not_mov_outside
  -- Step 4: A'_verts.card ≤ T.card * s
  have hA_card : A'_verts.card ≤ T.card * s := by
    -- By definition of $A'_verts$, we have $A'_verts = \bigcup_{c \in T} \{v \in V \mid ne.f v = c\}$.
    have hA'_verts_union : A'_verts = Finset.biUnion T (fun c => Finset.filter (fun v => ne.f v = c) Finset.univ) := by
      ext v; simp [A'_verts, Finset.mem_biUnion];
    rw [ hA'_verts_union, Finset.card_biUnion ];
    · refine' le_trans ( Finset.sum_le_sum fun x hx => show Finset.card ( Finset.filter ( fun v => ne.f v = x ) Finset.univ ) ≤ s from _ ) _;
      · exact ne.card_other x ( hT_ne_small x hx ) ( hT_ne_large x hx ) |> fun h => h.le;
      · simp +decide;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun v hvx hvy => hxy <| by aesop;
  -- Step 5: B_verts.card = q * s + 1
  have hB_card : B_verts.card = q * s + 1 := by
    exact non_acc_verts_card_q G r s hs ne hacc
  -- Step 6: Apply weight_function_contradiction
  exact weight_function_contradiction A'_verts B_verts Solo q T.card s hq_ge_1 ht hs0
    hA_card hB_card (fun z _ => Finset.filter_subset _ _)
    (fun z _ h => Finset.card_pos.mpr h)
    (restricted_Solo_card_le G r s hs hd hs0 ne hacc T hT_sub hT_ne_small hT_ne_large h_bad)
    (restricted_Solo_lower_bound G r s hs hd hs0 ne hacc T hT_sub ht h_bad)

set_option maxHeartbeats 3200000 in
/-- The weight argument restricted to the proper terminal set.
    When h_neg denies good solo vertices for terminal classes, we construct
    the minimal terminal set T_U and apply the restricted weight argument. -/
lemma terminal_weight_contradiction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (h_neg : ¬∃ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W ∧ W ≠ ne.small ∧ W ≠ ne.large ∧
      ne.f z = W ∧ ¬IsAccessible G ne.f ne.small (ne.f y₁) ∧
      G.Adj y₁ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) ∧
      (∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
        Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) ∧
      ((∃ X : Fin (r+1), X ≠ W ∧ IsAccessible G ne.f ne.small X ∧
        ∀ w, ne.f w = X → ¬G.Adj z w) ∨
       (∃ y₂ : V, y₂ ≠ y₁ ∧ ¬IsAccessible G ne.f ne.small (ne.f y₂) ∧
        G.Adj y₂ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) ∧
        ¬G.Adj y₁ y₂ ∧
        (∀ X : Fin (r+1), IsAccessible G ne.f ne.small X → X ≠ W →
          ∃ w, ne.f w = X ∧ G.Adj z w)))) :
    False := by
  -- Step 1: Extract bad property for terminal W from h_neg
  have h_bad_from_terminal : ∀ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W → W ≠ ne.small → W ≠ ne.large →
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
        Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂) := by
    intro W z y₁ hW_acc hW_ne_small hW_ne_large hz_color hy₁_nacc hadj huniq hW_term
    have h_not_movable : ∀ X, X ≠ W → IsAccessible G ne.f ne.small X →
        ∃ w, ne.f w = X ∧ G.Adj z w := by
      intro X hXW hXacc
      by_contra h_no_nbr; push Not at h_no_nbr
      exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc,
        hadj, huniq, hW_term, Or.inl ⟨X, hXW, hXacc, fun w hw => by
          exact fun hadj_zw => (h_no_nbr w hw).elim hadj_zw⟩⟩
    refine ⟨h_not_movable, ?_⟩
    intro y₂ hy₂_ne hy₂_nacc hy₂_adj hy₂_uniq
    by_contra h_not_adj
    exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc,
      hadj, huniq, hW_term,
      Or.inr ⟨y₂, hy₂_ne, hy₂_nacc, hy₂_adj, hy₂_uniq, h_not_adj,
        fun X hXacc hXW => h_not_movable X hXW hXacc⟩⟩
  -- Step 2: Get W from good_solo_vertex_exists (W will be non-terminal)
  obtain ⟨W₀, z₀, y₁₀, hW₀_acc, hW₀_ne_small, hW₀_ne_large, hz₀, hy₁₀_nacc,
    hadj₀, huniq₀, hcases₀⟩ := good_solo_vertex_exists G r s hs hd hs0 ne hacc
  -- W₀ is non-terminal since h_neg denies terminal W with good solo vertex
  have hW₀_nonterm : ¬∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W₀ →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W₀) C ne.small := by
    intro h; exact h_neg ⟨W₀, z₀, y₁₀, hW₀_acc, hW₀_ne_small, hW₀_ne_large, hz₀,
      hy₁₀_nacc, hadj₀, huniq₀, h, hcases₀⟩
  push Not at hW₀_nonterm
  obtain ⟨C₀, hC₀_acc, hC₀_ne_W₀, hC₀_cant⟩ := hW₀_nonterm
  -- Step 3: Construct T_{W₀} and find minimal non-terminal U
  set R := AuxAdj G ne.f with hR_def
  set acc_colors := Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)
  -- Define terminal set for a given non-terminal U
  let T_of (U : Fin (r + 1)) := acc_colors.filter (fun c => c ≠ U ∧
    ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) c ne.small)
  -- W₀ is non-terminal: T_of W₀ is nonempty (contains C₀)
  have hC₀_in : C₀ ∈ T_of W₀ :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC₀_acc⟩,
      hC₀_ne_W₀, hC₀_cant⟩
  -- The set of non-terminal accessible classes
  set NonTerm := acc_colors.filter (fun U => (T_of U).Nonempty) with hNonTerm_def
  have hW₀_nonterm' : W₀ ∈ NonTerm := by
    simp only [NonTerm, Finset.mem_filter]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW₀_acc⟩, ⟨C₀, hC₀_in⟩⟩
  -- Find U ∈ NonTerm minimizing |T_of U|
  obtain ⟨U, hU_mem, hU_min⟩ := NonTerm.exists_min_image (fun U => (T_of U).card)
    ⟨W₀, hW₀_nonterm'⟩
  have hU_acc : IsAccessible G ne.f ne.small U := by
    have := (Finset.mem_filter.mp hU_mem).1; exact (Finset.mem_filter.mp this).2
  have hU_nonterm_T : (T_of U).Nonempty := (Finset.mem_filter.mp hU_mem).2
  set T := T_of U with hT_def
  -- Step 4: T members are terminal (by terminal_set_members_are_terminal and minimality)
  have hT_terminal : ∀ W ∈ T, ∀ C : Fin (r + 1),
      IsAccessible G ne.f ne.small C → C ≠ W →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small := by
    intro W hW C hC_acc hC_ne
    have hU_nonterm_witness : ∃ C ∈ acc_colors, C ≠ U ∧
        ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) C ne.small := by
      obtain ⟨c₀, hc₀⟩ := hU_nonterm_T
      exact ⟨c₀, (Finset.mem_filter.mp hc₀).1,
        (Finset.mem_filter.mp hc₀).2.1, (Finset.mem_filter.mp hc₀).2.2⟩
    have hT_min : ∀ V ∈ acc_colors,
        (∃ C ∈ acc_colors, C ≠ V ∧
          ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ V) C ne.small) →
        T.card ≤ (acc_colors.filter (fun c => c ≠ V ∧
          ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ V) c ne.small)).card := by
      intro V hV hV_nonterm
      have hV_nonterm_T : (T_of V).Nonempty := by
        obtain ⟨C', hC'_acc, hC'_ne, hC'_cant⟩ := hV_nonterm
        exact ⟨C', Finset.mem_filter.mpr ⟨hC'_acc, hC'_ne, hC'_cant⟩⟩
      exact hU_min V (Finset.mem_filter.mpr ⟨hV, hV_nonterm_T⟩)
    exact terminal_set_members_are_terminal R ne.small acc_colors
      (fun c hc => (Finset.mem_filter.mp hc).2) U
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU_acc⟩)
      hU_nonterm_witness T rfl hT_min W hW C
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC_acc⟩) hC_ne
  -- T members are accessible, ≠ small, ≠ large
  have hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c := by
    intro c hc; exact (Finset.mem_filter.mp ((Finset.mem_filter.mp hc).1)).2
  have hT_ne_small : ∀ c ∈ T, c ≠ ne.small := by
    intro c hc habs; subst habs
    exact (Finset.mem_filter.mp hc).2.2 Relation.ReflTransGen.refl
  have hT_ne_large : ∀ c ∈ T, c ≠ ne.large := by
    intro c hc habs; subst habs; exact hacc ((Finset.mem_filter.mp ((Finset.mem_filter.mp hc).1)).2)
  -- Step 5: Bad property for T members
  have h_T_bad : ∀ W ∈ T, ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂) := by
    intro W hW z y₁ hz hy₁ hadj huniq
    exact h_bad_from_terminal W z y₁ (hT_sub W hW) (hT_ne_small W hW) (hT_ne_large W hW)
      hz hy₁ hadj huniq (hT_terminal W hW)
  -- Step 6: Non-movability from T to accessible classes outside T ∪ {U}
  have h_not_mov : ∀ W ∈ T, ∀ x : V, ne.f x = W →
      ∀ V_out : Fin (r + 1), IsAccessible G ne.f ne.small V_out →
      V_out ∉ T → V_out ≠ U →
      ∃ w, ne.f w = V_out ∧ G.Adj x w := by
    intro W hW x hx V_out hV_out_acc hV_out_not_T hV_out_ne_U
    -- If x had no neighbor in V_out, then AuxAdj(W, V_out)
    -- V_out can reach ne.small without U (since V_out ∉ T)
    -- So W could reach ne.small without U via V_out, contradicting W ∈ T
    by_contra h_no_nbr
    push Not at h_no_nbr
    have h_aux : AuxAdj G ne.f W V_out := ⟨x, hx, fun w hw => h_no_nbr w hw⟩
    have hW_props := (Finset.mem_filter.mp hW).2
    apply hW_props.2
    have hV_out_reach : Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) V_out ne.small := by
      have hV_out_in_acc : V_out ∈ acc_colors :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV_out_acc⟩
      have hV_not_T : V_out ∉ T := hV_out_not_T
      by_contra h_cant
      apply hV_not_T
      exact Finset.mem_filter.mpr ⟨hV_out_in_acc, hV_out_ne_U, h_cant⟩
    exact Relation.ReflTransGen.head ⟨h_aux, hW_props.1⟩ hV_out_reach
  -- Step 7: U ∉ T
  have hU_not_T : U ∉ T := by
    intro habs; exact (Finset.mem_filter.mp habs).2.1 rfl
  -- Apply restricted weight argument
  exact restricted_solo_weight_contradiction G r s hs hd hs0 ne hacc
    T hT_sub hT_ne_small hT_ne_large hU_nonterm_T h_T_bad U hU_acc hU_not_T h_not_mov

set_option maxHeartbeats 800000 in
/-- If there exists a terminal accessible class W_t (≠ small, ≠ large) such that
    no good solo vertex exists for W_t (i.e., h_neg denies the full existential
    with terminal property), then solo_weight_contradiction gives False.
    The key: h_neg gives the "bad" property for W_t (as proved by by_contra),
    and the edge counting for W_t's class versus B_verts gives contradiction. -/
lemma no_terminal_good_solo_contradiction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (W_t : Fin (r + 1))
    (_hWt_acc : IsAccessible G ne.f ne.small W_t)
    (_hWt_ne_small : W_t ≠ ne.small)
    (_hWt_terminal : ∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W_t →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W_t) C ne.small)
    (h_neg : ¬∃ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W ∧ W ≠ ne.small ∧ W ≠ ne.large ∧
      ne.f z = W ∧ ¬IsAccessible G ne.f ne.small (ne.f y₁) ∧
      G.Adj y₁ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) ∧
      (∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
        Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) ∧
      ((∃ X : Fin (r+1), X ≠ W ∧ IsAccessible G ne.f ne.small X ∧
        ∀ w, ne.f w = X → ¬G.Adj z w) ∨
       (∃ y₂ : V, y₂ ≠ y₁ ∧ ¬IsAccessible G ne.f ne.small (ne.f y₂) ∧
        G.Adj y₂ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) ∧
        ¬G.Adj y₁ y₂ ∧
        (∀ X : Fin (r+1), IsAccessible G ne.f ne.small X → X ≠ W →
          ∃ w, ne.f w = X ∧ G.Adj z w)))) :
    False := by
  -- Case split: are ALL accessible ≠ small ≠ large classes terminal?
  by_cases h_all_term : ∀ W : Fin (r + 1),
    IsAccessible G ne.f ne.small W → W ≠ ne.small → W ≠ ne.large →
    ∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small
  · -- All accessible ≠ small ≠ large are terminal.
    -- From h_neg, derive h_all_bad for ALL W, then use solo_weight_contradiction.
    apply solo_weight_contradiction G r s hs hd hs0 ne hacc
    intro W z y₁ hW_acc hW_ne_small hW_ne_large hz_color hy₁_nacc hadj huniq
    -- W is terminal by h_all_term
    have hW_term := h_all_term W hW_acc hW_ne_small hW_ne_large
    -- h_neg denies good solo vertex for terminal W
    -- First show z is not movable
    have h_not_movable : ∀ X, X ≠ W → IsAccessible G ne.f ne.small X →
        ∃ w, ne.f w = X ∧ G.Adj z w := by
      intro X hXW hXacc
      by_contra h_no
      push Not at h_no
      exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc, hadj, huniq,
        hW_term, Or.inl ⟨X, hXW, hXacc, fun w hw => h_no w hw⟩⟩
    refine ⟨h_not_movable, fun y₂ hy₂_ne hy₂_nacc hy₂_adj hy₂_uniq => ?_⟩
    by_contra h_not_adj
    exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc, hadj, huniq,
      hW_term, Or.inr ⟨y₂, hy₂_ne, hy₂_nacc, hy₂_adj, hy₂_uniq, h_not_adj,
        fun X hXacc hXW => h_not_movable X hXW hXacc⟩⟩
  · -- Some accessible W ≠ small ≠ large is NOT terminal.
    -- Directly apply the weight argument on the proper terminal set.
    push Not at h_all_term
    obtain ⟨U, hU_acc, hU_ne_small, hU_ne_large, C₀, hC₀_acc, hC₀_ne_U, hC₀_cant⟩ := h_all_term
    -- Derive False using the proper terminal set construction + weight argument.
    -- This is the content of the paper's Lemma 2.3 restricted to terminal classes.
    exact terminal_weight_contradiction G r s hs hd hs0 ne hacc h_neg

/-- Strengthened version of good_solo_vertex_exists that also guarantees
    the terminal property of W: every other accessible color can reach
    ne.small without passing through W. -/
lemma good_solo_vertex_exists_terminal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    ∃ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W ∧
      W ≠ ne.small ∧ W ≠ ne.large ∧
      ne.f z = W ∧
      ¬IsAccessible G ne.f ne.small (ne.f y₁) ∧
      G.Adj y₁ z ∧
      (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) ∧
      -- Terminal property of W
      (∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
        Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) ∧
      -- Either Case 1 or Case 2
      ((∃ X : Fin (r+1), X ≠ W ∧ IsAccessible G ne.f ne.small X ∧
        ∀ w, ne.f w = X → ¬G.Adj z w) ∨
       (∃ y₂ : V, y₂ ≠ y₁ ∧ ¬IsAccessible G ne.f ne.small (ne.f y₂) ∧
        G.Adj y₂ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) ∧
        ¬G.Adj y₁ y₂ ∧
        (∀ X : Fin (r+1), IsAccessible G ne.f ne.small X → X ≠ W →
          ∃ w, ne.f w = X ∧ G.Adj z w))) := by
  -- Use good_solo_vertex_exists (without terminal) and check if W is terminal
  obtain ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc,
    hadj_y₁_z, huniq_y₁, hcases⟩ :=
    good_solo_vertex_exists G r s hs hd hs0 ne hacc
  -- If W is already terminal, we're done
  by_cases hW_term : ∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small
  · exact ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc,
      hadj_y₁_z, huniq_y₁, hW_term, hcases⟩
  · -- W is NOT terminal. Use the weight argument restricted to terminal classes.
    -- By contradiction: assume no terminal W has good solo vertex.
    by_contra h_neg
    -- Since W is accessible and not terminal, all accessible ≠ small classes
    -- can't ALL be terminal. But we have at least one terminal class (from exists_terminal_color).
    obtain ⟨W_t, hWt_acc, hWt_ne_small, hWt_terminal⟩ :=
      exists_terminal_color G (r + 1) ne.f ne.small W hW_acc hW_ne_small
    apply solo_weight_contradiction G r s hs hd hs0 ne hacc
    intro W' z' y₁' hW'_acc hW'_ne_small hW'_ne_large hz'_color hy₁'_nacc hadj' huniq'
    -- Show bad property for W'
    have h_bad_part1 : ∀ X, X ≠ W' → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z' w := by
      intro X hXW' hXacc
      by_contra h_no
      -- z' is movable to X, giving Case 1 for W'
      -- If W' is terminal: h_neg gives contradiction
      -- If W' is non-terminal: use terminal_set_members_are_terminal
      push Not at h_no
      -- z' has no neighbor in X, so z' witnesses AuxAdj(W', X)
      -- We need to show W' is terminal to use h_neg
      -- Use the terminal set construction:
      -- If W' is terminal, directly get contradiction from h_neg
      by_cases hW'_term : ∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W' →
          Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W') C ne.small
      · exact h_neg ⟨W', z', y₁', hW'_acc, hW'_ne_small, hW'_ne_large, hz'_color,
          hy₁'_nacc, hadj', huniq', hW'_term,
          Or.inl ⟨X, hXW', hXacc, fun w hw hadj_zw => h_no w hw |>.elim hadj_zw⟩⟩
      · -- W' is non-terminal. Use terminal set construction to derive contradiction.
        exfalso
        -- W_t is terminal. From h_neg: W_t has bad property.
        -- Edge counting on W_t gives contradiction (when s ≥ 2).
        -- For s = 1: hacc is impossible (empty small class makes all accessible).
        exact no_terminal_good_solo_contradiction G r s hs hd hs0 ne hacc
          W_t hWt_acc hWt_ne_small hWt_terminal h_neg
    refine ⟨h_bad_part1, ?_⟩
    · -- Part 2: Clique property
      intro y₂' hy₂'_ne hy₂'_nacc hy₂'_adj hy₂'_uniq
      by_contra h_not_adj
      -- z' is not movable (from h_bad_part1) and y₁', y₂' are nonadjacent
      by_cases hW'_term : ∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W' →
          Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W') C ne.small
      · -- W' terminal: Case 2 contradicts h_neg
        exact h_neg ⟨W', z', y₁', hW'_acc, hW'_ne_small, hW'_ne_large, hz'_color,
          hy₁'_nacc, hadj', huniq', hW'_term,
          Or.inr ⟨y₂', hy₂'_ne, hy₂'_nacc, hy₂'_adj, hy₂'_uniq, h_not_adj,
            fun X hXacc hXW' => h_bad_part1 X hXW' hXacc⟩⟩
      · -- W' non-terminal: same argument as above
        exact no_terminal_good_solo_contradiction G r s hs hd hs0 ne hacc
          W_t hWt_acc hWt_ne_small hWt_terminal h_neg

omit [DecidableEq V] in
/-- Combining two equitable colorings on complementary sets into one equitable coloring
    of the whole graph. The two parts use disjoint ranges of Fin (a+b). -/
lemma combine_disjoint_equitable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A_set : Set V) [DecidablePred (· ∈ A_set)]
    (a b s_val : ℕ)
    (hA_card : Fintype.card ↥A_set = a * s_val)
    (hB_card : Fintype.card ↥(A_setᶜ) = b * s_val)
    (fA : ↥A_set → Fin a) (fB : ↥(A_setᶜ) → Fin b)
    (hfA_proper : IsProper (G.induce A_set) fA)
    (hfB_proper : IsProper (G.induce A_setᶜ) fB)
    (hfA_equitable : IsEquitable fA)
    (hfB_equitable : IsEquitable fB) :
    HasEquitableColoring G (a + b) := by
  use fun v => if h : v ∈ A_set then Fin.castAdd b ( fA ⟨ v, h ⟩ ) else Fin.natAdd a ( fB ⟨ v, by simpa using h ⟩ );
  refine' ⟨ fun v w hvw => _, fun c₁ c₂ => _ ⟩;
  · by_cases hv : v ∈ A_set <;> by_cases hw : w ∈ A_set <;> simp +decide [ hv, hw ];
    · exact hfA_proper _ _ ( by simpa [ hv, hw ] using hvw );
    · simp +decide [ Fin.ext_iff ];
      grind;
    · simp +decide [ Fin.ext_iff ];
      grind;
    · exact hfB_proper _ _ ( by simpa [ hv, hw ] using hvw );
  · -- By definition of $f$, we know that every vertex in $A_set$ is assigned a color from $\{0, 1, ..., a-1\}$ and every vertex in $A_setᶜ$ is assigned a color from $\{a, a+1, ..., a+b-1\}$.
    have h_classes : ∀ c : Fin (a + b), (cClass (fun v => if h : v ∈ A_set then Fin.castAdd b (fA ⟨v, h⟩) else Fin.natAdd a (fB ⟨v, by simpa using h⟩)) c).card = if h : c.val < a then (cClass fA ⟨c.val, by
      exact h⟩).card else (cClass fB ⟨c.val - a, by
      rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt c ]⟩).card := by
      intro c; split_ifs <;> simp_all +decide [ cClass ] ;
      · refine' Finset.card_bij ( fun v hv => ⟨ v, _ ⟩ ) _ _ _ <;> simp_all +decide [ Fin.ext_iff ];
        grind +locals;
        grind +splitImp;
      · rw [ Finset.card_filter, Finset.card_filter ];
        rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.filter ( fun x => x∉A_set ) Finset.univ ) ) ];
        · refine' Finset.sum_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ Fin.ext_iff ];
          grind;
        · grind
    generalize_proofs at *;
    -- By definition of $fA$ and $fB$, we know that every vertex in $A_set$ is assigned a color from $\{0, 1, ..., a-1\}$ and every vertex in $A_setᶜ$ is assigned a color from $\{a, a+1, ..., a+b-1\}$.
    have h_classes_fA : ∀ c : Fin a, (cClass fA c).card = s_val := by
      apply equitable_all_same_size hfA_equitable hA_card
    have h_classes_fB : ∀ c : Fin b, (cClass fB c).card = s_val := by
      apply equitable_all_same_size hfB_equitable hB_card
    generalize_proofs at *;
    grind +ring

/-! ### Cardinality lemmas for the non-accessible partition -/

/-- The non-accessible vertices have cardinality q*s + 1 -/
lemma non_acc_verts_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    (Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))).card =
    (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)).card * s + 1 := by
  have h_sum : ∑ c ∈ Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c), (cClass ne.f c).card = (Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c)).card * s + 1 := by
    have h_sum : ∑ c ∈ Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c), (cClass ne.f c).card = ∑ c ∈ Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c), (if c = ne.large then s + 1 else s) := by
      refine' Finset.sum_congr rfl fun c hc => _;
      split_ifs <;> simp_all +decide;
      · exact ne.card_large;
      · exact ne.card_other c ( by rintro rfl; exact hc ( Relation.ReflTransGen.refl ) ) ( by assumption );
    simp_all +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq' ];
    nlinarith only [ Nat.sub_add_cancel ( show 1 ≤ Finset.card ( Finset.filter ( fun c => ¬IsAccessible G ne.f ne.small c ) Finset.univ ) from Finset.card_pos.mpr ⟨ ne.large, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hacc ⟩ ⟩ ) ];
  rw [ ← h_sum, eq_comm ];
  rw [ ← Finset.card_biUnion ];
  · congr with v ; aesop;
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz hz' => hxy <| by aesop;

/-- Non-accessible vertices minus one have cardinality q*s -/
lemma non_acc_verts_minus_one_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (y₁ : V) (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁)) :
    ((Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))).erase y₁).card =
    (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)).card * s := by
  rw [ Finset.card_erase_of_mem ];
  · convert Nat.sub_eq_of_eq_add <| non_acc_verts_card G r s hs ne hacc using 1;
  · aesop

/-- Degree bound: a non-accessible vertex has at most q-1 neighbors in the non-accessible set -/
lemma non_acc_degree_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r)
    (ne : NearlyEquitable G (r + 1) s)
    (_hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (S : Finset V)
    (hS : S ⊆ Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v)))
    (v : V) (hv : v ∈ S) :
    (S.filter (fun w => G.Adj v w)).card ≤
    (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)).card - 1 := by
  -- Since v is in S, ne.f v is a non-accessible color.
  have hv_nonacc : ¬IsAccessible G ne.f ne.small (ne.f v) := by
    simpa using hS hv;
  -- Since v has at least m+1 neighbors with accessible colors, there are at least m+1 vertices in S that are not adjacent to v.
  have hv_acc_neighbors : Finset.card (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset v)) ≥ (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)).card := by
    have hv_acc_neighbors : Finset.card (Finset.image (fun w => ne.f w) (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset v))) ≥ (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)).card := by
      refine Finset.card_le_card ?_;
      intro c hc; have := non_acc_has_acc_neighbor G ( show IsAccessible G ne.f ne.small c from by simpa using hc ) hv_nonacc; aesop;
    exact hv_acc_neighbors.trans ( Finset.card_image_le );
  -- Since v has at least m+1 neighbors with accessible colors, there are at most r - (m+1) neighbors of v in S.
  have hv_neighbors_S : Finset.card (Finset.filter (fun w => G.Adj v w) S) + Finset.card (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset v)) ≤ G.degree v := by
    rw [ ← Finset.card_union_of_disjoint ];
    · exact Finset.card_le_card fun x hx => by aesop;
    · simp_all +decide [ Finset.disjoint_left ];
      exact fun w hw hw' => Finset.mem_filter.mp ( hS hw ) |>.2;
  have hv_deg : G.degree v ≤ r := by
    exact le_trans ( SimpleGraph.degree_le_maxDegree _ _ ) hd;
  have hv_card : Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) + Finset.card (Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c)) = r + 1 := by
    rw [ Finset.card_filter_add_card_filter_not, Finset.card_fin ];
  exact le_tsub_of_add_le_left ( by linarith )

/-! ### Equitable coloring of B⁻ (non-accessible vertices minus y₁) -/

set_option maxHeartbeats 6400000 in
/-- The non-accessible part minus y₁, as a subgraph, has an equitable q-coloring. -/
lemma B_minus_equitable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (_hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (ih_primary : ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (r' : ℕ),
      Fintype.card W < Fintype.card V →
      H.maxDegree ≤ r' → (r' + 1) ∣ Fintype.card W →
      HasEquitableColoring H (r' + 1))
    (y₁ : V) (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁)) :
    let B_minus : Set V := {v | ¬IsAccessible G ne.f ne.small (ne.f v) ∧ v ≠ y₁}
    let q := (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)).card
    HasEquitableColoring (G.induce B_minus) q := by
  revert ih_primary;
  intro ih
  set B_minus := {v : V | ¬IsAccessible G ne.f ne.small (ne.f v) ∧ v ≠ y₁}
  set q := (Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c)).card
  have hB_minus_card : Fintype.card B_minus = q * s := by
    convert non_acc_verts_minus_one_card G r s hs ne hacc y₁ hy₁_nacc using 1;
    rw [ Fintype.card_of_subtype ] ; aesop
  have h_ind : HasEquitableColoring (G.induce B_minus) q := by
    have h_ind : (G.induce B_minus).maxDegree ≤ q - 1 := by
      have h_ind : ∀ v : B_minus, (G.induce B_minus).degree v ≤ q - 1 := by
        intro v
        have h_deg_le : (Finset.univ.filter (fun w => G.Adj v w ∧ w ∈ B_minus)).card ≤ q - 1 := by
          have h_deg_le : (Finset.univ.filter (fun w => G.Adj v.val w ∧ ¬IsAccessible G ne.f ne.small (ne.f w))).card ≤ q - 1 := by
            convert non_acc_degree_bound G r s hs hd ne hacc ( Finset.univ.filter fun w => ¬IsAccessible G ne.f ne.small ( ne.f w ) ) _ v.val _ using 1;
            · exact congr_arg Finset.card ( by ext; aesop );
            · exact fun x hx => hx;
            · aesop;
          exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_deg_le
        have hsub :
            ((G.induce B_minus).neighborFinset v).map (.subtype (· ∈ B_minus)) ⊆
              Finset.univ.filter (fun w : V => G.Adj v w ∧ w ∈ B_minus) := by
          intro w hw
          simpa [SimpleGraph.map_neighborFinset_induce, SimpleGraph.mem_neighborFinset] using hw
        calc
          (G.induce B_minus).degree v =
              (((G.induce B_minus).neighborFinset v).map (.subtype (· ∈ B_minus))).card := by
            rw [SimpleGraph.degree]
            exact (Finset.card_map (s := (G.induce B_minus).neighborFinset v)
              (.subtype (· ∈ B_minus))).symm
          _ ≤ (Finset.univ.filter (fun w : V => G.Adj v w ∧ w ∈ B_minus)).card :=
            Finset.card_le_card hsub
          _ ≤ q - 1 := h_deg_le
      exact SimpleGraph.maxDegree_le_of_forall_degree_le _ _ h_ind
    by_cases hq : q = 0;
    · simp_all +decide [ Finset.ext_iff ];
      contrapose! hB_minus_card;
      simp +zetaDelta at *;
      grind;
    · have h_card_lt : Fintype.card B_minus < Fintype.card V := by
        rw [ Fintype.card_subtype ] ; exact Finset.card_lt_card ( Finset.filter_ssubset.mpr ⟨ y₁, by aesop ⟩ ) ;
      have h_dvd : q ∣ Fintype.card B_minus := by
        rw [hB_minus_card]
        exact dvd_mul_right q s
      let Hfin : SimpleGraph (Fin (Fintype.card B_minus)) :=
        (G.induce B_minus).overFin rfl
      let efin : G.induce B_minus ≃g Hfin :=
        (G.induce B_minus).overFinIso rfl
      haveI : DecidableRel Hfin.Adj := by
        dsimp [Hfin, SimpleGraph.overFin]
        infer_instance
      let W := ULift (Fin (Fintype.card B_minus))
      let H : SimpleGraph W :=
        Hfin.comap ((Equiv.ulift : W ≃ Fin (Fintype.card B_minus)).toEmbedding)
      let e : H ≃g Hfin :=
        SimpleGraph.Iso.comap
          (Equiv.ulift : W ≃ Fin (Fintype.card B_minus)) Hfin
      haveI : DecidableRel H.Adj := by
        dsimp [H]
        infer_instance
      have h_card_W : Fintype.card W = Fintype.card B_minus := by
        simp [W]
      have h_card_lt_lift : Fintype.card W < Fintype.card V := by
        rw [h_card_W]
        exact h_card_lt
      have h_ind_fin : Hfin.maxDegree ≤ q - 1 := by
        rwa [← efin.maxDegree_eq]
      have h_ind_lift : H.maxDegree ≤ q - 1 := by
        rwa [e.maxDegree_eq]
      have h_dvd_lift : q ∣ Fintype.card W := by
        rw [h_card_W]
        exact h_dvd
      have h_dvd_lift' : (q - 1 + 1) ∣ Fintype.card W := by
        simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)] using h_dvd_lift
      have h_col_H : HasEquitableColoring H q := by
        simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)]
          using ih W H (q - 1)
            h_card_lt_lift h_ind_lift h_dvd_lift'
      have h_col_Hfin : HasEquitableColoring Hfin q :=
        hasEquitableColoring_of_iso e h_col_H
      exact hasEquitableColoring_of_iso efin.symm h_col_Hfin
  exact h_ind

/-! ### Equitable coloring of A⁺ (accessible vertices plus y₁) -/

/-
Transfer a single AuxAdj step from the original graph to the induced A_plus subgraph.
    When c, d are accessible colors ≠ W_col, and AuxAdj G ne.f c d holds,
    the witness v has accessible color c (so v ∈ A_plus, v ≠ z, v ≠ y₁),
    and no d-colored neighbor changes in A_plus (since z maps to X, y₁ maps to W_col,
    neither equals c or d which are ≠ W_col).
-/
lemma auxadj_transfer_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (ne : NearlyEquitable G (r + 1) s)
    (W_col : Fin (r + 1)) (z y₁ : V) (X : Fin (r + 1))
    (hz_color : ne.f z = W_col)
    (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (_hXW : X ≠ W_col)
    (A_plus : Set V)
    (hA_def : A_plus = {v | IsAccessible G ne.f ne.small (ne.f v) ∨ v = y₁})
    (g : V → Fin (r + 1))
    (hg_def : g = fun v => if v = z then X else if v = y₁ then W_col else ne.f v)
    (φ : {c : Fin (r + 1) // IsAccessible G ne.f ne.small c} ≃ Fin m1)
    (hg_acc : ∀ v : V, v ∈ A_plus → IsAccessible G ne.f ne.small (g v))
    (f_A : ↥A_plus → Fin m1)
    (hf_def : f_A = fun v => φ ⟨g v.val, hg_acc v.val v.prop⟩)
    (c d : Fin (r + 1))
    (hc_acc : IsAccessible G ne.f ne.small c)
    (hd_acc : IsAccessible G ne.f ne.small d)
    (hc_ne_W : c ≠ W_col)
    (hd_ne_W : d ≠ W_col)
    (hd_ne_X : d ≠ X)
    (hadj_cd : AuxAdj G ne.f c d) :
    AuxAdj (G.induce A_plus) f_A (φ ⟨c, hc_acc⟩) (φ ⟨d, hd_acc⟩) := by
  obtain ⟨ v, hv, hv' ⟩ := hadj_cd;
  refine' ⟨ ⟨ v, _ ⟩, _, _ ⟩ <;> simp_all +decide;
  · grind;
  · grind

set_option maxHeartbeats 1600000 in
/-- The accessible part plus y₁, as a subgraph, has an equitable m1-coloring.
    This is the key construction that requires re-indexing colors via a bijection
    from the accessible colors to Fin m1, constructing a NearlyEquitable on the
    induced subgraph, and applying accessible_large_gives_equitable. -/
lemma A_plus_equitable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (_hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (W_col : Fin (r + 1)) (z y₁ : V)
    (hW_acc : IsAccessible G ne.f ne.small W_col)
    (hW_ne_small : W_col ≠ ne.small)
    (hW_ne_large : W_col ≠ ne.large)
    (hz_color : ne.f z = W_col)
    (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (hadj_y₁_z : G.Adj y₁ z)
    (huniq_y₁ : ∀ (w : V), ne.f w = W_col → w ≠ z → ¬G.Adj y₁ w)
    -- For Case 1: z is movable to X
    (X : Fin (r + 1))
    (hXW : X ≠ W_col)
    (hXacc : IsAccessible G ne.f ne.small X)
    (hXmov : ∀ (w : V), ne.f w = X → ¬G.Adj z w)
    -- Terminal property: every other accessible color can reach ne.small without W
    (hW_terminal : ∀ C : Fin (r + 1),
      IsAccessible G ne.f ne.small C → C ≠ W_col →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W_col) C ne.small) :
    let A_plus : Set V := {v | IsAccessible G ne.f ne.small (ne.f v) ∨ v = y₁}
    let m1 := (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card
    HasEquitableColoring (G.induce A_plus) m1 := by
  intro A_plus m1
  -- Preliminary facts
  have hz_ne_y₁ : z ≠ y₁ := by
    intro h; subst h; exact hy₁_nacc (hz_color ▸ hW_acc)
  have hy₁_ne_z : y₁ ≠ z := fun h => hz_ne_y₁ h.symm
  have hy₁_ne_W : ne.f y₁ ≠ W_col := by
    intro h; exact hy₁_nacc (h ▸ hW_acc)
  -- Define the bijection from accessible colors to Fin m1
  set accType := {c : Fin (r + 1) // IsAccessible G ne.f ne.small c}
  have hm1_eq : Fintype.card accType = m1 := by
    simp [m1, accType, Fintype.card_subtype]
  set φ : accType ≃ Fin m1 := (Fintype.equivFin accType).trans (finCongr hm1_eq)
  -- The swap coloring on V
  set g : V → Fin (r + 1) := fun v =>
    if v = z then X else if v = y₁ then W_col else ne.f v
  -- For v ∈ A_plus, g(v) is accessible
  have hg_acc : ∀ v : V, v ∈ A_plus → IsAccessible G ne.f ne.small (g v) := by
    intro v hv; simp only [g]
    split_ifs with h1 h2
    · exact hXacc
    · exact hW_acc
    · exact hv.resolve_right h2
  -- Define f_A : ↥A_plus → Fin m1
  set f_A : ↥A_plus → Fin m1 := fun v => φ ⟨g v.val, hg_acc v.val v.prop⟩
  have hX_ne_fy₁ : X ≠ ne.f y₁ := by
    intro h; exact hy₁_nacc (h ▸ hXacc)
  -- f_A is proper
  have hproper : IsProper (G.induce A_plus) f_A := by
    intro u v huv h_eq
    have hg_eq : g u.val = g v.val := by
      simpa [f_A] using congr_arg Subtype.val (φ.injective h_eq)
    by_cases huz : u.val = z
    · by_cases hvz : v.val = z
      · exact huv.ne (Subtype.ext (by simpa [huz, hvz]))
      · by_cases hvy : v.val = y₁
        · have hXW' : X = W_col := by
            simpa [g, huz, hvz, hvy, hy₁_ne_z] using hg_eq
          exact hXW hXW'
        · have hv_color : ne.f v.val = X := by
            simpa [g, huz, hvz, hvy] using hg_eq.symm
          exact hXmov v.val hv_color (by simpa [huz] using huv)
    · by_cases hvz : v.val = z
      · by_cases huy : u.val = y₁
        · have hXW' : W_col = X := by
            simpa [g, huz, hvz, huy, hy₁_ne_z] using hg_eq
          exact hXW hXW'.symm
        · have hu_color : ne.f u.val = X := by
            simpa [g, huz, hvz, huy] using hg_eq
          exact hXmov u.val hu_color (by simpa [hvz] using huv.symm)
      · by_cases huy : u.val = y₁
        · by_cases hvy : v.val = y₁
          · exact huv.ne (Subtype.ext (by simpa [huy, hvy]))
          · have hv_color : ne.f v.val = W_col := by
              simpa [g, huz, hvz, huy, hvy, hy₁_ne_z] using hg_eq.symm
            exact huniq_y₁ v.val hv_color hvz (by simpa [huy] using huv)
        · by_cases hvy : v.val = y₁
          · have hu_color : ne.f u.val = W_col := by
              simpa [g, huz, hvz, huy, hvy, hy₁_ne_z] using hg_eq
            exact huniq_y₁ u.val hu_color huz (by simpa [hvy] using huv.symm)
          · have h_ne_f_eq : ne.f u.val = ne.f v.val := by
              simpa [g, huz, hvz, huy, hvy] using hg_eq
            exact ne.proper u.val v.val huv h_ne_f_eq
  -- Handle by cases on X = ne.small
  by_cases hX_eq : X = ne.small
  · -- X = ne.small: all classes have size s, directly equitable
    refine ⟨f_A, hproper, ?_⟩
    intro c₁ c₂
    -- All classes have size s because:
    -- Each accessible color c maps to φ(c).
    -- Class φ(c) contains exactly the vertices in A_plus whose g-value is c.
    -- After the swap: each accessible class has size s.
    -- For any color $c$ in the accessible set, the size of the class in $A_plus$ is $s$.
    have h_class_size : ∀ c : { c : Fin (r + 1) // IsAccessible G ne.f ne.small c }, #(cClass f_A (φ c)) = s := by
      intro c
      have h_card : #(cClass f_A (φ c)) = #(cClass g (c.val)) := by
        refine' Finset.card_bij ( fun x hx => x.val ) _ _ _ <;> simp +decide [ cClass ];
        · aesop;
        · grind;
      by_cases hc : c.val = ne.small <;> by_cases hc' : c.val = W_col <;> simp_all +decide [ cClass ];
      · have h_card : #(cClass ne.f ne.small) = s - 1 := by
          exact ne.card_small;
        rw [ show ( Finset.filter ( fun v => g v = ne.small ) Finset.univ : Finset V ) = Finset.filter ( fun v => ne.f v = ne.small ) Finset.univ ∪ { z } from ?_, Finset.card_union ] <;> simp_all +decide ;
        · exact h_card.symm ▸ Nat.succ_pred_eq_of_pos hs0;
        · ext v; by_cases hv : v = z <;> by_cases hv' : v = y₁ <;> simp +decide [ hv, hv' ] ;
          · grind +revert;
          · grind +ring;
          · grind;
          · grind +ring;
      · rw [ show ( Finset.filter ( fun v => g v = W_col ) Finset.univ ) = { y₁ } ∪ ( Finset.filter ( fun v => ne.f v = W_col ) Finset.univ \ { z } ) from ?_, Finset.card_union ] <;> simp +decide [ *, Finset.card_sdiff ];
        · rw [ add_tsub_cancel_of_le ];
          · exact ne.card_other _ ( by aesop ) ( by aesop );
          · exact Finset.card_pos.mpr ⟨ z, by aesop ⟩;
        · grind;
      · convert ne.card_other c.val hc ( show c.val ≠ ne.large from ?_ ) using 1;
        · congr with v ; aesop;
        · exact fun h => hacc <| h ▸ c.2;
    rw [ show cClass f_A c₁ = cClass f_A ( φ ( φ.symm c₁ ) ) by simp +decide, show cClass f_A c₂ = cClass f_A ( φ ( φ.symm c₂ ) ) by simp +decide, h_class_size, h_class_size ] ; linarith
  · -- X ≠ ne.small: construct NearlyEquitable and use accessibility
    have hne_small_acc : IsAccessible G ne.f ne.small ne.small := Relation.ReflTransGen.refl
    set small_idx := φ ⟨ne.small, hne_small_acc⟩
    set large_idx := φ ⟨X, hXacc⟩
    have hne_sl : small_idx ≠ large_idx := by
      intro h
      exact hX_eq (Subtype.ext_iff.mp (φ.injective h)).symm
    have card_small : (cClass f_A small_idx).card = s - 1 := by
      convert ne.card_small using 1;
      refine' Finset.card_bij ( fun v hv => v ) _ _ _ <;> simp +decide ;
      · simp +zetaDelta at *;
        grind +ring;
      · grind
    have card_large : (cClass f_A large_idx).card = s + 1 := by
      -- The cardinality of the color class of large_idx in f_A is 1 (for z) plus the cardinality of {v ∈ A_plus | ne.f v = X}, which is s. So the total is 1 + s = s + 1.
      have card_large : (cClass f_A large_idx).card = 1 + (Finset.univ.filter (fun v => ne.f v = X ∧ v ∈ A_plus)).card := by
        have card_large : (cClass f_A large_idx).card = (Finset.filter (fun v => v.val = z) (Finset.univ : Finset ↑A_plus)).card + (Finset.filter (fun v => v.val ≠ z ∧ g v.val = X) (Finset.univ : Finset ↑A_plus)).card := by
          rw [ ← Finset.card_union_of_disjoint ];
          · refine' congr_arg Finset.card ( Finset.ext fun x => _ );
            simp +decide [ cClass, f_A, large_idx ];
            grind;
          · exact Finset.disjoint_filter.mpr ( by aesop );
        convert card_large using 2;
        · rw [ Finset.card_eq_one.mpr ];
          use ⟨z, by
            exact Or.inl ( by simpa [ hz_color ] using hW_acc )⟩
          generalize_proofs at *;
          grind +revert;
        · rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; congr ; ext ; simp +decide [ g ] ;
          grind +ring;
      have := ne.card_other X ( by tauto ) ; simp_all +decide ;
      rw [ add_comm, show ( Finset.univ.filter fun v => ne.f v = X ∧ v ∈ A_plus ) = Finset.univ.filter fun v => ne.f v = X from ?_, Finset.card_filter ] ; simp_all +decide;
      · convert this ( by rintro rfl; exact hacc hXacc ) using 1;
      · grind
    have card_other : ∀ c, c ≠ small_idx → c ≠ large_idx → (cClass f_A c).card = s := by
      -- Let $a$ be the accessible color that $\varphi$ maps to $c$.
      intro c hc_ne_small hc_ne_large
      obtain ⟨a, ha⟩ : ∃ a : accType, φ a = c := by
        exact φ.surjective c;
      by_cases haW : a.val = W_col;
      · have h_card_fA_W : (cClass f_A c).card = (Finset.univ.filter (fun v => ne.f v = W_col ∧ v ≠ z ∧ v ≠ y₁)).card + 1 := by
          have h_card_fA_W : (cClass f_A c).card = (Finset.univ.filter (fun v : A_plus => g v = W_col)).card := by
            refine' Finset.card_bij ( fun v hv => v ) _ _ _ <;> simp +decide;
            · intro v hv hv'; have := φ.injective ( hv'.trans ha.symm ) ; aesop;
            · grind;
          rw [ h_card_fA_W, show ( Finset.filter ( fun v : A_plus => g v = W_col ) Finset.univ ) = Finset.filter ( fun v : A_plus => ne.f v = W_col ∧ v ≠ z ∧ v ≠ y₁ ) Finset.univ ∪ { ⟨ y₁, Or.inr rfl ⟩ } from ?_, Finset.card_union ] <;> simp +decide [ *, Finset.filter_ne', Finset.filter_and ];
          · rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; congr ; ext ; simp +decide [ * ] ;
            exact fun _ _ _ => Or.inl <| by aesop;
          · ext ⟨v, hv⟩; simp [g];
            grind +ring;
        have h_card_fA_W : (Finset.univ.filter (fun v => ne.f v = W_col ∧ v ≠ z ∧ v ≠ y₁)).card = (Finset.univ.filter (fun v => ne.f v = W_col)).card - 1 := by
          rw [ show ( Finset.filter ( fun v => ne.f v = W_col ∧ v ≠ z ∧ v ≠ y₁ ) Finset.univ ) = Finset.filter ( fun v => ne.f v = W_col ) Finset.univ \ { z } from ?_, Finset.card_sdiff ] <;> simp +decide [ * ];
          grind;
        have := ne.card_other W_col hW_ne_small hW_ne_large; simp_all +decide [ cClass ] ;
        rw [ Nat.sub_add_cancel hs0 ];
      · convert ne.card_other a.val _ _ using 1;
        · refine' Finset.card_bij ( fun v hv => v.val ) _ _ _ <;> simp +decide [ cClass ];
          · intro v hv hv'; replace hv' := congr_arg φ.symm hv'; aesop;
          · grind;
        · grind;
        · exact fun h => hacc <| h ▸ a.2
    have card_total : Fintype.card ↥A_plus = m1 * s := by
      have hA_plus_card : (Finset.univ.filter (fun v => IsAccessible G ne.f ne.small (ne.f v))).card = m1 * s - 1 := by
        have hA_plus_card : (Finset.univ.filter (fun v => IsAccessible G ne.f ne.small (ne.f v))).card = (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)).card * s - 1 := by
          have := non_acc_verts_card G r s hs ne hacc
          simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
          exact eq_tsub_of_add_eq ( by nlinarith only [ this, Nat.sub_add_cancel ( show ( r + 1 ) * s ≥ Finset.card ( Finset.filter ( fun v => IsAccessible G ne.f ne.small ( ne.f v ) ) Finset.univ ) from Finset.card_le_univ _ |> le_trans <| by simp +decide [ hs ] ), Nat.sub_add_cancel ( show ( r + 1 ) ≥ Finset.card ( Finset.filter ( fun c => IsAccessible G ne.f ne.small c ) Finset.univ ) from Finset.card_le_univ _ |> le_trans <| by simp +decide ) ] );
        exact hA_plus_card;
      rw [ Fintype.card_subtype ];
      rw [ show ( Finset.filter ( Membership.mem A_plus ) Finset.univ : Finset V ) = Finset.filter ( fun v => IsAccessible G ne.f ne.small ( ne.f v ) ) Finset.univ ∪ { y₁ } from ?_, Finset.card_union ] <;> simp +decide [ * ];
      · have hm1_pos : 0 < m1 := by
          dsimp [m1]
          exact Finset.card_pos.mpr ⟨ne.small,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩⟩
        rw [ Nat.sub_add_cancel ( Nat.succ_le_of_lt (Nat.mul_pos hm1_pos hs0) ) ]
      · ext v; simp [A_plus];
        grind
    set ne_A : NearlyEquitable (G.induce A_plus) m1 s :=
      ⟨f_A, hproper, small_idx, large_idx, hne_sl, card_small, card_large, card_other, card_total⟩
    -- Prove accessibility by transferring the chain from the original graph
    -- Key: use nodup chain + auxadj_transfer_step
    have h_transfer : ∀ c : Fin (r + 1),
        (hc_acc : IsAccessible G ne.f ne.small c) →
        c ≠ W_col →
        Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W_col ∧ d ≠ X) c ne.small →
        Relation.ReflTransGen (AuxAdj (G.induce A_plus) f_A) (φ ⟨c, hc_acc⟩) small_idx := by
      have h_ind : ∀ (c d : Fin (r + 1)) (hc_acc : IsAccessible G ne.f ne.small c) (hd_acc : IsAccessible G ne.f ne.small d) (hc_ne_W : c ≠ W_col) (hd_ne_W : d ≠ W_col) (hd_ne_X : d ≠ X) (hadj_cd : AuxAdj G ne.f c d), AuxAdj (induce A_plus G) f_A (φ ⟨c, hc_acc⟩) (φ ⟨d, hd_acc⟩) := by
        intros c d hc_acc hd_acc hc_ne_W hd_ne_W hd_ne_X hadj_cd
        apply auxadj_transfer_step G r ne W_col z y₁ X hz_color hy₁_nacc hXW A_plus rfl g rfl φ hg_acc f_A rfl c d hc_acc hd_acc hc_ne_W hd_ne_W hd_ne_X hadj_cd;
      have h_ind : ∀ (c d : Fin (r + 1)) (hc_acc : IsAccessible G ne.f ne.small c) (hd_acc : IsAccessible G ne.f ne.small d) (hc_ne_W : c ≠ W_col) (hd_ne_W : d ≠ W_col) (hd_ne_X : d ≠ X), Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W_col ∧ d ≠ X) c d → Relation.ReflTransGen (AuxAdj (induce A_plus G) f_A) (φ ⟨c, hc_acc⟩) (φ ⟨d, hd_acc⟩) := by
        intros c d hc_acc hd_acc hc_ne_W hd_ne_W hd_ne_X hc_chain
        induction' hc_chain with c d hc hd ih
        all_goals generalize_proofs at *;
        · exact Relation.ReflTransGen.refl;
        · have h_ind : Relation.ReflTransGen (AuxAdj (induce A_plus G) f_A) (φ ⟨c, by
            contrapose! h_ind; simp_all +decide [ IsAccessible ] ;
            exact False.elim ( h_ind ( by exact Relation.ReflTransGen.head hd.1 ( by tauto ) ) )⟩) (φ ⟨d, hd_acc⟩) := by
            all_goals generalize_proofs at *;
            exact .single ( h_ind c d ‹_› ‹_› hd.2.1 hd_ne_W hd_ne_X hd.1 )
          generalize_proofs at *; (
          grind +extAll);
      grind
    -- Now extract nodup chain and show it avoids X in targets
    have hacc_X : IsAccessible (G.induce A_plus) f_A small_idx large_idx := by
      have hchain_orig := hW_terminal X hXacc hXW
      obtain ⟨l, hnodup, hchain, hhead, hlast, hlen⟩ :=
        exists_nodup_chain hchain_orig hX_eq
      -- The nodup chain avoids X in all tail elements
      -- Each tail element d has d ≠ X since l.Nodup and X = head
      -- Strengthen the chain to include d ≠ X
      contrapose! h_transfer;
      refine' ⟨ X, hXacc, hXW, _, _ ⟩;
      · refine' hchain_orig.recOn _ _;
        · rfl;
        · grind;
      · exact Not.imp h_transfer fun a => a
    exact accessible_large_gives_equitable (G.induce A_plus) m1 s ne_A hacc_X

/-! ### Case 1 and Case 2 helper lemmas -/

set_option maxHeartbeats 1600000 in
/-- Case 1: z is movable to accessible class X.
    We add ih (secondary induction) to the hypotheses since we may need it. -/
lemma non_accessible_case1
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (ih_primary : ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (r' : ℕ),
      Fintype.card W < Fintype.card V →
      H.maxDegree ≤ r' → (r' + 1) ∣ Fintype.card W →
      HasEquitableColoring H (r' + 1))
    (_q_val : ℕ)
    (W : Fin (r + 1)) (z y₁ : V)
    (hW_acc : IsAccessible G ne.f ne.small W)
    (hW_ne_small : W ≠ ne.small)
    (hW_ne_large : W ≠ ne.large)
    (hz_color : ne.f z = W)
    (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (hadj_y₁_z : G.Adj y₁ z)
    (huniq_y₁ : ∀ (w : V), ne.f w = W → w ≠ z → ¬G.Adj y₁ w)
    (X : Fin (r + 1))
    (hXW : X ≠ W)
    (hXacc : IsAccessible G ne.f ne.small X)
    (hXmov : ∀ (w : V), ne.f w = X → ¬G.Adj z w)
    -- Terminal property of W
    (hW_terminal : ∀ C : Fin (r + 1),
      IsAccessible G ne.f ne.small C → C ≠ W →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) :
    HasEquitableColoring G (r + 1) := by
  set A_plus := {v : V | IsAccessible G ne.f ne.small (ne.f v) ∨ v = y₁}
  set B_minus := {v : V | ¬IsAccessible G ne.f ne.small (ne.f v) ∧ v ≠ y₁};
  have hA_plus_card : Fintype.card A_plus = (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card * s := by
    have hA_plus_card : Fintype.card A_plus = Fintype.card V - Fintype.card B_minus := by
      rw [ Fintype.card_subtype, Fintype.card_subtype ];
      rw [ tsub_eq_of_eq_add_rev ];
      rw [ Fintype.card_eq_sum_ones, Finset.card_filter, Finset.card_filter ];
      rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ] ; aesop;
    have hB_minus_card' : Fintype.card B_minus =
        (Finset.univ.filter (fun c : Fin (r + 1) =>
          ¬IsAccessible G ne.f ne.small c)).card * s := by
      convert non_acc_verts_minus_one_card G r s hs ne hacc y₁ hy₁_nacc using 1;
      rw [ Fintype.card_of_subtype ] ; aesop;
    have h_card_sum' :
        (Finset.univ.filter (fun c : Fin (r + 1) =>
          IsAccessible G ne.f ne.small c)).card +
        (Finset.univ.filter (fun c : Fin (r + 1) =>
          ¬IsAccessible G ne.f ne.small c)).card = r + 1 := by
      rw [ Finset.card_filter_add_card_filter_not, Finset.card_fin ];
    have hmul :
        (r + 1) * s =
          (Finset.univ.filter (fun c : Fin (r + 1) =>
            IsAccessible G ne.f ne.small c)).card * s +
          (Finset.univ.filter (fun c : Fin (r + 1) =>
            ¬IsAccessible G ne.f ne.small c)).card * s := by
      calc
        (r + 1) * s =
            ((Finset.univ.filter (fun c : Fin (r + 1) =>
              IsAccessible G ne.f ne.small c)).card +
            (Finset.univ.filter (fun c : Fin (r + 1) =>
              ¬IsAccessible G ne.f ne.small c)).card) * s := by
          exact (congr_arg (fun n => n * s) h_card_sum').symm
        _ =
            (Finset.univ.filter (fun c : Fin (r + 1) =>
              IsAccessible G ne.f ne.small c)).card * s +
            (Finset.univ.filter (fun c : Fin (r + 1) =>
              ¬IsAccessible G ne.f ne.small c)).card * s := by
          rw [Nat.add_mul]
    rw [hA_plus_card, hs, hB_minus_card', hmul, Nat.add_sub_cancel_right]
  have hB_minus_card : Fintype.card B_minus = (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)).card * s := by
    convert non_acc_verts_minus_one_card G r s hs ne hacc y₁ hy₁_nacc using 1;
    rw [ Fintype.card_of_subtype ] ; aesop;
  have hA_plus_equitable : HasEquitableColoring (G.induce A_plus) (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c))) := by
    apply_rules [ A_plus_equitable ]
  have hB_minus_equitable : HasEquitableColoring (G.induce B_minus) (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c))) := by
    apply B_minus_equitable G r s hs hd hs0 ne hacc ih_primary y₁ hy₁_nacc;
  have h_card_sum : (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c))) + (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c))) = r + 1 := by
    rw [ Finset.card_filter_add_card_filter_not, Finset.card_fin ];
  have := @combine_disjoint_equitable V _ G;
  specialize this A_plus (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c))) (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c))) s hA_plus_card ?_;
  · simpa [Set.compl_setOf, A_plus, B_minus] using hB_minus_card
  · obtain ⟨ fA, hfA_proper, hfA_equitable ⟩ := hA_plus_equitable
    obtain ⟨ fB, hfB_proper, hfB_equitable ⟩ := hB_minus_equitable
    specialize this fA (fun v => fB ⟨v, by
      grind⟩) hfA_proper (by
    exact fun v w hvw => hfB_proper _ _ hvw) hfA_equitable (by
    intro c₁ c₂; exact (by
    convert hfB_equitable c₁ c₂ using 1;
    · refine' Finset.card_bij ( fun x hx => ⟨ x, by
        grind ⟩ ) _ _ _ <;> simp +decide [ cClass ];
      grind;
    · refine' congr_arg₂ _ ( Finset.card_bij ( fun x hx => ⟨ x, by
        grind ⟩ ) _ _ _ ) rfl
      all_goals generalize_proofs at *;
      · simp +decide [ cClass ];
      · grind;
      · exact fun b hb => ⟨ ⟨ b, by
          exact fun h => b.2.1 <| h.resolve_right b.2.2 ⟩, by
          grind +locals, rfl ⟩));
    rwa [ h_card_sum ] at this

lemma transGen_exists_ne_first_step {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) (hne : a ≠ b) :
    ∃ c, c ≠ a ∧ r a c ∧ Relation.ReflTransGen r c b := by
  induction' h with a b c h ih;
  · exact ⟨ a, Ne.symm hne, b, by rfl ⟩;
  · by_cases hac : a = c <;> simp_all +decide;
    · grind;
    · obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := ‹∃ d, ¬d = a ∧ r a d ∧ Relation.ReflTransGen r d c›; exact ⟨ d, hd₁, hd₂, hd₃.tail ‹_› ⟩ ;

set_option maxHeartbeats 6400000 in
/-- **Paper's Case 2**: When z is not movable to any accessible class and has
    two nonadjacent solo neighbors y₁, y₂, we construct a new NearlyEquitable
    coloring with fewer non-accessible classes by:
    - recoloring B⁻ via primary induction (equitable q-coloring)
    - adding z to a class with no z-neighbor
    - moving y₁ to W (which z vacated) -/
lemma non_accessible_case2_paper
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (ih_primary : ∀ (W : Type*) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj] (r' : ℕ),
        Fintype.card W < Fintype.card V →
        H.maxDegree ≤ r' → (r' + 1) ∣ Fintype.card W →
        HasEquitableColoring H (r' + 1))
    (q_val : ℕ)
    (ih : ∀ (ne' : NearlyEquitable G (r + 1) s),
      (Finset.univ.filter (fun c : Fin (r + 1) =>
        ¬IsAccessible G ne'.f ne'.small c)).card ≤ q_val →
      HasEquitableColoring G (r + 1))
    (hq' : (Finset.univ.filter (fun c : Fin (r + 1) =>
        ¬IsAccessible G ne.f ne.small c)).card ≤ q_val + 1)
    (W : Fin (r + 1)) (z y₁ y₂ : V)
    (hW_acc : IsAccessible G ne.f ne.small W)
    (hW_ne_small : W ≠ ne.small)
    (hW_ne_large : W ≠ ne.large)
    (hz_color : ne.f z = W)
    (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (hadj_y₁_z : G.Adj y₁ z)
    (huniq_y₁ : ∀ (w : V), ne.f w = W → w ≠ z → ¬G.Adj y₁ w)
    (hy₂ne : y₂ ≠ y₁)
    (hy₂nacc : ¬IsAccessible G ne.f ne.small (ne.f y₂))
    (hy₂adj : G.Adj y₂ z)
    (hy₂uniq : ∀ (w : V), ne.f w = W → w ≠ z → ¬G.Adj y₂ w)
    (hnonadj : ¬G.Adj y₁ y₂)
    (hnotmov : ∀ (X : Fin (r + 1)),
      IsAccessible G ne.f ne.small X → X ≠ W → ∃ w, ne.f w = X ∧ G.Adj z w)
    (hW_terminal : ∀ C : Fin (r + 1),
      IsAccessible G ne.f ne.small C → C ≠ W →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) :
    HasEquitableColoring G (r + 1) := by
  /-
  Paper's Case 2 proof (Kierstead-Kostochka, Theorem 2.4):
  1. Use B_minus_equitable to get equitable q-coloring g of G[B⁻]
  2. z has ≤ q-1 neighbors in B⁻ → z joins class Y of g
  3. Construct new NearlyEquitable coloring, show count drops
  4. Apply secondary induction
  -/
  -- === Step 1: Key sets and constants ===
  set nacc_colors := Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)
    with nacc_colors_def
  set q_nacc := nacc_colors.card with hq_nacc_def
  -- B_minus as a Set V (matching B_minus_equitable's definition)
  set B_minus_set : Set V := {v | ¬IsAccessible G ne.f ne.small (ne.f v) ∧ v ≠ y₁} with hBms_def
  -- B_minus as a Finset V (for counting)
  let B_minus := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v) ∧ v ≠ y₁)
  -- === Step 2: Get equitable q-coloring of G[B⁻] via existing lemma ===
  obtain ⟨g, hg_proper, hg_equitable⟩ : HasEquitableColoring (G.induce B_minus_set) q_nacc :=
    B_minus_equitable G r s hs hd hs0 ne hacc ih_primary y₁ hy₁_nacc
  -- === Step 3: Basic facts ===
  have hsmall_acc : IsAccessible G ne.f ne.small ne.small := Relation.ReflTransGen.refl
  have hnacc_pos : 0 < q_nacc := by
    exact Finset.card_pos.mpr ⟨ne.large, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc⟩⟩
  have hB_card : Fintype.card ↥B_minus_set = q_nacc * s := by
    convert non_acc_verts_minus_one_card G r s hs ne hacc y₁ hy₁_nacc using 1
    rw [Fintype.card_of_subtype]; aesop
  have hg_class_size : ∀ c : Fin q_nacc, (cClass g c).card = s :=
    equitable_all_same_size hg_equitable hB_card
  -- z is NOT in B_minus_set (z has accessible color W)
  have hz_not_in_B : z ∉ B_minus_set := by
    simp only [B_minus_set, Set.mem_setOf_eq, not_and]
    intro hnacc; exact absurd (hz_color ▸ hW_acc) hnacc
  -- y₂ IS in B_minus_set
  have hy₂_in_B : y₂ ∈ B_minus_set := by
    simp [B_minus_set]; exact ⟨hy₂nacc, hy₂ne⟩
  -- === Step 4: z has ≤ q-1 neighbors in B_minus → pigeonhole ===
  -- z has ≥ acc_colors.card neighbors in A⁺ = A ∪ {y₁}
  -- (m from hnotmov + 1 from y₁), so ≤ q-1 in B⁻
  have hz_B_deg : (B_minus.filter (fun w => G.Adj z w)).card ≤ q_nacc - 1 := by
    have hzacc_adj : Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)))) ≥ Finset.card (Finset.filter (fun c => IsAccessible G ne.f ne.small c) Finset.univ) - 1 := by
      have hzacc_adj : Finset.card (Finset.image ne.f (Finset.filter (fun w => G.Adj z w) (Finset.univ.filter (fun w => IsAccessible G ne.f ne.small (ne.f w))))) ≥ Finset.card (Finset.filter (fun c => IsAccessible G ne.f ne.small c) Finset.univ) - 1 := by
        have hzacc_adj : Finset.image ne.f (Finset.filter (fun w => G.Adj z w) (Finset.univ.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)))) ⊇ Finset.filter (fun c => IsAccessible G ne.f ne.small c) Finset.univ \ {W} := by
          grind;
        exact le_trans ( by rw [ Finset.card_sdiff ] ; aesop ) ( Finset.card_mono hzacc_adj );
      exact hzacc_adj.trans ( Finset.card_image_le );
    have hzacc_adj : Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)))) + Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ.filter (fun w => ¬IsAccessible G ne.f ne.small (ne.f w)))) ≤ r := by
      rw [ ← Finset.card_union_of_disjoint ];
      · have hzacc_adj : Finset.card (Finset.filter (fun w => G.Adj z w) Finset.univ) ≤ r := by
          convert hd.trans' ( G.degree_le_maxDegree z ) using 1;
          exact congr_arg Finset.card ( by ext; simp +decide );
        convert hzacc_adj using 2 ; ext w ; by_cases hw : IsAccessible G ne.f ne.small ( ne.f w ) <;> simp +decide [ hw ];
      · exact Finset.disjoint_left.mpr ( by aesop );
    have hzacc_adj : Finset.card (Finset.filter (fun c => IsAccessible G ne.f ne.small c) Finset.univ) + Finset.card (Finset.filter (fun c => ¬IsAccessible G ne.f ne.small c) Finset.univ) = r + 1 := by
      rw [ Finset.card_filter_add_card_filter_not, Finset.card_fin ];
    have hzacc_adj : Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ.filter (fun w => ¬IsAccessible G ne.f ne.small (ne.f w)))) ≥ Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ.filter (fun w => ¬IsAccessible G ne.f ne.small (ne.f w) ∧ w ≠ y₁))) + 1 := by
      refine' Finset.card_lt_card _;
      simp +decide [ Finset.ssubset_def, Finset.subset_iff ];
      exact ⟨ fun x hx₁ hx₂ hx₃ => ⟨ hx₁, hx₃ ⟩, y₁, hy₁_nacc, hadj_y₁_z.symm, by tauto ⟩;
    grind
  -- Pigeonhole: z can join some class Y of g
  have ⟨Y, hY_no_z_nbr⟩ : ∃ Y : Fin q_nacc,
      ∀ w : ↥B_minus_set, g w = Y → ¬G.Adj z w.val := by
    contrapose! hz_B_deg;
    choose f hf using hz_B_deg;
    refine' lt_of_lt_of_le _ ( Finset.card_le_card _ );
    any_goals exact Finset.image ( fun Y => ( f Y : V ) ) Finset.univ;
    · rw [ Finset.card_image_of_injective _ fun x y hxy => _ ] <;> simp_all +decide [ Fin.ext_iff ];
      grind;
    · simp +decide [ Finset.subset_iff, hf ];
      exact fun Y => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, f Y |>.2 ⟩
  -- === Step 5: Construct bijection φ : Fin q_nacc → non-accessible colors ===
  let φ_equiv := nacc_colors.equivFin
  let φ : Fin q_nacc → Fin (r + 1) := fun i => (φ_equiv.symm i).val
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    exact φ_equiv.symm.injective (Subtype.val_injective hab)
  have hφ_nacc : ∀ i, ¬IsAccessible G ne.f ne.small (φ i) := by
    intro i; exact (Finset.mem_filter.mp (φ_equiv.symm i).prop).2
  have hφ_ne_W : ∀ i, φ i ≠ W := fun i h => hφ_nacc i (h ▸ hW_acc)
  -- === Step 6: Define new coloring f' ===
  -- f'(y₁) = W, f'(v) = φ(g(v)) for v ∈ B⁻, f'(z) = φ(Y), else ne.f(v)
  let f' : V → Fin (r + 1) := fun v =>
    if v = y₁ then W
    else if hv : v ∈ B_minus_set then φ (g ⟨v, hv⟩)
    else if v = z then φ Y
    else ne.f v
  -- === Step 7: Show f' is proper ===
  have hf'_proper_paper : IsProper G f' := by
    intro u v huv;
    by_cases hu : u = y₁ <;> by_cases hv : v = y₁ <;> simp +decide [ hu, hv ] at huv ⊢;
    · grind;
    · simp +zetaDelta at *;
      split_ifs <;> simp_all +decide;
      (expose_names; exact Ne.intro fun a => huniq_y₁ u a h_1 (id (adj_symm G huv)));
    · by_cases huB : u ∈ B_minus_set <;> by_cases hvB : v ∈ B_minus_set <;> simp +decide [ huB, hvB, f' ] at huv ⊢;
      · have := hg_proper ⟨ u, huB ⟩ ⟨ v, hvB ⟩ ; simp_all +decide [ IsProper ] ;
        exact hφ_inj.ne this;
      · split_ifs <;> simp_all +decide [ IsProper ];
        · intro h; have := hφ_inj h; simp_all +decide ;
          exact hY_no_z_nbr u huB.1 huB.2 this huv.symm;
        · grind;
      · split_ifs <;> simp_all +decide [ IsProper ];
        · exact hφ_inj.ne ( by specialize hY_no_z_nbr v hvB.1 hvB.2; aesop );
        · exact fun h => hφ_nacc _ ( h ▸ huB );
      · by_cases huZ : u = z <;> by_cases hvZ : v = z <;> simp +decide [ hu, hv, huZ, hvZ ] at huB hvB ⊢;
        · exact huv.ne ( huZ.trans hvZ.symm );
        · grind +revert;
        · split_ifs <;> simp_all +decide [ SimpleGraph.adj_comm ];
          exact fun h => hφ_nacc Y <| h ▸ huB;
        · exact ne.proper u v huv
  have hf'_proper := hf'_proper_paper
  -- === Step 8: Show class sizes ===
  have hf'_small : (cClass f' ne.small).card = s - 1 := by
    have h_card_small_f'_eq : (cClass f' ne.small) = (cClass ne.f ne.small) \ {y₁} := by
      ext v; simp [f', cClass];
      grind +revert;
    have := ne.card_small; simp_all +decide [ Finset.card_sdiff ] ;
    by_cases hy₁ : ne.f y₁ = ne.small <;> simp_all +decide [ cClass ]
  have hf'_large : (cClass f' (φ Y)).card = s + 1 := by
    have hf'_phi_Y : cClass f' (φ Y) = Finset.image (fun w : B_minus_set => w.val) (cClass g Y) ∪ {z} := by
      ext v;
      simp +decide [ cClass ];
      simp +zetaDelta at *;
      split_ifs <;> simp +decide [ * ];
      · grind;
      · grind;
      · grind +splitIndPred;
    rw [ hf'_phi_Y, Finset.card_union ] ; simp +decide [ *, Finset.card_image_of_injective, Function.Injective ]
  have hf'_other : ∀ c, c ≠ ne.small → c ≠ φ Y → (cClass f' c).card = s := by
    intro c hc_ne_small hc_ne_Y
    by_cases hc_acc : IsAccessible G ne.f ne.small c;
    · by_cases hc_eq_W : c = W;
      · subst hc_eq_W;
        -- Since $c$ is accessible, the color class of $c$ in $f'$ is the same as in $ne.f$, which has size $s$.
        have h_color_class_c : cClass f' c = {y₁} ∪ (cClass ne.f c \ {z}) := by
          ext v; simp [f', cClass];
          by_cases hv : v = z <;> simp +decide [ hv, hz_color ];
          · grind;
          · by_cases hv : v ∈ B_minus_set <;> simp +decide [ hv, hφ_ne_W ];
            · exact fun h => False.elim ( hv.1 ( h ▸ hc_acc ) );
            · grind +ring;
        rw [ h_color_class_c, Finset.card_union_of_disjoint ] <;> simp +decide [ *, Finset.disjoint_singleton_left ];
        · rw [ Finset.card_sdiff ] ; simp +decide [ * ];
          rw [ ne.card_other _ hW_ne_small hW_ne_large, add_tsub_cancel_of_le ( Nat.succ_le_of_lt hs0 ) ];
        · grind +ring;
      · convert ne.card_other c hc_ne_small ( show c ≠ ne.large from _ ) using 1;
        · refine' Finset.card_bij ( fun v hv => v ) _ _ _ <;> simp +decide [ * ];
          · grind;
          · grind +revert;
        · exact fun h => hacc <| h ▸ hc_acc;
    · -- Since $c$ is not accessible, there exists $i$ such that $\phi(i) = c$.
      obtain ⟨i, hi⟩ : ∃ i : Fin q_nacc, φ i = c := by
        exact ⟨ φ_equiv ⟨ c, by aesop ⟩, by aesop ⟩;
      -- Since $c = \phi(i)$, the color class of $c$ under $f'$ is the same as the color class of $i$ under $g$.
      have hc_class_eq : cClass f' c = Finset.image (fun w : B_minus_set => w.val) (cClass g i) := by
        ext v; simp [f'];
        split_ifs <;> simp +decide [ ← hi, hφ_inj.eq_iff ];
        · exact iff_of_false ( Ne.symm ( hφ_ne_W i ) ) ( by aesop );
        · exact ⟨ fun h => ⟨ by assumption, h ⟩, fun ⟨ _, h ⟩ => h ⟩;
        · grind;
        · contrapose! hc_acc; aesop;
      rw [ hc_class_eq, Finset.card_image_of_injective _ fun x y hxy => by simpa [ Subtype.ext_iff ] using hxy, hg_class_size ]
  have hf'_small_ne_large : ne.small ≠ φ Y :=
    Ne.symm (fun h => hφ_nacc Y (h ▸ hsmall_acc))
  -- === Step 9: Build NearlyEquitable and apply secondary IH ===
  set ne' : NearlyEquitable G (r + 1) s :=
    ⟨f', hf'_proper, ne.small, φ Y, hf'_small_ne_large, hf'_small, hf'_large, hf'_other, hs⟩
  apply ih ne'
  show (Finset.univ.filter (fun c : Fin (r + 1) =>
      ¬IsAccessible G ne'.f ne'.small c)).card ≤ q_val
  -- KEY CLAIM: accessible colors under ne.f remain accessible under f'
  -- Helper: f' agrees with ne.f for accessible-colored vertices not y₁ or z
  have hf'_eq_acc : ∀ v, IsAccessible G ne.f ne.small (ne.f v) → v ≠ y₁ → v ≠ z →
      f' v = ne.f v := by
    -- Since v is accessible, it cannot be in B_minus_set, so the second condition (hv : v ∈ B_minus_set) is false.
    intros v hv_acc hv_ne_y₁ hv_ne_z
    simp [f', hv_ne_y₁, hv_ne_z];
    exact fun h => False.elim <| h.1 hv_acc
  -- Helper: color class c is unchanged under f' when c is accessible and c ≠ W
  have hcClass_eq_acc : ∀ c, IsAccessible G ne.f ne.small c → c ≠ W →
      cClass f' c = cClass ne.f c := by
    intro c hc hcW
    ext v
    simp [cClass];
    grind
  -- Helper: AuxAdj preserved for accessible colors ≠ W
  have hAuxAdj_pres : ∀ c d, AuxAdj G ne.f c d → c ≠ W → d ≠ W →
      IsAccessible G ne.f ne.small c → IsAccessible G ne.f ne.small d →
      AuxAdj G f' c d := by
    intros c d hcd hcW hdW hc hd
    simp [AuxAdj] at hcd ⊢;
    obtain ⟨ v, hv₁, hv₂ ⟩ := hcd;
    use v;
    grind
  -- Stronger AuxAdj preservation: only need d ≠ W (not c ≠ W)
  have hAuxAdj_pres2 : ∀ c d, AuxAdj G ne.f c d →
      IsAccessible G ne.f ne.small c → IsAccessible G ne.f ne.small d → d ≠ W →
      AuxAdj G f' c d := by
    intros c d hcd hc hd hd_ne_W;
    obtain ⟨ v, hv₁, hv₂ ⟩ := hcd;
    use v;
    grind +ring
  -- Non-W accessible preserved under f'
  have hacc_not_W : ∀ c, IsAccessible G ne.f ne.small c → c ≠ W →
      IsAccessible G f' ne.small c := by
    intro c hc hcW
    have h_path : Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) c ne.small := by
      exact hW_terminal c hc hcW;
    have h_path_f' : ∀ c d, Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) c d → IsAccessible G ne.f ne.small c → IsAccessible G ne.f ne.small d → d ≠ W → Relation.ReflTransGen (AuxAdj G f') c d := by
      intros c d h_path hc hd hdW
      induction' h_path with c d hcd ih;
      · exact Relation.ReflTransGen.refl;
      · rename_i h;
        exact Relation.ReflTransGen.trans ( h ( by
          exact Relation.ReflTransGen.head ( ih.1 ) ( by tauto ) ) ih.2 ) ( Relation.ReflTransGen.single ( hAuxAdj_pres2 _ _ ih.1 ( by
          exact Relation.ReflTransGen.head ( ih.1 ) ( by tauto ) ) hd hdW ) );
    exact h_path_f' c ne.small h_path hc ( by exact Relation.ReflTransGen.refl ) ( by tauto )
  -- W accessible under f'
  have hacc_W : IsAccessible G f' ne.small W := by
    have hW_trans : Relation.TransGen (AuxAdj G ne.f) W ne.small :=
      (Relation.reflTransGen_iff_eq_or_transGen.mp hW_acc).resolve_left (Ne.symm hW_ne_small)
    obtain ⟨d, hd_ne_W, hd_adj, hd_path⟩ := transGen_exists_ne_first_step hW_trans hW_ne_small
    have hd_acc : IsAccessible G ne.f ne.small d := hd_path
    exact Relation.ReflTransGen.head
      (hAuxAdj_pres2 W d hd_adj hW_acc hd_acc hd_ne_W)
      (hacc_not_W d hd_acc hd_ne_W)
  -- Main claim: accessible colors under ne.f remain accessible under f'
  have hacc_preserved : ∀ c, IsAccessible G ne.f ne.small c → IsAccessible G f' ne.small c := by
    intro c hc
    by_cases hcW : c = W
    · exact hcW ▸ hacc_W
    · exact hacc_not_W c hc hcW
  -- y₂ is movable to W under f': no W-colored neighbor
  have hy₂_mov_W : ∀ w, f' w = W → ¬G.Adj y₂ w := by
    intro w hw
    simp [f'] at hw;
    by_cases hw' : w = y₁ <;> simp +decide [ hw' ] at hw ⊢;
    · exact Not.imp hnonadj fun a => id (adj_symm G a);
    · grind
  -- f'(y₂) has non-accessible color under ne.f
  have hf'_y₂_nacc_old : ¬IsAccessible G ne.f ne.small (f' y₂) := by
    grind
  -- f'(y₂) is accessible under f' (via W)
  have hy₂_acc_f' : IsAccessible G f' ne.small (f' y₂) :=
    (hacc_preserved W hW_acc).head ⟨y₂, rfl, hy₂_mov_W⟩
  -- Count argument
  have hsubset : Finset.univ.filter (fun c => ¬IsAccessible G f' ne.small c) ⊆
      Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact fun h => hc (hacc_preserved c h)
  have hstrict : Finset.univ.filter (fun c => ¬IsAccessible G f' ne.small c) ⊂
      Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c) := by
    refine hsubset.ssubset_of_ne ?_
    intro h
    have hmem : f' y₂ ∈ Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf'_y₂_nacc_old⟩
    rw [← h] at hmem
    exact (Finset.mem_filter.mp hmem).2 hy₂_acc_f'
  linarith [Finset.card_lt_card hstrict]

/-
The non-accessible case of nearly_equitable_to_equitable, with primary IH.
    This is the heart of the Kierstead-Kostochka proof (Lemmas 2.2-2.3).
-/
lemma non_accessible_case
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (ih_primary : ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (r' : ℕ),
      Fintype.card W < Fintype.card V →
      H.maxDegree ≤ r' → (r' + 1) ∣ Fintype.card W →
      HasEquitableColoring H (r' + 1)) :
    HasEquitableColoring G (r + 1) := by
  suffices h_sec : ∀ q_val, ∀ (ne : NearlyEquitable G (r + 1) s),
      (Finset.univ.filter (fun c : Fin (r + 1) =>
        ¬IsAccessible G ne.f ne.small c)).card ≤ q_val →
      HasEquitableColoring G (r + 1) from
    h_sec _ ne le_rfl
  intro q_val
  induction q_val with
  | zero =>
    intro ne' hq'
    -- If q = 0, all colors accessible, so ne'.large is accessible
    have : IsAccessible G ne'.f ne'.small ne'.large := by
      by_contra h
      have : 1 ≤ (Finset.univ.filter
          (fun c : Fin (r + 1) => ¬IsAccessible G ne'.f ne'.small c)).card :=
        Finset.card_pos.mpr ⟨ne'.large, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
      omega
    exact accessible_large_gives_equitable G (r + 1) s ne' this
  | succ q_val ih =>
    intro ne' hq'
    by_cases hacc' : IsAccessible G ne'.f ne'.small ne'.large
    · exact accessible_large_gives_equitable G (r + 1) s ne' hacc'
    · -- Non-accessible: apply good_solo_vertex_exists_terminal and handle cases
      obtain ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc,
        hadj_y₁_z, huniq_y₁, hW_terminal, hcases⟩ :=
        good_solo_vertex_exists_terminal G r s hs hd hs0 ne' hacc'
      rcases hcases with ⟨X, hXW, hXacc, hXmov⟩ | ⟨y₂, hy₂ne, hy₂nacc, hy₂adj, hy₂uniq, hnonadj, hnotmov⟩
      · exact non_accessible_case1 G r s hs hd hs0 ne' hacc' ih_primary
          q_val W z y₁ hW_acc hW_ne_small hW_ne_large hz_color hy₁_nacc
          hadj_y₁_z huniq_y₁ X hXW hXacc hXmov hW_terminal
      · -- Case 2: z not movable, y₁ and y₂ nonadjacent solo neighbors
        exact non_accessible_case2_paper G r s hs hd hs0 ne' hacc' ih_primary q_val ih hq'
            W z y₁ y₂ hW_acc hW_ne_small hW_ne_large hz_color hy₁_nacc hadj_y₁_z huniq_y₁
            hy₂ne hy₂nacc hy₂adj hy₂uniq hnonadj
            (fun X hXacc hXW => hnotmov X hXacc hXW) hW_terminal

/-- For a fixed type, induction on edges. The `ih_primary` parameter provides
    the H-S theorem for types with strictly fewer elements. -/
lemma hajnal_szemeredi_edge_induction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : G.maxDegree ≤ r) (hdiv : (r + 1) ∣ Fintype.card V)
    (ih_primary : ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (r' : ℕ),
      Fintype.card W < Fintype.card V →
      H.maxDegree ≤ r' → (r' + 1) ∣ Fintype.card W →
      HasEquitableColoring H (r' + 1)) :
    HasEquitableColoring G (r + 1) := by
  -- Inner induction on number of edges
  have h_ind : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj],
      G'.maxDegree ≤ r → HasEquitableColoring G' (r + 1) := by
    intro G' _ hG'
    induction' n : G'.edgeFinset.card using Nat.strong_induction_on with n ih generalizing G'
    by_cases h_edge : G'.edgeFinset.Nonempty
    · obtain ⟨e, he⟩ := h_edge
      have h_ind : HasEquitableColoring (G'.deleteEdges {e}) (r + 1) := by
        apply ih (G'.deleteEdges {e}).edgeFinset.card
        · rw [← n]; exact edgeFinset_card_deleteEdges_lt G' e he
        · exact le_trans (maxDegree_deleteEdges_le _ _) hG'
        · rfl
      apply induction_step_with_callback G' r hdiv hG' e
        (by rwa [SimpleGraph.mem_edgeFinset] at he) h_ind
      intro s hs_eq hs0 ne
      by_cases hacc : IsAccessible G' ne.f ne.small ne.large
      · exact accessible_large_gives_equitable G' (r + 1) s ne hacc
      · exact non_accessible_case G' r s hs_eq hG' hs0 ne ih_primary
    · exact equitable_coloring_of_edgeless G' r (by
        ext e; simp only [Set.mem_empty_iff_false, iff_false]
        intro he; exact h_edge ⟨e, SimpleGraph.mem_edgeFinset.mpr he⟩)
  exact h_ind G h

set_option maxHeartbeats 400000 in
/-- Outer induction on vertex count, providing ih_primary. -/
private theorem hajnal_szemeredi_outer' : ∀ (n : ℕ)
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (r : ℕ),
    Fintype.card W ≤ n →
    H.maxDegree ≤ r → (r + 1) ∣ Fintype.card W →
    HasEquitableColoring H (r + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro W _ _ H _ r hn hmax hdiv
    exact hajnal_szemeredi_edge_induction H r hmax hdiv
      (fun W' _ _ H' _ r' hcard hmax' hdiv' =>
        ih (Fintype.card W') (by omega) H' r' le_rfl hmax' hdiv')

/-- Hajnal-Szemerédi Theorem, divisible case. -/
theorem hajnal_szemeredi_divisible' (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : G.maxDegree ≤ r) (hdiv : (r + 1) ∣ Fintype.card V) :
    HasEquitableColoring G (r + 1) :=
  hajnal_szemeredi_outer' _ G r le_rfl h hdiv

/-! ## Padding construction for the general case -/

/-- The padded graph: G on V, complete graph on Fin p, no cross edges. -/
noncomputable def paddedGraph (G : SimpleGraph V) (p : ℕ) :
    SimpleGraph (V ⊕ Fin p) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr i, Sum.inr j => i ≠ j
    | _, _ => False
  symm := by
    intro x y
    match x, y with
    | Sum.inl u, Sum.inl v => exact fun h => G.symm h
    | Sum.inr i, Sum.inr j => exact fun h => Ne.symm h
    | Sum.inl _, Sum.inr _ => exact False.elim
    | Sum.inr _, Sum.inl _ => exact False.elim
  loopless := ⟨fun x => by match x with
    | Sum.inl v => exact G.loopless.irrefl v
    | Sum.inr i => simp⟩

noncomputable instance paddedGraph_decRel (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) :
    DecidableRel (paddedGraph G p).Adj := by
  intro x y
  cases x <;> cases y <;> simp [paddedGraph] <;> infer_instance

omit [Fintype V] [DecidableEq V] in
@[simp]
lemma paddedGraph_adj_inl_inl (G : SimpleGraph V) (p : ℕ) (u v : V) :
    (paddedGraph G p).Adj (Sum.inl u) (Sum.inl v) ↔ G.Adj u v := by
  simp [paddedGraph]

omit [Fintype V] [DecidableEq V] in
@[simp]
lemma paddedGraph_adj_inr_inr (G : SimpleGraph V) (p : ℕ) (i j : Fin p) :
    (paddedGraph G p).Adj (Sum.inr i) (Sum.inr j) ↔ i ≠ j := by
  simp [paddedGraph]

omit [Fintype V] [DecidableEq V] in
@[simp]
lemma paddedGraph_adj_inl_inr (G : SimpleGraph V) (p : ℕ) (v : V) (i : Fin p) :
    ¬(paddedGraph G p).Adj (Sum.inl v) (Sum.inr i) := by
  simp [paddedGraph]

omit [Fintype V] [DecidableEq V] in
@[simp]
lemma paddedGraph_adj_inr_inl (G : SimpleGraph V) (p : ℕ) (i : Fin p) (v : V) :
    ¬(paddedGraph G p).Adj (Sum.inr i) (Sum.inl v) := by
  simp [paddedGraph]

omit [DecidableEq V] in
lemma paddedGraph_card (p : ℕ) :
    Fintype.card (V ⊕ Fin p) = Fintype.card V + p := by
  simp [Fintype.card_sum]

omit [DecidableEq V] in
lemma paddedGraph_degree_inl (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) (v : V) :
    (paddedGraph G p).degree (Sum.inl v) = G.degree v := by
  refine' Finset.card_bij (fun w _hw => Sum.elim id (fun i => by tauto) w) _ _ _ <;>
    simp +decide

lemma paddedGraph_degree_inr (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) (i : Fin p) :
    (paddedGraph G p).degree (Sum.inr i) = p - 1 := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
  rw [show ((paddedGraph G p).neighborSet (Sum.inr i)).toFinset =
    Finset.image Sum.inr (Finset.univ.erase i) from ?_,
    Finset.card_image_of_injective _ fun x y hxy ↦ by simpa using hxy]
  · simp +decide [Finset.card_univ]
  · ext x; aesop

lemma paddedGraph_maxDegree_le (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) (r : ℕ)
    (hG : G.maxDegree ≤ r) (hp : p ≤ r + 1) :
    (paddedGraph G p).maxDegree ≤ r := by
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro x
  cases x
  · rw [paddedGraph_degree_inl]
    exact le_trans (SimpleGraph.degree_le_maxDegree _ _) hG
  · rw [paddedGraph_degree_inr]; omega

omit [Fintype V] [DecidableEq V] in
lemma paddedGraph_proper_restrict (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ)
    {k : ℕ} (f : (V ⊕ Fin p) → Fin k) (hf : IsProper (paddedGraph G p) f) :
    IsProper G (f ∘ Sum.inl) := by
  intro u v huv
  exact hf (Sum.inl u) (Sum.inl v) ((paddedGraph_adj_inl_inl G p u v).mpr huv)

omit [Fintype V] [DecidableEq V] in
lemma paddedGraph_proper_inr_injective (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ)
    {k : ℕ} (f : (V ⊕ Fin p) → Fin k) (hf : IsProper (paddedGraph G p) f) :
    Function.Injective (f ∘ Sum.inr) := by
  intro i j hij
  by_contra h
  exact hf (Sum.inr i) (Sum.inr j) ((paddedGraph_adj_inr_inr G p i j).mpr h) hij

/-- In an equitable coloring where k | |V|, all classes have the same size. -/
lemma equitable_classes_equal_of_dvd {W : Type*} [Fintype W] [DecidableEq W]
    {k : ℕ} (f : W → Fin k)
    (hequit : IsEquitable f) (hdvd : k ∣ Fintype.card W) (c : Fin k) :
    (cClass f c).card = Fintype.card W / k := by
  obtain ⟨m, hm⟩ := hdvd
  have h_sum : ∑ c : Fin k, (cClass f c).card = Fintype.card W := by
    simp +decide only [cClass, Finset.card_eq_sum_ones, Finset.sum_fiberwise (Finset.univ : Finset W)]
    rw [Fintype.card_eq_sum_ones]
  have h_min : ∀ c : Fin k, m ≤ (cClass f c).card := by
    contrapose! h_sum
    refine' ne_of_lt (lt_of_lt_of_le (Finset.sum_lt_sum _ _) _)
    use fun i => m
    · exact fun i _ => by obtain ⟨j, hj⟩ := h_sum; linarith [hequit i j]
    · aesop
    · simp +decide [hm]
  rw [hm, Nat.mul_div_cancel_left _ (Fin.pos c)]
  exact le_antisymm
    (le_of_not_gt fun h => by
      have := Finset.sum_lt_sum (fun a _ => h_min a) ⟨c, Finset.mem_univ c, h⟩
      simp_all +decide)
    (h_min c)

omit [DecidableEq V] in
/-- cClass of a composition with Sum.inl counts vertices from V only. -/
lemma cClass_comp_inl_card {k : ℕ} {p : ℕ}
    (f : (V ⊕ Fin p) → Fin k) (c : Fin k) :
    (cClass (f ∘ Sum.inl) c).card =
      (cClass f c).card - (Finset.univ.filter (fun i : Fin p => f (Sum.inr i) = c)).card := by
  unfold cClass
  refine' eq_tsub_of_add_eq _
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  exact Eq.symm (Fintype.sum_sum_type fun x => if f x = c then 1 else 0)

/-- The equitability of the restriction, with divisibility hypothesis. -/
lemma paddedGraph_equitable_restrict (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ)
    {k : ℕ} (f : (V ⊕ Fin p) → Fin k)
    (hf_proper : IsProper (paddedGraph G p) f)
    (hf_equitable : IsEquitable f)
    (hdvd : k ∣ Fintype.card (V ⊕ Fin p)) :
    IsEquitable (f ∘ Sum.inl) := by
  have h_eq_classes : ∀ c : Fin k, (cClass f c).card = (Fintype.card (V ⊕ Fin p)) / k :=
    fun c => equitable_classes_equal_of_dvd f hf_equitable hdvd c
  have h_inj_classes : ∀ c : Fin k, ((cClass f c).card - (cClass (f ∘ Sum.inl) c).card) ≤ 1 := by
    intro c
    have h_inj_classes_aux :
        ((Finset.univ.filter (fun i : Fin p => f (Sum.inr i) = c)).card) ≤ 1 := by
      have := paddedGraph_proper_inr_injective G p f hf_proper
      exact Finset.card_le_one.2 fun i hi j hj => this <| by aesop
    rw [cClass_comp_inl_card]
    omega
  intro c₁ c₂
  specialize h_inj_classes c₂
  simp_all +decide [cClass_comp_inl_card]
  omega

/-- Divisibility lemma for padding. -/
lemma padding_dvd (n k : ℕ) (hk : 0 < k) : k ∣ (n + (k - n % k) % k) := by
  suffices h : (n + (k - n % k) % k) % k = 0 by exact Nat.dvd_of_mod_eq_zero h
  calc (n + (k - n % k) % k) % k
      = (n % k + ((k - n % k) % k) % k) % k := by rw [Nat.add_mod]
    _ = (n % k + (k - n % k) % k) % k := by rw [Nat.mod_mod_of_dvd]; exact dvd_refl k
    _ = _ := by
        by_cases h0 : n % k = 0
        · simp [h0]
        · have : n % k < k := Nat.mod_lt n hk
          have : 0 < n % k := Nat.pos_of_ne_zero h0
          rw [Nat.mod_eq_of_lt (by omega : k - n % k < k)]
          have : n % k + (k - n % k) = k := by omega
          rw [this, Nat.mod_self]

/-- **Hajnal-Szemerédi Theorem**.
    If G has maximum degree at most r, then G has an equitable (r+1)-coloring. -/
theorem hajnal_szemeredi (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : G.maxDegree ≤ r) :
    HasEquitableColoring G (r + 1) := by
  set kk := r + 1
  set n := Fintype.card V
  set p := (kk - n % kk) % kk
  have hk_pos : 0 < kk := Nat.succ_pos r
  have hp_lt : p < kk := Nat.mod_lt _ hk_pos
  have hdiv : kk ∣ (n + p) := padding_dvd n kk hk_pos
  have hcard : Fintype.card (V ⊕ Fin p) = n + p := paddedGraph_card p
  have hmaxdeg : (paddedGraph G p).maxDegree ≤ r :=
    paddedGraph_maxDegree_le G p r h (by omega)
  have hdiv' : kk ∣ Fintype.card (V ⊕ Fin p) := by rw [hcard]; exact hdiv
  obtain ⟨f', hf'_proper, hf'_equitable⟩ := hajnal_szemeredi_divisible'
    (paddedGraph G p) r hmaxdeg hdiv'
  exact ⟨f' ∘ Sum.inl,
    paddedGraph_proper_restrict G p f' hf'_proper,
    paddedGraph_equitable_restrict G p f' hf'_proper hf'_equitable hdiv'⟩

/-! ## Clique cover version -/

/-- Vertex-disjoint copies of K_r in a graph. -/
def HasDisjointCliques (G : SimpleGraph V) (r m : ℕ) : Prop :=
  ∃ f : Fin m → Finset V,
    (∀ i, (f i).card = r) ∧
    (∀ i, ∀ v ∈ f i, ∀ w ∈ f i, v ≠ w → G.Adj v w) ∧
    (∀ i j, i ≠ j → Disjoint (f i) (f j))

/-- **Hajnal-Szemerédi Theorem** (clique cover version). -/
theorem hajnal_szemeredi_clique_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (r m : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card V = r * m)
    (hmin : m * (r - 1) ≤ G.minDegree) :
    HasDisjointCliques G r m := by
  obtain ⟨f, hf_prop⟩ :
    ∃ f : V → Fin m, IsProper (Gᶜ) f ∧ IsEquitable f := by
      convert hajnal_szemeredi Gᶜ (m - 1) _
      · rcases m with (_ | m) <;> simp_all +decide [HasEquitableColoring]
        simp_all +decide [Fintype.card_eq_zero_iff]
        simp +decide [IsProper, IsEquitable]
      · have h_deg_complement : ∀ v : V, (Gᶜ).degree v ≤ m - 1 := by
          intro v
          have h_deg_v : G.degree v ≥ m * (r - 1) := le_trans hmin (G.minDegree_le_degree v)
          have h_deg_complement_v : Gᶜ.degree v = r * m - 1 - G.degree v := by
            simp +decide [← hcard, SimpleGraph.degree_compl]
          simp_all +decide [SimpleGraph.degree_compl]
          cases r <;> cases m <;> norm_num at * ; linarith
        exact SimpleGraph.maxDegree_le_of_forall_degree_le Gᶜ (m - 1) h_deg_complement
  refine' ⟨fun i => cClass f i, _, _, _⟩ <;> simp_all +decide [IsProper, IsEquitable]
  · have h_sum : ∑ i : Fin m, (cClass f i).card = r * m := by
      rw [← hcard, ← Finset.card_biUnion]
      · congr with v; aesop
      · exact fun i _ j _ hij =>
          Finset.disjoint_filter.2 fun v _ hvi hvj => hij <| hvi.symm.trans hvj
    have h_card_ge_r : ∀ i : Fin m, (cClass f i).card ≥ r := by
      intro i
      by_contra h_contra
      have h_card_lt_r : (cClass f i).card < r := lt_of_not_ge h_contra
      have h_card_le_r_minus_1 : ∀ j : Fin m, (cClass f j).card ≤ r - 1 + 1 :=
        fun j => by linarith [hf_prop.2 j i, Nat.sub_add_cancel hr]
      exact absurd h_sum (ne_of_lt (lt_of_lt_of_le
        (Finset.sum_lt_sum (fun x _ => h_card_le_r_minus_1 x)
          ⟨i, Finset.mem_univ i, by omega⟩)
        (by simp +decide [Nat.sub_add_cancel hr]; nlinarith)))
    exact fun i => le_antisymm
      (le_of_not_gt fun hi => by
        have := Finset.sum_lt_sum (fun a _ => h_card_ge_r a)
          ⟨i, Finset.mem_univ i, hi⟩
        simp_all +decide [mul_comm])
      (h_card_ge_r i)
  · grind
  · exact fun i j hij => Finset.disjoint_filter.2 fun v => by aesop

#print axioms hajnal_szemeredi_clique_cover
-- 'Erdos914.HajnalSzemeredi.hajnal_szemeredi_clique_cover' depends on axioms: [propext, choice,
-- Quot.sound]

end HajnalSzemeredi

end Erdos914

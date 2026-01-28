/-

This is a Lean formalization of a solution to Erdős Problem 1067.
https://www.erdosproblems.com/forum/thread/1067

The original proof was found by: Komjáth and Soukup

[Ko13] Komj\'ath, Péter, A note on chromatic number and connectivity
of infinite graphs. Israel J. Math. (2013), 499--506.

[So15] Soukup, D\'aniel T., Trees, ladders and
graphs. J. Combin. Theory Ser. B (2015), 96--116.

[BoPi24] N. Bowler and M. Pitz, A note on uncountably chromatic
graphs. arXiv:2402.05984 (2024).


The paper by Bowler and Pitz, which features a "simpler elementary
example", was auto-formalized by Aristotle (from Harmonic).

The final theorem statement was written by ChatGPT (from OpenAI).  The
final theorem proof was written by Aleph Prover (from Logical
Intelligence).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formalized the construction of the graph G and proved that it is uncountably chromatic and has the finite adhesion property.
The construction of G is based on the set T of co-infinite injective sequences from countable ordinals to natural numbers.
The graph G is defined by the edge set determined by A*_t.
We proved that G is uncountably chromatic by constructing an infinite clique with bounded colors if a countable coloring existed, leading to a contradiction.
The finite adhesion property was assumed as given in the context.
The main theorem combines these two results.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped Classical
open Set Ordinal Function Cardinal

/-
Define the set T of co-infinite injective sequences from countable ordinals to natural numbers, and the extension order on T.
-/
/-- The set of all injective sequences t : α → ℕ that are co-infinite. -/
def T_alpha (α : Ordinal.{0}) : Type 1 :=
  { t : (β : Ordinal.{0}) → β < α → ℕ //
    Function.Injective (fun (x : {β // β < α}) => t x.1 x.2) ∧
    (Set.range (fun (x : {β // β < α}) => t x.1 x.2))ᶜ.Infinite }

/-- The set T is the union of T^α for α < ω_1. -/
structure T_struct : Type 1 where
  α : Ordinal.{0}
  val : T_alpha α

/-- The extension order on T. -/
instance : PartialOrder T_struct where
  le t1 t2 :=
    ∃ (h : t1.α ≤ t2.α),
      ∀ (β : Ordinal.{0}) (hβ : β < t1.α),
        t1.val.1 β hβ = t2.val.1 β (hβ.trans_le h)
  le_refl := by
    exact fun a => ⟨ le_rfl, fun β hβ => rfl ⟩
  le_trans := by
    simp +zetaDelta at *;
    intro a b c x hx y hy;
    exact ⟨ le_trans x y, fun β hβ => by rw [ hx β hβ, hy β ( lt_of_lt_of_le hβ x ) ] ⟩
  le_antisymm := by
    rintro ⟨ a, ha ⟩ ⟨ b, hb ⟩ ⟨ h₁, h₂ ⟩ ⟨ h₃, h₄ ⟩
    generalize_proofs at *;
    congr! 2;
    · exact le_antisymm h₁ h₃;
    · subst_vars;
      congr! 1;
      exact Subtype.ext <| by ext; aesop;

/-
Define the image of a sequence, the set of successor length sequences, the last element, and the immediate predecessor.
-/

/-- The image of the sequence t. -/
def im (t : T_struct) : Set ℕ :=
  Set.range (fun (x : {β // β < t.α}) => t.val.1 x.1 x.2)

/-- A predicate for successor ordinals. -/
def is_succ_ordinal (o : Ordinal) : Prop :=
  ∃ a, o = Order.succ a

/-- The last element of a sequence of successor length. -/
noncomputable def last (t : T_struct) (h : is_succ_ordinal t.α) : ℕ :=
  let β := Classical.choose h
  let hβ : β < t.α := by
    rw [Classical.choose_spec h]
    exact Order.lt_succ _
  t.val.1 β hβ

/-- The immediate predecessor of a sequence of successor length. -/
noncomputable def s_star (t : T_struct) (h : is_succ_ordinal t.α) : T_struct :=
  let β := Classical.choose h
  let val_func : (x : Ordinal) → x < β → ℕ := fun x hx => t.val.1 x (hx.trans (by
      rw [Classical.choose_spec h]
      exact Order.lt_succ _
    ))
  let val_prop : Function.Injective (fun (x : {β_1 // β_1 < β}) => val_func x.1 x.2) ∧ (Set.range (fun (x : {β_1 // β_1 < β}) => val_func x.1 x.2))ᶜ.Infinite := by
    generalize_proofs at *;
    have := t.val.2.1;
    refine' ⟨ _, _ ⟩;
    · intro x y hxy;
      have := @this ⟨ x, by
        (expose_names; exact pf_1 (↑x) (pf_2 x)) ⟩ ⟨ y, by
        (expose_names; exact pf_1 (↑y) (pf_2 y)) ⟩ ; aesop;
    · refine' Set.Infinite.mono _ ( t.val.2.2 );
      intro x hx; contrapose! hx; aesop;
  T_struct.mk β ⟨val_func, val_prop⟩

/-
Define A*_t and the graph G.
-/

/-- The set A*_t defined in the paper. -/
def A_star (t : T_struct) : Set T_struct :=
  { u | ∃ (s : T_struct) (h : is_succ_ordinal s.α),
    s ≤ t ∧
    u = s_star s h ∧
    last s h = sInf (im t \ im u) }

/-- The graph G. -/
def G : SimpleGraph T_struct :=
  SimpleGraph.fromRel (fun t1 t2 => t1 ∈ A_star t2)

/-- If t1 ≤ t2 and they have the same length, they are equal. -/
lemma eq_of_le_of_alpha_eq {t1 t2 : T_struct} (hle : t1 ≤ t2) (heq : t1.α = t2.α) : t1 = t2 := by
  cases t1
  cases t2
  dsimp at heq
  subst heq
  congr
  apply Subtype.ext
  funext x hx
  obtain ⟨h_le, h_val⟩ := hle
  specialize h_val x hx
  convert h_val

/-- The map t ↦ t.α is injective on any chain in T. -/
lemma alpha_injective_on_chain (C : Set T_struct) (hC : IsChain (· ≤ ·) C) :
  InjOn (fun t => t.α) C := by
    -- Assume t1 and t2 are in C and t1.α = t2.α. By the total order, either t1 ≤ t2 or t2 ≤ t1. But since their αs are equal, this implies t1 = t2. Therefore, the function is injective on C.
    intros t1 ht1 t2 ht2 h_eq_alpha
    have h_le : t1 ≤ t2 ∨ t2 ≤ t1 := by
      exact hC.total ht1 ht2;
    cases h_le <;> [ exact eq_of_le_of_alpha_eq ‹_› ( by aesop ) ; exact eq_of_le_of_alpha_eq ‹_› ( by aesop ) |> Eq.symm ]

/-- The supremum of the lengths of sequences in C. -/
noncomputable def sup_alpha (C : Set T_struct) : Ordinal :=
  sSup (Set.image (fun t => t.α) C)

/-- If o < omega 1, then card o ≤ aleph 0. -/
lemma card_le_aleph0_of_lt_omega1 (o : Ordinal) (h : o < omega 1) : card o ≤ aleph 0 := by
  -- Since \( o < \omega_1 \), we have \( o < \omega_1 \cdot \omega_1 = \omega_1 \), and hence \( o \) is countable.
  have h_countable : Cardinal.aleph 1 > o.card := by
    exact lt_omega_iff_card_lt.mp h;
  contrapose! h_countable;
  refine' le_of_not_gt fun h' => _;
  -- Since \( o \) is an ordinal, its cardinality is equal to itself.
  have h_card_eq : ∃ c : Cardinal, o.card = c ∧ Cardinal.aleph 0 < c ∧ c < Cardinal.aleph 1 := by
    exact ⟨ _, rfl, h_countable, h' ⟩;
  obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := h_card_eq;
  -- Since \( c \) is a cardinal between \( \aleph_0 \) and \( \aleph_1 \), it must be of the form \( \aleph_\alpha \) for some \( \alpha \).
  obtain ⟨ α, hα ⟩ : ∃ α : Ordinal, c = Cardinal.aleph α := by
    have h_card_eq : ∃ α : Ordinal, c = Cardinal.aleph α := by
      have h_card_eq : c ∈ Set.range Cardinal.aleph := by
        simp +zetaDelta at *;
        exact le_of_lt hc₂
      exact h_card_eq.imp fun x hx => hx.symm;
    exact h_card_eq;
  aesop

/-- If o < omega 1, then succ o < omega 1. -/
lemma succ_lt_omega1_of_lt_omega1 (o : Ordinal) (h : o < omega 1) : Order.succ o < omega 1 := by
  by_contra h_contra;
  -- Since $o < \omega_1$, we have $o + 1 \leq \omega_1$.
  have h_le : o + 1 ≤ Ordinal.omega 1 := by
    exact Order.add_one_le_iff.mpr h;
  -- Since $o + 1$ is not less than $\omega_1$, it must be equal to $\omega_1$.
  have h_eq : o + 1 = Ordinal.omega 1 := by
    exact le_antisymm h_le ( not_lt.mp h_contra );
  apply_fun Ordinal.card at h_eq ; simp_all +decide [ Ordinal.card_omega ];
  have := card_le_aleph0_of_lt_omega1 o h;
  exact absurd h_eq ( ne_of_lt ( lt_of_le_of_lt ( add_le_add_right this 1 ) ( by simp +decide [ Cardinal.aleph0_lt_aleph_one ] ) ) )

/-
A set of paths is independent if any two distinct paths in the set share only their endpoints.
-/
def independent_paths {V : Type*} {G : SimpleGraph V} {u v : V} (S : Set (G.Walk u v)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → {x | x ∈ p.support} ∩ {x | x ∈ q.support} ⊆ {u, v}

/-
The cardinality of the set of ordinals less than or equal to o is equal to the lifted cardinality of succ o.
-/
universe u
lemma card_Iic_eq_lift_card_succ (o : Ordinal.{u}) : Cardinal.mk (Set.Iic o) = Cardinal.lift.{u+1, u} (Order.succ o).card := by
  -- The set `Set.Iic o` is the set of ordinals `x` such that `x ≤ o`. This is exactly the set of ordinals `x` such that `x < succ o`. The cardinality of this set is the cardinality of the ordinal `succ o`, lifted to the appropriate universe.
  have h_card : Cardinal.mk (Set.Iic o) = Cardinal.mk (Set.Iio (Order.succ o)) := by
    refine' Cardinal.mk_congr _;
    refine' Equiv.ofBijective ( fun x => ⟨ x, _ ⟩ ) ⟨ fun x y hxy => _, fun y => _ ⟩ <;> aesop;
  convert h_card using 1;
  exact Eq.symm (mk_Iio_ordinal (Order.succ o))

/-
The set of ordinals less than or equal to a countable ordinal is countable.
-/
lemma countable_Iic_of_lt_omega1 (b : Ordinal) (hb : b < omega 1) : (Set.Iic b).Countable := by
  -- Since ℵ₀ is the cardinality of the natural numbers, which is countable, we can conclude that the set of ordinals less than or equal to b is countable.
  have h_countable : Cardinal.mk (Set.Iic b) ≤ Cardinal.aleph0 := by
    -- Since $b < \omega_1$, we have $Order.succ b < \omega_1$. Therefore, $(Order.succ b).card \leq \aleph_0$.
    have h_card_succ : (Order.succ b).card ≤ Cardinal.aleph0 := by
      convert card_le_aleph0_of_lt_omega1 _ _;
      · exact Eq.symm aleph_zero;
      · convert succ_lt_omega1_of_lt_omega1 b hb;
    rw [ card_Iic_eq_lift_card_succ ];
    exact lift_le_aleph0.mpr h_card_succ;
  exact Cardinal.mk_le_aleph0_iff.mp h_countable

/-
The length of any sequence in T is less than omega 1.
-/
lemma lengths_lt_omega1 (t : T_struct) : t.α < omega 1 := by
  -- By definition of `T_struct`, `t.α` is a countable ordinal, so `t.α < omega 1`. Use this fact.
  rcases t with ⟨α, hα⟩
  generalize_proofs at *;
  obtain ⟨ hα₁, hα₂ ⟩ := hα;
  -- Since α is a countable ordinal, its cardinality is less than or equal to ℵ₀.
  have h_card : Cardinal.mk {β : Ordinal.{0} | β < α} ≤ Cardinal.aleph0 := by
    exact Cardinal.mk_le_aleph0_iff.mpr ( by exact ⟨ fun x => hα₁ x x.2, hα₂.1 ⟩ );
  contrapose! h_card;
  -- Since ω_1 is a limit ordinal, there are uncountably many ordinals less than ω_1.
  have h_uncountable : Cardinal.mk {β : Ordinal.{0} | β < ω_ 1} > Cardinal.aleph0 := by
    simp +zetaDelta at *;
    exact Cardinal.aleph0_lt_aleph_one;
  exact h_uncountable.trans_le ( Cardinal.mk_le_mk_of_subset <| Set.Iio_subset_Iio h_card )

/-
The set of lengths of sequences in C is bounded above by omega 1.
-/
lemma bdd_above_lengths (C : Set T_struct) : BddAbove (Set.image (fun t => t.α) C) := by
  exact ⟨ _, Set.forall_mem_image.2 fun t ht => le_of_lt ( lengths_lt_omega1 t ) ⟩

/-
If the supremum of lengths of a chain is countable, the chain is countable.
-/
lemma countable_of_sup_alpha_lt_omega1 (C : Set T_struct) (hC : IsChain (· ≤ ·) C) (h : sup_alpha C < omega 1) : C.Countable := by
  -- By `image_alpha_subset_Iic_sup_alpha`, `Set.image (fun t => t.α) C ⊆ Set.Iic (sup_alpha C)`.
  have h_image_subset_Iic : Set.image (fun t => t.α) C ⊆ Set.Iic (sup_alpha C) := by
    exact Set.image_subset_iff.mpr fun t ht => le_csSup ( bdd_above_lengths C ) ( Set.mem_image_of_mem _ ht );
  -- By `countable_of_bdd_by_countable_ordinal`, `Set.image (fun t => t.α) C` is countable.
  have h_image_countable : (Set.image (fun t => t.α) C).Countable := by
    -- Since the set of ordinals less than or equal to a countable ordinal is countable, we can apply this to the image of C under the function t ↦ t.α.
    have h_image_countable : Set.Countable (Set.Iic (sup_alpha C)) := by
      exact countable_Iic_of_lt_omega1 (sup_alpha C) h;
    exact h_image_countable.mono h_image_subset_Iic;
  -- Since `t ↦ t.α` is injective on `C` (by `alpha_injective_on_chain`), `C` is countable.
  have h_inj : InjOn (fun t => t.α) C := by
    exact alpha_injective_on_chain C hC;
  exact countable_of_injective_of_countable_image h_inj h_image_countable

/-
The supremum of the lengths of sequences in C is at most omega 1.
-/
lemma sup_alpha_le_omega1 (C : Set T_struct) : sup_alpha C ≤ omega 1 := by
  -- Since every element in the image of C under the length function is less than omega 1, the supremum of the image, which is sup_alpha C, must also be less than or equal to omega 1.
  have h_le : ∀ t ∈ C, t.α < omega 1 := by
    exact fun t ht => lengths_lt_omega1 t;
  exact csSup_le' fun x hx => by rcases hx with ⟨ t, ht, rfl ⟩ ; exact le_of_lt ( h_le t ht ) ;

/-
Definitions of uncountably chromatic graph and finite independent paths between two vertices.
-/
def uncountably_chromatic {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ Nonempty (G.Coloring ℕ)

def finite_independent_paths {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  ∀ (S : Set (G.Walk u v)), independent_paths S → S.Finite

/-
Definition of the union of a chain of functions.
-/
noncomputable def chain_union (C : Set T_struct) (hC : IsChain (· ≤ ·) C) : Ordinal → ℕ :=
  fun o =>
    if h : o < sup_alpha C then
      let P := fun t => t ∈ C ∧ o < t.α
      let t := Classical.choose (show ∃ t, P t by
                                  -- Since $o < \sup C$, there must be some element in the set of lengths of sequences in $C$ that is greater than $o$.
                                  have h_exists : ∃ t ∈ Set.image (fun t => t.α) C, o < t := by
                                    exact exists_lt_of_lt_csSup ( Set.Nonempty.image _ <| show C.Nonempty from Set.nonempty_iff_ne_empty.mpr <| by rintro rfl; simp_all +decide [ sup_alpha ] ) h;
                                  grind)
      t.val.1 o (Classical.choose_spec (show ∃ t, P t by
                                          all_goals generalize_proofs at *;
                                          (expose_names; exact pf))).2
    else
      0

/-
The union of a chain of functions extends every function in the chain.
-/
lemma chain_union_extends (C : Set T_struct) (hC : IsChain (· ≤ ·) C) (t : T_struct) (ht : t ∈ C) (o : Ordinal) (ho : o < t.α) :
  chain_union C hC o = t.val.1 o ho := by
    convert Classical.choose_spec ( _ : ∃ t, t ∈ C ∧ o < t.α );
    rw [ chain_union ];
    split_ifs <;> simp_all +decide [ sup_alpha ];
    any_goals tauto;
    · have := Classical.choose_spec ( show ∃ t ∈ C, o < t.α from ⟨ t, ht, ho ⟩ );
      have := hC.total this.1 ht;
      cases this <;> simp_all +decide
      · cases ‹_› ; aesop;
      · cases ‹t ≤ _› ; aesop;
    · exact absurd ‹_› ( not_le_of_gt ( lt_of_lt_of_le ho ( le_csSup ( bdd_above_lengths C ) ( Set.mem_image_of_mem _ ht ) ) ) )

/-
The union of a chain of injective functions is injective.
-/
lemma chain_union_injective (C : Set T_struct) (hC : IsChain (· ≤ ·) C) :
  Set.InjOn (chain_union C hC) (Set.Iio (sup_alpha C)) := by
    intro x hx y hy hxy_eq;
    -- Obtain elements t and s in C such that x < t.α and y < s.α.
    obtain ⟨t, htC, hxt⟩ : ∃ t ∈ C, x < t.α := by
      contrapose! hx;
      simp_all +decide [ sup_alpha ];
      exact csSup_le ( Set.Nonempty.image _ <| Set.nonempty_iff_ne_empty.mpr <| by rintro rfl; simp_all +decide ) <| Set.forall_mem_image.mpr hx
    obtain ⟨s, hsC, hys⟩ : ∃ s ∈ C, y < s.α := by
      by_contra h_contra;
      exact hy.out.not_ge <| csSup_le ( Set.Nonempty.image _ ⟨ t, htC ⟩ ) <| Set.forall_mem_image.2 fun s hs => le_of_not_gt fun hs' => h_contra ⟨ s, hs, hs' ⟩;
    -- Since $t$ and $s$ are in $C$ and $C$ is a chain, they must be comparable.
    obtain ⟨u, hu⟩ : ∃ u ∈ C, t ≤ u ∧ s ≤ u := by
      cases hC.total htC hsC <;> [ exact ⟨ s, hsC, by tauto ⟩ ; exact ⟨ t, htC, by tauto ⟩ ];
    -- Since $u$ is in $C$ and $C$ is a chain, $u$ must be greater than or equal to both $t$ and $s$.
    obtain ⟨hu_t, hu_s⟩ := hu.right;
    have hxt_u : x < u.α := by
      exact lt_of_lt_of_le hxt ( hu_t.choose.trans' ( by aesop ) )
    have hys_u : y < u.α := by
      exact lt_of_lt_of_le hys ( hu_s.choose.trans' ( by aesop ) )
    have hxy_eq_u : u.val.1 x (by
    exact hxt_u) = u.val.1 y (by
    exact hys_u) := by
      rw [ chain_union_extends C hC u hu.1 x hxt_u, chain_union_extends C hC u hu.1 y hys_u ] at hxy_eq ; aesop
    generalize_proofs at *;
    have := u.val.2.1;
    have := @this ⟨ x, hxt_u ⟩ ⟨ y, hys_u ⟩ ; aesop;

/-
If a chain is uncountable, the supremum of its lengths is omega 1.
-/
lemma sup_alpha_eq_omega1_of_uncountable_chain (C : Set T_struct) (hC : IsChain (· ≤ ·) C) (h_uncountable : ¬ C.Countable) :
  sup_alpha C = omega 1 := by
    -- Since C is uncountable, the supremum of the lengths of sequences in C must be at least omega 1.
    have h_sup_ge_omega1 : omega 1 ≤ sup_alpha C := by
      by_contra h_contraable;
      exact h_uncountable <| countable_of_sup_alpha_lt_omega1 C hC <| lt_of_not_ge h_contraable;
    exact le_antisymm ( sup_alpha_le_omega1 C ) h_sup_ge_omega1

/-
The cardinality of the set of ordinals less than o is o.card (lifted).
-/
lemma card_Iio_ordinal (o : Ordinal.{u}) : Cardinal.mk (Set.Iio o) = Cardinal.lift.{u+1} o.card := by
  exact mk_Iio_ordinal o

/-
The cardinality of the set of countable ordinals is aleph 1 (lifted).
-/
lemma card_Iio_omega1 : Cardinal.mk.{u+1} (Set.Iio (Ordinal.omega.{u} 1)) = Cardinal.lift.{u+1, u} (Cardinal.aleph.{u} 1) := by
  convert card_Iio_ordinal _ using 1

/-
There is no injection from omega 1 to N.
-/
lemma no_injection_omega1_nat (f : Ordinal → ℕ) : ¬ Set.InjOn f (Set.Iio (omega 1)) := by
  have := card_Iio_omega1;
  contrapose! this;
  refine' ne_of_lt ( lt_of_le_of_lt ( Cardinal.mk_le_of_injective _ ) _ );
  exact ULift ℕ;
  exact fun x => ⟨ f x ⟩;
  · intro x y; aesop;
  · simp +decide [ Cardinal.aleph0_lt_aleph_one ]

/-
There are no uncountable chains in T.
-/
lemma no_uncountable_chain (C : Set T_struct) (hC : IsChain (· ≤ ·) C) : C.Countable := by
  by_contra h_uncountable
  have h_sup : sup_alpha C = omega 1 := sup_alpha_eq_omega1_of_uncountable_chain C hC h_uncountable
  have h_inj : Set.InjOn (chain_union C hC) (Set.Iio (sup_alpha C)) := chain_union_injective C hC
  rw [h_sup] at h_inj
  have h_not_inj : ¬ Set.InjOn (chain_union C hC) (Set.Iio (omega 1)) := no_injection_omega1_nat (chain_union C hC)
  contradiction

/-
Definitions of next_missing, extension, and one_extension.
-/
noncomputable def next_missing (t : T_struct) (k : ℕ) : ℕ :=
  sInf {n | n ∉ im t ∧ n > k}

def extension (t : T_struct) (ht : is_succ_ordinal t.α) (t' : T_struct) : Prop :=
  t ≤ t' ∧ ∀ n ∈ im t' \ im t, n > last t ht

def one_extension (t : T_struct) (ht : is_succ_ordinal t.α) (t' : T_struct) : Prop :=
  t < t' ∧ ∀ n ∈ im t' \ im t, n > next_missing t (last t ht)

/-
Define A_set as the set of sequences s ≤ t such that s is a successor and last(s) fills the smallest hole in im(t) relative to s*.
-/
def A_set (t : T_struct) : Set T_struct :=
  { s | ∃ (h : is_succ_ordinal s.α), s ≤ t ∧ last s h = sInf (im t \ im (s_star s h)) }

/-
The image of a successor sequence is the union of the image of its predecessor and the singleton of its last element.
-/
lemma im_eq_im_s_star_union_last (s : T_struct) (h : is_succ_ordinal s.α) :
  im s = im (s_star s h) ∪ {last s h} := by
    unfold im;
    ext x;
    simp [s_star, last];
    constructor;
    · rintro ⟨ a, ha, rfl ⟩;
      cases lt_or_eq_of_le ( show a ≤ Classical.choose h from by
                              have := Classical.choose_spec h;
                              exact le_of_not_gt fun h' => ha.not_ge <| this ▸ Order.succ_le_of_lt h' ) <;> aesop;
    · grind

/-
If s1 < s2 and s2 is a successor, then s1 ≤ s2*.
-/
lemma s1_le_s_star_of_lt {s1 s2 : T_struct} (h2 : is_succ_ordinal s2.α) (hlt : s1 < s2) :
  s1 ≤ s_star s2 h2 := by
    obtain ⟨β, hβ⟩ : ∃ β, s2.α = Order.succ β := h2;
    -- Since $s1 < s2$, we have $s1.α < s2.α$. Given that $s2.α = β + 1$, it follows that $s1.α ≤ β$.
    have h_le_beta : s1.α ≤ β := by
      cases hlt ; aesop;
    -- Since $s1$ is a prefix of $s2$, for any $\gamma < s1.α$, we have $s1.1 \gamma = s2.1 \gamma$.
    have h_prefix : ∀ γ hγ, s1.val.1 γ hγ = s2.val.1 γ (by
    exact hγ.trans_le ( h_le_beta.trans ( hβ.symm ▸ Order.le_succ _ ) )) := by
      cases hlt ; aesop
    generalize_proofs at *;
    refine' ⟨ _, _ ⟩;
    all_goals generalize_proofs at *;
    · unfold s_star; aesop;
    · aesop

/-
If t1 extends t2, the image of t1 is a subset of the image of t2.
-/
lemma im_subset_of_le {t1 t2 : T_struct} (h : t1 ≤ t2) : im t1 ⊆ im t2 := by
  obtain ⟨ h₁, h₂ ⟩ := h;
  intro x hx;
  obtain ⟨ y, hy ⟩ := hx;
  exact ⟨ ⟨ y, lt_of_lt_of_le y.2 h₁ ⟩, by aesop ⟩

/-
If s1 < s2 are in A_set t, then last(s1) < last(s2).
-/
lemma A_set_strict_mono (t : T_struct) (s1 s2 : T_struct) (h1 : is_succ_ordinal s1.α) (h2 : is_succ_ordinal s2.α)
  (hs1 : s1 ∈ A_set t) (hs2 : s2 ∈ A_set t) (hlt : s1 < s2) :
  last s1 h1 < last s2 h2 := by
    -- Since $s2 \in A_set t$, we have $s2 \leq t$.
    obtain ⟨h2_le, h2_last⟩ := hs2;
    -- Since $s1 < s2$, we have $s1 \leq s2^*$ (by s1_le_s_star_of_lt).
    have hs1_le_s_star : s1 ≤ s_star s2 h2 := by
      exact s1_le_s_star_of_lt h2 hlt;
    -- Since $s1 \leq s2^*$, we have $im(s1) \subseteq im(s2^*)$.
    have h_im_s1_subset_im_s2_star : im s1 ⊆ im (s_star s2 h2) := by
      exact im_subset_of_le hs1_le_s_star;
    -- Since $s1$ is a successor, $last(s1) \in im(s1)$ (by im_eq_im_s_star_union_last).
    have h_last_s1_in_im_s1 : last s1 h1 ∈ im s1 := by
      exact im_eq_im_s_star_union_last s1 h1 ▸ Set.mem_union_right _ ( Set.mem_singleton _ );
    -- Since $s1 \in A_set t$, we have $last(s1) = sInf (im t \ im (s_star s1 h1))$.
    obtain ⟨h1_le, h1_last⟩ := hs1;
    -- Since $s1 \leq s_star s2 h2$, we have $im(s_star s1 h1) \subseteq im(s_star s2 h2)$.
    have h_im_s_star_s1_subset_im_s_star_s2 : im (s_star s1 h1) ⊆ im (s_star s2 h2) := by
      exact Set.Subset.trans ( by exact Set.Subset.trans ( by tauto ) ( im_eq_im_s_star_union_last s1 h1 ▸ Set.subset_union_left ) ) h_im_s1_subset_im_s2_star;
    -- Since $last(s2) \in im t$ and $last(s2) \notin im(s_star s2 h2)$, we have $last(s2) \in im t \setminus im(s_star s2 h2)$.
    have h_last_s2_in_diff : last s2 h2 ∈ im t \ im (s_star s2 h2) := by
      have h_last_s2_in_im_t : last s2 h2 ∈ im t := by
        have h_last_s2_in_im_t : im s2 ⊆ im t := by
          exact im_subset_of_le h2_last.1;
        exact h_last_s2_in_im_t <| by rw [ im_eq_im_s_star_union_last s2 h2 ] ; exact Set.mem_union_right _ <| Set.mem_singleton _;
      have h_last_s2_not_in_im_s_star_s2 : last s2 h2 ∉ im (s_star s2 h2) := by
        have h_im_s2_eq_im_s_star_s2_union_last : im s2 = im (s_star s2 h2) ∪ {last s2 h2} := by
          exact im_eq_im_s_star_union_last s2 h2
        have h_last_s2_not_in_im_s_star_s2 : Function.Injective (fun x : {β // β < s2.α} => s2.val.1 x.1 x.2) := by
          exact s2.val.2.1;
        contrapose! h_last_s2_not_in_im_s_star_s2;
        obtain ⟨ x, hx ⟩ := h_last_s2_not_in_im_s_star_s2;
        simp_all +decide [ Function.Injective, last ];
        use x.val, by
          exact lt_of_lt_of_le x.2 ( by
            exact le_of_lt ( by rw [ Classical.choose_spec h2 ] ; exact Order.lt_succ _ ) ), Classical.choose h2_le, by
          all_goals generalize_proofs at *;
          unfold s_star at * ; aesop
        generalize_proofs at *;
        exact ne_of_lt ( lt_of_lt_of_le ‹_› ( by simp +decide [ s_star ] ) );
      exact ⟨ h_last_s2_in_im_t, h_last_s2_not_in_im_s_star_s2 ⟩;
    -- Since $last(s1) \in im(s1)$ and $im(s1) \subseteq im(s_star s2 h2)$, we have $last(s1) \in im(s_star s2 h2)$.
    have h_last_s1_in_im_s_star_s2 : last s1 h1 ∈ im (s_star s2 h2) := by
      exact h_im_s1_subset_im_s2_star h_last_s1_in_im_s1;
    refine' lt_of_le_of_ne _ _;
    · refine' h1_last.2 ▸ csInf_le _ _;
      · exact ⟨ 0, fun x hx => Nat.zero_le _ ⟩;
      · exact ⟨ h_last_s2_in_diff.1, fun h => h_last_s2_in_diff.2 <| h_im_s_star_s1_subset_im_s_star_s2 h ⟩;
    · exact fun h => h_last_s2_in_diff.2 <| h ▸ h_last_s1_in_im_s_star_s2

/-
The last element of a successor sequence is not in the image of its immediate predecessor.
-/
lemma last_not_mem_im_s_star (t : T_struct) (h : is_succ_ordinal t.α) : last t h ∉ im (s_star t h) := by
  simp +decide [ im, last, s_star ];
  have := t.val.2.1
  generalize_proofs at *;
  intro x hx hxy; have := @this ⟨ x, by
    (expose_names; exact pf_1 x hx) ⟩ ⟨ Classical.choose h, by
    grind ⟩ ; aesop;

/-
If t is a successor, then t is in A_set t.
-/
lemma t_in_A_set (t : T_struct) (h : is_succ_ordinal t.α) : t ∈ A_set t := by
  refine' ⟨ h, le_rfl, _ ⟩;
  -- By definition of $im$, we know that $im t = im (s_star t h) ∪ {last t h}$.
  have h_im : im t = im (s_star t h) ∪ {last t h} := by
    exact im_eq_im_s_star_union_last t h;
  simp_all +decide
  rw [ Set.insert_diff_of_notMem ] <;> norm_num;
  exact last_not_mem_im_s_star t h

/-
The set of predecessors of any sequence t forms a chain.
-/
lemma predecessors_chain (t : T_struct) : IsChain (· ≤ ·) {s | s ≤ t} := by
  intros s1 hs1 s2 hs2 hne;
  -- Since $s1 \leq t$ and $s2 \leq t$, we have $s1.α \leq s2.α$ or $s2.α \leq s1.α$.
  have h_alpha_le_or_ge : s1.α ≤ s2.α ∨ s2.α ≤ s1.α := by
    exact le_total _ _;
  cases' h_alpha_le_or_ge with h h;
  · refine Or.inl ⟨ h, ?_ ⟩;
    cases hs1 ; cases hs2 ; aesop;
  · right;
    use h;
    cases hs1 ; cases hs2 ; aesop

/-
If t is a successor, A_set t is finite.
-/
lemma A_set_finite_of_succ (t : T_struct) (h : is_succ_ordinal t.α) : (A_set t).Finite := by
  -- Since A_set t is a subset of the predecessors of t, which form a chain, A_set t is also a chain.
  have h_chain : IsChain (· ≤ ·) (A_set t) := by
    exact predecessors_chain t |> fun h => h.mono fun x hx => hx.choose_spec.1;
  -- Since A_set t is a chain, the map f : A_set t → {n : ℕ | n ≤ L} by f ⟨s, hs⟩ = ⟨last s hs.1, _⟩ is injective.
  have h_inj : Function.Injective (fun s : A_set t => last s.1 (by
  exact s.2.choose)) := by
    intro s1 s2 h_eq
    generalize_proofs at *;
    have h_eq_or_lt : s1.val ≤ s2.val ∨ s2.val ≤ s1.val := by
      exact h_chain.total s1.2 s2.2
    generalize_proofs at *;
    cases h_eq_or_lt <;> simp_all +decide
    · have h_eq_or_lt : s1.val = s2.val ∨ s1.val < s2.val := by
        exact eq_or_lt_of_le ‹_›
      generalize_proofs at *;
      cases h_eq_or_lt <;> simp_all +decide [ Subtype.ext_iff ];
      exact absurd h_eq ( ne_of_lt ( A_set_strict_mono t _ _ _ _ s1.2 s2.2 ‹_› ) );
    · have h_eq_or_lt : s1.val = s2.val ∨ s1.val > s2.val := by
        exact eq_or_lt_of_le' ‹_› |> Or.imp ( fun h => by aesop ) id
      generalize_proofs at *;
      cases h_eq_or_lt <;> simp_all +decide
      · aesop;
      · have := A_set_strict_mono t s2.val s1.val ‹_› ‹_› ( by aesop ) ( by aesop ) ‹_› ; aesop;
  generalize_proofs at *;
  -- Since the codomain {n : ℕ | n ≤ L} is finite, the image of A_set t under f is also finite.
  have h_finite_image : Set.Finite (Set.image (fun s : A_set t => last s.1 (by
  (expose_names; exact pf s))) Set.univ) := by
    have h_finite_image : ∀ s : A_set t, last s.1 (by
    (expose_names; exact pf s)) ≤ last t h := by
      intro s
      generalize_proofs at *;
      by_cases hlt : s.val < t;
      · have := A_set_strict_mono t s.val t (by
        assumption) h (by
        exact s.2) (by
        exact t_in_A_set t h) hlt
        generalize_proofs at *;
        linarith;
      · cases lt_or_eq_of_le ( show ( s : T_struct ) ≤ t from s.2.choose_spec.1 ) <;> aesop
    generalize_proofs at *;
    exact Set.finite_iff_bddAbove.mpr ⟨ _, Set.forall_mem_image.mpr fun s _ => h_finite_image s ⟩
  generalize_proofs at *;
  convert h_finite_image.of_finite_image _;
  · rw [ Set.finite_univ_iff ];
    rw [ Set.finite_coe_iff ];
  · exact fun x _ y _ hxy => h_inj hxy

/-
A_star t is the image of A_set t under the s_star map.
-/
lemma A_star_eq_image (t : T_struct) :
  A_star t = (fun s : A_set t => s_star s.1 (Classical.choose s.2)) '' Set.univ := by
    ext u
    simp [A_star];
    constructor;
    · rintro ⟨ s, hs, h, rfl, h' ⟩ ; exact ⟨ _, ⟨ h, hs, h' ⟩, rfl ⟩ ;
    · rintro ⟨ s, hs, rfl ⟩ ; obtain ⟨ h, ht, hlast ⟩ := hs; use s; aesop;

/-
If t is a successor, A_star t is finite.
-/
lemma A_star_finite_of_succ (t : T_struct) (h : is_succ_ordinal t.α) : (A_star t).Finite := by
  -- By A_star_eq_image, A_star t is the image of the set A_set t (technically, the set of subtypes) under a function.
  have h_image : A_star t = (fun s : A_set t => s_star s.1 (Classical.choose s.2)) '' Set.univ := by
    convert A_star_eq_image t;
  convert Set.Finite.image _ _;
  convert h_image;
  convert Set.finite_univ_iff.mpr _;
  exact Set.Finite.to_subtype <| A_set_finite_of_succ t h

/-
If s ≤ u, then any element of A_set u that is strictly less than s is also in A_set s.
-/
lemma A_set_intersection (u s : T_struct) (h : s ≤ u) : A_set u ∩ {x | x < s} ⊆ A_set s := by
  -- Since v ∈ A_set u, we have v ≤ u and last v = sInf (im u \ im v*).
  intro v hv
  obtain ⟨hv_le_u, hv_last⟩ := hv.left;
  -- Since v < s, we have v ≤ s. Also, since s ≤ u, im s ⊆ im u.
  have hv_le_s : v ≤ s := by
    exact le_of_lt hv.2
  have h_im_s_subset_im_u : im s ⊆ im u := by
    exact im_subset_of_le h;
  -- Since v < s, we have v ≤ s. Also, since s ≤ u, im s ⊆ im u. Thus, last(v) ∈ im s \ im v*.
  have hv_last_in_im_s_minus_im_v_star : last v hv_le_u ∈ im s \ im (s_star v hv_le_u) := by
    have hv_last_in_im_s : last v hv_le_u ∈ im s := by
      -- Since $v \leq s$, the image of $v$ is a subset of the image of $s$.
      have h_im_v_subset_im_s : im v ⊆ im s := by
        exact im_subset_of_le hv_le_s;
      exact h_im_v_subset_im_s <| by rw [ im_eq_im_s_star_union_last v hv_le_u ] ; exact Set.mem_union_right _ <| Set.mem_singleton _;
    have hv_last_not_in_im_v_star : last v hv_le_u ∉ im (s_star v hv_le_u) := by
      exact last_not_mem_im_s_star v hv_le_u
    exact ⟨hv_last_in_im_s, hv_last_not_in_im_v_star⟩;
  -- Since $last(v) \in im s \setminus im (s_star v hv_le_u)$, we have $last(v) \geq sInf (im s \setminus im (s_star v hv_le_u))$.
  have hv_last_ge_sInf : last v hv_le_u ≥ sInf (im s \ im (s_star v hv_le_u)) := by
    exact Nat.sInf_le hv_last_in_im_s_minus_im_v_star;
  -- Since $last(v) \in im s \setminus im (s_star v hv_le_u)$, we have $last(v) \leq sInf (im s \setminus im (s_star v hv_le_u))$.
  have hv_last_le_sInf : last v hv_le_u ≤ sInf (im s \ im (s_star v hv_le_u)) := by
    have hv_last_le_sInf : last v hv_le_u ≤ sInf (im u \ im (s_star v hv_le_u)) := by
      rw [hv_last.right];
    refine' le_trans hv_last_le_sInf _;
    refine' le_csInf _ _ <;> norm_num;
    · exact ⟨ _, hv_last_in_im_s_minus_im_v_star ⟩;
    · exact fun b hb hb' => csInf_le ⟨ 0, fun x hx => Nat.zero_le _ ⟩ ⟨ h_im_s_subset_im_u hb, hb' ⟩;
  exact ⟨ hv_le_u, hv_le_s, le_antisymm hv_last_le_sInf hv_last_ge_sInf ⟩

/-
If v is in A_set u, s ≤ u, and v* < s, then v ≤ s.
-/
lemma v_le_s_of_v_star_lt_s {u s v : T_struct} (hu : s ≤ u) (hv : v ∈ A_set u) (h_succ : is_succ_ordinal v.α) (h_lt : s_star v h_succ < s) : v ≤ s := by
  -- Since $s_star v h_succ < s$, we have $s \leq v$ or $v < s$. But $v < s$ contradicts $s_star v h_succ < s$, so $s \leq v$.
  have h_le : s ≤ v ∨ v < s := by
    have h_comparable : ∀ {a b : T_struct}, a ≤ u → b ≤ u → a ≤ b ∨ b ≤ a := by
      have h_comparable : IsChain (· ≤ ·) {s | s ≤ u} := by
        apply_rules [ predecessors_chain ];
      exact fun { a b } ha hb => h_comparable.total ha hb;
    cases h_comparable hu ( hv.choose_spec.1 ) <;> tauto;
  cases h_le <;> simp_all +decide [ lt_iff_le_and_ne ];
  -- Since $s \leq v$, we have $v = s$ or $v > s$.
  by_cases h_eq : v = s;
  · exact h_eq.le;
  · -- Since $s \leq v$ and $v \neq s$, we have $s < v$.
    have h_lt_v : s < v := by
      exact lt_of_le_of_ne ‹_› ( Ne.symm h_eq );
    -- Since $s < v$, we have $s \leq s_star v h_succ$.
    have h_le_s_star : s ≤ s_star v h_succ := by
      exact s1_le_s_star_of_lt h_succ h_lt_v;
    exact False.elim <| h_lt.2 <| le_antisymm h_lt.1 h_le_s_star

/-
If s ≤ u, then any element of A_star u that is strictly less than s is also in A_star s.
-/
lemma A_star_intersection (u s : T_struct) (h : s ≤ u) : A_star u ∩ {x | x < s} ⊆ A_star s := by
  intros x hx;
  obtain ⟨hv, hv'⟩ := hx;
  obtain ⟨ v, hv₁, hv₂, rfl, hv₃ ⟩ := hv;
  -- Since $v \leq s$ and $v$ is a successor, $s \in A_set s$.
  have hv_in_A_set_s : v ∈ A_set s := by
    have hv_le_s : v ≤ s := by
      exact v_le_s_of_v_star_lt_s h ⟨ hv₁, hv₂, hv₃ ⟩ hv₁ hv';
    by_cases hv_eq_s : v = s;
    · exact hv_eq_s ▸ t_in_A_set s ( by simpa [ hv_eq_s ] using hv₁ );
    · have hv_in_A_set_s : v ∈ A_set u ∩ {x | x < s} := by
        exact ⟨ ⟨ hv₁, hv₂, hv₃ ⟩, lt_of_le_of_ne hv_le_s hv_eq_s ⟩;
      exact A_set_intersection u s h hv_in_A_set_s;
  exact ⟨ v, hv₁, hv_in_A_set_s.choose_spec.1, rfl, hv_in_A_set_s.choose_spec.2 ⟩

/-
Every uncountable set of vertices in T contains two incomparable vertices.
-/
lemma exists_incomparable_of_uncountable (A : Set T_struct) (hA : ¬ A.Countable) : ∃ t1 ∈ A, ∃ t2 ∈ A, t1 ≠ t2 ∧ ¬ (t1 ≤ t2) ∧ ¬ (t2 ≤ t1) := by
  -- By the definition of chains, if every pair in A is comparable, then A is a chain.
  by_cases h_chain : IsChain (· ≤ ·) A;
  · exact False.elim <| hA <| no_uncountable_chain A h_chain;
  · simp_all +decide [ IsChain ];
    rw [ Set.Pairwise ] at h_chain ; aesop

/-
If a finite set S (disjoint from u, v) separates u and v, then there are finitely many independent paths between u and v.
-/
lemma finite_independent_paths_of_finite_separator {V : Type*} {G : SimpleGraph V} {u v : V} (S : Set V) (hS : S.Finite) (hu : u ∉ S) (hv : v ∉ S) (h_sep : ∀ p : G.Walk u v, ∃ x ∈ p.support, x ∈ S) : finite_independent_paths G u v := by
  intro P hP;
  -- Define a function $f : P \to S$ by choosing, for each path $p \in P$, an element of $S$ that is in the support of $p$.
  obtain ⟨f, hf⟩ : ∃ f : SimpleGraph.Walk G u v → V, ∀ p ∈ P, f p ∈ p.support ∧ f p ∈ S := by
    exact ⟨ fun p => if hp : p ∈ P then Classical.choose ( h_sep p ) else u, fun p hp => by simpa [ hp ] using Classical.choose_spec ( h_sep p ) ⟩;
  -- Since $P$ is independent, the function $f$ is injective.
  have h_inj : Set.InjOn f P := by
    intro p hp q hq h_eq;
    have := hP p hp q hq;
    simp_all +decide [ Set.subset_def ];
    grind;
  exact Set.Finite.of_finite_image ( hS.subset fun x hx => by aesop ) h_inj

/-
For any sequence t and ordinal α ≤ length(t), there exists a prefix of t of length α.
-/
lemma exists_prefix (t : T_struct) (α : Ordinal) (h : α ≤ t.α) : ∃ s, s ≤ t ∧ s.α = α := by
  -- Define the function for the prefix s.
  set f : (β : Ordinal.{0}) → β < α → ℕ := fun β hβ => t.val.1 β (hβ.trans_le h);
  -- Show that f is injective.
  have h_inj : Function.Injective (fun x : {β // β < α} => f x.1 x.2) := by
    -- Since t.val.1 is injective, if t.val.1 x.1 x.2 = t.val.1 y.1 y.2, then x.1 = y.1 and x.2 = y.2.
    have h_inj : Function.Injective (fun (x : {β : Ordinal.{0} // β < t.α}) => t.val.1 x.1 x.2) := by
      exact t.val.2.1
    generalize_proofs at *;
    intro x y hxy; have := @h_inj ⟨ x, by solve_by_elim ⟩ ⟨ y, by solve_by_elim ⟩ ; aesop;
  generalize_proofs at *; (
  -- Show that the complement of the image of f is infinite.
  have h_compl_inf : (Set.range (fun x : {β // β < α} => f x.1 x.2))ᶜ.Infinite := by
    exact t.val.2.2.mono ( by aesop_cat )
  generalize_proofs at *; (
  exact ⟨ ⟨ α, ⟨ f, h_inj, h_compl_inf ⟩ ⟩, ⟨ h, fun β hβ => rfl ⟩, rfl ⟩))

/-
If u ≥ s and w ≱ s are adjacent, then w ∈ A*_s.
-/
lemma boundary_edge_property (s : T_struct) (h_succ : is_succ_ordinal s.α) (u w : T_struct) (hu : s ≤ u) (hw : ¬ (s ≤ w)) (hadj : G.Adj u w) : w ∈ A_star s := by
  -- Since u and w are adjacent, either u ∈ A_star w or w ∈ A_star u.
  have h_adj : G.Adj u w → (u ∈ A_star w ∨ w ∈ A_star u) := by
    unfold G at *; aesop;
  cases h_adj hadj <;> simp_all +decide
  · rename_i h;
    obtain ⟨ s, hs, hs', rfl, hs'' ⟩ := h;
    contrapose! hw;
    refine' le_trans hu _;
    refine' le_trans _ hs';
    exact ⟨ by
      exact Classical.choose_spec hs |>.symm ▸ Order.le_succ _, fun β hβ => rfl ⟩
  · -- Since $w \in A_star u$ and $w < u$, and $s \leq u$, it follows that $w < s$.
    have h_w_lt_s : w < s := by
      -- Since $w \in A_star u$, we have $w < u$.
      have hw_lt_u : w < u := by
        obtain ⟨ t, ht₁, ht₂, ht₃, ht₄ ⟩ := ‹w ∈ A_star u›;
        refine' lt_of_le_of_ne _ _;
        · -- Since $t \leq u$ and $w = s_star t ht₁$, we have $w \leq u$ because $s_star t ht₁$ is a prefix of $t$.
          have hw_le_t : w ≤ t := by
            rw [ht₃];
            exact ⟨ by rw [ Classical.choose_spec ht₁ ] ; exact Order.le_succ _, fun β hβ => by aesop ⟩;
          exact le_trans hw_le_t ht₂;
        · exact SimpleGraph.Adj.ne' hadj;
      -- Since $s$ and $w$ are comparable and $s \not\leq w$, we must have $w < s$.
      have h_comparable : s ≤ w ∨ w ≤ s := by
        have := predecessors_chain u; exact this.total ( show s ∈ { x | x ≤ u } from hu ) ( show w ∈ { x | x ≤ u } from hw_lt_u.le ) ;
      exact lt_of_le_of_ne ( h_comparable.resolve_left hw ) ( by aesop );
    apply A_star_intersection u s hu |> fun h => h ⟨ by aesop, h_w_lt_s ⟩

/-
If a property holds at the start of a walk but not at the end, there is an edge where it flips.
-/
lemma exists_edge_property {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (P : V → Prop) (hu : P u) (hv : ¬ P v) :
  ∃ x y, G.Adj x y ∧ x ∈ p.support ∧ y ∈ p.support ∧ P x ∧ ¬ P y := by
    -- If the list is not empty, we can take the last element, which is v, and its predecessor, which is the second-to-last element.
    induction' p with u v p ih;
    · contradiction;
    · by_cases h : P p <;> aesop

/-
If two sequences are incomparable, they must differ at some index.
-/
lemma exists_diff_index (t1 t2 : T_struct) (h : ¬ (t1 ≤ t2) ∧ ¬ (t2 ≤ t1)) : ∃ α, ∃ (h1 : α < t1.α) (h2 : α < t2.α), t1.val.1 α h1 ≠ t2.val.1 α h2 := by
  -- Suppose for contradiction that for all α < min(t1.α, t2.α), t1(α) = t2(α).
  by_cases h_eq : t1.α ≤ t2.α;
  · contrapose! h;
    -- Since $t1.α \leq t2.α$, we can conclude that $t1 \leq t2$ by the definition of the partial order.
    have h_le : t1 ≤ t2 := by
      exact ⟨ h_eq, fun x hx => h x hx ( lt_of_lt_of_le hx h_eq ) ⟩;
    tauto;
  · contrapose! h;
    rintro -;
    refine' ⟨ le_of_not_ge h_eq, _ ⟩;
    exact fun β hβ => Eq.symm ( h β ( lt_of_lt_of_le hβ ( le_of_not_ge h_eq ) ) hβ )

/-
If a walk goes from a node u ≥ s to a node v not ≥ s, it must pass through A*_s.
-/
lemma boundary_of_subtree (s : T_struct) (h_succ : is_succ_ordinal s.α) (u v : T_struct) (hu : s ≤ u) (hv : ¬ (s ≤ v)) (p : G.Walk u v) : ∃ x ∈ p.support, x ∈ A_star s := by
  -- By `exists_edge_property`, there exist `x, y` in `p.support` such that `G.Adj x y`, `s ≤ x`, and `¬ (s ≤ y)`.
  obtain ⟨x, y, hxy, hx, hy⟩ : ∃ x y : T_struct, G.Adj x y ∧ x ∈ p.support ∧ y ∈ p.support ∧ s ≤ x ∧ ¬(s ≤ y) := by
    exact exists_edge_property p (LE.le s) hu hv
  generalize_proofs at *; (
  exact ⟨ y, hy.1, by simpa using boundary_edge_property s h_succ x y hy.2.1 hy.2.2 hxy ⟩)

/-
The immediate predecessor of a successor sequence is strictly less than the sequence.
-/
lemma s_star_lt (t : T_struct) (h : is_succ_ordinal t.α) : s_star t h < t := by
  -- By definition of $s_star$, we know that $s_star t h \leq t$.
  have h_s_star_le_t : s_star t h ≤ t := by
    use le_of_lt (by
      rw [Classical.choose_spec h]
      exact Order.lt_succ _
    );
    aesop;
  refine' lt_of_le_of_ne h_s_star_le_t _;
  intro h_eqop;
  -- If $t = s_star t h$, then their lengths would be equal, contradicting the definition of $s_star$.
  have h_len_eq : t.α = (s_star t h).α := by
    rw [h_eqop];
  obtain ⟨ β, hβ ⟩ := h;
  unfold s_star at * ; aesop

/-
Any element in A*_t is strictly less than t.
-/
lemma mem_A_star_lt (t : T_struct) (u : T_struct) (h : u ∈ A_star t) : u < t := by
  obtain ⟨ s, h1, h2, rfl, h3 ⟩ := h;
  exact lt_of_lt_of_le ( s_star_lt s h1 ) h2

/-
Every uncountable set of vertices in G contains two points which are connected by only finitely many independent paths in G.
-/
theorem finite_adhesion_property : ∀ (A : Set T_struct), ¬ A.Countable → ∃ t1 ∈ A, ∃ t2 ∈ A, t1 ≠ t2 ∧ finite_independent_paths G t1 t2 := by
  intro A hA
  obtain ⟨t1, ht1, t2, ht2, h_ne, h_incomp⟩ : ∃ t1 ∈ A, ∃ t2 ∈ A, t1 ≠ t2 ∧ ¬ (t1 ≤ t2) ∧ ¬ (t2 ≤ t1) := by
    -- By `exists_incomparable_of_uncountable`, there exist `t1, t2 ∈ A` such that `t1` and `t2` are incomparable. Use this lemma.
    apply exists_incomparable_of_uncountable A hA
  obtain ⟨α, hα1, hα2, h_diff⟩ : ∃ α, ∃ (h1 : α < t1.α) (h2 : α < t2.α), t1.val.1 α h1 ≠ t2.val.1 α h2 := by
    -- By `exists_diff_index`, let `α` be the first index where they differ. Use this lemma.
    apply exists_diff_index t1 t2 h_incomp
  obtain ⟨s, hs_le_t1, hs_len⟩ : ∃ s, s ≤ t1 ∧ s.α = α + 1 := by
    -- Apply the lemma exists_prefix with α + 1 and the fact that α + 1 ≤ t1.α (since α < t1.α implies α + 1 ≤ t1.α).
    apply exists_prefix t1 (α + 1) (by
    exact Order.add_one_le_iff.mpr hα1)
  have hs_succ : is_succ_ordinal s.α := by
    exact ⟨ α, hs_len ⟩
  have hs_not_le_t2 : ¬ (s ≤ t2) := by
    intro h;
    cases hs_le_t1 ; cases h ; aesop
  have h_sep : ∀ p : G.Walk t1 t2, ∃ v ∈ p.support, v ∈ A_star s := by
    -- Apply the boundary_of_subtree lemma with u = t1 and v = t2.
    apply boundary_of_subtree s hs_succ t1 t2 hs_le_t1 hs_not_le_t2
  have h_finite : (A_star s).Finite := by
    -- Apply the lemma that states A_star s is finite when s is a successor ordinal.
    apply A_star_finite_of_succ s hs_succ
  have h_t1_not_mem : t1 ∉ A_star s := by
    -- By definition of $A^*_s$, if $t1 \in A^*_s$, then $t1$ must be strictly less than $s$.
    intro h_mem
    have h_lt_s : t1 < s := by
      -- By definition of $A^*_s$, if $t1 \in A^*_s$, then $t1$ must be strictly less than $s$ because $A^*_s$ consists of elements that are strictly less than $s$.
      apply mem_A_star_lt s t1 h_mem
    generalize_proofs at *;
    exact lt_irrefl t1 (lt_of_lt_of_le h_lt_s hs_le_t1)
  have h_t2_not_mem : t2 ∉ A_star s := by
    -- By `mem_A_star_lt`, if `t2 ∈ A_star s`, then `t2 < s`.
    by_contra h_contra
    have h_lt : t2 < s := by
      exact mem_A_star_lt s t2 h_contra
    generalize_proofs at *; (
    -- Since $t2 < s$ and $s \le t1$, we have $t2 < t1$, contradicting $h_incomp$.
    have h_contra : t2 < t1 := by
      -- Since $t2 < s$ and $s \leq t1$, we can conclude $t2 < t1$ by transitivity.
      apply lt_of_lt_of_le h_lt hs_le_t1
    generalize_proofs at *; (exact h_incomp.2 (le_of_lt h_contra)))
  refine ⟨t1, ht1, t2, ht2, h_ne, ?_⟩
  apply finite_independent_paths_of_finite_separator (A_star s) h_finite h_t1_not_mem h_t2_not_mem h_sep

/-
Helper function for appending a value.
-/
noncomputable def T_append_val (t : T_struct) (n : ℕ) : (β : Ordinal) → β < Order.succ t.α → ℕ :=
  fun β _ => if h : β < t.α then t.val.1 β h else n

/-
The image of the appended value function is co-infinite.
-/
lemma T_append_cofinite (t : T_struct) (n : ℕ) :
  (Set.range (fun x : {β // β < Order.succ t.α} => T_append_val t n x.1 x.2))ᶜ.Infinite := by
    unfold T_append_val;
    refine' Set.Infinite.mono _ ( t.val.2.2.diff <| Set.finite_singleton n );
    intro x hx; aesop

/-- The function for the appended sequence. -/
noncomputable def T_append_func (t : T_struct) (n : ℕ) : {β // β < Order.succ t.α} → ℕ :=
  fun x => T_append_val t n x.1 x.2

/-
Value of T_append_func for indices less than t.α.
-/
/-- Value of T_append_func for indices less than t.α. -/
lemma T_append_func_lt (t : T_struct) (n : ℕ) (x : Ordinal) (hx : x < Order.succ t.α) (h_lt : x < t.α) :
  T_append_func t n ⟨x, hx⟩ = t.val.1 x h_lt := by
    -- By definition of T_append_func, we have T_append_func t n ⟨x, hx⟩ = T_append_val t n x hx.
    simp [T_append_func, T_append_val];
    grind

/-
Value of T_append_func at the last index.
-/
/-- Value of T_append_func at the last index. -/
lemma T_append_func_last (t : T_struct) (n : ℕ) :
  T_append_func t n ⟨t.α, Order.lt_succ t.α⟩ = n := by
    unfold T_append_func T_append_val; aesop;

/-
The image of T_append_func is the union of the image of t and {n}.
-/
/-- The image of T_append_func is the union of the image of t and {n}. -/
lemma range_T_append_func (t : T_struct) (n : ℕ) :
  Set.range (T_append_func t n) = im t ∪ {n} := by
    -- To prove equality of sets, we show each set is a subset of the other.
    apply Set.ext
    intro y
    simp [T_append_func, im];
    constructor <;> intro h;
    · unfold T_append_val at h; aesop;
    · rcases h with ( rfl | ⟨ a, ha, rfl ⟩ ) <;> [ refine' ⟨ t.α, le_rfl, _ ⟩ ; refine' ⟨ a, le_of_lt ha, _ ⟩ ] <;> unfold T_append_val <;> aesop

/-
If the index is less than t.α, the value is in im t.
-/
/-- If the index is less than t.α, the value is in im t. -/
lemma T_append_func_mem_im_of_lt (t : T_struct) (n : ℕ) (x : {β // β < Order.succ t.α}) (h : x.1 < t.α) :
  T_append_func t n x ∈ im t := by
    exact T_append_func_lt t n x.1 x.2 h ▸ ⟨ ⟨ _, h ⟩, rfl ⟩

/-
Explicit injectivity of T_append_func.
-/
/-- Explicit injectivity of T_append_func. -/
lemma T_append_func_injective_explicit (t : T_struct) (n : ℕ) (hn : n ∉ im t) :
  ∀ x y : {β // β < Order.succ t.α}, T_append_func t n x = T_append_func t n y → x = y := by
    intro x y hxyop;
    -- By definition of T_append_func, if T_append_func t n x = T_append_func t n y, then either both x and y are less than t.α, or one of them is equal to t.α.
    by_cases hx : x.1 < t.α
    by_cases hy : y.1 < t.α;
    · have h_inj : Function.Injective (fun x : {β // β < t.α} => t.val.1 x.1 x.2) := by
        exact t.val.2.1;
      have h_eq : t.val.1 x.1 hx = t.val.1 y.1 hy := by
        convert hxyop using 1;
        · exact T_append_func_lt t n x.1 x.2 hx ▸ rfl;
        · exact Eq.symm ( T_append_func_lt t n y.1 y.2 hy );
      have := @h_inj ⟨ x, hx ⟩ ⟨ y, hy ⟩ ; aesop;
    · -- Since $y.1 \geq t.α$, we have $T_append_func t n y = n$.
      have hy_val : T_append_func t n y = n := by
        exact dif_neg ( by simpa using hy );
      exact False.elim <| hn <| hy_val ▸ hxyop ▸ T_append_func_mem_im_of_lt t n x hx;
    · -- Since $x$ is not less than $t.α$, we have $x.1 = t.α$.
      have hx_eq : x.1 = t.α := by
        exact le_antisymm ( Order.le_of_lt_succ x.2 ) ( not_lt.mp hx );
      -- Since $x$ is not less than $t.α$, we have $T_append_func t n x = n$.
      have hx_val : T_append_func t n x = n := by
        convert T_append_func_last t n;
      -- Since $n \notin im t$, we have $T_append_func t n y = n$ implies $y.1 = t.α$.
      have hy_eq : y.1 = t.α := by
        by_cases hy : y.1 < t.α;
        · exact False.elim <| hn <| hx_val ▸ hxyop ▸ T_append_func_mem_im_of_lt t n y hy;
        · exact le_antisymm ( Order.le_of_lt_succ y.2 ) ( not_lt.mp hy );
      grind

/-
T_append_func is injective if n is not in the image of t.
-/
/-- T_append_func is injective if n is not in the image of t. -/
lemma T_append_func_injective (t : T_struct) (n : ℕ) (hn : n ∉ im t) :
  Function.Injective (T_append_func t n) := by
    convert T_append_func_injective_explicit t n hn using 1

/-
Appending a value to a sequence in T.
-/
/-- Appending a value to a sequence in T. -/
noncomputable def T_append (t : T_struct) (n : ℕ) (hn : n ∉ im t) : T_struct :=
  T_struct.mk (Order.succ t.α) ⟨T_append_val t n, ⟨T_append_func_injective t n hn, T_append_cofinite t n⟩⟩

/-
The appended sequence is a successor ordinal.
-/
/-- The appended sequence is a successor ordinal. -/
lemma T_append_is_succ (t : T_struct) (n : ℕ) (hn : n ∉ im t) : is_succ_ordinal (T_append t n hn).α := by
  exact ⟨ t.α, rfl ⟩

/-
The last element of the appended sequence is n.
-/
/-- The last element of the appended sequence is n. -/
lemma T_append_last (t : T_struct) (n : ℕ) (hn : n ∉ im t) (h : is_succ_ordinal (T_append t n hn).α) :
  last (T_append t n hn) h = n := by
    convert T_append_func_last t n;
    rw [ last ];
    unfold T_append at * ; aesop

/-
The predecessor of the appended sequence is t.
-/
/-- The predecessor of the appended sequence is t. -/
lemma T_append_s_star (t : T_struct) (n : ℕ) (hn : n ∉ im t) (h : is_succ_ordinal (T_append t n hn).α) :
  s_star (T_append t n hn) h = t := by
    -- By definition of $s_star$, we have that $s_star (T_append t n hn) h = t$.
    apply eq_of_le_of_alpha_eq;
    · unfold s_star T_append;
      refine' ⟨ _, _ ⟩;
      all_goals norm_num +zetaDelta at *;
      unfold T_append_val; aesop;
    · unfold s_star;
      unfold T_append at *; aesop;

/-
The image of the appended sequence is the union of the image of t and {n}.
-/
/-- The image of the appended sequence is the union of the image of t and {n}. -/
lemma im_T_append (t : T_struct) (n : ℕ) (hn : n ∉ im t) :
  im (T_append t n hn) = im t ∪ {n} := by
    convert range_T_append_func t n

/-
An infinite clique in a properly colored graph cannot have bounded colors.
-/
/-- An infinite clique in a properly colored graph cannot have bounded colors. -/
lemma infinite_clique_unbounded_colors {V : Type*} (G : SimpleGraph V) (c : G.Coloring ℕ) (K : Set V) (hK : G.IsClique K) (hK_inf : K.Infinite) :
  ¬ BddAbove (Set.image c K) := by
    rintro ⟨ B, hB ⟩;
    -- Since $K$ is an infinite clique, for any two distinct vertices $u, v \in K$, we have $G.Adj u v$.
    have h_adj : ∀ u v : V, u ∈ K → v ∈ K → u ≠ v → G.Adj u v := by
      exact fun u v hu hv huv => hK hu hv huv;
    -- Since $K$ is an infinite clique, for any two distinct vertices $u, v \in K$, we have $c u ≠ c v$.
    have h_distinct_colors : ∀ u v : V, u ∈ K → v ∈ K → u ≠ v → c u ≠ c v := by
      exact fun u v hu hv huv => c.valid ( h_adj u v hu hv huv );
    have h_infinite_colors : Set.Infinite (c '' K) := by
      exact Set.Infinite.image ( fun u => by contrapose! h_distinct_colors; aesop ) hK_inf;
    exact h_infinite_colors ( Set.finite_iff_bddAbove.mpr ⟨ B, hB ⟩ )

/-
The element skipped by a 1-extension is the smallest missing number greater than the last element of t.
-/
/-- The element skipped by a 1-extension. -/
noncomputable def skipped_element (t : T_struct) (ht : is_succ_ordinal t.α) : ℕ :=
  next_missing t (last t ht)

/-
The skipped element is not in the image of t.
-/
/-- The skipped element is not in the image of t. -/
lemma skipped_element_not_mem_im (t : T_struct) (ht : is_succ_ordinal t.α) :
  skipped_element t ht ∉ im t := by
    -- By definition of `next_missing`, the element `next_missing t (last t ht)` is the smallest natural number greater than `last t ht` that is not in the image of `t`.
    have h_next_missing_def : ∃ n, n ∉ im t ∧ n > last t ht ∧ ∀ m, m ∉ im t → m > last t ht → n ≤ m := by
      have h_nonempty : ∃ n, n ∉ im t ∧ n > last t ht := by
        have h_nonempty : Set.Infinite (Set.range (fun x : {β // β < t.α} => t.val.1 x.1 x.2))ᶜ := by
          exact t.2.2.2;
        exact Exists.elim ( h_nonempty.exists_gt ( last t ht ) ) fun n hn => ⟨ n, hn.1, hn.2 ⟩;
      exact ⟨ Nat.find h_nonempty, Nat.find_spec h_nonempty |>.1, Nat.find_spec h_nonempty |>.2, fun m hm₁ hm₂ => Nat.find_min' h_nonempty ⟨ hm₁, hm₂ ⟩ ⟩;
    cases' h_next_missing_def with n hn;
    have h_next_missing_eq : sInf {n | n ∉ im t ∧ n > last t ht} = n := by
      exact le_antisymm ( csInf_le ⟨ _, fun m hm => hn.2.2 m hm.1 hm.2 ⟩ ⟨ hn.1, hn.2.1 ⟩ ) ( le_csInf ⟨ n, hn.1, hn.2.1 ⟩ fun m hm => hn.2.2 m hm.1 hm.2 );
    unfold skipped_element; aesop;

/-
The skipped element is greater than the last element.
-/
/-- The skipped element is greater than the last element. -/
lemma skipped_element_gt_last (t : T_struct) (ht : is_succ_ordinal t.α) :
  skipped_element t ht > last t ht := by
    -- Since every element in the set {n | n ∉ im t ∧ n > last t ht} is greater than last t ht, the infimum of this set must also be greater than last t ht.
    have h_inf_gt : ∀ n ∈ {n | n ∉ im t ∧ n > last t ht}, n > last t ht := by
      grind;
    -- Since the set {n | n ∉ im t ∧ n > last t ht} is non-empty, its infimum is greater than last t ht.
    have h_nonempty : {n | n ∉ im t ∧ n > last t ht}.Nonempty := by
      have h_nonempty : Set.Infinite (Set.range (fun x : {β // β < t.α} => t.val.1 x.1 x.2))ᶜ := by
        convert t.val.2.2 using 1;
      exact Set.Infinite.nonempty ( h_nonempty.diff ( Set.finite_le_nat ( last t ht ) ) ) |> fun ⟨ n, hn ⟩ => ⟨ n, hn.1, not_le.mp fun h => hn.2 <| Set.mem_setOf_eq.mpr h ⟩;
    -- Since the set {n | n ∉ im t ∧ n > last t ht} is non-empty, its infimum is greater than last t ht by the definition of infimum.
    apply Nat.sInf_mem h_nonempty |> fun h => h_inf_gt _ h

/-
A vertex t0 is a counterexample if all its extensions have a "bad" 1-extension.
-/
/-- A vertex t0 is a counterexample if all its extensions have a "bad" 1-extension. -/
def is_counterexample (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) : Prop :=
  ∀ t' (ht' : is_succ_ordinal t'.α), extension t0 ht0 t' →
    ∃ t'', one_extension t' ht' t'' ∧ c t'' ≤ c (s_star t0 ht0)

/-
Helper definitions to extract the "bad" 1-extension from a counterexample.
-/
/-- Choose a 1-extension with bounded color from a counterexample. -/
noncomputable def choose_extension (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α)
  (h_counter : is_counterexample c t0 ht0) (t : T_struct) (ht : is_succ_ordinal t.α) (h_ext : extension t0 ht0 t) : T_struct :=
  Classical.choose (h_counter t ht h_ext)

/-- The chosen extension is a 1-extension. -/
lemma choose_extension_is_one_extension (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α)
  (h_counter : is_counterexample c t0 ht0) (t : T_struct) (ht : is_succ_ordinal t.α) (h_ext : extension t0 ht0 t) :
  one_extension t ht (choose_extension c t0 ht0 h_counter t ht h_ext) :=
  (Classical.choose_spec (h_counter t ht h_ext)).1

/-- The chosen extension has bounded color. -/
lemma choose_extension_color_le (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α)
  (h_counter : is_counterexample c t0 ht0) (t : T_struct) (ht : is_succ_ordinal t.α) (h_ext : extension t0 ht0 t) :
  c (choose_extension c t0 ht0 h_counter t ht h_ext) ≤ c (s_star t0 ht0) :=
  (Classical.choose_spec (h_counter t ht h_ext)).2

/-
Reflexivity of extension.
-/
/-- Reflexivity of extension. -/
lemma extension_refl (t : T_struct) (ht : is_succ_ordinal t.α) : extension t ht t := by
  exact ⟨ le_rfl, by aesop ⟩

/-
One-extension implies extension.
-/
/-- One-extension implies extension. -/
lemma one_extension_implies_extension (t : T_struct) (ht : is_succ_ordinal t.α) (t' : T_struct) :
  one_extension t ht t' → extension t ht t' := by
    intro h_one_extension
    obtain ⟨t'_lt, t'_missing⟩ := h_one_extension
    have t'_le : t ≤ t' := by
      exact le_of_lt t'_lt;
    exact ⟨ t'_le, fun n hn => t'_missing n hn |> lt_of_le_of_lt ( skipped_element_gt_last t ht |> le_of_lt ) ⟩

/-
Transitivity of extension.
-/
/-- Transitivity of extension. -/
lemma extension_trans (t1 : T_struct) (h1 : is_succ_ordinal t1.α) (t2 : T_struct) (h2 : is_succ_ordinal t2.α) (t3 : T_struct) :
  extension t1 h1 t2 → extension t2 h2 t3 → last t2 h2 > last t1 h1 → extension t1 h1 t3 := by
    intros h_ext1 h_ext2 h_last
    constructor;
    · exact le_trans h_ext1.1 h_ext2.1;
    · intro n hn; cases' em ( n ∈ im t2 ) with h h <;> simp_all +decide [ extension ] ;
      linarith [ h_ext2.2 n hn.1 h ]

/-
If t' is a 1-extension of t, then the skipped element is not in the image of t'.
-/
/-- If t' is a 1-extension of t, then the skipped element is not in the image of t'. -/
lemma skipped_element_not_mem_im_of_one_extension (t : T_struct) (ht : is_succ_ordinal t.α) (t' : T_struct) :
  one_extension t ht t' → skipped_element t ht ∉ im t' := by
    intro h
    obtain ⟨h_lt, h_one_ext⟩ := h
    by_contra h_contra;
    by_cases h_in_t : skipped_element t ht ∈ im t;
    · exact absurd h_in_t ( skipped_element_not_mem_im t ht );
    · exact absurd ( h_one_ext _ ⟨ h_contra, h_in_t ⟩ ) ( by simp +decide [ skipped_element ] )

/-
Appending the skipped element creates an extension.
-/
/-- Appending the skipped element creates an extension. -/
lemma T_append_skipped_element_extension (t : T_struct) (ht : is_succ_ordinal t.α) (t' : T_struct) (h_one : one_extension t ht t') :
  extension t ht (T_append t' (skipped_element t ht) (skipped_element_not_mem_im_of_one_extension t ht t' h_one)) := by
    refine' ⟨ _, _ ⟩
    generalize_proofs at *;
    · -- Since $t < t'$, we have $t \leq t'$.
      have h_le : t ≤ t' := by
        exact h_one.1.1;
      exact le_trans h_le ( by
        have h_le : t'.α ≤ (T_append t' (skipped_element t ht) ‹_›).α := by
          exact Order.le_succ _;
        exact ⟨ h_le, fun x hx => by
          -- Since $x < t'.α$, we can apply the definition of $T_append$ to conclude that $t'.val x hx = T_append t' (skipped_element t ht) pf✝.val x hx$.
          apply Eq.symm; exact (by
          convert T_append_func_lt t' ( skipped_element t ht ) x _ hx using 1;
          exact lt_of_lt_of_le hx ( Order.le_succ _ )) ⟩ );
    · intro n hn
      generalize_proofs at *;
      have h_im : n ∈ im t' ∪ {skipped_element t ht} := by
        have h_im : im (T_append t' (skipped_element t ht) ‹_›) = im t' ∪ {skipped_element t ht} := by
          (expose_names; exact im_T_append t' (skipped_element t ht) pf)
        generalize_proofs at *;
        aesop;
      generalize_proofs at *;
      have h_gt : n > last t ht := by
        cases h_im <;> simp_all +decide [ one_extension ];
        · exact lt_of_le_of_lt ( Nat.le_of_lt ( skipped_element_gt_last t ht ) ) ( h_one.2 n ‹_› ( by aesop ) );
        · exact skipped_element_gt_last t ht
      generalize_proofs at *;
      exact h_gt

/-
The last element of a successor sequence is not in the image of any of its proper prefixes.
-/
lemma last_not_mem_im_of_lt (t1 t2 : T_struct) (h2 : is_succ_ordinal t2.α) (hlt : t1 < t2) :
  last t2 h2 ∉ im t1 := by
    -- Since $t1 < t2$, the last element of $t2$ is not in the image of $t2$'s predecessor, and thus not in the image of $t1$.
    have h_not_in_predecessor : last t2 h2 ∉ im (s_star t2 h2) := by
      exact last_not_mem_im_s_star t2 h2;
    -- Since $t1 < t2$, we have $t1 \leq s_star t2 h2$.
    have h_le : t1 ≤ s_star t2 h2 := by
      exact s1_le_s_star_of_lt h2 hlt;
    exact fun h => h_not_in_predecessor <| im_subset_of_le h_le h

/-
If tn extends t0 strictly, then the last element of tn is greater than the last element of t0.
-/
lemma last_gt_last_of_extension (t0 tn : T_struct) (ht0 : is_succ_ordinal t0.α) (htn : is_succ_ordinal tn.α)
  (h_ext : extension t0 ht0 tn) (h_ne : tn ≠ t0) : last tn htn > last t0 ht0 := by
    obtain ⟨ hlt, hle ⟩ := h_ext;
    -- By last_not_mem_im_of_lt, last tn doesn't belong to the image of t0.
    have h_last_not_in_im_t0 : last tn htn ∉ im t0 := by
      apply last_not_mem_im_of_lt t0 tn htn;
      exact lt_of_le_of_ne hlt h_ne.symm;
    exact hle _ ⟨ by simp [ *, im_eq_im_s_star_union_last ], h_last_not_in_im_t0 ⟩

/-
Transitivity step for extension, handling the case where the intermediate vertex might be equal to the start.
-/
lemma extension_step (t0 tn tn_next : T_struct) (ht0 : is_succ_ordinal t0.α) (htn : is_succ_ordinal tn.α)
  (h_ext : extension t0 ht0 tn) (h_ext_next : extension tn htn tn_next) : extension t0 ht0 tn_next := by
    by_cases htn_eq_t0 : tn = t0;
    · unfold extension at *; aesop;
    · apply extension_trans t0 ht0 tn htn tn_next h_ext h_ext_next;
      apply last_gt_last_of_extension t0 tn ht0 htn h_ext htn_eq_t0

/-
The sequence of extensions constructed from a counterexample.
-/
noncomputable def bad_seq_data (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) :
  (n : ℕ) → { t // extension t0 ht0 t ∧ is_succ_ordinal t.α }
| 0 => ⟨t0, extension_refl t0 ht0, ht0⟩
| n + 1 =>
  let ⟨tn, h_ext, h_succ⟩ := bad_seq_data c t0 ht0 h_counter n
  let tn'' := choose_extension c t0 ht0 h_counter tn h_succ h_ext
  let h_one := choose_extension_is_one_extension c t0 ht0 h_counter tn h_succ h_ext
  let an := skipped_element tn h_succ
  let h_not_mem := skipped_element_not_mem_im_of_one_extension tn h_succ tn'' h_one
  let tn_next := T_append tn'' an h_not_mem
  let h_ext_next := T_append_skipped_element_extension tn h_succ tn'' h_one
  let h_trans := extension_step t0 tn tn_next ht0 h_succ h_ext h_ext_next
  let h_succ_next := T_append_is_succ tn'' an h_not_mem
  ⟨tn_next, h_trans, h_succ_next⟩

/-
The sequence tn and its properties.
-/
noncomputable def get_tn (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) : T_struct :=
  (bad_seq_data c t0 ht0 h_counter n).val

lemma get_tn_is_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  is_succ_ordinal (get_tn c t0 ht0 h_counter n).α :=
  (bad_seq_data c t0 ht0 h_counter n).property.2

lemma get_tn_extends (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  extension t0 ht0 (get_tn c t0 ht0 h_counter n) :=
  (bad_seq_data c t0 ht0 h_counter n).property.1

/-
Defining the intermediate extension tn'' and its property.
-/
noncomputable def get_tn_double_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) : T_struct :=
  choose_extension c t0 ht0 h_counter (get_tn c t0 ht0 h_counter n) (get_tn_is_succ c t0 ht0 h_counter n) (get_tn_extends c t0 ht0 h_counter n)

lemma get_tn_double_prime_is_one_extension (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  one_extension (get_tn c t0 ht0 h_counter n) (get_tn_is_succ c t0 ht0 h_counter n) (get_tn_double_prime c t0 ht0 h_counter n) := by
    exact Classical.choose_spec ( h_counter ( get_tn c t0 ht0 h_counter n ) ( get_tn_is_succ c t0 ht0 h_counter n ) ( get_tn_extends c t0 ht0 h_counter n ) ) |>.1

/-
The sequence of skipped elements an.
-/
noncomputable def get_an (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) : ℕ :=
  skipped_element (get_tn c t0 ht0 h_counter n) (get_tn_is_succ c t0 ht0 h_counter n)

/-
The skipped element is strictly greater than the last element of the current sequence.
-/
lemma get_an_gt_last (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  get_an c t0 ht0 h_counter n > last (get_tn c t0 ht0 h_counter n) (get_tn_is_succ c t0 ht0 h_counter n) := by
    exact skipped_element_gt_last _ _

/-
If a sequence is equal to an appended sequence, its last element is the appended value.
-/
lemma last_eq_of_eq_append {t1 : T_struct} {t2 : T_struct} {n : ℕ} {hn : n ∉ im t2} (h1 : is_succ_ordinal t1.α) (heq : t1 = T_append t2 n hn) : last t1 h1 = n := by
  convert T_append_last t2 n hn _ using 1;
  grind;
  exact T_append_is_succ t2 n hn

/-
The recurrence relation for the sequence tn.
-/
lemma get_tn_next_eq (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  get_tn c t0 ht0 h_counter (n + 1) = T_append (get_tn_double_prime c t0 ht0 h_counter n) (get_an c t0 ht0 h_counter n) (skipped_element_not_mem_im_of_one_extension (get_tn c t0 ht0 h_counter n) (get_tn_is_succ c t0 ht0 h_counter n) (get_tn_double_prime c t0 ht0 h_counter n) (get_tn_double_prime_is_one_extension c t0 ht0 h_counter n)) := by
    unfold get_tn get_tn_double_prime get_an;
    rw [ bad_seq_data ];
    unfold get_tn; aesop;

/-
The last element of the (n+1)-th sequence is the n-th skipped element.
-/
lemma last_get_tn_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  last (get_tn c t0 ht0 h_counter (n + 1)) (get_tn_is_succ c t0 ht0 h_counter (n + 1)) = get_an c t0 ht0 h_counter n := by
  apply last_eq_of_eq_append (get_tn_is_succ c t0 ht0 h_counter (n + 1)) (get_tn_next_eq c t0 ht0 h_counter n)

/-
The sequence of skipped elements is strictly increasing.
-/
lemma get_an_increasing (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  get_an c t0 ht0 h_counter n < get_an c t0 ht0 h_counter (n + 1) := by
    -- By definition of `get_an`, we have `get_an n = last (get_tn (n+1))`.
    have h_an_n : get_an c t0 ht0 h_counter n = last (get_tn c t0 ht0 h_counter (n + 1)) (get_tn_is_succ c t0 ht0 h_counter (n + 1)) := by
      exact Eq.symm (last_get_tn_succ c t0 ht0 h_counter n)
    generalize_proofs at *;
    exact h_an_n.symm ▸ get_an_gt_last _ _ _ _ _

/-
$t_n \le t_n''$.
-/
lemma get_tn_le_get_tn_double_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  get_tn c t0 ht0 h_counter n ≤ get_tn_double_prime c t0 ht0 h_counter n := by
  apply (one_extension_implies_extension _ _ _ (get_tn_double_prime_is_one_extension c t0 ht0 h_counter n)).1

/-
$t_n'' \le t_{n+1}$.
-/
lemma get_tn_double_prime_le_get_tn_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  get_tn_double_prime c t0 ht0 h_counter n ≤ get_tn c t0 ht0 h_counter (n + 1) := by
    have h_s_star_lt : s_star (get_tn c t0 ht0 h_counter (n + 1)) (get_tn_is_succ c t0 ht0 h_counter (n + 1)) < get_tn c t0 ht0 h_counter (n + 1) := by
      exact s_star_lt _ _;
    -- By definition of $s_star$, we know that $s_star (get_tn c t0 ht0 h_counter (n + 1)) (get_tn_is_succ c t0 ht0 h_counter (n + 1)) = get_tn_double_prime c t0 ht0 h_counter n$.
    have h_s_star_eq : s_star (get_tn c t0 ht0 h_counter (n + 1)) (get_tn_is_succ c t0 ht0 h_counter (n + 1)) = get_tn_double_prime c t0 ht0 h_counter n := by
      convert T_append_s_star _ _ _ _;
      convert get_tn_next_eq c t0 ht0 h_counter n;
      exact
        T_append_is_succ (get_tn_double_prime c t0 ht0 h_counter n) (get_an c t0 ht0 h_counter n)
          (skipped_element_not_mem_im_of_one_extension (get_tn c t0 ht0 h_counter n)
            (get_tn_is_succ c t0 ht0 h_counter n) (get_tn_double_prime c t0 ht0 h_counter n)
            (get_tn_double_prime_is_one_extension c t0 ht0 h_counter n));
    exact h_s_star_eq ▸ le_of_lt h_s_star_lt

/-
The sequence tn is monotonic.
-/
lemma get_tn_mono (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) {m n : ℕ} (h : m ≤ n) :
  get_tn c t0 ht0 h_counter m ≤ get_tn c t0 ht0 h_counter n := by
    induction' h with k hk ih;
    · rfl;
    · exact le_trans ih ( le_trans ( get_tn_le_get_tn_double_prime _ _ _ _ _ ) ( get_tn_double_prime_le_get_tn_succ _ _ _ _ _ ) )

/-
The sequence tn'' is monotonic.
-/
lemma get_tn_double_prime_mono (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) {m n : ℕ} (h : m ≤ n) :
  get_tn_double_prime c t0 ht0 h_counter m ≤ get_tn_double_prime c t0 ht0 h_counter n := by
    -- By definition of `get_tn_double_prime`, we know that `get_tn_double_prime m ≤ get_tn (m + 1)`.
    have h_le_tn_succ : get_tn_double_prime c t0 ht0 h_counter m ≤ get_tn c t0 ht0 h_counter (m + 1) := by
      exact get_tn_double_prime_le_get_tn_succ c t0 ht0 h_counter m;
    by_cases hmn : m < n;
    · -- By definition of `get_tn_double_prime`, we know that `get_tn_double_prime m ≤ get_tn (m + 1) ≤ get_tn n`.
      have h_le_tn : get_tn_double_prime c t0 ht0 h_counter m ≤ get_tn c t0 ht0 h_counter n := by
        exact le_trans h_le_tn_succ ( get_tn_mono c t0 ht0 h_counter ( Nat.succ_le_of_lt hmn ) );
      -- By definition of `get_tn_double_prime`, we know that `get_tn n ≤ get_tn_double_prime n`.
      have h_le_tn_double_prime : get_tn c t0 ht0 h_counter n ≤ get_tn_double_prime c t0 ht0 h_counter n := by
        exact get_tn_le_get_tn_double_prime c t0 ht0 h_counter n
      exact le_trans h_le_tn h_le_tn_double_prime;
    · cases eq_or_lt_of_le h <;> aesop

/-
The predecessor of $t_{n+1}$ is $t_n''$.
-/
lemma s_star_tn_next (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  s_star (get_tn c t0 ht0 h_counter (n + 1)) (get_tn_is_succ c t0 ht0 h_counter (n + 1)) = get_tn_double_prime c t0 ht0 h_counter n := by
    convert T_append_s_star _ _ _ _ using 1;
    congr! 1;
    convert get_tn_next_eq c t0 ht0 h_counter n using 1;
    exact
      T_append_is_succ (get_tn_double_prime c t0 ht0 h_counter n) (get_an c t0 ht0 h_counter n)
        (skipped_element_not_mem_im_of_one_extension (get_tn c t0 ht0 h_counter n)
          (get_tn_is_succ c t0 ht0 h_counter n) (get_tn_double_prime c t0 ht0 h_counter n)
          (get_tn_double_prime_is_one_extension c t0 ht0 h_counter n))

/-
The n-th skipped element is in the image of the (n+1)-th sequence.
-/
lemma get_an_mem_im_tn_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  get_an c t0 ht0 h_counter n ∈ im (get_tn c t0 ht0 h_counter (n + 1)) := by
  rw [get_tn_next_eq c t0 ht0 h_counter n]
  rw [im_T_append]
  exact Set.mem_union_right _ (Set.mem_singleton _)

/-
The appended element is in the image of the appended sequence.
-/
lemma mem_im_T_append (t : T_struct) (n : ℕ) (hn : n ∉ im t) : n ∈ im (T_append t n hn) := by
  rw [im_T_append]
  exact Set.mem_union_right _ (Set.mem_singleton _)

/-
The sequence vn and its properties.
-/
noncomputable def get_vn (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) : T_struct :=
  get_tn_double_prime c t0 ht0 h_counter n

lemma get_vn_le_tn_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  get_vn c t0 ht0 h_counter n ≤ get_tn c t0 ht0 h_counter (n + 1) :=
  get_tn_double_prime_le_get_tn_succ c t0 ht0 h_counter n

/-
$t_{m+1} \le t_n''$ for $m < n$.
-/
lemma get_tn_succ_le_get_tn_double_prime_of_lt (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) {m n : ℕ} (h : m < n) :
  get_tn c t0 ht0 h_counter (m + 1) ≤ get_tn_double_prime c t0 ht0 h_counter n := by
  apply le_trans (get_tn_mono c t0 ht0 h_counter (Nat.succ_le_of_lt h))
  apply get_tn_le_get_tn_double_prime

/-
The m-th skipped element is in the image of the n-th sequence for m < n.
-/
lemma get_an_mem_im_vn_of_lt (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) {m n : ℕ} (h : m < n) :
  get_an c t0 ht0 h_counter m ∈ im (get_vn c t0 ht0 h_counter n) := by
  apply im_subset_of_le (get_tn_succ_le_get_tn_double_prime_of_lt c t0 ht0 h_counter h)
  apply get_an_mem_im_tn_succ

/-
The n-th skipped element is not in the image of the n-th sequence.
-/
lemma get_an_not_mem_im_vn (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  get_an c t0 ht0 h_counter n ∉ im (get_vn c t0 ht0 h_counter n) := by
  apply skipped_element_not_mem_im_of_one_extension
  apply get_tn_double_prime_is_one_extension

/-
The image of $t_{n+1}$ is the image of $t_n''$ union $\{a_n\}$.
-/
lemma im_tn_succ_eq_im_vn_union_an (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  im (get_tn c t0 ht0 h_counter (n + 1)) = im (get_vn c t0 ht0 h_counter n) ∪ {get_an c t0 ht0 h_counter n} := by
  rw [get_tn_next_eq c t0 ht0 h_counter n]
  rw [im_T_append]
  rfl

/-
The difference between the image of $t_{n+1}$ and $t_n''$ is exactly $\{a_n\}$.
-/
lemma im_tn_succ_diff_im_vn (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  im (get_tn c t0 ht0 h_counter (n + 1)) \ im (get_vn c t0 ht0 h_counter n) = {get_an c t0 ht0 h_counter n} := by
    -- By definition of $im$, we know that $im (get_tn c t0 ht0 h_counter (n + 1)) = im (get_vn c t0 ht0 h_counter n) ∪ {get_an c t0 ht0 h_counter n}$.
    have h_im : im (get_tn c t0 ht0 h_counter (n + 1)) = im (get_vn c t0 ht0 h_counter n) ∪ {get_an c t0 ht0 h_counter n} := by
      exact im_tn_succ_eq_im_vn_union_an c t0 ht0 h_counter n;
    rw [ h_im, Set.union_diff_cancel_left ];
    simp +zetaDelta at *;
    exact get_an_not_mem_im_vn c t0 ht0 h_counter n

/-
Elements added in step n+1 are greater than or equal to the n-th skipped element.
-/
lemma im_vn_succ_diff_ge_an (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  ∀ x ∈ im (get_vn c t0 ht0 h_counter (n + 1)) \ im (get_vn c t0 ht0 h_counter n), x ≥ get_an c t0 ht0 h_counter n := by
    intro x hx
    by_contra h_contra;
    -- `x` must be in `im (get_vn c t0 ht0 h_counter (n + 1)) \ im (get_tn c t0 ht0 h_counter (n + 1))`.
    have hx_in_diff : x ∈ im (get_vn c t0 ht0 h_counter (n + 1)) \ im (get_tn c t0 ht0 h_counter (n + 1)) := by
      refine' ⟨ hx.1, _ ⟩;
      intro hx'_tn_succ
      have hx_in_im_vn : x ∈ im (get_vn c t0 ht0 h_counter n) := by
        have hx'_tn_succ : x ∈ im (get_tn c t0 ht0 h_counter (n + 1)) \ im (get_vn c t0 ht0 h_counter n) := by
          exact ⟨ hx'_tn_succ, hx.2 ⟩;
        have := im_tn_succ_diff_im_vn c t0 ht0 h_counter n; aesop;
      exact hx.2 hx_in_im_vn;
    -- By definition of `get_vn`, we know that `get_vn c t0 ht0 h_counter (n + 1)` is a 1-extension of `get_tn c t0 ht0 h_counter (n + 1)`.
    have h_one_extension : one_extension (get_tn c t0 ht0 h_counter (n + 1)) (get_tn_is_succ c t0 ht0 h_counter (n + 1)) (get_vn c t0 ht0 h_counter (n + 1)) := by
      exact get_tn_double_prime_is_one_extension _ _ _ _ _ |> fun h => by aesop;
    rcases h_one_extension with ⟨h₁, h₂⟩;
    specialize h₂ x hx_in_diff;
    exact h_contra <| h₂.le.trans' <| le_of_lt <| by linarith! [ get_an_gt_last c t0 ht0 h_counter n, get_an_gt_last c t0 ht0 h_counter ( n + 1 ), last_get_tn_succ c t0 ht0 h_counter n, last_get_tn_succ c t0 ht0 h_counter ( n + 1 ) ] ;

/-
The `next_missing` value satisfies its defining properties.
-/
lemma next_missing_spec (t : T_struct) (k : ℕ) : next_missing t k ∉ im t ∧ next_missing t k > k := by
  have h_next_missing_nonempty : {n | n ∉ im t ∧ n > k}.Nonempty := by
    -- Since the complement of `im t` is infinite, there must exist some element in the complement that is greater than `k`.
    have h_compl_inf : (im t)ᶜ.Infinite := by
      exact t.2.2.2;
    exact Exists.elim ( h_compl_inf.exists_gt k ) fun n hn => ⟨ n, hn.1, hn.2 ⟩;
  exact ⟨ Nat.sInf_mem h_next_missing_nonempty |>.1, Nat.sInf_mem h_next_missing_nonempty |>.2 ⟩

/-
The sequence `an` is monotonic.
-/
lemma get_an_mono (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) {m n : ℕ} (h : m ≤ n) :
  get_an c t0 ht0 h_counter m ≤ get_an c t0 ht0 h_counter n := by
  induction h with
  | refl => exact le_rfl
  | step h ih => exact le_trans ih (le_of_lt (get_an_increasing c t0 ht0 h_counter _))

/-
The m-th skipped element is the minimum of the difference between the n-th and m-th images.
-/
lemma get_an_is_min_diff (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) {m n : ℕ} (h : m < n) :
  get_an c t0 ht0 h_counter m = sInf (im (get_vn c t0 ht0 h_counter n) \ im (get_vn c t0 ht0 h_counter m)) := by
    refine' le_antisymm ( le_csInf _ _ ) ( csInf_le _ _ );
    · exact ⟨ _, get_an_mem_im_vn_of_lt c t0 ht0 h_counter h, get_an_not_mem_im_vn c t0 ht0 h_counter m ⟩;
    · norm_num +zetaDelta at *;
      intro b hb₁ hb₂;
      have h_diff : ∃ i ∈ Finset.Icc m (n - 1), b ∈ im (get_vn c t0 ht0 h_counter (i + 1)) ∧ b ∉ im (get_vn c t0 ht0 h_counter i) := by
        induction' h with k hk;
        · exact ⟨ m, by norm_num, hb₁, hb₂ ⟩;
        · by_cases h : b ∈ im (get_vn c t0 ht0 h_counter k);
          · exact Exists.elim ( ‹b ∈ im ( get_vn c t0 ht0 h_counter k ) → ∃ i ∈ Finset.Icc m ( k - 1 ), b ∈ im ( get_vn c t0 ht0 h_counter ( i + 1 ) ) ∧ b ∉ im ( get_vn c t0 ht0 h_counter i ) › h ) fun i hi => ⟨ i, Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hi.1 |>.1, Nat.le_trans ( Finset.mem_Icc.mp hi.1 |>.2 ) ( Nat.pred_le _ ) ⟩, hi.2.1, hi.2.2 ⟩;
          · exact ⟨ k, Finset.mem_Icc.mpr ⟨ by linarith [ Nat.succ_le_iff.mp hk ], by simp +decide ⟩, hb₁, h ⟩;
      obtain ⟨ i, hi₁, hi₂, hi₃ ⟩ := h_diff;
      refine' le_trans _ ( im_vn_succ_diff_ge_an c t0 ht0 h_counter i b _ );
      · exact get_an_mono c t0 ht0 h_counter ( Finset.mem_Icc.mp hi₁ |>.1 );
      · aesop;
    · exact ⟨ 0, fun x hx => Nat.zero_le x ⟩;
    · exact ⟨ get_an_mem_im_vn_of_lt _ _ _ _ h, get_an_not_mem_im_vn _ _ _ _ _ ⟩

/-
The sequence $t_n''$ forms a clique.
-/
lemma tn_double_prime_adj (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) {m n : ℕ} (h : m < n) :
  G.Adj (get_tn_double_prime c t0 ht0 h_counter m) (get_tn_double_prime c t0 ht0 h_counter n) := by
    -- By definition of $get_tn_double_prime$, we know that $get_tn_double_prime m$ is connected to $get_tn_double_prime n$ if there's a common element in their images that's greater than the last element of $get_tn_double_prime m$.
    have h_adj : get_tn c t0 ht0 h_counter (m + 1) ≤ get_tn_double_prime c t0 ht0 h_counter n ∧ s_star (get_tn c t0 ht0 h_counter (m + 1)) (get_tn_is_succ c t0 ht0 h_counter (m + 1)) = get_tn_double_prime c t0 ht0 h_counter m := by
      exact ⟨ get_tn_succ_le_get_tn_double_prime_of_lt c t0 ht0 h_counter h, s_star_tn_next c t0 ht0 h_counter m ⟩;
    -- By definition of $G.Adj$, we need to show that $get_tn_double_prime c t0 ht0 h_counter m$ and $get_tn_double_prime c t0 ht0 h_counter n$ differ by exactly one element and that element is greater than the last element of $get_tn_double_prime c t0 ht0 h_counter m$.
    apply And.intro;
    · intro h_eq; have := get_an_not_mem_im_vn c t0 ht0 h_counter m; have := get_an_not_mem_im_vn c t0 ht0 h_counter n; simp_all +decide ;
      have h_contra : get_an c t0 ht0 h_counter m ∈ im (get_vn c t0 ht0 h_counter n) := by
        exact get_an_mem_im_vn_of_lt c t0 ht0 h_counter h;
      unfold get_vn at *; aesop;
    · -- Since $get_tn (m+1)$ is an extension of $get_tn_double_prime m$, and $get_tn (m+1)$ is in $A_set (get_tn_double_prime n)$, it follows that $get_tn_double_prime m$ is in $A_star (get_tn_double_prime n)$.
      left
      exact (by
      use get_tn c t0 ht0 h_counter ( m + 1 );
      refine' ⟨ _, h_adj.1, h_adj.2.symm, _ ⟩;
      convert get_an_is_min_diff c t0 ht0 h_counter h using 1;
      exact last_get_tn_succ c t0 ht0 h_counter m)

/-
The sequence $t_n''$ forms a clique.
-/
lemma tn_double_prime_adj_new (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) {m n : ℕ} (h : m < n) :
  G.Adj (get_tn_double_prime c t0 ht0 h_counter m) (get_tn_double_prime c t0 ht0 h_counter n) := by
    exact tn_double_prime_adj c t0 ht0 h_counter h

/-
The sequence $t_n''$ forms a clique.
-/
lemma tn_double_prime_adj_final (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) {m n : ℕ} (h : m < n) :
  G.Adj (get_tn_double_prime c t0 ht0 h_counter m) (get_tn_double_prime c t0 ht0 h_counter n) := by
    convert tn_double_prime_adj_new c t0 ht0 h_counter h using 1

/-
The colors of the clique vertices are bounded.
-/
lemma get_tn_double_prime_color_le (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) (n : ℕ) :
  c (get_tn_double_prime c t0 ht0 h_counter n) ≤ c (s_star t0 ht0) := by
  apply choose_extension_color_le

/-
The sequence $t_n''$ is strictly monotonic.
-/
lemma get_tn_double_prime_strict_mono (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (h_counter : is_counterexample c t0 ht0) :
  StrictMono (get_tn_double_prime c t0 ht0 h_counter) := by
    -- By definition of `get_tn_double_prime`, we have `get_tn_double_prime c t0 ht0 h_counter (n + 1) > get_tn_double_prime c t0 ht0 h_counter n`.
    have h_strict_mono : ∀ n, get_tn_double_prime c t0 ht0 h_counter (n + 1) > get_tn_double_prime c t0 ht0 h_counter n := by
      intro n
      have h_le : get_tn_double_prime c t0 ht0 h_counter n ≤ get_tn_double_prime c t0 ht0 h_counter (n + 1) := by
        exact get_tn_double_prime_mono c t0 ht0 h_counter ( Nat.le_succ _ );
      refine' h_le.lt_of_ne' _;
      intro h_eq;
      have := get_tn_double_prime_is_one_extension c t0 ht0 h_counter ( n + 1 ) ; simp_all +decide [ one_extension ] ;
      exact this.1.not_ge ( get_vn_le_tn_succ c t0 ht0 h_counter n );
    exact strictMono_nat_of_lt_succ h_strict_mono

/-
The claim from the paper: every vertex has an extension with the property that all its 1-extensions have larger color.
-/
def claim_statement (c : G.Coloring ℕ) (t : T_struct) (ht : is_succ_ordinal t.α) : Prop :=
  ∃ t', ∃ (ht' : is_succ_ordinal t'.α), extension t ht t' ∧
    ∀ t'', one_extension t' ht' t'' → c t'' > c (s_star t ht)

/-
The claim from the paper holds: every vertex has an extension with the property that all its 1-extensions have larger color.
-/
lemma claim_true (c : G.Coloring ℕ) : ∀ t (ht : is_succ_ordinal t.α), claim_statement c t ht := by
  intro t ht;
  by_contra! h;
  -- By definition of `is_counterexample`, if `t` is a counterexample, then for all extensions `t'` of `t`, there exists a 1-extension `t''` of `t'` with `c t'' ≤ c (s_star t ht)`.
  have h_counterexample : is_counterexample c t ht := by
    intro t' ht' h_ext
    by_contra h_contra;
    exact h ⟨ t', ht', h_ext, fun t'' ht'' => not_not.mp fun h => h_contra ⟨ t'', ht'', le_of_not_gt h ⟩ ⟩;
  -- By definition of `is_counterexample`, the sequence `get_tn_double_prime` forms an infinite clique with bounded colors.
  have h_clique : Set.Infinite (Set.range (fun n => get_tn_double_prime c t ht h_counterexample n)) ∧ ∀ t'' ∈ Set.range (fun n => get_tn_double_prime c t ht h_counterexample n), c t'' ≤ c (s_star t ht) := by
    exact ⟨ Set.infinite_range_of_injective ( StrictMono.injective ( get_tn_double_prime_strict_mono c t ht h_counterexample ) ), by rintro _ ⟨ n, rfl ⟩ ; exact get_tn_double_prime_color_le c t ht h_counterexample n ⟩;
  -- Apply the lemma `infinite_clique_unbounded_colors` to obtain a contradiction.
  have := infinite_clique_unbounded_colors G c (Set.range (fun n => get_tn_double_prime c t ht h_counterexample n));
  exact this ( fun x hx y hy hxy => by obtain ⟨ m, rfl ⟩ := hx; obtain ⟨ n, rfl ⟩ := hy; exact if hmn : m < n then tn_double_prime_adj_final c t ht h_counterexample hmn else tn_double_prime_adj_final c t ht h_counterexample ( lt_of_le_of_ne ( le_of_not_gt hmn ) ( Ne.symm <| by aesop ) ) |> fun h => h.symm ) h_clique.1 <| ⟨ c ( s_star t ht ), Set.forall_mem_image.2 h_clique.2 ⟩

/-
Choice function for the extension guaranteed by the claim.
-/
noncomputable def choose_claim_extension (c : G.Coloring ℕ) (t : T_struct) (ht : is_succ_ordinal t.α) : T_struct :=
  Classical.choose (claim_true c t ht)

noncomputable def choose_claim_extension_is_succ (c : G.Coloring ℕ) (t : T_struct) (ht : is_succ_ordinal t.α) : is_succ_ordinal (choose_claim_extension c t ht).α :=
  Classical.choose (Classical.choose_spec (claim_true c t ht))

lemma choose_claim_extension_spec (c : G.Coloring ℕ) (t : T_struct) (ht : is_succ_ordinal t.α) :
  let t' := choose_claim_extension c t ht
  let ht' := choose_claim_extension_is_succ c t ht
  extension t ht t' ∧ ∀ t'', one_extension t' ht' t'' → c t'' > c (s_star t ht) :=
  Classical.choose_spec (Classical.choose_spec (claim_true c t ht))

/-
The sequence of vertices $t_n$ constructed in the proof.
-/
noncomputable def construction_seq_data (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) :
  (n : ℕ) → { t : T_struct // is_succ_ordinal t.α }
| 0 => ⟨t0, ht0⟩
| n + 1 =>
  let ⟨tn, htn⟩ := construction_seq_data c t0 ht0 n
  let tn' := choose_claim_extension c tn htn
  let htn' := choose_claim_extension_is_succ c tn htn
  let a_odd := next_missing tn' (last tn' htn')
  let a_even := next_missing tn' a_odd
  let tn_next := T_append tn' a_even (next_missing_spec tn' a_odd).1
  let htn_next := T_append_is_succ tn' a_even (next_missing_spec tn' a_odd).1
  ⟨tn_next, htn_next⟩

/-
Extracting the components of the construction.
-/
noncomputable def get_construction_tn (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) : T_struct :=
  (construction_seq_data c t0 ht0 n).val

lemma get_construction_tn_is_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  is_succ_ordinal (get_construction_tn c t0 ht0 n).α :=
  (construction_seq_data c t0 ht0 n).property

noncomputable def get_construction_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) : T_struct :=
  choose_claim_extension c (get_construction_tn c t0 ht0 n) (get_construction_tn_is_succ c t0 ht0 n)

lemma get_construction_tn_prime_is_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  is_succ_ordinal (get_construction_tn_prime c t0 ht0 n).α :=
  choose_claim_extension_is_succ c (get_construction_tn c t0 ht0 n) (get_construction_tn_is_succ c t0 ht0 n)

lemma get_construction_tn_prime_extends (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  extension (get_construction_tn c t0 ht0 n) (get_construction_tn_is_succ c t0 ht0 n) (get_construction_tn_prime c t0 ht0 n) :=
  (choose_claim_extension_spec c (get_construction_tn c t0 ht0 n) (get_construction_tn_is_succ c t0 ht0 n)).1

lemma get_construction_tn_prime_spec (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  ∀ t'', one_extension (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n) t'' →
    c t'' > c (s_star (get_construction_tn c t0 ht0 n) (get_construction_tn_is_succ c t0 ht0 n)) :=
  (choose_claim_extension_spec c (get_construction_tn c t0 ht0 n) (get_construction_tn_is_succ c t0 ht0 n)).2

/-
Extracting the skipped elements $a_{2n+1}$ and $a_{2n+2}$.
-/
noncomputable def get_construction_a_odd (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) : ℕ :=
  let tn' := get_construction_tn_prime c t0 ht0 n
  let htn' := get_construction_tn_prime_is_succ c t0 ht0 n
  next_missing tn' (last tn' htn')

noncomputable def get_construction_a_even (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) : ℕ :=
  let tn' := get_construction_tn_prime c t0 ht0 n
  next_missing tn' (get_construction_a_odd c t0 ht0 n)

lemma get_construction_tn_succ_eq (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  get_construction_tn c t0 ht0 (n + 1) = T_append (get_construction_tn_prime c t0 ht0 n) (get_construction_a_even c t0 ht0 n) (next_missing_spec (get_construction_tn_prime c t0 ht0 n) (get_construction_a_odd c t0 ht0 n)).1 := by
  simp [get_construction_tn, construction_seq_data, get_construction_tn_prime, get_construction_a_odd, get_construction_a_even]

/-
The constructed sequence $t_n$ is monotonic.
-/
lemma get_construction_tn_mono (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m ≤ n) :
  get_construction_tn c t0 ht0 m ≤ get_construction_tn c t0 ht0 n := by
    induction' h with n hn ih;
    · rfl;
    · refine' le_trans ih _;
      -- By definition of $get\_construction\_tn$, we have $get\_construction\_tn c t0 ht0 (n + 1) = T\_append (get\_construction\_tn\_prime c t0 ht0 n) (get\_construction\_a\_even c t0 ht0 n)$.
      rw [get_construction_tn_succ_eq];
      refine' le_trans _ ( s_star_lt _ _ |> le_of_lt );
      have := get_construction_tn_prime_extends c t0 ht0 n;
      convert this.1;
      exact T_append_s_star _ _ _ _;
      exact T_append_is_succ _ _ _

/-
The set of constructed vertices forms a chain.
-/
lemma construction_chain_is_chain (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) :
  IsChain (· ≤ ·) (Set.range (get_construction_tn c t0 ht0)) := by
  intro x hx y hy hxy
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  cases le_total m n with
  | inl h => left; exact get_construction_tn_mono c t0 ht0 h
  | inr h => right; exact get_construction_tn_mono c t0 ht0 h

/-
The limit sequence $\hat{t}$.
-/
noncomputable def t_hat (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) : Ordinal → ℕ :=
  chain_union (Set.range (get_construction_tn c t0 ht0)) (construction_chain_is_chain c t0 ht0)

/-
The odd skipped element is strictly less than the even skipped element.
-/
lemma get_construction_a_odd_lt_even (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  get_construction_a_odd c t0 ht0 n < get_construction_a_even c t0 ht0 n := by
  unfold get_construction_a_even
  apply (next_missing_spec _ _).2

/-
The odd skipped element is not in the image of the current prime sequence.
-/
lemma get_construction_a_odd_not_mem_im_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  get_construction_a_odd c t0 ht0 n ∉ im (get_construction_tn_prime c t0 ht0 n) := by
    exact next_missing_spec _ _ |>.1

/-
The odd skipped element is not in the image of the next sequence.
-/
lemma get_construction_a_odd_not_mem_im_tn_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  get_construction_a_odd c t0 ht0 n ∉ im (get_construction_tn c t0 ht0 (n + 1)) := by
    rw [ get_construction_tn_succ_eq ];
    rw [ im_T_append ];
    simp +zetaDelta at *;
    exact ⟨ by linarith [ get_construction_a_odd_lt_even c t0 ht0 n ], by simpa using get_construction_a_odd_not_mem_im_tn_prime c t0 ht0 n ⟩

/-
The difference between the image of the next sequence and the prime sequence is exactly the even skipped element.
-/
lemma im_tn_succ_diff_im_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  im (get_construction_tn c t0 ht0 (n + 1)) \ im (get_construction_tn_prime c t0 ht0 n) = {get_construction_a_even c t0 ht0 n} := by
    -- By definition of `get_construction_tn_succ_eq`, we have `im (get_construction_tn c t0 ht0 (n + 1)) = im (get_construction_tn_prime c t0 ht0 n) ∪ {get_construction_a_even c t0 ht0 n}`.
    have h_im_succ : im (get_construction_tn c t0 ht0 (n + 1)) = im (get_construction_tn_prime c t0 ht0 n) ∪ {get_construction_a_even c t0 ht0 n} := by
      rw [ get_construction_tn_succ_eq ];
      exact
        im_T_append (get_construction_tn_prime c t0 ht0 n) (get_construction_a_even c t0 ht0 n)
          (next_missing_spec (get_construction_tn_prime c t0 ht0 n)
              (get_construction_a_odd c t0 ht0 n)).left;
    -- By definition of set difference, we can rewrite the left-hand side using the union.
    simp [h_im_succ];
    ext x;
    by_cases hx : x = get_construction_a_even c t0 ht0 n <;> simp +decide [ hx ];
    exact next_missing_spec _ _ |>.1

/-
The last element of the (n+1)-th sequence is the even skipped element of step n.
-/
lemma last_construction_tn_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  last (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1)) = get_construction_a_even c t0 ht0 n := by
    have := get_construction_tn_succ_eq c t0 ht0 n
    generalize_proofs at *;
    (expose_names; exact last_eq_of_eq_append pf_1 this)

/-
The odd skipped element is strictly greater than the last element of the prime sequence.
-/
lemma get_construction_a_odd_gt_last_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  get_construction_a_odd c t0 ht0 n > last (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n) := by
    exact next_missing_spec _ _ |>.2

/-
The last element of the next sequence is greater than the last element of the prime sequence.
-/
lemma last_tn_succ_gt_last_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  last (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1)) > last (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n) := by
    -- By combining the results from `last_construction_tn_succ`, `get_construction_a_odd_lt_even`, and `get_construction_a_odd_gt_last_prime`, we can conclude the proof.
    have h_last_gt : last (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1)) = get_construction_a_even c t0 ht0 n ∧ get_construction_a_odd c t0 ht0 n < get_construction_a_even c t0 ht0 n ∧ get_construction_a_odd c t0 ht0 n > last (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n) := by
      exact ⟨ last_construction_tn_succ c t0 ht0 n, get_construction_a_odd_lt_even c t0 ht0 n, get_construction_a_odd_gt_last_prime c t0 ht0 n ⟩;
    linarith

/-
The last element of the prime sequence is at least the last element of the current sequence.
-/
lemma last_tn_prime_ge_last_tn (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  last (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n) ≥ last (get_construction_tn c t0 ht0 n) (get_construction_tn_is_succ c t0 ht0 n) := by
    by_cases h : get_construction_tn_prime c t0 ht0 n = get_construction_tn c t0 ht0 n;
    · grind;
    · have h_last_gt : last (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n) > last (get_construction_tn c t0 ht0 n) (get_construction_tn_is_succ c t0 ht0 n) := by
        apply last_gt_last_of_extension;
        · exact get_construction_tn_prime_extends c t0 ht0 n;
        · assumption;
      exact le_of_lt h_last_gt

/-
Elements added in step n+1 are strictly greater than the last element of step n.
-/
lemma im_construction_tn_succ_diff_gt_last (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  ∀ x ∈ im (get_construction_tn c t0 ht0 (n + 1)) \ im (get_construction_tn c t0 ht0 n), x > last (get_construction_tn c t0 ht0 n) (get_construction_tn_is_succ c t0 ht0 n) := by
    intro x hx_missing_spec
    generalize_proofs at *;
    -- By definition of $get_construction_tn$, we know that $x$ is either in the image of $get_construction_tn_prime c t0 ht0 n$ or is the even skipped element.
    by_cases hx_prime : x ∈ im (get_construction_tn_prime c t0 ht0 n)
    generalize_proofs at *;
    · have h_extension : extension (get_construction_tn c t0 ht0 n) ‹_› (get_construction_tn_prime c t0 ht0 n) := by
        exact get_construction_tn_prime_extends c t0 ht0 n;
      unfold extension at h_extension; aesop;
    · -- Since $x$ is not in the image of $get_construction_tn_prime c t0 ht0 n$, it must be the even skipped element.
      have hx_even : x = get_construction_a_even c t0 ht0 n := by
        have := im_tn_succ_diff_im_tn_prime c t0 ht0 n; simp_all +decide [ Set.ext_iff ] ;
        grind
      generalize_proofs at *;
      -- Since $a_{odd} n > last (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n)$ and $a_{even} n > a_{odd} n$, we have $a_{even} n > last (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n)$.
      have h_even_gt_last_prime : get_construction_a_even c t0 ht0 n > last (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n) := by
        exact lt_trans ( get_construction_a_odd_gt_last_prime c t0 ht0 n ) ( get_construction_a_odd_lt_even c t0 ht0 n )
      generalize_proofs at *;
      exact hx_even.symm ▸ lt_of_le_of_lt ( last_tn_prime_ge_last_tn c t0 ht0 n ) h_even_gt_last_prime

/-
The odd skipped element is strictly less than the last element of the next sequence.
-/
lemma get_construction_a_odd_lt_last_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  get_construction_a_odd c t0 ht0 n < last (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1)) := by
    have := get_construction_a_odd_lt_even c t0 ht0 n; ( have := last_construction_tn_succ c t0 ht0 n; ( aesop ) ; )

/-
The last element of the next sequence is strictly less than the next odd skipped element.
-/
lemma last_succ_lt_get_construction_a_odd_succ (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  last (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1)) < get_construction_a_odd c t0 ht0 (n + 1) := by
    exact last_tn_prime_ge_last_tn c t0 ht0 ( n + 1 ) |> lt_of_le_of_lt <| get_construction_a_odd_gt_last_prime c t0 ht0 ( n + 1 )

/-
The (m+1)-th sequence is less than or equal to the n-th prime sequence for m < n.
-/
lemma get_construction_tn_succ_le_tn_prime_of_lt (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m < n) :
  get_construction_tn c t0 ht0 (m + 1) ≤ get_construction_tn_prime c t0 ht0 n := by
    -- Since $m < n$, we have $m + 1 \leq n$.
    have h_le : m + 1 ≤ n := by
      grind;
    -- Since $m + 1 \leq n$, we can apply the monotonicity of the sequence.
    have h_monotone : get_construction_tn c t0 ht0 (m + 1) ≤ get_construction_tn c t0 ht0 n := by
      exact get_construction_tn_mono c t0 ht0 h_le;
    refine le_trans h_monotone ?_;
    have := get_construction_tn_prime_extends c t0 ht0 n;
    cases this ; aesop

/-
The sequence of odd skipped elements is strictly increasing.
-/
lemma get_construction_a_odd_strict_mono (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  get_construction_a_odd c t0 ht0 n < get_construction_a_odd c t0 ht0 (n + 1) := by
    -- By the properties of the sequences, we know that `a_odd (n+1) > last (tn (n+1))` (by `last_succ_lt_get_construction_a_odd_succ`).
    have h_lastlt_a_odd_succ : last (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1)) < get_construction_a_odd c t0 ht0 (n + 1) := by
      exact last_succ_lt_get_construction_a_odd_succ c t0 ht0 n;
    -- By the properties of the sequences, we know that `last (tn (n+1)) = a_even n` (by `last_construction_tn_succ`).
    have h_last_eq_a_even : last (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1)) = get_construction_a_even c t0 ht0 n := by
      exact last_construction_tn_succ c t0 ht0 n;
    linarith [ get_construction_a_odd_lt_even c t0 ht0 n ]

/-
The last element of the m-th sequence is strictly greater than the n-th odd skipped element for m > n.
-/
lemma last_construction_tn_gt_a_odd_of_gt (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m > n) :
  last (get_construction_tn c t0 ht0 m) (get_construction_tn_is_succ c t0 ht0 m) > get_construction_a_odd c t0 ht0 n := by
    induction' h with k hk;
    · exact get_construction_a_odd_lt_last_succ c t0 ht0 n;
    · have h_last_gt : last (get_construction_tn c t0 ht0 (k + 1)) (get_construction_tn_is_succ c t0 ht0 (k + 1)) = get_construction_a_even c t0 ht0 k := by
        exact last_construction_tn_succ c t0 ht0 k;
      have h_last_gt : last (get_construction_tn_prime c t0 ht0 k) (get_construction_tn_prime_is_succ c t0 ht0 k) ≥ last (get_construction_tn c t0 ht0 k) (get_construction_tn_is_succ c t0 ht0 k) := by
        exact last_tn_prime_ge_last_tn c t0 ht0 k;
      linarith [ get_construction_a_odd_lt_even c t0 ht0 k, get_construction_a_odd_gt_last_prime c t0 ht0 k ]

/-
The next sequence extends the current prime sequence.
-/
lemma get_construction_tn_succ_extends_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  extension (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n) (get_construction_tn c t0 ht0 (n + 1)) := by
    refine' ⟨ _, _ ⟩;
    · rw [ get_construction_tn_succ_eq ];
      unfold T_append;
      unfold T_append_val;
      refine' ⟨ _, _ ⟩;
      exact le_of_lt ( Order.lt_succ _ );
      grind;
    · intro x hxop;
      -- Since $x$ is in the image of $get_construction_tn c t0 ht0 (n + 1)$ but not in the image of $get_construction_tn_prime c t0 ht0 n$, it must be the even skipped element $get_construction_a_even c t0 ht0 n$.
      have hx_even : x = get_construction_a_even c t0 ht0 n := by
        have := im_tn_succ_diff_im_tn_prime c t0 ht0 n; aesop;
      exact hx_even.symm ▸ get_construction_a_odd_lt_even c t0 ht0 n |> lt_of_le_of_lt ( get_construction_a_odd_gt_last_prime c t0 ht0 n |> le_of_lt )

/-
The image of the (m+1)-th sequence is a subset of the image of the n-th prime sequence for m < n.
-/
lemma im_tn_succ_subset_im_tn_prime_of_lt (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m < n) :
  im (get_construction_tn c t0 ht0 (m + 1)) ⊆ im (get_construction_tn_prime c t0 ht0 n) := by
    -- Since $m < n$, we have $get_construction_tn c t0 ht0 (m + 1) \le get_construction_tn_prime c t0 ht0 n$.
    have h_le : get_construction_tn c t0 ht0 (m + 1) ≤ get_construction_tn_prime c t0 ht0 n := by
      exact get_construction_tn_succ_le_tn_prime_of_lt c t0 ht0 h;
    exact im_subset_of_le h_le

/-
The n-th sequence extends the m-th sequence for m ≤ n.
-/
lemma extension_tn_of_le (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m ≤ n) :
  extension (get_construction_tn c t0 ht0 m) (get_construction_tn_is_succ c t0 ht0 m) (get_construction_tn c t0 ht0 n) := by
    -- By induction on $k$, we can show that for any $m \leq n$, the $m$-th sequence is an extension of the $n$-th sequence.
    induction' h with k hk
    all_goals generalize_proofs at *;
    · (expose_names; exact extension_refl (get_construction_tn c t0 ht0 m) pf);
    · apply_rules [ extension_step ];
      any_goals exact get_construction_tn_is_succ c t0 ht0 k;
      any_goals apply_rules [ extension_refl ];
      apply_rules [ extension_step ];
      any_goals exact get_construction_tn_prime_is_succ c t0 ht0 k;
      any_goals apply_rules [ extension_refl ];
      · exact get_construction_tn_prime_extends c t0 ht0 k;
      · exact get_construction_tn_succ_extends_tn_prime c t0 ht0 k

/-
The m-th even skipped element is in the difference of the images of the n-th and m-th prime sequences for m < n.
-/
lemma a_even_mem_diff_im_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m < n) :
  get_construction_a_even c t0 ht0 m ∈ im (get_construction_tn_prime c t0 ht0 n) \ im (get_construction_tn_prime c t0 ht0 m) := by
    refine' ⟨ _, _ ⟩;
    · have h_mem : get_construction_a_even c t0 ht0 m ∈ im (get_construction_tn c t0 ht0 (m + 1)) := by
        exact mem_im_T_append _ _ ( next_missing_spec _ _ |>.1 );
      exact Set.mem_of_subset_of_mem ( im_tn_succ_subset_im_tn_prime_of_lt c t0 ht0 h ) h_mem;
    · have := next_missing_spec ( get_construction_tn_prime c t0 ht0 m ) ( get_construction_a_odd c t0 ht0 m ) ; aesop;

/-
The image of the next sequence is the union of the image of the prime sequence and the even skipped element.
-/
lemma im_construction_tn_succ_eq_im_tn_prime_union_a_even (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  im (get_construction_tn c t0 ht0 (n + 1)) = im (get_construction_tn_prime c t0 ht0 n) ∪ {get_construction_a_even c t0 ht0 n} := by
    -- By definition of `get_construction_tn`, we have `get_construction_tn c t0 ht0 (n + 1) = T_append (get_construction_tn_prime c t0 ht0 n) (get_construction_a_even c t0 ht0 n) (next_missing_spec (get_construction_tn_prime c t0 ht0 n) (get_construction_a_odd c t0 ht0 n)).1`.
    have h_def : get_construction_tn c t0 ht0 (n + 1) = T_append (get_construction_tn_prime c t0 ht0 n) (get_construction_a_even c t0 ht0 n) (next_missing_spec (get_construction_tn_prime c t0 ht0 n) (get_construction_a_odd c t0 ht0 n)).1 := by
      exact rfl
    generalize_proofs at *; (
    rw [ h_def, im_T_append ])

/-
Decomposition of the difference of images of prime sequences.
-/
lemma diff_decomposition (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m < n) :
  im (get_construction_tn_prime c t0 ht0 n) \ im (get_construction_tn_prime c t0 ht0 m) = {get_construction_a_even c t0 ht0 m} ∪ (im (get_construction_tn_prime c t0 ht0 n) \ im (get_construction_tn c t0 ht0 (m + 1))) := by
    apply Set.eq_of_subset_of_subset;
    · intro x hx
      obtain ⟨hx_in_n, hx_not_in_m⟩ := hx
      have hx_in_n_or_m_plus_1 : x ∈ im (get_construction_tn_prime c t0 ht0 n) ∧ (x ∉ im (get_construction_tn c t0 ht0 (m + 1)) ∨ x = get_construction_a_even c t0 ht0 m) := by
        have hx_in_n_or_m_plus_1 : x ∈ im (get_construction_tn_prime c t0 ht0 n) ∧ (x ∉ im (get_construction_tn c t0 ht0 (m + 1)) ∨ x ∈ ({get_construction_a_even c t0 ht0 m} : Set ℕ)) := by
          have h_im_tn_prime_union_a_even : im (get_construction_tn_prime c t0 ht0 m) ∪ {get_construction_a_even c t0 ht0 m} = im (get_construction_tn c t0 ht0 (m + 1)) := by
            exact Eq.symm (im_construction_tn_succ_eq_im_tn_prime_union_a_even c t0 ht0 m)
          grind;
        exact hx_in_n_or_m_plus_1.imp_right fun h => h.imp id fun h => by simpa using h;
      generalize_proofs at *; (
      grind);
    · intro x hxaesop;
      cases hxaesop <;> simp_all +decide
      · have := a_even_mem_diff_im_tn_prime c t0 ht0 h; aesop;
      · have := im_tn_succ_subset_im_tn_prime_of_lt c t0 ht0 h; simp_all +decide [ Set.subset_def ] ;
        intro hx; have := this x; simp_all +decide [ im_construction_tn_succ_eq_im_tn_prime_union_a_even ] ;

/-
The n-th prime sequence extends the (m+1)-th sequence for m < n.
-/
lemma extension_tn_succ_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m < n) :
  extension (get_construction_tn c t0 ht0 (m + 1)) (get_construction_tn_is_succ c t0 ht0 (m + 1)) (get_construction_tn_prime c t0 ht0 n) := by
    have h_extension : extension (get_construction_tn c t0 ht0 (m + 1)) (get_construction_tn_is_succ c t0 ht0 (m + 1)) (get_construction_tn c t0 ht0 n) := by
      exact extension_tn_of_le c t0 ht0 h;
    have h_extension_prime : extension (get_construction_tn c t0 ht0 n) (get_construction_tn_is_succ c t0 ht0 n) (get_construction_tn_prime c t0 ht0 n) := by
      exact get_construction_tn_prime_extends c t0 ht0 n;
    apply_rules [ extension_step ]

/-
Elements in the difference of the n-th prime sequence and the (m+1)-th sequence are strictly greater than the last element of the (m+1)-th sequence.
-/
lemma im_tn_prime_diff_tn_succ_gt_last (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m < n) :
  ∀ x ∈ im (get_construction_tn_prime c t0 ht0 n) \ im (get_construction_tn c t0 ht0 (m + 1)), x > last (get_construction_tn c t0 ht0 (m + 1)) (get_construction_tn_is_succ c t0 ht0 (m + 1)) := by
    -- By definition of extension, elements in the difference are `> last`.
    have h_ext : extension (get_construction_tn c t0 ht0 (m + 1)) (get_construction_tn_is_succ c t0 ht0 (m + 1)) (get_construction_tn_prime c t0 ht0 n) := by
      exact extension_tn_succ_tn_prime c t0 ht0 h;
    exact h_ext.2

/-
The minimum of the difference between the images of the n-th and m-th prime sequences is the m-th even skipped element.
-/
lemma min_diff_im_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m < n) :
  sInf (im (get_construction_tn_prime c t0 ht0 n) \ im (get_construction_tn_prime c t0 ht0 m)) = get_construction_a_even c t0 ht0 m := by
    rw [ diff_decomposition c t0 ht0 h ];
    refine' le_antisymm ( csInf_le _ _ ) ( le_csInf _ _ );
    · exact ⟨ 0, fun x hx => Nat.zero_le x ⟩;
    · exact Set.mem_union_left _ ( Set.mem_singleton _ );
    · exact ⟨ _, Set.mem_union_left _ ( Set.mem_singleton _ ) ⟩;
    · simp +zetaDelta at *;
      intro a ha₁ ha₂; exact le_of_not_gt fun ha₃ => ha₂ <| by have := im_tn_prime_diff_tn_succ_gt_last c t0 ht0 h a ⟨ ha₁, by aesop ⟩ ; linarith [ last_construction_tn_succ c t0 ht0 m ] ;

/-
The predecessor of the next sequence is the prime sequence.
-/
lemma s_star_tn_succ_eq_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  s_star (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1)) = get_construction_tn_prime c t0 ht0 n := by
    -- By definition of `T_append`, the predecessor of the appended sequence is the original sequence.
    have h_predecessor : ∀ (t : T_struct) (k : ℕ) (hk : k ∉ im t), s_star (T_append t k hk) (T_append_is_succ t k hk) = t := by
      exact fun t k hk ↦ T_append_s_star t k hk (T_append_is_succ t k hk);
    exact h_predecessor _ _ ( next_missing_spec _ _ |>.1 )

/-
The (m+1)-th sequence is in the A-set of the n-th prime sequence for m < n.
-/
lemma tn_succ_in_A_set_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m < n) :
  get_construction_tn c t0 ht0 (m + 1) ∈ A_set (get_construction_tn_prime c t0 ht0 n) := by
    have h_last : last (get_construction_tn c t0 ht0 (m + 1)) (get_construction_tn_is_succ c t0 ht0 (m + 1)) = sInf (im (get_construction_tn_prime c t0 ht0 n) \ im (get_construction_tn_prime c t0 ht0 m)) := by
      rw [ min_diff_im_tn_prime c t0 ht0 h, last_construction_tn_succ ];
    refine' ⟨ _, _ ⟩;
    exact get_construction_tn_is_succ c t0 ht0 ( m + 1 );
    exact ⟨ get_construction_tn_succ_le_tn_prime_of_lt c t0 ht0 h, h_last ▸ by rw [ s_star_tn_succ_eq_tn_prime ] ⟩

/-
The m-th prime sequence is in the A-star set of the n-th prime sequence for m < n.
-/
lemma tn_prime_in_A_star_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {m n : ℕ} (h : m < n) :
  get_construction_tn_prime c t0 ht0 m ∈ A_star (get_construction_tn_prime c t0 ht0 n) := by
    -- By definition of $s_star$, we know that $s_star (get_construction_tn c t0 ht0 (m + 1)) = get_construction_tn_prime c t0 ht0 m$.
    have h_s_star : s_star (get_construction_tn c t0 ht0 (m + 1)) (get_construction_tn_is_succ c t0 ht0 (m + 1)) = get_construction_tn_prime c t0 ht0 m := by
      exact s_star_tn_succ_eq_tn_prime c t0 ht0 m;
    -- By definition of $A_set$, we know that $get_construction_tn c t0 ht0 (m + 1) \in A_set (get_construction_tn_prime c t0 ht0 n)$.
    have h_A_set : get_construction_tn c t0 ht0 (m + 1) ∈ A_set (get_construction_tn_prime c t0 ht0 n) := by
      exact tn_succ_in_A_set_tn_prime c t0 ht0 h;
    unfold A_star A_set at *; aesop;

/-
The length of the limit sequence is countable.
-/
noncomputable def t_hat_alpha (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) : Ordinal :=
  sup_alpha (Set.range (get_construction_tn c t0 ht0))

/-
The limit sequence is injective on its domain.
-/
lemma t_hat_injective_on_sup (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) :
  Set.InjOn (t_hat c t0 ht0) (Set.Iio (t_hat_alpha c t0 ht0)) := by
    convert chain_union_injective _ _

/-
Elements added to the sequence after step n+1 are strictly greater than the n-th odd skipped element.
-/
lemma im_tn_diff_gt_a_odd (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {n m : ℕ} (h : n + 1 < m) :
  ∀ x ∈ im (get_construction_tn c t0 ht0 m) \ im (get_construction_tn c t0 ht0 (n + 1)), x > get_construction_a_odd c t0 ht0 n := by
    induction' h with m h ih;
    · intro x hx
      have hx_gt_last : x > last (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1)) := by
        have := im_construction_tn_succ_diff_gt_last c t0 ht0 ( n + 1 ) x hx; aesop;
      refine' lt_of_le_of_lt _ hx_gt_last;
      exact le_of_lt ( get_construction_a_odd_lt_last_succ c t0 ht0 n );
    · -- By combining the induction hypothesis and the fact that the elements added in step m+1 are greater than the last element of the m-th sequence, we can conclude the proof.
      intros x hx
      by_cases hx_m : x ∈ im (get_construction_tn c t0 ht0 m);
      · exact ih x ⟨ hx_m, hx.2 ⟩;
      · have hx_m1 : x ∈ im (get_construction_tn c t0 ht0 (m + 1)) \ im (get_construction_tn c t0 ht0 m) := by
          exact ⟨ hx.1, hx_m ⟩;
        have hx_m1_gt_last : x > last (get_construction_tn c t0 ht0 m) (get_construction_tn_is_succ c t0 ht0 m) := by
          exact im_construction_tn_succ_diff_gt_last c t0 ht0 m x hx_m1;
        have hx_m1_gt_a_odd : last (get_construction_tn c t0 ht0 m) (get_construction_tn_is_succ c t0 ht0 m) > get_construction_a_odd c t0 ht0 n := by
          apply last_construction_tn_gt_a_odd_of_gt;
          exact Nat.lt_of_succ_lt ( Nat.lt_of_succ_le h );
        linarith

/-
Elements added to the sequence at step k+1 are strictly greater than the n-th odd skipped element if k > n.
-/
lemma elements_added_gt_a_odd (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {n k : ℕ} (h : n < k) :
  ∀ x ∈ im (get_construction_tn c t0 ht0 (k + 1)) \ im (get_construction_tn c t0 ht0 k), x > get_construction_a_odd c t0 ht0 n := by
    -- By definition of `im_construction_tn_succ_diff_gt_last`, we know that any element in the difference is greater than the last element of the k-th sequence.
    have h_last_k_gt_a_odd_k : last (get_construction_tn c t0 ht0 k) (get_construction_tn_is_succ c t0 ht0 k) > get_construction_a_odd c t0 ht0 n := by
      -- Apply the lemma last_construction_tn_gt_a_odd_of_gt with m = k and n = n.
      apply last_construction_tn_gt_a_odd_of_gt; assumption;
    have h_im_construction_tn_succ_diff_gt_last : ∀ x ∈ im (get_construction_tn c t0 ht0 (k + 1)) \ im (get_construction_tn c t0 ht0 k), x > last (get_construction_tn c t0 ht0 k) (get_construction_tn_is_succ c t0 ht0 k) := by
      exact fun x a ↦ im_construction_tn_succ_diff_gt_last c t0 ht0 k x a;
    exact fun x hx => lt_trans h_last_k_gt_a_odd_k ( h_im_construction_tn_succ_diff_gt_last x hx )

/-
The n-th odd skipped element is not in the image of the k-th sequence for k ≤ n.
-/
lemma a_odd_not_mem_im_tn_of_le (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {n k : ℕ} (h : k ≤ n) :
  get_construction_a_odd c t0 ht0 n ∉ im (get_construction_tn c t0 ht0 k) := by
    -- By definition of `get_construction_a_odd`, we know that `get_construction_a_odd c t0 ht0 n ∉ im (get_construction_tn_prime c t0 ht0 n)`.
    have h_not_in_prime : get_construction_a_odd c t0 ht0 n ∉ im (get_construction_tn_prime c t0 ht0 n) := by
      exact get_construction_a_odd_not_mem_im_tn_prime c t0 ht0 n;
    contrapose! h_not_in_prime;
    -- By definition of `get_construction_tn`, we know that `get_construction_tn c t0 ht0 k ≤ get_construction_tn c t0 ht0 n`.
    have h_le : get_construction_tn c t0 ht0 k ≤ get_construction_tn c t0 ht0 n := by
      exact get_construction_tn_mono c t0 ht0 h;
    have h_le_prime : get_construction_tn c t0 ht0 n ≤ get_construction_tn_prime c t0 ht0 n := by
      exact get_construction_tn_prime_extends c t0 ht0 n |>.1;
    have h_le_prime : im (get_construction_tn c t0 ht0 k) ⊆ im (get_construction_tn_prime c t0 ht0 n) := by
      exact Set.Subset.trans ( im_subset_of_le h_le ) ( im_subset_of_le h_le_prime );
    exact h_le_prime h_not_in_prime

/-
The n-th odd skipped element is not in the image of the k-th sequence for k > n.
-/
lemma a_odd_not_mem_im_tn_of_gt (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) {n k : ℕ} (h : n < k) :
  get_construction_a_odd c t0 ht0 n ∉ im (get_construction_tn c t0 ht0 k) := by
    induction' h with k hk ih;
    · exact get_construction_a_odd_not_mem_im_tn_succ c t0 ht0 n;
    · -- By Lemma `elements_added_gt_a_odd`, elements added to the sequence at step `k+1` are strictly greater than the `n`-th odd skipped element if `k > n`.
      have h_elements_added_gt : ∀ x ∈ im (get_construction_tn c t0 ht0 (k + 1)) \ im (get_construction_tn c t0 ht0 k), x > get_construction_a_odd c t0 ht0 n := by
        exact fun x a ↦ elements_added_gt_a_odd c t0 ht0 hk x a;
      exact fun h => not_le_of_gt ( h_elements_added_gt _ ⟨ h, by aesop ⟩ ) le_rfl

/-
The limit sequence extends each constructed sequence.
-/
lemma t_hat_extends_tn (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) (x : Ordinal) (hx : x < (get_construction_tn c t0 ht0 n).α) :
  t_hat c t0 ht0 x = (get_construction_tn c t0 ht0 n).val.1 x hx := by
    apply chain_union_extends;
    exact Set.mem_range_self n

/-
The image of the limit sequence is the union of the images of the constructed sequences.
-/
lemma im_t_hat_eq_Union_im_tn (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) :
  Set.range (fun x : {β // β < t_hat_alpha c t0 ht0} => t_hat c t0 ht0 x.1) = ⋃ n, im (get_construction_tn c t0 ht0 n) := by
    -- By definition of $t_hat$, we know that its range is the union of the ranges of the sequences $t_n$.
    apply Set.ext
    intro y
    simp [t_hat, t_hat_alpha];
    constructor <;> intro h;
    · obtain ⟨ a, ha, rfl ⟩ := h;
      contrapose! ha;
      refine' csSup_le' _;
      rintro _ ⟨ t, ⟨ n, rfl ⟩, rfl ⟩;
      exact le_of_not_gt fun h => ha n <| by
        convert Set.mem_range_self _;
        convert t_hat_extends_tn c t0 ht0 n a h;
        swap;
        exacts [ ⟨ a, h ⟩, rfl ];
    · obtain ⟨ n, hn ⟩ := h;
      obtain ⟨ x, hx, rfl ⟩ := hn;
      refine' ⟨ x, _, _ ⟩;
      · refine' lt_of_lt_of_le x.2 ( le_csSup _ _ );
        · exact bdd_above_lengths (range (get_construction_tn c t0 ht0));
        · exact ⟨ _, ⟨ n, rfl ⟩, rfl ⟩;
      · convert t_hat_extends_tn c t0 ht0 n x x.2 using 1

/-
The n-th odd skipped element is not in the image of the limit sequence.
-/
lemma a_odd_not_mem_im_t_hat (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  get_construction_a_odd c t0 ht0 n ∉ Set.range (fun x : {β // β < t_hat_alpha c t0 ht0} => t_hat c t0 ht0 x.1) := by
    rw [ im_t_hat_eq_Union_im_tn ];
    simp +zetaDelta at *;
    intro k hk; cases le_or_gt k n <;> [ exact a_odd_not_mem_im_tn_of_le _ _ _ ‹_› ‹_›; exact a_odd_not_mem_im_tn_of_gt _ _ _ ‹_› ‹_› ] ;

/-
The limit sequence is co-infinite.
-/
lemma t_hat_cofinite (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) :
  (Set.range (fun x : {β // β < t_hat_alpha c t0 ht0} => t_hat c t0 ht0 x.1))ᶜ.Infinite := by
    have h_infinite : Set.Infinite (Set.range (fun n : ℕ => get_construction_a_odd c t0 ht0 n)) := by
      exact Set.infinite_range_of_injective ( StrictMono.injective ( strictMono_nat_of_lt_succ fun n => get_construction_a_odd_strict_mono c t0 ht0 n ) );
    refine h_infinite.mono ?_;
    intro x hx; obtain ⟨ n, rfl ⟩ := hx; exact a_odd_not_mem_im_t_hat c t0 ht0 n;

/-
The limit sequence as an element of T.
-/
noncomputable def t_hat_struct (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) : T_struct :=
  { α := t_hat_alpha c t0 ht0,
    val := ⟨fun β hβ => t_hat c t0 ht0 β, ⟨by
      intro x y h
      apply Subtype.eq
      apply t_hat_injective_on_sup c t0 ht0
      · exact x.2
      · exact y.2
      · exact h,
      t_hat_cofinite c t0 ht0⟩⟩ }

/-
The limit sequence is strictly greater than the n-th prime sequence.
-/
lemma t_hat_gt_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  get_construction_tn_prime c t0 ht0 n < t_hat_struct c t0 ht0 := by
    -- Since `t_hat` extends `tn (n+1)`, we have `tn (n+1) ≤ t_hat`.
    have h_tn_succ_le_t_hat : get_construction_tn c t0 ht0 (n + 1) ≤ t_hat_struct c t0 ht0 := by
      unfold t_hat_struct;
      refine' ⟨ _, fun x hx => _ ⟩;
      refine' le_csSup _ _;
      exact bdd_above_lengths (range (get_construction_tn c t0 ht0));
      exact Set.mem_image_of_mem _ ( Set.mem_range_self _ );
      exact Eq.symm (t_hat_extends_tn c t0 ht0 (n + 1) x hx);
    -- By definition of `get_construction_tn_prime`, we know that `get_construction_tn_prime c t0 ht0 n` is an initial segment of `get_construction_tn c t0 ht0 (n + 1)`.
    have h_prime_initial_segment : get_construction_tn_prime c t0 ht0 n ≤ get_construction_tn c t0 ht0 (n + 1) := by
      exact get_construction_tn_succ_extends_tn_prime c t0 ht0 n |>.1;
    refine' lt_of_le_of_ne ( le_trans h_prime_initial_segment h_tn_succ_le_t_hat ) _;
    intro h_eq;
    have h_contradiction : (get_construction_tn_prime c t0 ht0 n).α < t_hat_alpha c t0 ht0 := by
      have h_contradiction : (get_construction_tn_prime c t0 ht0 n).α < (get_construction_tn c t0 ht0 (n + 1)).α := by
        have h_contradiction : (get_construction_tn_prime c t0 ht0 n).α < (get_construction_tn_prime c t0 ht0 n).α + 1 := by
          exact lt_add_one (get_construction_tn_prime c t0 ht0 n).α;
        convert h_contradiction using 1;
      refine' lt_of_lt_of_le h_contradiction _;
      apply le_csSup;
      · exact bdd_above_lengths (range (get_construction_tn c t0 ht0));
      · exact ⟨ _, ⟨ n + 1, rfl ⟩, rfl ⟩;
    exact h_contradiction.ne ( by rw [ h_eq ] ; rfl )

/-
Elements in the difference of the limit sequence image and the n-th prime sequence image are strictly greater than the n-th odd skipped element.
-/
lemma im_t_hat_diff_im_tn_prime_gt_a_odd (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  ∀ x ∈ Set.range (fun x : {β // β < t_hat_alpha c t0 ht0} => t_hat c t0 ht0 x.1) \ im (get_construction_tn_prime c t0 ht0 n), x > get_construction_a_odd c t0 ht0 n := by
    intro x hx
    obtain ⟨k, hk⟩ : ∃ k, x ∈ im (get_construction_tn c t0 ht0 k) := by
      have := im_t_hat_eq_Union_im_tn c t0 ht0 ▸ hx.1; aesop;
    generalize_proofs at *;
    by_cases hk_le_n : k ≤ n + 1;
    · cases hk_le_n.eq_or_lt <;> simp_all +decide [ Nat.lt_succ_iff ];
      · have := im_construction_tn_succ_eq_im_tn_prime_union_a_even c t0 ht0 n; simp_all +decide [ Set.ext_iff ] ;
        exact get_construction_a_odd_lt_even c t0 ht0 n;
      · -- Since $k \leq n$, we have $im (get_construction_tn c t0 ht0 k) \subseteq im (get_construction_tn_prime c t0 ht0 n)$.
        have h_subset : im (get_construction_tn c t0 ht0 k) ⊆ im (get_construction_tn_prime c t0 ht0 n) := by
          have h_subset : get_construction_tn c t0 ht0 k ≤ get_construction_tn_prime c t0 ht0 n := by
            have h_subset : get_construction_tn c t0 ht0 k ≤ get_construction_tn c t0 ht0 n := by
              apply get_construction_tn_mono; assumption;
            exact le_trans h_subset ( get_construction_tn_prime_extends c t0 ht0 n |> fun h => h.1 );
          exact im_subset_of_le h_subset;
        exact False.elim <| hx.2 <| h_subset hk;
    · have h_diff : ∀ x ∈ im (get_construction_tn c t0 ht0 k) \ im (get_construction_tn c t0 ht0 (n + 1)), x > get_construction_a_odd c t0 ht0 n := by
        intro x hx;
        convert im_tn_diff_gt_a_odd c t0 ht0 ( show n + 1 < k from lt_of_not_ge hk_le_n ) x hx using 1;
      by_cases hx_in_tn_succ : x ∈ im (get_construction_tn c t0 ht0 (n + 1));
      · have h_union : im (get_construction_tn c t0 ht0 (n + 1)) = im (get_construction_tn_prime c t0 ht0 n) ∪ {get_construction_a_even c t0 ht0 n} := by
          exact im_construction_tn_succ_eq_im_tn_prime_union_a_even c t0 ht0 n;
        simp_all +decide [ Set.ext_iff ];
        exact get_construction_a_odd_lt_even c t0 ht0 n;
      · exact h_diff x ⟨ hk, hx_in_tn_succ ⟩

/-
The limit sequence is a 1-extension of the n-th prime sequence.
-/
lemma t_hat_is_one_extension (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  one_extension (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n) (t_hat_struct c t0 ht0) := by
    have h_t_hat_gt_tn_prime : get_construction_tn_prime c t0 ht0 n < t_hat_struct c t0 ht0 := by
      exact t_hat_gt_tn_prime c t0 ht0 n
    have h_im_t_hat_diff_im_tn_prime_gt_a_odd : ∀ x ∈ Set.range (fun x : {β // β < t_hat_alpha c t0 ht0} => t_hat c t0 ht0 x.1) \ im (get_construction_tn_prime c t0 ht0 n), x > get_construction_a_odd c t0 ht0 n := by
      apply im_t_hat_diff_im_tn_prime_gt_a_odd c t0 ht0 n;
    exact ⟨ h_t_hat_gt_tn_prime, by
      convert h_im_t_hat_diff_im_tn_prime_gt_a_odd using 1 ⟩

/-
The limit sequence is a 1-extension of the n-th prime sequence.
-/
lemma t_hat_is_one_extension_new (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  one_extension (get_construction_tn_prime c t0 ht0 n) (get_construction_tn_prime_is_succ c t0 ht0 n) (t_hat_struct c t0 ht0) := by
    convert t_hat_is_one_extension c t0 ht0 n using 1

/-
The color of the limit sequence is strictly greater than the color of the predecessor of the (n+1)-th sequence.
-/
lemma c_t_hat_gt_c_tn_prime (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) (n : ℕ) :
  c (t_hat_struct c t0 ht0) > c (s_star (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1))) := by
    have h1 := t_hat_is_one_extension_new c t0 ht0 (n + 1)
    have h2 := get_construction_tn_prime_spec c t0 ht0 (n + 1) (t_hat_struct c t0 ht0) h1
    exact h2

/-
The set of prime sequences forms a clique in G.
-/
lemma tn_prime_is_clique (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) :
  G.IsClique (Set.range (get_construction_tn_prime c t0 ht0)) := by
    intro u hu v hv huv;
    -- Since $u \neq v$, we have either $u \in A^\star(v)$ or $v \in A^\star(u)$.
    have h_cases : u ∈ A_star v ∨ v ∈ A_star u := by
      obtain ⟨m, hm⟩ : ∃ m, u = get_construction_tn_prime c t0 ht0 m := by
        aesop
      obtain ⟨n, hn⟩ : ∃ n, v = get_construction_tn_prime c t0 ht0 n := by
        grind
      have h_cases : m < n ∨ n < m := by
        grind;
      cases h_cases <;> [ left; right ] <;> rw [ hm, hn ] <;> (expose_names; exact tn_prime_in_A_star_tn_prime c t0 ht0 h);
    exact ⟨ by tauto, by tauto ⟩

/-
The sequence of prime vertices constructed in the proof is strictly monotonic.
-/
lemma tn_prime_strict_mono (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) :
  StrictMono (get_construction_tn_prime c t0 ht0) := by
    refine' strictMono_nat_of_lt_succ _;
    intro n
    have h_lt : get_construction_tn_prime c t0 ht0 n < get_construction_tn c t0 ht0 (n + 1) := by
      apply lt_of_le_of_ne; exact (by
      apply (get_construction_tn_succ_extends_tn_prime c t0 ht0 n).left); exact (by
      have := last_tn_succ_gt_last_tn_prime c t0 ht0 n; aesop;);
    have h_le : get_construction_tn c t0 ht0 (n + 1) ≤ get_construction_tn_prime c t0 ht0 (n + 1) := by
      apply get_construction_tn_prime_extends c t0 ht0 (n + 1) |>.1
    exact lt_of_lt_of_le h_lt h_le

/-
The range of the sequence of prime vertices is infinite.
-/
lemma tn_prime_range_infinite (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) :
  (Set.range (get_construction_tn_prime c t0 ht0)).Infinite := by
    exact Set.infinite_range_of_injective ( StrictMono.injective ( tn_prime_strict_mono c t0 ht0 ) )

/-
The colors of the prime vertices are bounded.
-/
lemma tn_prime_colors_bounded (c : G.Coloring ℕ) (t0 : T_struct) (ht0 : is_succ_ordinal t0.α) :
  BddAbove (Set.image c (Set.range (get_construction_tn_prime c t0 ht0))) := by
    -- By definition of $c$, we know that for any $t' \in \text{range}(get_construction_tn_prime c t0 ht0)$, $c(t') < c(\hat{t})$.
    have h_c_lt_c_hat : ∀ t' ∈ Set.range (get_construction_tn_prime c t0 ht0), c t' < c (t_hat_struct c t0 ht0) := by
      rintro _ ⟨ n, rfl ⟩;
      -- By definition of $c$, we know that $c(t'_n) < c(\hat{t})$ for all $n$.
      have h_c_lt_c_hat : ∀ n, c (s_star (get_construction_tn c t0 ht0 (n + 1)) (get_construction_tn_is_succ c t0 ht0 (n + 1))) < c (t_hat_struct c t0 ht0) := by
        exact fun n ↦ c_t_hat_gt_c_tn_prime c t0 ht0 n;
      convert h_c_lt_c_hat n using 1;
      exact congr_arg _ ( s_star_tn_succ_eq_tn_prime c t0 ht0 n ▸ rfl );
    exact ⟨ _, Set.forall_mem_image.2 fun t' ht' => le_of_lt ( h_c_lt_c_hat t' ht' ) ⟩

/-
The graph G is uncountably chromatic.
-/
theorem G_uncountably_chromatic : uncountably_chromatic G := by
  intro c;
  -- Let $t_0$ be any sequence of successor length (e.g., a sequence of lengt 1).
  obtain ⟨t0, ht0⟩ : ∃ t0 : T_struct, is_succ_ordinal t0.α := by
    constructor;
    swap
    constructor;
    constructor;
    rotate_left;
    exact fun _ _ => 0 + 1;
    exact 1;
    field_simp;
    · exact ⟨ 0, by norm_num ⟩;
    · exact ⟨ by aesop_cat, Set.infinite_of_forall_exists_gt fun n => ⟨ n + 2, by aesop_cat, by linarith ⟩ ⟩;
  -- Let $K = \{t'_n \mid n \in \mathbb{N}\}$ be the set of prime vertices.
  set K := Set.range (get_construction_tn_prime c.some t0 ht0);
  -- The set $K$ is infinite (by `tn_prime_range_infinite`).
  have hK_infinite : K.Infinite := by
    exact tn_prime_range_infinite c.some t0 ht0;
  -- The colors of $K$ are bounded (by `tn_prime_colors_bounded`).
  have hK_colors_bounded : BddAbove (Set.image c.some K) := by
    exact tn_prime_colors_bounded c.some t0 ht0;
  -- This contradicts the fact that an infinite clique cannot have bounded colors (by `infinite_clique_unbounded_colors`).
  have h_contradiction : G.IsClique K → Set.Infinite K → ¬BddAbove (Set.image c.some K) := by
    exact fun a a_1 ↦ infinite_clique_unbounded_colors G c.some K a hK_infinite;
  exact h_contradiction ( tn_prime_is_clique c.some t0 ht0 ) hK_infinite hK_colors_bounded

/-
The graph G is uncountably chromatic and has the finite adhesion property.
-/
theorem main_theorem : uncountably_chromatic G ∧ (∀ (A : Set T_struct), ¬ A.Countable → ∃ t1 ∈ A, ∃ t2 ∈ A, t1 ≠ t2 ∧ finite_independent_paths G t1 t2) := by
  refine' ⟨ G_uncountably_chromatic, _ ⟩;
  exact fun A a ↦ finite_adhesion_property A a

open scoped Classical
open Set Ordinal Function Cardinal

theorem G_has_omega1_coloring: Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) := by
  classical
  refine ⟨
    SimpleGraph.Coloring.mk (G := G)
      (color := fun t : T_struct =>
        (⟨t.α, by
            simpa using (lengths_lt_omega1 t)⟩ : Set.Iio (Ordinal.omega.{0} 1)))
      ?_⟩
  intro t1 t2 hadj
  have hadj' : t1 ≠ t2 ∧ (t1 ∈ A_star t2 ∨ t2 ∈ A_star t1) := by
    simpa [G] using
      (SimpleGraph.fromRel_adj (r := fun a b : T_struct => a ∈ A_star b) t1 t2).1 hadj
  rcases hadj' with ⟨hne, hmem⟩
  cases hmem with
  | inl h12 =>
      have hlt : t1 < t2 := mem_A_star_lt t2 t1 h12
      intro hcol
      have halpha : t1.α = t2.α := by
        simpa using congrArg Subtype.val hcol
      have : t1 = t2 := eq_of_le_of_alpha_eq (le_of_lt hlt) halpha
      exact (ne_of_lt hlt) this
  | inr h21 =>
      have hlt : t2 < t1 := mem_A_star_lt t1 t2 h21
      intro hcol
      have halpha : t1.α = t2.α := by
        simpa using congrArg Subtype.val hcol
      have : t2 = t1 := eq_of_le_of_alpha_eq (le_of_lt hlt) halpha.symm
      exact (ne_of_lt hlt) this

theorem finite_independent_paths_induce_of_finite {V : Type*} (G : SimpleGraph V) (S : Set V) (u v : S) :
  finite_independent_paths G u.1 v.1 → finite_independent_paths (G.induce S) u v := by
  classical
  intro hfin P hP
  let ι : G.induce S ↪g G := SimpleGraph.Embedding.induce (G := G) S
  let f : G.induce S →g G := ι.toHom
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (by simpa using hxy)
  let Q : Set (G.Walk u.1 v.1) := (fun p : (G.induce S).Walk u v => p.map f) '' P
  have hQ : independent_paths (G := G) (u := u.1) (v := v.1) Q := by
    intro p hp q hq hpq
    rcases hp with ⟨p0, hp0, rfl⟩
    rcases hq with ⟨q0, hq0, rfl⟩
    have hpq0 : p0 ≠ q0 := by
      intro h
      apply hpq
      simp [h]
    have hsubset : {x | x ∈ p0.support} ∩ {x | x ∈ q0.support} ⊆ ({u, v} : Set S) :=
      hP p0 hp0 q0 hq0 hpq0
    intro x hx
    rcases hx with ⟨hx_p, hx_q⟩
    have hx_p' : x ∈ p0.support.map f := by
      simpa [SimpleGraph.Walk.support_map] using hx_p
    have hx_q' : x ∈ q0.support.map f := by
      simpa [SimpleGraph.Walk.support_map] using hx_q
    rcases List.mem_map.1 hx_p' with ⟨y, hy, hyx⟩
    rcases List.mem_map.1 hx_q' with ⟨z, hz, hzx⟩
    have hyz : y = z := hinj (hyx.trans hzx.symm)
    have hyq : y ∈ q0.support := by
      simpa [hyz.symm] using hz
    have hyuv : y ∈ ({u, v} : Set S) :=
      hsubset ⟨hy, hyq⟩
    have hyuv' : y = u ∨ y = v := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hyuv
    cases hyuv' with
    | inl hyu =>
        have hx' : x = u.1 := by
          have : f u = x := by
            simpa [hyu] using hyx
          simpa [f] using this.symm
        simp [hx']
    | inr hyv =>
        have hx' : x = v.1 := by
          have : f v = x := by
            simpa [hyv] using hyx
          simpa [f] using this.symm
        simp [hx']
  have hQfin : Q.Finite := hfin Q hQ
  have h_injOn : Set.InjOn (fun p : (G.induce S).Walk u v => p.map f) P := by
    intro p hp q hq hpq
    exact (SimpleGraph.Walk.map_injective_of_injective (f := f) hinj u v) hpq
  exact Set.Finite.of_finite_image hQfin h_injOn

theorem uncountably_chromatic_induce_not_countable {V : Type*} (G : SimpleGraph V) (S : Set V) : uncountably_chromatic (G.induce S) → ¬ S.Countable := by
  intro hchrom hS
  -- contrapositive
  -- obtain injection from S into ℕ
  rcases (Set.countable_iff_exists_injective.1 hS) with ⟨f, hf⟩
  -- build a coloring of the induced graph
  have : Nonempty ((G.induce S).Coloring ℕ) := by
    refine ⟨?_, ?_⟩
    · exact f
    · intro u v huv
      have hne : u ≠ v := by
        exact SimpleGraph.Adj.ne huv
      exact hf.ne hne
  -- contradiction
  exact hchrom this

/- Conjecture: every graph with chromatic number `ℵ₁` contains an (induced) subgraph
which is infinitely connected (i.e. not `finite_independent_paths` between any two
distinct vertices) and still has chromatic number `ℵ₁`. -/
def erdos_1067 : Prop :=
  ∀ {V : Type*} (G : SimpleGraph V),
    (Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧ uncountably_chromatic G) →
      ∃ (S : Set V),
        (Nonempty ((G.induce S).Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧
            uncountably_chromatic (G.induce S)) ∧
        ∀ u v : S, u ≠ v → ¬ finite_independent_paths (G.induce S) u v

theorem not_erdos_1067: ¬erdos_1067.{1} := by
  intro h
  classical
  have hG :
      (Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧ uncountably_chromatic G) :=
    ⟨G_has_omega1_coloring, G_uncountably_chromatic⟩
  rcases h (G := G) hG with ⟨S, hS, hconn⟩
  have hSnotcount : ¬ S.Countable := by
    exact uncountably_chromatic_induce_not_countable (G := G) (S := S) hS.2
  rcases finite_adhesion_property (A := S) hSnotcount with ⟨t1, ht1, t2, ht2, htne, hfin⟩
  let u : S := ⟨t1, ht1⟩
  let v : S := ⟨t2, ht2⟩
  have huv : u ≠ v := by
    intro huv'
    apply htne
    exact congrArg Subtype.val huv'
  have hfin' : finite_independent_paths (G.induce S) u v := by
    exact finite_independent_paths_induce_of_finite (G := G) (S := S) (u := u) (v := v) hfin
  exact (hconn u v huv) hfin'

#print axioms not_erdos_1067
-- 'not_erdos_1067' depends on axioms: [propext, Classical.choice, Quot.sound]

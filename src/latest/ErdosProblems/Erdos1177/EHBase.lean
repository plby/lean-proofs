-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Defs
import ErdosProblems.Erdos1177.AmalgHelpers

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The Erdős–Hajnal base case: uncountably chromatic graphs contain `K_{n,ℵ₁}`

This file formalizes the graph-theoretic base case underlying Reiher's
Theorem 1.2 (our `E4_Reiher`).  The statement is:

> For every natural number `n`, every graph `G` of uncountable chromatic number
> contains the complete bipartite graph `K_{n, ℵ₁}` (and hence `K_{n,n}`).

Reference: C. Reiher, *Graphs of large girth*, arXiv:2403.13571, §3.6,
Theorem (Erdős & Hajnal); originally Erdős–Hajnal, Acta Math. Hungar. 17 (1966),
Corollary 5.6.

## Proof outline (a transfinite-recursion-free rendering of the survey proof)

Fix `n`.  Argue by strong induction on the cardinal `κ = #V`.  Assume `G` is not
countably colourable but `K_{n,ℵ₁}`-free; we derive a contradiction by producing
a countable colouring.

* Call `M ⊆ V` *`n`-closed* (`NClosed`) if every `x ∉ M` has fewer than `n`
  neighbours in `M`.  Because `G` is `K_{n,ℵ₁}`-free, every `n`-set has countable
  common neighbourhood, so the finitary closure `cl X` (iterate "add vertices
  with `≥ n` neighbours") is `n`-closed with `#(cl X) ≤ #X + ℵ₀`.
* Enumerate `V` by `Idx = κ.ord.ToType`; set `M a = cl (e '' {b ≤ a})`.  This is
  monotone, each `M a` is `n`-closed with `#(M a) < κ`, and the sets cover `V`.
* `rank x := least a with x ∈ M a`.  Then the "back-neighbours"
  `{y | G.Adj x y ∧ rank y < rank x}` lie in `M_{<rank x} = ⋃_{b<rank x} M b`,
  which is `n`-closed (a monotone union of `n`-closed sets stays `n`-closed
  because `n` is finite), so there are `< n` of them.  Each level
  `{x | rank x = a} ⊆ M a` has size `< κ`, hence is countably colourable by the
  induction hypothesis.
* From a rank function with `< n` back-neighbours and countably-colourable
  levels one builds a countable colouring by well-founded recursion on `rank`:
  colour `x` inside the `n`-block `[n·g(x), n·g(x)+n)` (where `g` is a level
  colouring) avoiding the `< n` colours of its back-neighbours.
-/

open Cardinal

namespace Erdos1177

universe u

variable {V : Type u}

/-- A graph `G` is *countably colourable* if its vertices can be properly
coloured by `ℕ`. -/
def GCountColorable (G : SimpleGraph V) : Prop :=
  ∃ c : V → ℕ, ∀ x y, G.Adj x y → c x ≠ c y

/-- `GCountColorable` is exactly `ℵ₀`-colourability of the associated hypergraph. -/
theorem gCountColorable_iff_colorableBy (G : SimpleGraph V) :
    GCountColorable G ↔ (SimpleGraph.toHG G).ColorableBy ℵ₀ := by
  constructor;
  · rintro ⟨ c, hc ⟩;
    refine' ⟨ _, _ ⟩;
    convert! ( nonempty_equiv_of_countable ( α := ℕ ) ( β := Quotient.out ℵ₀ ) ).some ∘ c;
    convert! Cardinal.mk_le_aleph0_iff.mp _;
    convert! Cardinal.mk_out ℵ₀ |> le_of_eq;
    exact Cardinal.infinite_iff.2 ( by simp +decide );
    intro e he; obtain ⟨ x, y, hxy, rfl ⟩ := he; specialize hc x y hxy; aesop;
  · rintro ⟨ c, hc ⟩;
    obtain ⟨ f, hf ⟩ := Cardinal.eq.1 ( Cardinal.mk_out ℵ₀ );
    use fun x => ( f ( c x ) ).down;
    intro x y hxy; have := hc _ ( by exact ⟨ x, y, hxy, rfl ⟩ ) ; simp_all +decide [ Function.LeftInverse, Function.RightInverse ] ;
    grind

/-- `G` contains `K_{n, ℵ₁}`: `n` distinct vertices with a common neighbourhood of
size at least `ℵ₁`, disjoint from the `n` vertices. -/
def HasKnAleph1 (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (a : Fin n → V) (B : Set V), Function.Injective a ∧ ℵ₁ ≤ #B ∧
    (∀ i, a i ∉ B) ∧ (∀ i, ∀ b ∈ B, G.Adj (a i) b)

/-! ### Closed sets and the finitary closure operator -/

/-- The neighbours of `x` lying in `M`. -/
def nbhdIn (G : SimpleGraph V) (x : V) (M : Set V) : Set V := {y | y ∈ M ∧ G.Adj x y}

/-- `M` is *`n`-closed* if no vertex outside `M` has `n` or more neighbours in `M`. -/
def NClosed (G : SimpleGraph V) (n : ℕ) (M : Set V) : Prop :=
  ∀ x, x ∉ M → #(nbhdIn G x M) < (n : Cardinal)

/-- One closure step: add every vertex having `≥ n` neighbours in `X`. -/
def closeStep (G : SimpleGraph V) (n : ℕ) (X : Set V) : Set V :=
  X ∪ {x | (n : Cardinal) ≤ #(nbhdIn G x X)}

/-- The `k`-fold closure step. -/
def closeIter (G : SimpleGraph V) (n : ℕ) (X : Set V) : ℕ → Set V
  | 0 => X
  | k + 1 => closeStep G n (closeIter G n X k)

/-- The finitary `n`-closure of `X`. -/
def cl (G : SimpleGraph V) (n : ℕ) (X : Set V) : Set V := ⋃ k, closeIter G n X k

/-! ### Countable common neighbourhoods (from `K_{n,ℵ₁}`-freeness) -/

/-
If `G` is `K_{n,ℵ₁}`-free then any injective `n`-tuple has countable common
neighbourhood (excluding the tuple itself).
-/
theorem commonNbhd_le_aleph0 (G : SimpleGraph V) (n : ℕ) (hfree : ¬ HasKnAleph1 G n)
    (a : Fin n → V) (ha : Function.Injective a) :
    #({v | (∀ i, v ≠ a i) ∧ ∀ i, G.Adj (a i) v}) ≤ ℵ₀ := by
  contrapose! hfree;
  -- Since the cardinality of the set is greater than ℵ₀, it must be at least ℵ₁.
  have h_card_ge_aleph1 : ℵ₁ ≤ #(↥{v : V | (∀ i, v ≠ a i) ∧ ∀ i, G.Adj (a i) v}) := by
    convert! Order.succ_le_of_lt hfree using 1;
    simp +zetaDelta at *;
  exact ⟨ a, _, ha, h_card_ge_aleph1, fun i => by aesop, fun i => by aesop ⟩

/-
The set of vertices with `≥ n` neighbours in `X` has cardinality at most
`#X + ℵ₀`, when `G` is `K_{n,ℵ₁}`-free.
-/
theorem closeStep_card_le (G : SimpleGraph V) (n : ℕ) (hfree : ¬ HasKnAleph1 G n)
    (X : Set V) : #(closeStep G n X) ≤ #X + ℵ₀ := by
  -- Every vertex in the closure step has at least `n` neighbours in `X`.
  have h_closure_step : {x | (n : Cardinal) ≤ #(nbhdIn G x X)} ⊆ ⋃ (a : {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X}), {v | (∀ i, v ≠ a.1 i) ∧ ∀ i, G.Adj (a.1 i) v} := by
    intro x hx; simp_all +decide [ Set.subset_def ] ;
    -- Since $x$ has at least $n$ neighbors in $X$, we can choose $n$ distinct neighbors from $X$.
    obtain ⟨a, ha⟩ : ∃ a : Fin n → V, Function.Injective a ∧ ∀ i, a i ∈ X ∧ G.Adj x (a i) := by
      obtain ⟨ s, hs ⟩ := Cardinal.le_mk_iff_exists_subset.mp hx;
      have := Cardinal.eq.1 hs.2;
      obtain ⟨ e ⟩ := this;
      exact ⟨ fun i => e.symm ⟨ i ⟩ |>.1, fun i j hij => by simpa [ Fin.ext_iff ] using! e.symm.injective ( Subtype.ext hij ), fun i => ⟨ hs.1 ( e.symm ⟨ i ⟩ |>.2 ) |>.1, hs.1 ( e.symm ⟨ i ⟩ |>.2 ) |>.2 ⟩ ⟩;
    exact ⟨ a, fun i => by intro hi; have := ha.2 i; simp_all +decide [ SimpleGraph.adj_comm ], ⟨ ha.1, fun i => ha.2 i |>.1 ⟩, fun i => ha.2 i |>.2.symm ⟩;
  -- The index set has cardinality at most `#X + ℵ₀`.
  have h_index_card : #( {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X} ) ≤ #(X : Set V) + ℵ₀ := by
    have h_index_card : #( {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X} ) ≤ #(Fin n → X) := by
      fapply Cardinal.mk_le_of_injective;
      exacts [ fun a => fun i => ⟨ a.val i, a.property.2 i ⟩, fun a b h => Subtype.ext <| funext fun i => by simpa using! congr_fun h i ];
    by_cases hX : Infinite X <;> simp_all +decide [ Cardinal.mk_fintype ];
    · refine' le_trans h_index_card _;
      rcases n with ( _ | n ) <;> simp_all +decide [ Cardinal.power_nat_eq ];
      exact le_add_of_nonneg_of_le ( zero_le ) ( by simp +decide );
    · exact le_trans h_index_card ( le_add_of_nonneg_of_le ( by positivity ) ( by exact le_of_lt ( Cardinal.lt_aleph0_of_finite _ ) ) );
  -- Each common-neighbourhood set has cardinality at most `ℵ₀`.
  have h_common_nbhd_card : ∀ a : {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X}, #( {v | (∀ i, v ≠ a.1 i) ∧ ∀ i, G.Adj (a.1 i) v} : Set V ) ≤ ℵ₀ := by
    exact fun a => commonNbhd_le_aleph0 G n hfree a.1 a.2.1;
  -- Therefore, the cardinality of the closure step is at most `#X + ℵ₀`.
  have h_closure_step_card : #( {x | (n : Cardinal) ≤ #(nbhdIn G x X)} : Set V ) ≤ (#(X : Set V) + ℵ₀) * ℵ₀ := by
    refine' le_trans ( Cardinal.mk_le_mk_of_subset h_closure_step ) _;
    refine' le_trans ( Cardinal.mk_iUnion_le _ ) _;
    gcongr;
    exact ciSup_le' fun a => h_common_nbhd_card a;
  convert! Cardinal.mk_union_le _ _ |> le_trans <| add_le_add_left h_closure_step_card _ using 1;
  any_goals exact X;
  · grind +locals;
  · simp +decide [ add_comm, add_left_comm, add_assoc ];
    rw [ ← add_assoc, Cardinal.add_eq_max ];
    · rw [ Cardinal.add_eq_max ];
      · simp +decide [ max_assoc ];
      · exact le_max_left _ _;
    · norm_num

/-! ### Basic closure properties -/

theorem subset_closeIter (G : SimpleGraph V) (n : ℕ) (X : Set V) (k : ℕ) :
    X ⊆ closeIter G n X k := by
  induction' k with k ih;
  · rfl;
  · exact Set.Subset.trans ih ( Set.subset_union_left )

theorem closeIter_mono_index (G : SimpleGraph V) (n : ℕ) (X : Set V) {k l : ℕ}
    (h : k ≤ l) : closeIter G n X k ⊆ closeIter G n X l := by
  induction h <;> simp_all +decide [ closeIter ];
  exact Set.Subset.trans ‹_› ( Set.subset_union_left )

theorem subset_cl (G : SimpleGraph V) (n : ℕ) (X : Set V) : X ⊆ cl G n X := by
  exact Set.subset_iUnion_of_subset 0 ( by rfl )

/-
`cl` is monotone in its set argument.
-/
theorem cl_mono (G : SimpleGraph V) (n : ℕ) {X Y : Set V} (h : X ⊆ Y) :
    cl G n X ⊆ cl G n Y := by
  refine Set.iUnion_subset fun k => ?_;
  refine' Set.Subset.trans _ ( Set.subset_iUnion _ ( k + 1 ) );
  induction' k with k ih;
  · exact Set.Subset.trans h ( Set.subset_union_left );
  · refine' Set.union_subset_union ih _;
    exact fun x hx => le_trans hx.out ( Cardinal.mk_le_mk_of_subset <| by exact fun y hy => by exact ⟨ ih hy.1, hy.2 ⟩ )

/-
The closure is `n`-closed.
-/
theorem nclosed_cl (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (X : Set V) :
    NClosed G n (cl G n X) := by
  intro x hx;
  contrapose! hx;
  obtain ⟨ s, hs ⟩ := Cardinal.le_mk_iff_exists_subset.mp hx;
  -- Since $s$ is a subset of $nbhdIn G x (cl G n X)$ and $s$ has cardinality $n$, there exists some $k$ such that $s \subseteq closeIter G n X k$.
  obtain ⟨ k, hk ⟩ : ∃ k, s ⊆ closeIter G n X k := by
    have h_finite : ∀ y ∈ s, ∃ k, y ∈ closeIter G n X k := by
      exact fun y hy => Set.mem_iUnion.mp ( hs.1 hy |>.1 );
    choose! k hk using h_finite;
    have h_finite : Set.Finite s := by
      exact Set.finite_coe_iff.mp ( Cardinal.lt_aleph0_iff_finite.mp ( hs.2.symm ▸ Cardinal.nat_lt_aleph0 n ) );
    exact ⟨ h_finite.toFinset.sup k, fun y hy => closeIter_mono_index G n X ( Finset.le_sup ( f := k ) ( h_finite.mem_toFinset.mpr hy ) ) ( hk y hy ) ⟩;
  -- Since $s$ is a subset of $closeIter G n X k$ and $s$ has cardinality $n$, we have $n \leq #(nbhdIn G x (closeIter G n X k))$.
  have h_card : n ≤ #(nbhdIn G x (closeIter G n X k)) := by
    refine' hs.2 ▸ Cardinal.mk_le_mk_of_subset _;
    exact fun y hy => ⟨ hk hy, hs.1 hy |>.2 ⟩;
  exact Set.mem_iUnion.mpr ⟨ k + 1, by exact Set.mem_union_right _ h_card ⟩

/-
The closure has size at most `#X + ℵ₀`.
-/
theorem cl_card_le (G : SimpleGraph V) (n : ℕ) (hfree : ¬ HasKnAleph1 G n)
    (X : Set V) : #(cl G n X) ≤ #X + ℵ₀ := by
  -- By induction on $k$, we show that $|closeIter G n X k| \leq |X| + \aleph_0$ for all $k$.
  have h_ind : ∀ k, #(closeIter G n X k) ≤ #X + ℵ₀ := by
    intro k;
    induction' k with k ih;
    · exact le_add_right le_rfl;
    · convert! le_trans ( closeStep_card_le G n hfree _ ) _ using 1;
      convert! add_le_add_right ih ℵ₀ using 1;
      · rw [ add_comm ];
      · rw [ add_comm, Cardinal.add_eq_max ];
        · rw [ Cardinal.add_eq_right ]; all_goals exact le_max_left _ _;
        · norm_num;
  convert! Cardinal.mk_iUnion_le _ |> le_trans <| ?_;
  rotate_left;
  exact ULift ℕ;
  use fun k => closeIter G n X k.down;
  · simp +decide [ Cardinal.mk_nat ];
    refine' le_trans ( mul_le_mul_right ( ciSup_le h_ind ) _ ) _;
    simp +decide [ Cardinal.aleph0_le_add_iff ];
  · ext; simp [cl]

/-
A monotone union of `n`-closed sets over an initial segment stays `n`-closed
(because `n` is finite).
-/
theorem nclosed_biUnion_lt {σ : Type u} [LinearOrder σ] (G : SimpleGraph V) (n : ℕ)
    (hn : 1 ≤ n) (M : σ → Set V) (hmono : Monotone M) (hcl : ∀ b, NClosed G n (M b))
    (a : σ) : NClosed G n (⋃ b ∈ {b : σ | b < a}, M b) := by
  intro x hx;
  by_contra h_contra;
  obtain ⟨s, hs⟩ : ∃ s : Finset V, s.card = n ∧ ∀ y ∈ s, y ∈ nbhdIn G x (⋃ b ∈ {b | b < a}, M b) := by
    obtain ⟨ s, hs ⟩ := Cardinal.le_mk_iff_exists_subset.mp ( le_of_not_gt h_contra );
    cases' Set.Finite.exists_finset_coe ( show Set.Finite s from Set.finite_coe_iff.mp ( Cardinal.lt_aleph0_iff_finite.mp ( by rw [ hs.2 ] ; exact Cardinal.nat_lt_aleph0 _ ) ) ) ; aesop;
  -- For each `y ∈ s`, there exists `b < a` such that `y ∈ M b`.
  obtain ⟨b, hb⟩ : ∃ b < a, ∀ y ∈ s, y ∈ M b := by
    have h_exists_b : ∀ y ∈ s, ∃ b < a, y ∈ M b := by
      intro y hy; specialize hs; have := hs.2 y hy; unfold nbhdIn at this; aesop;
    choose! b hb₁ hb₂ using h_exists_b;
    use Finset.max' (Finset.image (fun y => b y.1 y.2) (Finset.attach s)) (by
    exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_attach _ ⟨ Classical.choose ( Finset.card_pos.mp ( by linarith ) ), Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ) ⟩ ) ⟩)
    generalize_proofs at *;
    refine' ⟨ _, _ ⟩;
    · simp +decide [ Finset.max' ];
      exact fun y hy => hb₁ y hy;
    · intro y hy; exact hmono ( Finset.le_max' _ _ <| Finset.mem_image_of_mem _ <| Finset.mem_attach _ ⟨ y, hy ⟩ ) <| hb₂ _ _;
  have h_card : #(nbhdIn G x (M b)) ≥ n := by
    refine' le_trans _ ( Cardinal.mk_le_mk_of_subset <| show ( s : Set V ) ⊆ nbhdIn G x ( M b ) from _ );
    · simp +decide [ hs.1 ];
    · exact fun y hy => ⟨ hb.2 y hy, hs.2 y hy |>.2 ⟩;
  exact not_lt_of_ge h_card ( hcl b x ( by aesop ) )

/-! ### The core: a rank function with few back-neighbours gives a colouring -/

/-
**Core colouring lemma.**  Suppose there is a `rank : V → σ` (into a
well-order) such that every vertex has fewer than `n` neighbours of strictly
smaller rank, and each rank level is countably colourable.  Then `G` is countably
colourable.
-/
theorem countColorable_of_rank {σ : Type u} [LinearOrder σ] [WellFoundedLT σ]
    (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (rank : V → σ)
    (hback : ∀ x, #({y | G.Adj x y ∧ rank y < rank x}) < (n : Cardinal))
    (hlevel : ∀ a : σ, ∃ g : V → ℕ,
      ∀ x y, rank x = a → rank y = a → G.Adj x y → g x ≠ g y) :
    GCountColorable G := by
  choose g hg using hlevel;
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : V → Fin (2 * n + 1), ∀ a b, G.Adj a b → rank a ≠ rank b → c₂ a ≠ c₂ b := by
    have h_colorable : ∀ x : V, ∃ finset : Finset V, {y | G.Adj x y ∧ rank y < rank x} = (finset : Set V) ∧ finset.card ≤ n := by
      intro x
      obtain ⟨s, hs⟩ : ∃ s : Finset V, {y | G.Adj x y ∧ rank y < rank x} = (s : Set V) := by
        have h_finite : Set.Finite {y | G.Adj x y ∧ rank y < rank x} := by
          exact Set.finite_coe_iff.mp ( Cardinal.lt_aleph0_iff_finite.mp ( lt_of_lt_of_le ( hback x ) ( Cardinal.nat_lt_aleph0 _ |> le_of_lt ) ) );
        exact ⟨ h_finite.toFinset, by simpa ⟩;
      specialize hback x; rw [ hs ] at hback; simp_all +decide [ Cardinal.mk_fintype ] ;
      linarith;
    choose finset hfinset using h_colorable;
    convert! colorable_of_out ( SimpleGraph.mk ( fun x y => G.Adj x y ∧ rank x ≠ rank y ) ( by
      exact ⟨fun x y h => ⟨ h.1.symm, Ne.symm h.2 ⟩⟩ ) ( by
      exact ⟨ fun x hx => hx.1.ne rfl ⟩ ) ) n finset ( fun x => ( hfinset x ).2 ) ( fun x y hxy => by
      cases lt_or_gt_of_ne hxy.2 <;> simp_all +decide [ Set.ext_iff ];
      · exact Or.inr ( hfinset y |>.1 x |>.1 ⟨ hxy.1.symm, by tauto ⟩ );
      · exact Or.inl ( hfinset x |>.1 y |>.1 ⟨ hxy.1, by assumption ⟩ ) ) using 1;
    · grind +splitImp;
    · exact Classical.decRel _;
  use fun x => (2 * n + 1) * g (rank x) x + c₂ x |> Nat.cast;
  intro x y hxy; by_cases h : rank x = rank y <;> simp_all +decide [ Fin.ext_iff ] ;
  · exact fun h' => hg ( rank y ) x y ( by aesop ) ( by aesop ) hxy ( by nlinarith [ Fin.is_lt ( c₂ x ), Fin.is_lt ( c₂ y ) ] );
  · exact fun h' => hc₂ x y hxy h <| by nlinarith [ show g ( rank x ) x = g ( rank y ) y from by nlinarith [ Fin.is_lt ( c₂ x ), Fin.is_lt ( c₂ y ) ] ] ;

/-! ### Induced subgraphs preserve `K_{n,ℵ₁}`-freeness -/

/-
A `K_{n,ℵ₁}` in an induced subgraph lifts to `G`; hence `K_{n,ℵ₁}`-freeness
passes to induced subgraphs.
-/
theorem hasKnAleph1_of_induce (G : SimpleGraph V) (n : ℕ) (M : Set V)
    (h : HasKnAleph1 (G.induce M) n) : HasKnAleph1 G n := by
  obtain ⟨ a, B, ha, hB, hB', hB'' ⟩ := h;
  refine' ⟨ fun i => a i, Subtype.val '' B, _, _, _, _ ⟩;
  · exact Subtype.coe_injective.comp ha;
  · rw [ Cardinal.mk_image_eq ] ; aesop;
    exact Subtype.coe_injective;
  · grind;
  · aesop

/-! ### The main base-case theorem -/

/-
A graph on a countable vertex type is countably colourable (colour injectively).
-/
theorem gCountColorable_of_le_aleph0 (G : SimpleGraph V) (h : #V ≤ ℵ₀) :
    GCountColorable G := by
  have h_countable : Infinite V → Nonempty (V ↪ ℕ) := by
    exact fun _ => Cardinal.lift_mk_le'.mp ( by simpa using! h );
  by_cases hV : Infinite V;
  · obtain ⟨ c ⟩ := h_countable hV; exact ⟨ c, fun x y hxy => by simpa using! c.injective.ne hxy.ne ⟩ ;
  · simp_all +decide [ Infinite ];
    obtain ⟨c, hc⟩ : ∃ c : V → Fin (Nat.card V), Function.Injective c := by
      haveI := Fintype.ofFinite V;
      exact ⟨ fun x => Fintype.equivFinOfCardEq ( by simp +decide [ Nat.card_eq_fintype_card ] ) x, by simp +decide [ Function.Injective ] ⟩;
    exact ⟨ fun x => c x, fun x y hxy => by simpa [ Fin.ext_iff ] using! hc.ne hxy.ne ⟩

/-- **The core reduction.**  If `G` is `K_{n,ℵ₁}`-free (`n ≥ 1`), its vertex type
is uncountable, and every strictly smaller `K_{n,ℵ₁}`-free graph is countably
colourable, then `G` itself is countably colourable.  This is the closed-set
filtration argument: build `M a = cl (e '' {b ≤ a})` over an enumeration
`e : κ.ord.ToType ≃ V`, take `rank x` = least `a` with `x ∈ M a`, and apply
`countColorable_of_rank` (back-neighbours are `< n` by closedness; each level lies
in some `M a` of size `< κ`, hence is countably colourable by the hypothesis). -/
theorem countColorable_of_smaller (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n)
    (hfree : ¬ HasKnAleph1 G n) (hbig : ℵ₀ < #V)
    (IH : ∀ (W : Type u) (GW : SimpleGraph W), #W < #V → ¬ HasKnAleph1 GW n →
      GCountColorable GW) :
    GCountColorable G := by
  classical
  obtain ⟨e⟩ : Nonempty ((#V).ord.ToType ≃ V) :=
    Cardinal.eq.1 (by simp)
  set Idx := (#V).ord.ToType
  set M : Idx → Set V := fun a => cl G n (e '' {b | b ≤ a}) with hM
  have hmono : Monotone M := by
    intro a b hab
    exact cl_mono _ _ (Set.image_mono (fun x hx => le_trans hx.out hab))
  have hcl : ∀ a, NClosed G n (M a) := fun a => nclosed_cl G n hn _
  have hsmall : ∀ a, #(M a) < #V := by
    intro a
    have h1 : #(M a) ≤ #(e '' {b : Idx | b ≤ a}) + ℵ₀ := cl_card_le G n hfree _
    have h2 : #(e '' {b : Idx | b ≤ a}) ≤ #(Set.Iio a) + 1 := by
      refine le_trans Cardinal.mk_image_le ?_
      refine le_trans (Cardinal.mk_le_mk_of_subset
        (show {b : Idx | b ≤ a} ⊆ insert a (Set.Iio a) from ?_)) Cardinal.mk_insert_le
      intro x hx
      have hx' : x ≤ a := hx
      rcases lt_or_eq_of_le hx' with h | h
      · exact Or.inr h
      · exact Or.inl h
    have h3 : #(Set.Iio a) < #V := Cardinal.mk_Iio_ord_toType a
    have haleph : ℵ₀ ≤ #V := le_of_lt hbig
    have h4 : #(Set.Iio a) + 1 < #V :=
      Cardinal.add_lt_of_lt haleph h3 (lt_of_lt_of_le Cardinal.one_lt_aleph0 haleph)
    calc #(M a) ≤ #(e '' {b : Idx | b ≤ a}) + ℵ₀ := h1
      _ ≤ (#(Set.Iio a) + 1) + ℵ₀ := by gcongr
      _ < #V := Cardinal.add_lt_of_lt haleph h4 hbig
  have hcov : ∀ x, x ∈ M (e.symm x) :=
    fun x => subset_cl _ _ _ ⟨e.symm x, by simp, by simp⟩
  set rank : V → Idx :=
    fun x => (wellFounded_lt (α := Idx)).min {a | x ∈ M a} ⟨e.symm x, hcov x⟩ with hrank
  have hmemR : ∀ x, x ∈ M (rank x) :=
    fun x => (wellFounded_lt (α := Idx)).min_mem {a | x ∈ M a} ⟨e.symm x, hcov x⟩
  have hleast : ∀ x b, b < rank x → x ∉ M b := by
    intro x b hb hmem
    exact (wellFounded_lt (α := Idx)).not_lt_min {a | x ∈ M a} hmem hb
  apply countColorable_of_rank G n hn rank
  · intro x
    set a := rank x
    set U := ⋃ b ∈ {b : Idx | b < a}, M b with hU
    have hUcl : NClosed G n U := nclosed_biUnion_lt G n hn M hmono hcl a
    have hxU : x ∉ U := by
      intro hx
      obtain ⟨b, hb₁, hb₂⟩ := Set.mem_iUnion₂.mp hx
      exact hleast x b hb₁ hb₂
    have hback : #(nbhdIn G x U) < n := hUcl x hxU
    have hsubset : {y | G.Adj x y ∧ rank y < rank x} ⊆ nbhdIn G x U :=
      fun y hy => ⟨Set.mem_iUnion₂.mpr ⟨rank y, hy.2, hmemR y⟩, hy.1⟩
    exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hsubset) hback
  · intro a
    have h_induce : ¬ HasKnAleph1 (G.induce (M a)) n :=
      fun hh => hfree (hasKnAleph1_of_induce G n (M a) hh)
    obtain ⟨c, hc⟩ := IH (↥(M a)) (SimpleGraph.induce (M a) G) (hsmall a) h_induce
    refine ⟨fun x => if hx : x ∈ M a then c ⟨x, hx⟩ else 0, ?_⟩
    intro x y hrx hry hadj
    have hx : x ∈ M a := hrx ▸ hmemR x
    have hy : y ∈ M a := hry ▸ hmemR y
    simp only [dif_pos hx, dif_pos hy]
    exact hc ⟨x, hx⟩ ⟨y, hy⟩ hadj

/-- **Erdős–Hajnal base case.**  Every graph of uncountable chromatic number
contains `K_{n, ℵ₁}` for every `n`. -/
theorem eh_hasKnAleph1 (G : SimpleGraph V)
    (h : ¬ (SimpleGraph.toHG G).ColorableBy ℵ₀) (n : ℕ) : HasKnAleph1 G n := by
  rw [← gCountColorable_iff_colorableBy] at h
  have key : ∀ κ : Cardinal.{u}, ∀ (W : Type u) (GW : SimpleGraph W),
      #W = κ → ¬ GCountColorable GW → HasKnAleph1 GW n := by
    refine fun κ => Cardinal.lt_wf.induction
      (C := fun κ => ∀ (W : Type u) (GW : SimpleGraph W),
        #W = κ → ¬ GCountColorable GW → HasKnAleph1 GW n) κ ?_
    intro κ IH W GW hcard hncc
    have hbig : ℵ₀ < #W := by
      by_contra hle
      exact hncc (gCountColorable_of_le_aleph0 GW (not_lt.mp hle))
    by_cases hn0 : n = 0
    · subst hn0
      refine ⟨Fin.elim0, Set.univ, ?_, ?_, ?_, ?_⟩
      · intro a; exact a.elim0
      · rw [Cardinal.mk_univ]; exact Cardinal.succ_aleph0 ▸ Order.succ_le_of_lt hbig
      · intro a; exact a.elim0
      · intro a; exact a.elim0
    · by_contra hfree
      refine hncc (countColorable_of_smaller GW n (Nat.one_le_iff_ne_zero.mpr hn0)
        hfree hbig ?_)
      intro W' GW' hlt hfree'
      by_contra hncc'
      exact hfree' (IH (#W') (hcard ▸ hlt) W' GW' rfl hncc')
  exact key (#V) V G rfl h

/-- `G` contains a (finite) complete bipartite graph `K_{m,m}`: two disjoint
`m`-element vertex sets, complete between them. -/
def HasKmm (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ a b : Fin m → V, Function.Injective a ∧ Function.Injective b ∧
    (∀ i j, a i ≠ b j) ∧ (∀ i j, G.Adj (a i) (b j))

/-- **Erdős–Hajnal, finite form.**  Every graph of uncountable chromatic number
contains `K_{m,m}` for every `m`. -/
theorem eh_hasKmm (G : SimpleGraph V)
    (h : ¬ (SimpleGraph.toHG G).ColorableBy ℵ₀) (m : ℕ) : HasKmm G m := by
  obtain ⟨a, B, ha, hB, hB', hB''⟩ : ∃ (a : Fin m → V) (B : Set V), Function.Injective a ∧ ℵ₁ ≤ #B ∧ (∀ i, a i ∉ B) ∧ (∀ i, ∀ b ∈ B, G.Adj (a i) b) := by
    convert! eh_hasKnAleph1 G h m;
  obtain ⟨b, hb⟩ : ∃ b : Fin m → V, Function.Injective b ∧ ∀ i, b i ∈ B := by
    have hB_inf : Infinite B := by
      contrapose! hB;
      exact lt_of_le_of_lt ( Cardinal.mk_le_aleph0 ) ( Cardinal.aleph0_lt_aleph_one );
    have := hB_inf.natEmbedding;
    exact ⟨ fun i => this i, fun i j hij => by simpa [ Fin.ext_iff ] using! this.injective ( Subtype.ext hij ), fun i => this i |>.2 ⟩;
  exact ⟨ a, b, ha, hb.1, fun i j => by intro H; have := hB' i; have := hb.2 j; aesop, fun i j => hB'' i _ ( hb.2 j ) ⟩

end Erdos1177

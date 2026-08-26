-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Structures

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite bridge decomposition (§5): the forward direction

This file proves that every member of the class `B`, and more generally the
`IntrinsicObligatory` predicate, behaves well: members of `B` satisfy the
intrinsic condition (linear, every hyperedge-node incident with a bridge, every
Berge cycle even), and the intrinsic condition is invariant under the
isolated-vertex reduction and under isomorphism.

These are the pieces of `prop:finite-decomposition` that do not require the
quotient-forest reconstruction.
-/

open Cardinal

namespace Erdos1177

open Classical

universe u

/-! ### General cyclic-parity lemmas on `ZMod m` -/

/-
A function on the cycle `ZMod m` that never changes between consecutive
indices is constant.
-/
theorem zmod_const_of_succ_eq {m : ℕ} [NeZero m] {α : Type*} (s : ZMod m → α)
    (h : ∀ i, s i = s (i + 1)) (i : ZMod m) : s i = s 0 := by
  have h_ind : ∀ k : ℕ, s (k : ZMod m) = s 0 := by
    intro k; induction' k with k ih <;> norm_num at *;
    rw [ ← h, ih ];
  simpa using! h_ind i.val

/-
If a `Bool`-valued function on the cycle `ZMod m` changes at most once
(any two change-points coincide), then it never changes.
-/
theorem zmod_succ_eq_of_unique_change {m : ℕ} [NeZero m] (s : ZMod m → Bool)
    (h : ∀ i j, s i ≠ s (i + 1) → s j ≠ s (j + 1) → i = j) (i : ZMod m) :
    s i = s (i + 1) := by
  by_contra h_contra;
  -- Let $T$ be the set of indices where $s$ changes.
  set T := Finset.univ.filter (fun i => s i ≠ s (i + 1)) with hT_def
  have hT_card : T.card ≤ 1 := by
    exact Finset.card_le_one.mpr fun x hx y hy => h x y ( Finset.mem_filter.mp hx |>.2 ) ( Finset.mem_filter.mp hy |>.2 );
  have hT_even : Even T.card := by
    have hT_even : ∑ i : ZMod m, (if s i then 1 else 0 : ZMod 2) + ∑ i : ZMod m, (if s (i + 1) then 1 else 0 : ZMod 2) = 0 := by
      erw [ Equiv.sum_comp ( Equiv.addRight 1 ) fun i => if s i = true then 1 else 0 ] ; ring;
      grind;
    have hT_even : ∑ i : ZMod m, (if s i ≠ s (i + 1) then 1 else 0 : ZMod 2) = ∑ i : ZMod m, (if s i then 1 else 0 : ZMod 2) + ∑ i : ZMod m, (if s (i + 1) then 1 else 0 : ZMod 2) := by
      rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; by_cases hi : s i <;> by_cases hi' : s ( i + 1 ) <;> simp +decide [ hi, hi' ] ;
    simp_all +decide [ Finset.sum_ite ];
    rw [ ZMod.natCast_eq_zero_iff ] at hT_even ; exact even_iff_two_dvd.mpr hT_even;
  exact absurd hT_even ( by rw [ show T.card = 1 by exact le_antisymm hT_card ( Finset.card_pos.mpr ⟨ i, by aesop ⟩ ) ] ; decide )

/-
A `ZMod 2`-valued function on the cycle `ZMod m` that increments by `1` at
every step forces `m` to be even.
-/
theorem zmod_even_of_alt {m : ℕ} [NeZero m] (s : ZMod m → ZMod 2)
    (h : ∀ i, s (i + 1) = s i + 1) : Even m := by
  have h_m_even : ∀ k : ℕ, s k = s 0 + k := by
    intro k; induction k <;> simp_all +decide [ ← add_assoc ] ;
  specialize h_m_even m; simp_all +decide ;
  rw [ ZMod.natCast_eq_zero_iff ] at h_m_even ; exact even_iff_two_dvd.mpr h_m_even

/-! ### The intrinsic condition is invariant under `reduce` -/

/-
A vertex lying on an edge is not isolated.
-/
theorem FTS.not_isolated_of_mem {F : FTS} {x : F.V} {e : Finset F.V}
    (he : e ∈ F.edges) (hx : x ∈ e) : ¬ F.Isolated x := by
  exact fun h => h e he hx

/-
Restricting an `F`-edge to non-isolated vertices gives an edge of the
reduction (all vertices of an edge are non-isolated).
-/
theorem FTS.subtype_edge_mem {F : FTS} {e : Finset F.V} (he : e ∈ F.edges) :
    Finset.subtype (fun x => ¬ F.Isolated x) e ∈ F.reduce.edges := by
  exact Finset.mem_image.mpr ⟨ ⟨ e, he ⟩, Finset.mem_attach _ _, rfl ⟩

/-
The restriction of an edge, mapped back by the subtype inclusion, is the
original edge.
-/
theorem FTS.subtype_map_eq {F : FTS} {e : Finset F.V} (he : e ∈ F.edges) :
    (Finset.subtype (fun x => ¬ F.Isolated x) e).map
      (Function.Embedding.subtype (fun x => ¬ F.Isolated x)) = e := by
  ext x; simp [Finset.mem_map, Finset.mem_subtype];
  exact fun hx => FTS.not_isolated_of_mem he hx

/-
The subtype-inclusion image of a reduce-edge is an `F`-edge.
-/
theorem FTS.reduce_edge_map_mem {F : FTS} {d : Finset F.reduce.V} (hd : d ∈ F.reduce.edges) :
    d.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)) ∈ F.edges := by
  simp_all +decide [ FTS.reduce ];
  grind +suggestions

/-- Transport a Berge cycle of the reduction up to `F` (same length). -/
noncomputable def BergeCycle.ofReduce {F : FTS} (c : BergeCycle F.reduce) : BergeCycle F where
  m := c.m
  hm := c.hm
  v := fun i => Function.Embedding.subtype (fun x => ¬ F.Isolated x) (c.v i)
  e := fun i => ⟨(c.e i).1.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)),
    FTS.reduce_edge_map_mem (c.e i).2⟩
  vinj := fun i j h => c.vinj ((Function.Embedding.subtype _).injective h)
  einj := by
    intro i j h
    apply c.einj
    have h2 : (c.e i).1.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)) =
        (c.e j).1.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)) := by
      simpa using! congrArg Subtype.val h
    exact Subtype.ext (Finset.map_injective _ h2)
  mem_left := fun i => Finset.mem_map_of_mem _ (c.mem_left i)
  mem_right := fun i => Finset.mem_map_of_mem _ (c.mem_right i)

/-- Transport a Berge cycle of `F` down to the reduction (same length). -/
noncomputable def BergeCycle.toReduce {F : FTS} (c : BergeCycle F) : BergeCycle F.reduce where
  m := c.m
  hm := c.hm
  v := fun i => ⟨c.v i, FTS.not_isolated_of_mem (c.e i).2 (c.mem_left i)⟩
  e := fun i => ⟨Finset.subtype (fun x => ¬ F.Isolated x) (c.e i).1,
    FTS.subtype_edge_mem (c.e i).2⟩
  vinj := fun i j h => c.vinj (by simpa using! congrArg Subtype.val h)
  einj := by
    intro i j h
    apply c.einj
    apply Subtype.ext
    have h1 := FTS.subtype_map_eq (c.e i).2
    have h2 := FTS.subtype_map_eq (c.e j).2
    have hh : Finset.subtype (fun x => ¬ F.Isolated x) (c.e i).1
        = Finset.subtype (fun x => ¬ F.Isolated x) (c.e j).1 := congrArg Subtype.val h
    rw [← h1, ← h2, hh]
  mem_left := fun i => by
    rw [Finset.mem_subtype]; exact c.mem_left i
  mem_right := fun i => by
    rw [Finset.mem_subtype]; exact c.mem_right i

/-
The intrinsic condition is unaffected by isolated vertices.
-/
theorem FTS.intrinsic_reduce_iff (F : FTS) :
    F.IntrinsicObligatory ↔ F.reduce.IntrinsicObligatory := by
  constructor <;> intro h;
  · obtain ⟨hlin, hbr, hev⟩ := h;
    refine' ⟨ _, _, _ ⟩;
    · intro e₁ he₁ e₂ he₂ hne;
      convert! hlin _ ( FTS.reduce_edge_map_mem he₁ ) _ ( FTS.reduce_edge_map_mem he₂ ) _ using 1;
      · rw [ ← Finset.map_inter ] ; aesop;
      · exact fun h => hne <| Finset.map_injective ( Function.Embedding.subtype _ ) h;
    · intro ed
      obtain ⟨w, hw⟩ := hbr ⟨ed.1.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)), FTS.reduce_edge_map_mem ed.2⟩
      use ⟨w, by
        grind +suggestions⟩
      generalize_proofs at *;
      simp_all +decide [ IsBridgeInc, OnBergeCycle ];
      intro c i hi; specialize hw; have := hw.2 ( BergeCycle.ofReduce c ) i; simp_all +decide [ BergeCycle.ofReduce ] ;
      exact ⟨ fun h => this.1 <| by simpa using! congr_arg Subtype.val h, fun h => this.2 <| by simpa using! congr_arg Subtype.val h ⟩;
    · exact fun c => hev ( BergeCycle.ofReduce c );
  · refine' ⟨ _, _, _ ⟩;
    · intro e₁ he₁ e₂ he₂ hne;
      convert! h.1 ( Finset.subtype ( fun x => ¬ F.Isolated x ) e₁ ) ( FTS.subtype_edge_mem he₁ ) ( Finset.subtype ( fun x => ¬ F.Isolated x ) e₂ ) ( FTS.subtype_edge_mem he₂ ) _ using 1;
      · refine' Finset.card_bij ( fun x hx => ⟨ x, _ ⟩ ) _ _ _ <;> simp_all +decide [ Finset.subtype ];
        exact fun h => h e₁ he₁ hx.1;
        · exact fun x hx₁ hx₂ => ⟨ ⟨ x, ⟨ hx₁, FTS.not_isolated_of_mem he₁ hx₁ ⟩, rfl ⟩, ⟨ x, ⟨ hx₂, FTS.not_isolated_of_mem he₂ hx₂ ⟩, rfl ⟩ ⟩;
        · grind;
        · grind +suggestions;
      · contrapose! hne;
        convert! congr_arg ( fun s => s.map ( Function.Embedding.subtype ( fun x => ¬ F.Isolated x ) ) ) hne using 1 <;> simp +decide [ FTS.subtype_map_eq ];
        · grind +suggestions;
        · exact Eq.symm ( Finset.filter_true_of_mem fun x hx => FTS.not_isolated_of_mem he₂ hx );
    · intro ed
      obtain ⟨w, hw⟩ : ∃ w ∈ Finset.subtype (fun x => ¬F.Isolated x) ed.val, IsBridgeInc F.reduce w ⟨Finset.subtype (fun x => ¬F.Isolated x) ed.val, FTS.subtype_edge_mem ed.prop⟩ := by
        convert! h.2.1 ⟨ _, FTS.subtype_edge_mem ed.2 ⟩ using 1;
      refine' ⟨ w, _, _ ⟩ <;> simp_all +decide [ IsBridgeInc, OnBergeCycle ];
      intro c i hi; specialize hw; have := hw.2.2 ( BergeCycle.toReduce c ) i; simp_all +decide [ BergeCycle.toReduce ] ;
      exact ⟨ fun h => this.1 <| Subtype.ext h, fun h => this.2 <| Subtype.ext h ⟩;
    · intro c;
      convert! h.2.2 ( BergeCycle.toReduce c ) using 1

/-! ### The intrinsic condition is transported across isomorphism -/

/-
Isomorphic finite triple systems have the same intrinsic behaviour.
-/
theorem intrinsic_iso {F G : FTS} (h : FTS.Iso F G) (hF : F.IntrinsicObligatory) :
    G.IntrinsicObligatory := by
  refine' ⟨ _, _, _ ⟩;
  · obtain ⟨ φ, hφ ⟩ := h;
    intro e₁ he₁ e₂ he₂ hne;
    have h_card : (Finset.map (Equiv.toEmbedding φ.symm) e₁ ∩ Finset.map (Equiv.toEmbedding φ.symm) e₂).card ≤ 1 := by
      have := hF.1 ( Finset.map φ.symm.toEmbedding e₁ ) ?_ ( Finset.map φ.symm.toEmbedding e₂ ) ?_ ?_ <;> simp_all +decide [ Finset.map_map ];
    convert! h_card using 1;
    rw [ ← Finset.card_image_of_injective _ φ.symm.injective ] ; congr ; ext ; aesop;
  · intro ed;
    obtain ⟨ φ, hφ ⟩ := h;
    obtain ⟨ w', hw' ⟩ := hF.2.1 ⟨ Finset.map φ.symm.toEmbedding ed.val, by
      rw [ hφ ];
      convert! ed.2 using 1;
      ext; simp +decide [ Finset.mem_map ] ; ⟩
    generalize_proofs at *;
    refine' ⟨ φ w', _, _ ⟩ <;> simp_all +decide [ IsBridgeInc ];
    contrapose! hw';
    intro hw''; obtain ⟨ c, i, hi, hi' ⟩ := hw'; use ⟨ c.m, c.hm, fun j => φ.symm ( c.v j ), fun j => ⟨ Finset.map φ.symm.toEmbedding ( c.e j |>.1 ), by
      convert! hφ _ |>.2 _ using 1;
      simp +decide [ Finset.map_map, Equiv.symm_trans_self ] ⟩, by
      exact fun x y hxy => c.vinj <| by simpa using! hxy;, by
      intro j k hjk; have := c.einj; aesop;, by
      exact fun i => Finset.mem_map.mpr ⟨ c.v i, c.mem_left i, by simp +decide ⟩, by
      simp +decide [ Finset.mem_map, c.mem_right ] ⟩ ; aesop;
  · intro c
    obtain ⟨φ, hφ⟩ := h
    have h_cycle : ∃ c' : BergeCycle F, c'.m = c.m := by
      refine' ⟨ ⟨ c.m, c.hm, fun i => φ.symm ( c.v i ), fun i => ⟨ Finset.map φ.symm.toEmbedding ( c.e i |>.1 ), _ ⟩, _, _, _, _ ⟩, rfl ⟩ <;> simp_all +decide [ Function.Injective ];
      · simp +decide [ Finset.map_map, Equiv.toEmbedding_apply ];
      · exact c.vinj;
      · exact c.einj;
      · exact fun i => c.mem_left i;
      · exact c.mem_right;
    exact h_cycle.choose_spec ▸ hF.2.2 _

/-! ### Forward direction: generators and closure operations preserve the
intrinsic condition -/

/-
Edgeless systems satisfy the intrinsic condition vacuously.
-/
theorem edgeless_intrinsic (F : FTS) (h : F.edges = ∅) : F.IntrinsicObligatory := by
  refine' ⟨ _, _, _ ⟩;
  · intro e₁ he₁ e₂ he₂; aesop;
  · grind;
  · intro c;
    exact absurd ( c.e 0 |>.2 ) ( by simp +decide [ h ] )

/-! ### The private-vertex expansion -/

/-
Every edge of `graphExpansion J` has the standard three-element shape.
-/
theorem expansion_edge_cases {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] {s : Finset ((graphExpansion J).V)}
    (hs : s ∈ (graphExpansion J).edges) :
    ∃ e : {x : Sym2 VJ // x ∈ J.edgeFinset},
      s = {Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e} := by
  unfold graphExpansion at hs; aesop;

/-
The two core endpoints of an expansion edge are `J`-adjacent.
-/
theorem expansion_endpoints_adj {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] (e : {x : Sym2 VJ // x ∈ J.edgeFinset}) :
    J.Adj (Quot.out e.1).1 (Quot.out e.1).2 := by
  have hmem : e.val ∈ J.edgeSet := by
    grind +suggestions;
  rw [ ← Quot.out_eq e.val ] at hmem; exact hmem;

/-
The private vertex `Sum.inr e` lies on exactly the edge for `e`.
-/
theorem expansion_private {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] {s : Finset ((graphExpansion J).V)}
    (hs : s ∈ (graphExpansion J).edges) {e : {x : Sym2 VJ // x ∈ J.edgeFinset}}
    (hmem : Sum.inr e ∈ s) :
    s = {Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e} := by
  obtain ⟨d, rfl⟩ := expansion_edge_cases J hs
  have h : e = d := by simpa using hmem
  subst d
  rfl

/-
The private-vertex expansion is linear.
-/
theorem expansion_linear {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] : (graphExpansion J).Linear := by
  intro e₁ he₁ e₂ he₂ hne; simp_all +decide [ Finset.subset_iff ] ;
  obtain ⟨ a₁, ha₁ ⟩ := expansion_edge_cases J he₁
  obtain ⟨ a₂, ha₂ ⟩ := expansion_edge_cases J he₂;
  have h_diff : a₁ ≠ a₂ := by
    intro h
    subst a₂
    exact hne (ha₁.trans ha₂.symm)
  by_contra h_contra;
  have h_core : ∃ p q : VJ, p ≠ q ∧ Sum.inl p ∈ e₁ ∧ Sum.inl p ∈ e₂ ∧ Sum.inl q ∈ e₁ ∧ Sum.inl q ∈ e₂ := by
    obtain ⟨ p, hp, q, hq, hpq ⟩ := Finset.one_lt_card.mp ( not_le.mp h_contra );
    have hnpriv : ∀ d, Sum.inr d ∉ e₁ ∩ e₂ := by
      intro d hd
      exact hne ((expansion_private J he₁ (Finset.mem_inter.mp hd).1).trans
        (expansion_private J he₂ (Finset.mem_inter.mp hd).2).symm)
    cases p with
    | inr d => exact False.elim (hnpriv d hp)
    | inl p =>
      cases q with
      | inr d => exact False.elim (hnpriv d hq)
      | inl q =>
        exact ⟨p, q, fun h => hpq (congrArg Sum.inl h),
          (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2,
          (Finset.mem_inter.mp hq).1, (Finset.mem_inter.mp hq).2⟩
  obtain ⟨ p, q, hpq, hp₁, hp₂, hq₁, hq₂ ⟩ := h_core;
  have hvalue (a : {x : Sym2 VJ // x ∈ J.edgeFinset})
      (hp : p = (Quot.out a.1).1 ∨ p = (Quot.out a.1).2)
      (hq : q = (Quot.out a.1).1 ∨ q = (Quot.out a.1).2) : a.val = s(p, q) := by
    have hout : s((Quot.out a.1).1, (Quot.out a.1).2) = a.val := Quot.out_eq a.val
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact False.elim (hpq (hp.trans hq.symm))
    · rw [hp, hq]; exact hout.symm
    · rw [hp, hq, Sym2.eq_swap]; exact hout.symm
    · exact False.elim (hpq (hp.trans hq.symm))
  have h₁ : a₁.val = s(p, q) := hvalue a₁
    (by simpa [ha₁] using hp₁) (by simpa [ha₁] using hq₁)
  have h₂ : a₂.val = s(p, q) := hvalue a₂
    (by simpa [ha₂] using hp₂) (by simpa [ha₂] using hq₂)
  exact h_diff (Subtype.ext (h₁.trans h₂.symm))

/-
In the expansion, every hyperedge-node is incident with a bridge (its
private vertex).
-/
theorem expansion_bridge {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj]
    (ed : {e : Finset ((graphExpansion J).V) // e ∈ (graphExpansion J).edges}) :
    ∃ w ∈ ed.1, IsBridgeInc (graphExpansion J) w ed := by
  obtain ⟨ e, he ⟩ := expansion_edge_cases J ed.2; use Sum.inr e; simp_all +decide [ IsBridgeInc ] ;
  rintro ⟨ c, i, hi, hvi ⟩;
  cases' hvi with hvi hvi <;> have := c.mem_left i <;> have := c.mem_right i <;> simp_all +decide [ Finset.ext_iff ];
  · have := c.mem_right ( i - 1 ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
    have := expansion_private J ( c.e ( i - 1 ) |>.2 ) this; simp_all +decide [ Finset.ext_iff ] ;
    have := c.einj ( show c.e ( i - 1 ) = c.e i from ?_ ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
    · rcases c with ⟨ _ | _ | m, hm, v, e, vinj, einj, mem_left, mem_right ⟩ <;> cases this ; contradiction;
    · exact Subtype.ext <| Finset.ext fun x => by aesop;
  · have := c.mem_left ( i + 1 ) ; have := c.mem_right ( i + 1 ) ; simp_all +decide [ Finset.ext_iff ] ;
    have := c.einj ( show c.e ( i + 1 ) = c.e i from ?_ ) ; simp_all +decide [ add_assoc ] ;
    · rcases c with ⟨ _ | _ | m, hm, v, e, vinj, einj, mem_left, mem_right ⟩ <;> cases this ; contradiction;
    · have := expansion_private J ( c.e ( i + 1 ) |>.2 ) ‹_›; aesop;

/-
In a Berge cycle of the expansion, every point-node is a core vertex.
-/
theorem expansion_cycle_core {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] (c : BergeCycle (graphExpansion J)) (i : ZMod c.m) :
    ∃ a : VJ, c.v i = Sum.inl a := by
  by_contra h_contra;
  obtain ⟨e, he⟩ : ∃ e : {x : Sym2 VJ // x ∈ J.edgeFinset}, c.v i = Sum.inr e := by
    cases h : c.v i <;> aesop;
  have h_eq : (c.e i).1 = {Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e} ∧ (c.e (i - 1)).1 = {Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e} := by
    have := c.mem_left i; have := c.mem_right ( i - 1 ) ; simp_all +decide [ Finset.ext_iff ] ;
    have := expansion_private J ( c.e i |>.2 ) ‹_›; have := expansion_private J ( c.e ( i - 1 ) |>.2 ) ‹_›; aesop;
  cases c ; simp_all +decide [ ZMod ];
  rename_i k hk₁ hk₂ hk₃ hk₄ hk₅ hk₆;
  have := @hk₄ ( i - 1 ) i; simp_all +decide [ ZMod ] ;
  cases ‹ℕ› <;> simp_all +decide [ ZMod ];
  · contradiction;
  · exact absurd ( this ( Subtype.ext <| by aesop ) ) ( by linarith )

/-
The expansion of a bipartite graph has only even Berge cycles.
-/
theorem expansion_even {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] (hJ : J.Colorable 2) (c : BergeCycle (graphExpansion J)) :
    Even c.m := by
  obtain ⟨ col, hcol ⟩ := hJ;
  -- Define `a : ZMod c.m → VJ` by `a i := (expansion_cycle_core J c i).choose`, so `c.v i = Sum.inl (a i)` for all `i`.
  set a : ZMod c.m → VJ := fun i => (expansion_cycle_core J c i).choose
  have ha : ∀ i, c.v i = Sum.inl (a i) := by
    exact fun i => ( expansion_cycle_core J c i ).choose_spec;
  -- Claim `hadj : ∀ i, J.Adj (a i) (a (i+1))`.
  have hadj : ∀ i, J.Adj (a i) (a (i + 1)) := by
    intro i
    obtain ⟨e, he⟩ := expansion_edge_cases J (c.e i).2
    have hx : a i ∈ ({(Quot.out e.1).1, (Quot.out e.1).2} : Finset VJ) := by
      have := c.mem_left i; simp_all +decide [ Finset.ext_iff ] ;
      grind
    have hy : a (i + 1) ∈ ({(Quot.out e.1).1, (Quot.out e.1).2} : Finset VJ) := by
      have := c.mem_right i; simp_all +decide [ Finset.ext_iff ] ;
      grind
    have hxy : a i ≠ a (i + 1) := by
      have := c.vinj.ne ( show i ≠ i + 1 from by
                            haveI := Fact.mk ( show 1 < c.m from c.hm ) ; simp +decide ; ) ; simp_all +decide [ ZMod ] ;
      exact fun h => this <| h ▸ rfl
    have h_adj : J.Adj (a i) (a (i + 1)) := by
      have h_adj : J.Adj (Quot.out e.1).1 (Quot.out e.1).2 := by
        grind +suggestions;
      simp_all +decide [ SimpleGraph.adj_comm ];
      cases hx <;> cases hy <;> simp_all +decide [ SimpleGraph.adj_comm ]
    exact h_adj;
  haveI : NeZero c.m := ⟨by have := c.hm; omega⟩
  apply zmod_even_of_alt (fun i => (col (a i) : ZMod 2))
  intro i
  have hne : col (a i) ≠ col (a (i + 1)) := hcol (hadj i)
  generalize hx : col (a i) = x at *
  generalize hy : col (a (i + 1)) = y at *
  fin_cases x <;> fin_cases y <;> norm_num at *
  exact (ZMod.natCast_self 2).symm

/-- The private-vertex expansion of a bipartite graph satisfies the intrinsic
condition. -/
theorem expansion_intrinsic {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] (hJ : J.Colorable 2) : (graphExpansion J).IntrinsicObligatory :=
  ⟨expansion_linear J, expansion_bridge J, expansion_even J hJ⟩

/-! ### Disjoint union -/

/-
Every edge of a disjoint union comes from exactly one side.
-/
theorem disjUnion_edge_cases {F G : FTS} {e : Finset (F.V ⊕ G.V)}
    (he : e ∈ (F.disjUnion G).edges) :
    (∃ d ∈ F.edges, e = d.map Function.Embedding.inl) ∨
    (∃ d ∈ G.edges, e = d.map Function.Embedding.inr) := by
  unfold FTS.disjUnion at he; aesop;

/-
In a Berge cycle of a disjoint union, all point-nodes lie on the same side.
-/
theorem disjUnion_berge_side {F G : FTS} (c : BergeCycle (F.disjUnion G)) :
    (∀ i, ∃ a : F.V, c.v i = Sum.inl a) ∨ (∀ i, ∃ b : G.V, c.v i = Sum.inr b) := by
  -- Let `s : ZMod c.m → Bool := fun i => (c.v i).isLeft`.
  set s : ZMod c.m → Bool := fun i => (c.v i).isLeft;
  -- By `zmod_const_of_succ_eq s hconst`, `s i = s 0` for all `i`.
  have h_const : ∀ i : ZMod c.m, s i = s 0 := by
    have hconst : ∀ i, s i = s (i + 1) := by
      intro i;
      obtain ⟨d, hd, hmap⟩ | ⟨d, hd, hmap⟩ := disjUnion_edge_cases (c.e i).2
      all_goals
        have hl := c.mem_left i
        have hr := c.mem_right i
        rw [hmap] at hl hr
        obtain ⟨a, ha, hva⟩ := Finset.mem_map.mp hl
        obtain ⟨b, hb, hvb⟩ := Finset.mem_map.mp hr
        dsimp [s]
        rw [← hva, ← hvb]
        rfl
    convert! zmod_const_of_succ_eq s hconst using 1;
    exact ⟨ by linarith [ c.hm ] ⟩;
  cases h : s 0 <;> simp_all +decide [ Sum.isLeft_iff, Sum.isRight_iff ];
  · exact Or.inr fun i => by specialize h_const i; cases h : c.v i <;> aesop;
  · exact Or.inl fun i => by cases h : c.v i <;> specialize h_const i <;> aesop;

/-- Extract a Berge cycle of `F` from an all-left Berge cycle of the disjoint
union (same length). -/
noncomputable def BergeCycle.ofDisjLeft {F G : FTS} (c : BergeCycle (F.disjUnion G))
    (hv : ∀ i, ∃ a : F.V, c.v i = Sum.inl a)
    (he : ∀ i, ∃ d : Finset F.V, d ∈ F.edges ∧ (c.e i).1 = d.map Function.Embedding.inl) :
    BergeCycle F where
  m := c.m
  hm := c.hm
  v := fun i => (hv i).choose
  e := fun i => ⟨(he i).choose, (he i).choose_spec.1⟩
  vinj := by
    intro i j hij
    apply c.vinj
    rw [(hv i).choose_spec, (hv j).choose_spec]
    exact congrArg Sum.inl hij
  einj := by
    intro i j hij
    apply c.einj
    apply Subtype.ext
    have hd : (he i).choose = (he j).choose := congrArg Subtype.val hij
    rw [(he i).choose_spec.2, (he j).choose_spec.2, hd]
  mem_left := by
    intro i
    have h1 := c.mem_left i
    rw [(hv i).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1
  mem_right := by
    intro i
    have h1 := c.mem_right i
    rw [(hv (i + 1)).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1

/-- Extract a Berge cycle of `G` from an all-right Berge cycle of the disjoint
union (same length). -/
noncomputable def BergeCycle.ofDisjRight {F G : FTS} (c : BergeCycle (F.disjUnion G))
    (hv : ∀ i, ∃ b : G.V, c.v i = Sum.inr b)
    (he : ∀ i, ∃ d : Finset G.V, d ∈ G.edges ∧ (c.e i).1 = d.map Function.Embedding.inr) :
    BergeCycle G where
  m := c.m
  hm := c.hm
  v := fun i => (hv i).choose
  e := fun i => ⟨(he i).choose, (he i).choose_spec.1⟩
  vinj := by
    intro i j hij
    apply c.vinj
    rw [(hv i).choose_spec, (hv j).choose_spec]
    exact congrArg Sum.inr hij
  einj := by
    intro i j hij
    apply c.einj
    apply Subtype.ext
    have hd : (he i).choose = (he j).choose := congrArg Subtype.val hij
    rw [(he i).choose_spec.2, (he j).choose_spec.2, hd]
  mem_left := by
    intro i
    have h1 := c.mem_left i
    rw [(hv i).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1
  mem_right := by
    intro i
    have h1 := c.mem_right i
    rw [(hv (i + 1)).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1

/-
In an all-left Berge cycle, each edge is an `inl`-image of an `F`-edge.
-/
theorem disjUnion_berge_edges_left {F G : FTS} (c : BergeCycle (F.disjUnion G))
    (hv : ∀ i, ∃ a : F.V, c.v i = Sum.inl a) :
    ∀ i, ∃ d : Finset F.V, d ∈ F.edges ∧ (c.e i).1 = d.map Function.Embedding.inl := by
  intro i
  obtain ⟨d, hd⟩ := disjUnion_edge_cases (c.e i).2;
  · use d;
  · obtain ⟨ d, hd, h ⟩ := ‹_›; specialize hv i; obtain ⟨ a, ha ⟩ := hv; have := c.mem_left i; simp_all +decide [ Finset.mem_map ] ;
    tauto

/-
In an all-right Berge cycle, each edge is an `inr`-image of a `G`-edge.
-/
theorem disjUnion_berge_edges_right {F G : FTS} (c : BergeCycle (F.disjUnion G))
    (hv : ∀ i, ∃ b : G.V, c.v i = Sum.inr b) :
    ∀ i, ∃ d : Finset G.V, d ∈ G.edges ∧ (c.e i).1 = d.map Function.Embedding.inr := by
  intro i
  obtain ⟨d, hd⟩ := disjUnion_edge_cases (c.e i).2;
  · obtain ⟨ b, hb ⟩ := hv i; have := c.mem_left i; simp_all +decide [ Finset.mem_map ] ;
    tauto;
  · tauto

/-
Disjoint union is linear if both factors are.
-/
theorem disjUnion_linear {F G : FTS} (hF : F.Linear) (hG : G.Linear) :
    (F.disjUnion G).Linear := by
  intro e₁ he₁ e₂ he₂ hne;
  rcases disjUnion_edge_cases he₁ with ( ⟨ d₁, hd₁, rfl ⟩ | ⟨ d₁, hd₁, rfl ⟩ ) <;> rcases disjUnion_edge_cases he₂ with ( ⟨ d₂, hd₂, rfl ⟩ | ⟨ d₂, hd₂, rfl ⟩ ) <;> simp_all +decide [ Finset.card_map ];
  · rw [ ← Finset.map_inter ];
    rw [ Finset.card_map ] ; exact hF _ hd₁ _ hd₂ hne;
  · rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
    simp +decide [ Finset.ext_iff ];
    exact fun a ha x hx => by rintro ⟨ ⟩ ;
  · rw [ Finset.card_eq_zero.mpr ] <;> norm_num [ Finset.ext_iff ];
    exact fun a ha x hx => by rintro ⟨ ⟩ ;
  · rw [ ← Finset.map_inter ] ; aesop;

/-
Disjoint union has only even Berge cycles if both factors do.
-/
theorem disjUnion_even {F G : FTS} (hF : ∀ c : BergeCycle F, Even c.m)
    (hG : ∀ c : BergeCycle G, Even c.m) (c : BergeCycle (F.disjUnion G)) : Even c.m := by
  cases' disjUnion_berge_side c with hv hv;
  · convert! hF ( BergeCycle.ofDisjLeft c hv ( disjUnion_berge_edges_left c hv ) ) using 1;
  · specialize hG (BergeCycle.ofDisjRight c hv (disjUnion_berge_edges_right c hv));
    exact hG

/-
Disjoint union: every hyperedge-node is incident with a bridge.
-/
theorem disjUnion_bridge {F G : FTS} (hF : F.IntrinsicObligatory)
    (hG : G.IntrinsicObligatory)
    (ed : {e : Finset (F.disjUnion G).V // e ∈ (F.disjUnion G).edges}) :
    ∃ w ∈ ed.1, IsBridgeInc (F.disjUnion G) w ed := by
  -- Let's consider the two cases from `disjUnion_edge_cases`.
  obtain ⟨d, hd, hdamap⟩ | ⟨d, hd, hdamap⟩ := disjUnion_edge_cases ed.2;
  · obtain ⟨ w, hw₁, hw₂ ⟩ := hF.2.1 ⟨ d, hd ⟩;
    refine' ⟨ Sum.inl w, _, _ ⟩ <;> simp_all +decide [ IsBridgeInc ];
    · exact ⟨ w, hw₁, rfl ⟩;
    · refine' ⟨ ⟨ w, hw₁, rfl ⟩, _ ⟩;
      rintro ⟨ c, i, hi, hi' ⟩;
      -- By `disjUnion_berge_side`, `c` is all-left or all-right. If it were the right case, `c.v i` and `c.v (i+1)` would be `Sum.inr _`, contradicting `hi'` (which says one of them is `Sum.inl w`, and `Sum.inl w ≠ Sum.inr _`). So `c` must be all-left.
      have h_all_left : ∀ i, ∃ a : F.V, c.v i = Sum.inl a := by
        cases' disjUnion_berge_side c with hv hv;
        · exact hv;
        · cases hv i ; cases hv ( i + 1 ) ; aesop;
      refine' hw₂ ⟨ BergeCycle.ofDisjLeft c h_all_left ( disjUnion_berge_edges_left c h_all_left ), i, _, _ ⟩ <;> simp_all +decide [ BergeCycle.ofDisjLeft ];
      · grind +splitImp;
      · have hvi := (h_all_left i).choose_spec
        have hvj := (h_all_left (i + 1)).choose_spec
        exact hi'.imp (fun h => Sum.inl_injective (hvi.symm.trans h))
          (fun h => Sum.inl_injective (hvj.symm.trans h))
  · obtain ⟨ w, hw₁, hw₂ ⟩ := hG.2.1 ⟨ d, hd ⟩;
    refine' ⟨ Sum.inr w, _, _ ⟩ <;> simp_all +decide [ IsBridgeInc, OnBergeCycle ];
    · exact ⟨ w, hw₁, rfl ⟩;
    · refine' ⟨ ⟨ w, hw₁, rfl ⟩, _ ⟩;
      intro c i hi;
      cases' disjUnion_berge_side c with hv hv;
      · exact ⟨ by obtain ⟨ a, ha ⟩ := hv i; aesop, by obtain ⟨ a, ha ⟩ := hv ( i + 1 ) ; aesop ⟩;
      · specialize hw₂ ( BergeCycle.ofDisjRight c hv ( disjUnion_berge_edges_right c hv ) ) i
        have hvi := (hv i).choose_spec
        have hvj := (hv (i + 1)).choose_spec
        simp only [BergeCycle.ofDisjRight] at hw₂ ⊢
        have heq : (disjUnion_berge_edges_right c hv i).choose = d := by
          apply Finset.map_injective Function.Embedding.inr
          exact (disjUnion_berge_edges_right c hv i).choose_spec.2.symm.trans
            ((congrArg Subtype.val hi).trans hdamap)
        have hnot := hw₂ (Subtype.ext heq)
        exact ⟨fun h => hnot.1 (Sum.inr_injective (hvi.symm.trans h)),
          fun h => hnot.2 (Sum.inr_injective (hvj.symm.trans h))⟩

/-- Disjoint union preserves the intrinsic condition. -/
theorem disjUnion_intrinsic {F G : FTS} (hF : F.IntrinsicObligatory)
    (hG : G.IntrinsicObligatory) : (F.disjUnion G).IntrinsicObligatory :=
  ⟨disjUnion_linear hF.1 hG.1, disjUnion_bridge hF hG,
    disjUnion_even hF.2.2 hG.2.2⟩

/-! ### One-point amalgamation -/

/-- Extract a Berge cycle of `F` from a Berge cycle of a host `H` all of whose
point-nodes and edges come from `F` via an embedding `ρ` (same length). -/
noncomputable def BergeCycle.ofEmbedding {F H : FTS} (ρ : F.V ↪ H.V)
    (c : BergeCycle H)
    (hv : ∀ i, ∃ a : F.V, c.v i = ρ a)
    (he : ∀ i, ∃ d : Finset F.V, d ∈ F.edges ∧ (c.e i).1 = d.map ρ) : BergeCycle F where
  m := c.m
  hm := c.hm
  v := fun i => (hv i).choose
  e := fun i => ⟨(he i).choose, (he i).choose_spec.1⟩
  vinj := by
    intro i j hij
    apply c.vinj
    rw [(hv i).choose_spec, (hv j).choose_spec]
    exact congrArg (⇑ρ) hij
  einj := by
    intro i j hij
    apply c.einj
    apply Subtype.ext
    have hd : (he i).choose = (he j).choose := congrArg Subtype.val hij
    rw [(he i).choose_spec.2, (he j).choose_spec.2, hd]
  mem_left := by
    intro i
    have h1 := c.mem_left i
    rw [(hv i).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1
  mem_right := by
    intro i
    have h1 := c.mem_right i
    rw [(hv (i + 1)).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1

/-- The embedding of `G` into the amalgam, sending `y` to the glue point `x`. -/
def amalgEmbG (F G : FTS) (x : F.V) (y : G.V) : G.V ↪ (F.amalgamate G x y).V :=
  ⟨fun b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩, by
    intro a b hab
    simp only at hab
    by_cases ha : a = y <;> by_cases hb : b = y
    · rw [ha, hb]
    · rw [dif_pos ha, dif_neg hb] at hab; exact absurd hab Sum.inl_ne_inr
    · rw [dif_neg ha, dif_pos hb] at hab; exact absurd hab Sum.inr_ne_inl
    · rw [dif_neg ha, dif_neg hb] at hab; exact congrArg Subtype.val (Sum.inr_injective hab)⟩

/-
Every edge of the amalgam comes from `F` (via `inl`) or from `G` (via
`amalgEmbG`).
-/
theorem amalgamate_edge_cases {F G : FTS} {x : F.V} {y : G.V}
    {e : Finset (F.amalgamate G x y).V} (he : e ∈ (F.amalgamate G x y).edges) :
    (∃ d ∈ F.edges, e = d.map Function.Embedding.inl) ∨
    (∃ d ∈ G.edges, e = d.map (amalgEmbG F G x y)) := by
  simpa [FTS.amalgamate, amalgEmbG, eq_comm] using he

/-
An `F`-edge (an `inl`-image) and a `G`-edge (an `amalgEmbG`-image) meet only
in the glue point `Sum.inl x`.
-/
theorem amalgamate_cross_inter {F G : FTS} {x : F.V} {y : G.V}
    {dF : Finset F.V} {dG : Finset G.V} (hdG : dG ∈ G.edges)
    {w : (F.amalgamate G x y).V}
    (h1 : w ∈ dF.map Function.Embedding.inl) (h2 : w ∈ dG.map (amalgEmbG F G x y)) :
    w = Sum.inl x := by
  simp_all +decide [ Finset.ext_iff, Finset.mem_map ];
  obtain ⟨ a, ha, rfl ⟩ := h1; obtain ⟨ b, hb, hb' ⟩ := h2; simp_all +decide [ amalgEmbG ] ;
  split_ifs at hb' <;> tauto

/-
In a Berge cycle of the amalgam, all edges lie on the same side.
-/
theorem amalgamate_berge_side {F G : FTS} {x : F.V} {y : G.V}
    (c : BergeCycle (F.amalgamate G x y)) :
    (∀ i, ∃ d ∈ F.edges, (c.e i).1 = d.map Function.Embedding.inl) ∨
    (∀ i, ∃ d ∈ G.edges, (c.e i).1 = d.map (amalgEmbG F G x y)) := by
  -- By definition of $s$, we know that for any $i$, $s i$ is true if and only if there exists a $d \in F.edges$ such that $(c.e i).1 = d.map Function.Embedding.inl$.
  set s : ZMod c.m → Bool := fun i => ∃ d ∈ F.edges, (c.e i).1 = d.map Function.Embedding.inl;
  have h_change : ∀ i j, s i ≠ s (i + 1) → s j ≠ s (j + 1) → i = j := by
    intros i j hi hj
    have h_vertex : c.v (i + 1) = Sum.inl x ∧ c.v (j + 1) = Sum.inl x := by
      have h_vertex : ∀ i, s i ≠ s (i + 1) → c.v (i + 1) = Sum.inl x := by
        intros i hi; by_cases hi' : s i <;> simp_all +decide [ decide_eq_false ] ;
        · obtain ⟨ dF, hdF, hdF' ⟩ := (by
          grind +splitImp : ∃ dF ∈ F.edges, (c.e i).1 = dF.map Function.Embedding.inl)
          obtain ⟨ dG, hdG, hdG' ⟩ := (by
          have := amalgamate_edge_cases ( c.e ( i + 1 ) |>.2 ) ; aesop; : ∃ dG ∈ G.edges, (c.e (i + 1)).1 = dG.map (amalgEmbG F G x y));
          have := c.mem_right i; have := c.mem_left ( i + 1 ) ; simp_all +decide [ Finset.ext_iff ] ;
          have := amalgamate_cross_inter hdG ( by aesop ) ( by aesop ) ; aesop;
        · obtain ⟨ d₁, hd₁, hd₁' ⟩ := (by
          grind +suggestions : ∃ d ∈ G.edges, (c.e i).1 = d.map (amalgEmbG F G x y))
          obtain ⟨ d₂, hd₂, hd₂' ⟩ := (by
          grind +splitImp : ∃ d ∈ F.edges, (c.e (i + 1)).1 = d.map Function.Embedding.inl);
          have h_vertex : c.v (i + 1) ∈ (c.e i).1 ∧ c.v (i + 1) ∈ (c.e (i + 1)).1 := by
            exact ⟨ c.mem_right i, c.mem_left ( i + 1 ) ⟩;
          have := amalgamate_cross_inter hd₁ ( show c.v ( i + 1 ) ∈ d₂.map Function.Embedding.inl from by aesop ) ( show c.v ( i + 1 ) ∈ d₁.map ( amalgEmbG F G x y ) from by aesop ) ; aesop;
      exact ⟨ h_vertex i hi, h_vertex j hj ⟩;
    have := c.vinj ( show c.v ( i + 1 ) = c.v ( j + 1 ) from by aesop ) ; aesop;
  -- By `zmod_succ_eq_of_unique_change s hchange`, `∀ i, s i = s (i+1)`, and then `zmod_const_of_succ_eq s _` gives `s i = s 0` for all `i`.
  have h_const : ∀ i, s i = s 0 := by
    convert! zmod_const_of_succ_eq s ( zmod_succ_eq_of_unique_change s h_change ) using 1; all_goals exact ⟨ by linarith [ c.hm ] ⟩;
  by_cases h : s 0 <;> simp_all +decide [ decide_eq_true_iff ];
  · grind +qlia;
  · right;
    intro i; specialize h_const i; simp_all +decide [ s ] ;
    have := amalgamate_edge_cases ( c.e i |>.2 ) ; aesop;

/-- If all edges are `F`-edges, all point-nodes are `inl`-images. -/
theorem amalgamate_berge_vertsF {F G : FTS} {x : F.V} {y : G.V}
    (c : BergeCycle (F.amalgamate G x y))
    (he : ∀ i, ∃ d ∈ F.edges, (c.e i).1 = d.map Function.Embedding.inl) :
    ∀ i, ∃ a : F.V, c.v i = Sum.inl a := by
  intro i
  obtain ⟨d, _, hde⟩ := he i
  have hmem := c.mem_left i
  rw [hde, Finset.mem_map] at hmem
  obtain ⟨a, _, hEq⟩ := hmem
  exact ⟨a, hEq.symm⟩

/-- If all edges are `G`-edges, all point-nodes are `amalgEmbG`-images. -/
theorem amalgamate_berge_vertsG {F G : FTS} {x : F.V} {y : G.V}
    (c : BergeCycle (F.amalgamate G x y))
    (he : ∀ i, ∃ d ∈ G.edges, (c.e i).1 = d.map (amalgEmbG F G x y)) :
    ∀ i, ∃ b : G.V, c.v i = amalgEmbG F G x y b := by
  intro i
  obtain ⟨d, _, hde⟩ := he i
  have hmem := c.mem_left i
  rw [hde, Finset.mem_map] at hmem
  obtain ⟨b, _, hEq⟩ := hmem
  exact ⟨b, hEq.symm⟩

/-
The amalgam is linear if both factors are.
-/
theorem amalgamate_linear {F G : FTS} (x : F.V) (y : G.V) (hF : F.Linear) (hG : G.Linear) :
    (F.amalgamate G x y).Linear := by
  intro e₁ he₁ e₂ he₂ hne;
  apply Finset.card_le_one.mpr;
  intro a ha b hb; obtain ⟨ d₁, hd₁, rfl ⟩ | ⟨ d₁, hd₁, rfl ⟩ := amalgamate_edge_cases he₁ <;> obtain ⟨ d₂, hd₂, rfl ⟩ | ⟨ d₂, hd₂, rfl ⟩ := amalgamate_edge_cases he₂ <;> simp_all +decide [ Finset.ext_iff ] ;
  · have := hF d₁ hd₁ d₂ hd₂ ( by aesop ) ; simp_all +decide [ Finset.card_le_one ] ;
    grind +suggestions;
  · have := amalgamate_cross_inter hd₂ ( show a ∈ d₁.map Function.Embedding.inl from by aesop ) ( show a ∈ d₂.map ( amalgEmbG F G x y ) from by aesop ) ; have := amalgamate_cross_inter hd₂ ( show b ∈ d₁.map Function.Embedding.inl from by aesop ) ( show b ∈ d₂.map ( amalgEmbG F G x y ) from by aesop ) ; aesop;
  · have := amalgamate_cross_inter hd₁ ( show a ∈ d₂.map Function.Embedding.inl from by aesop ) ( show a ∈ d₁.map ( amalgEmbG F G x y ) from by aesop ) ; have := amalgamate_cross_inter hd₁ ( show b ∈ d₂.map Function.Embedding.inl from by aesop ) ( show b ∈ d₁.map ( amalgEmbG F G x y ) from by aesop ) ; aesop;
  · have := hG d₁ hd₁ d₂ hd₂; simp_all +decide [ Finset.card_le_one ] ;
    grind +suggestions

/-
The amalgam has only even Berge cycles if both factors do.
-/
theorem amalgamate_even {F G : FTS} (x : F.V) (y : G.V) (hF : ∀ c : BergeCycle F, Even c.m)
    (hG : ∀ c : BergeCycle G, Even c.m) (c : BergeCycle (F.amalgamate G x y)) : Even c.m := by
  cases' amalgamate_berge_side c with heF heG;
  · convert! hF ( BergeCycle.ofEmbedding ( Function.Embedding.inl : F.V ↪ ( F.amalgamate G x y ).V ) c ( amalgamate_berge_vertsF c heF ) heF ) using 1;
  · convert! hG ( BergeCycle.ofEmbedding ( amalgEmbG F G x y ) c ( amalgamate_berge_vertsG c heG ) heG ) using 1

/-
An `F`-edge and a `G`-edge of the amalgam are never the same set (a `G`-edge
contains at least two `Sum.inr` vertices, an `F`-edge none).
-/
theorem amalgamate_FG_ne {F G : FTS} {x : F.V} {y : G.V} {dF : Finset F.V} {dG : Finset G.V}
    (hdG : dG ∈ G.edges) :
    dF.map Function.Embedding.inl ≠ dG.map (amalgEmbG F G x y) := by
  by_contra h_eq;
  obtain ⟨ b, hb, hb' ⟩ := Finset.exists_mem_ne ( by linarith [ FTS.card3 G dG hdG ] : 1 < Finset.card dG ) y ; have := Finset.mem_map.mp ( h_eq.symm ▸ Finset.mem_map.mpr ⟨ b, hb, rfl ⟩ ) ; simp_all +decide [ Finset.mem_map ] ;
  obtain ⟨ a, ha, ha' ⟩ := this; simp_all +decide [ amalgEmbG ] ;
  cases ha'

/-
The amalgam: every hyperedge-node is incident with a bridge.
-/
theorem amalgamate_bridge {F G : FTS} (x : F.V) (y : G.V) (hF : F.IntrinsicObligatory)
    (hG : G.IntrinsicObligatory)
    (ed : {e : Finset (F.amalgamate G x y).V // e ∈ (F.amalgamate G x y).edges}) :
    ∃ w ∈ ed.1, IsBridgeInc (F.amalgamate G x y) w ed := by
  rcases amalgamate_edge_cases ed.2 with ( ⟨ d, hd, hde ⟩ | ⟨ d, hd, hde ⟩ ) <;> simp_all +decide [ IsBridgeInc ];
  · obtain ⟨ w, hw₁, hw₂ ⟩ := hF.2.1 ⟨ d, hd ⟩;
    refine' ⟨ w, hw₁, _ ⟩;
    rintro ⟨ c, i, hi, hi' ⟩;
    cases' amalgamate_berge_side c with heF heG;
    · refine' hw₂.2 ⟨ BergeCycle.ofEmbedding ( Function.Embedding.inl : F.V ↪ ( F.amalgamate G x y ).V ) c ( amalgamate_berge_vertsF c heF ) heF, i, _, _ ⟩ <;> simp_all +decide [ BergeCycle.ofEmbedding ];
      · grind;
      · have hvi := (amalgamate_berge_vertsF c heF i).choose_spec
        have hvj := (amalgamate_berge_vertsF c heF (i + 1)).choose_spec
        exact hi'.imp (fun h => Sum.inl_injective (hvi.symm.trans h))
          (fun h => Sum.inl_injective (hvj.symm.trans h))
    · obtain ⟨ d', hd', hde' ⟩ := heG i; simp_all +decide [ Finset.ext_iff ] ;
      have := amalgamate_FG_ne hd' ( show d.map Function.Embedding.inl = d'.map ( amalgEmbG F G x y ) from ?_ ) ; aesop;
      ext; simp [hde'];
      convert! hde' _ using 1;
  · obtain ⟨ w, hw₁, hw₂ ⟩ := hG.2.1 ⟨ d, hd ⟩;
    refine' ⟨ w, hw₁, _ ⟩ ; contrapose! hw₂ ; simp_all +decide [ IsBridgeInc, OnBergeCycle ] ;
    obtain ⟨ c, i, hi, hi' ⟩ := hw₂; cases' amalgamate_berge_side c with heF heG;
    · obtain ⟨ dF, hdF, hdF' ⟩ := heF i; have := Finset.mem_map.mp ( hdF' ▸ hi.symm ▸ hde.symm ▸ Finset.mem_map.mpr ⟨ w, hw₁, rfl ⟩ ) ; simp_all +decide [ Finset.mem_map ] ;
      grind +suggestions;
    · refine' ⟨ BergeCycle.ofEmbedding ( amalgEmbG F G x y ) c ( amalgamate_berge_vertsG c heG ) heG, i, _, _ ⟩ <;> simp_all +decide [ BergeCycle.ofEmbedding ];
      · grind +revert;
      · have hvi := (amalgamate_berge_vertsG c heG i).choose_spec
        have hvj := (amalgamate_berge_vertsG c heG (i + 1)).choose_spec
        have hinj := (amalgEmbG F G x y).injective
        grind only [Function.Injective]

/-- One-point amalgamation preserves the intrinsic condition. -/
theorem amalgamate_intrinsic {F G : FTS} (x : F.V) (y : G.V)
    (hF : F.IntrinsicObligatory) (hG : G.IntrinsicObligatory) :
    (F.amalgamate G x y).IntrinsicObligatory :=
  ⟨amalgamate_linear x y hF.1 hG.1, amalgamate_bridge x y hF hG,
    amalgamate_even x y hF.2.2 hG.2.2⟩

/-- **Forward direction of `prop:finite-decomposition`**: every member of the
class `B` satisfies the intrinsic condition. -/
theorem bclass_intrinsic {F : FTS} (h : Bclass F) : F.IntrinsicObligatory := by
  induction h with
  | edgeless F hF => exact edgeless_intrinsic F hF
  | expansion J hJ => exact expansion_intrinsic J hJ
  | iso hiso _ ih => exact intrinsic_iso hiso ih
  | union _ _ ihF ihG => exact disjUnion_intrinsic ihF ihG
  | amalg x y _ _ ihF ihG => exact amalgamate_intrinsic x y ihF ihG

end Erdos1177

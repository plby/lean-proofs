import Mathlib
import ErdosProblems.Erdos550.ProfileLemma

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Forest data from a tree centroid, and the profile lemma

This file constructs the `parent`/`rank`/`home`/`rootOf` data required by
`tree_embed_from_allocation`, directly from a tree `T` and a centroid `z`, and
then assembles the **profile lemma** of *A Resolution of Erdős Problem 550*
(E. Li) by feeding the `count_and_load` allocation into the abstract embedding.

* `parentT G z v` — the unique neighbour of `v` strictly closer to `z` (the
  forest parent of `v` in `T − z`), or `none` if `v` is `z` or a neighbour of
  `z` (a root).
* `rankT G z v = dist z v` — the acyclicity certificate.
* `rootOf G z v` — the neighbour of `z` whose branch contains `v` (the root of
  `v`'s component of `T − z`).
-/

open SimpleGraph Finset

namespace Erdos550

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The forest parent of `v` (towards `z`): a neighbour `u ≠ z` of `v` strictly
closer to `z`.  Roots (neighbours of `z`) and `z` itself get `none`. -/
noncomputable def parentT (G : SimpleGraph V) (z v : V) : Option V :=
  if h : ∃ u, u ≠ z ∧ G.Adj v u ∧ G.dist z u < G.dist z v then some (Classical.choose h) else none

/-- Acyclicity certificate: distance to `z`. -/
noncomputable def rankT (G : SimpleGraph V) (z v : V) : ℕ := G.dist z v

open Classical in
/-- The root of `v`'s branch: the neighbour of `z` whose branch contains `v`. -/
noncomputable def rootOf (G : SimpleGraph V) (z v : V) : V :=
  if h : ∃ w, G.Adj z w ∧ v ∈ branch G z w then Classical.choose h else z

variable {G : SimpleGraph V} {z : V}

/-! ## Structural lemmas for `parentT`/`rankT`. -/

theorem parentT_ne (v u : V) (h : parentT G z v = some u) : u ≠ z := by
  unfold parentT at h; split_ifs at h ; simp_all +decide only [ne_eq] ;
  exact h ▸ Classical.choose_spec ‹∃ u, u ≠ z ∧ G.Adj v u ∧ G.dist z u < G.dist z v› |>.1

theorem parentT_adj (v u : V) (h : parentT G z v = some u) : G.Adj v u := by
  have := Classical.choose_spec ( show ∃ u, u ≠ z ∧ G.Adj v u ∧ G.dist z u < G.dist z v from by
                                    unfold parentT at h; aesop; )
  generalize_proofs at *;
  unfold parentT at h; aesop;

theorem parentT_rank (v u : V) (h : parentT G z v = some u) :
    rankT G z u < rankT G z v := by
  unfold parentT at h;
  split_ifs at h ; simp_all +decide [ rankT ];
  exact h ▸ Classical.choose_spec ‹∃ u, u ≠ z ∧ G.Adj v u ∧ G.dist z u < G.dist z v› |>.2.2

theorem parentT_root_adj (hG : G.IsTree) (v : V) (hv : v ≠ z)
    (h : parentT G z v = none) : G.Adj z v := by
  obtain ⟨u, huv, hdu⟩ : ∃ u, G.Adj v u ∧ G.dist z u < G.dist z v := by
    obtain ⟨p, hp⟩ := hG.1.exists_walk_length_eq_dist v z
    cases p with
    | nil => exact absurd rfl hv
    | @cons _ u _ hvu q =>
      refine ⟨u, hvu, ?_⟩
      have hle : G.dist u z ≤ q.length := SimpleGraph.dist_le q
      have hge : q.length + 1 = G.dist v z := by rw [← hp, SimpleGraph.Walk.length_cons]
      have e1 : G.dist z u = G.dist u z := SimpleGraph.dist_comm
      have e2 : G.dist z v = G.dist v z := SimpleGraph.dist_comm
      omega
  by_cases hu' : u = z
  · subst hu'; exact huv.symm
  · exfalso
    have hex : ∃ u, u ≠ z ∧ G.Adj v u ∧ G.dist z u < G.dist z v := ⟨u, hu', huv, hdu⟩
    have hsome : parentT G z v = some (Classical.choose hex) := by
      unfold parentT; rw [dif_pos hex]
    rw [h] at hsome; exact absurd hsome.symm (Option.some_ne_none _)

theorem parentT_nbr_none (w : V) (h : G.Adj z w) : parentT G z w = none := by
  unfold parentT; simp +decide only [ne_eq, dite_eq_right_iff, reduceCtorEq, imp_false, not_exists, not_and, not_lt] ;
  intro x hx hx';
  exact ⟨ Ne.symm hx, SimpleGraph.Adj.reachable h |> SimpleGraph.Reachable.trans <| SimpleGraph.Adj.reachable hx' ⟩

/- In a tree, the toward-`z` neighbour `a` of `v` is unique. -/
omit [Fintype V] [DecidableEq V] in
theorem pred_unique (hG : G.IsTree) (v a b : V) (ha : G.Adj v a) (hb : G.Adj v b)
    (hda : G.dist z a + 1 = G.dist z v) (hdb : G.dist z b + 1 = G.dist z v) : a = b := by
  obtain ⟨pa, hpa⟩ := hG.1.exists_walk_length_eq_dist a z
  obtain ⟨pb, hpb⟩ := hG.1.exists_walk_length_eq_dist b z
  have ea : G.dist a z = G.dist z a := SimpleGraph.dist_comm
  have eb : G.dist b z = G.dist z b := SimpleGraph.dist_comm
  have evz : G.dist v z = G.dist z v := SimpleGraph.dist_comm
  have la : (SimpleGraph.Walk.cons ha pa).length = G.dist v z := by
    rw [SimpleGraph.Walk.length_cons, hpa]; omega
  have lb : (SimpleGraph.Walk.cons hb pb).length = G.dist v z := by
    rw [SimpleGraph.Walk.length_cons, hpb]; omega
  have heq : SimpleGraph.Walk.cons ha pa = SimpleGraph.Walk.cons hb pb :=
    (hG.existsUnique_path v z).unique
      (SimpleGraph.Walk.isPath_of_length_eq_dist _ la)
      (SimpleGraph.Walk.isPath_of_length_eq_dist _ lb)
  have := congrArg (fun p => p.getVert 1) heq
  simpa [SimpleGraph.Walk.getVert_cons_succ] using! this

/-- In a tree, the toward-`z` neighbour of a non-root vertex is unique, so an
adjacent pair off `z` is a parent edge in one direction. -/
theorem parentT_edge (hG : G.IsTree) (u v : V) (huv : G.Adj u v)
    (hu : u ≠ z) (hv : v ≠ z) :
    parentT G z u = some v ∨ parentT G z v = some u := by
  rcases hG.dist_eq_dist_add_one_of_adj z huv with hd | hd
  · left
    have hex : ∃ w, w ≠ z ∧ G.Adj u w ∧ G.dist z w < G.dist z u := ⟨v, hv, huv, by omega⟩
    have hsome : parentT G z u = some (Classical.choose hex) := by unfold parentT; rw [dif_pos hex]
    rw [hsome, Option.some.injEq]
    obtain ⟨hwz, hadjw, hdw⟩ := Classical.choose_spec hex
    have hdwu : G.dist z (Classical.choose hex) + 1 = G.dist z u := by
      rcases hG.dist_eq_dist_add_one_of_adj z hadjw with h | h <;> omega
    exact pred_unique hG u (Classical.choose hex) v hadjw huv hdwu (by omega)
  · right
    have hex : ∃ w, w ≠ z ∧ G.Adj v w ∧ G.dist z w < G.dist z v := ⟨u, hu, huv.symm, by omega⟩
    have hsome : parentT G z v = some (Classical.choose hex) := by unfold parentT; rw [dif_pos hex]
    rw [hsome, Option.some.injEq]
    obtain ⟨hwz, hadjw, hdw⟩ := Classical.choose_spec hex
    have hdwv : G.dist z (Classical.choose hex) + 1 = G.dist z v := by
      rcases hG.dist_eq_dist_add_one_of_adj z hadjw with h | h <;> omega
    exact pred_unique hG v (Classical.choose hex) u hadjw huv.symm hdwv (by omega)

/-! ## Branch root lemmas. -/

omit [DecidableEq V] in
theorem exists_unique_root (hG : G.IsTree) (v : V) (hv : v ≠ z) :
    ∃! w, G.Adj z w ∧ v ∈ branch G z w := by
  have mem_iff : ∀ w, v ∈ branch G z w ↔ G.dist v w < G.dist v z := by
    intro w; simp [branch]
  obtain ⟨w0, hadj0, hdist0⟩ : ∃ w, G.Adj z w ∧ G.dist z v = G.dist w v + 1 := by
    obtain ⟨p, hp⟩ := hG.1.exists_walk_length_eq_dist z v
    cases p with
    | nil => exact absurd rfl hv.symm
    | @cons _ b _ hzb q =>
      refine ⟨b, hzb, ?_⟩
      have htri : G.dist z v ≤ G.dist z b + G.dist b v := (hzb.reachable).dist_triangle_left v
      have h1 : G.dist z b = 1 := by rw [SimpleGraph.dist_eq_one_iff_adj]; exact hzb
      have hle : G.dist b v ≤ q.length := SimpleGraph.dist_le q
      have hge : q.length + 1 = G.dist z v := by rw [← hp, SimpleGraph.Walk.length_cons]
      omega
  have hmem0 : v ∈ branch G z w0 := by
    rw [mem_iff]
    have e1 : G.dist v w0 = G.dist w0 v := SimpleGraph.dist_comm
    have e2 : G.dist v z = G.dist z v := SimpleGraph.dist_comm
    omega
  refine ⟨w0, ⟨hadj0, hmem0⟩, ?_⟩
  rintro w' ⟨hadj', hmem'⟩
  rw [mem_iff] at hmem'
  have hsum' : G.dist z v = G.dist w' v + 1 := by
    have htri : G.dist z v ≤ G.dist z w' + G.dist w' v := hadj'.reachable.dist_triangle_left v
    have h1 : G.dist z w' = 1 := by rw [SimpleGraph.dist_eq_one_iff_adj]; exact hadj'
    have e1 : G.dist v w' = G.dist w' v := SimpleGraph.dist_comm
    have e2 : G.dist v z = G.dist z v := SimpleGraph.dist_comm
    omega
  obtain ⟨q', hq'⟩ := hG.1.exists_walk_length_eq_dist w' v
  obtain ⟨q0, hq0⟩ := hG.1.exists_walk_length_eq_dist w0 v
  have lenP' : (SimpleGraph.Walk.cons hadj' q').length = G.dist z v := by
    rw [SimpleGraph.Walk.length_cons, hq']; omega
  have lenP0 : (SimpleGraph.Walk.cons hadj0 q0).length = G.dist z v := by
    rw [SimpleGraph.Walk.length_cons, hq0]; omega
  have heq : SimpleGraph.Walk.cons hadj' q' = SimpleGraph.Walk.cons hadj0 q0 :=
    (hG.existsUnique_path z v).unique
      (SimpleGraph.Walk.isPath_of_length_eq_dist _ lenP')
      (SimpleGraph.Walk.isPath_of_length_eq_dist _ lenP0)
  have := congrArg (fun p => p.getVert 1) heq
  simpa [SimpleGraph.Walk.getVert_cons_succ] using! this

/-
For a neighbour `w` of `z`, the branch of `w` consists exactly of the vertices
`v` lying one step further from `z` through `w`.
-/
omit [DecidableEq V] in
theorem mem_branch_iff_dist {w : V} (hw : G.Adj z w) (v : V) :
    v ∈ branch G z w ↔ G.dist z v = G.dist w v + 1 := by
  constructor;
  · intro hv
    have h_dist : G.dist z v ≤ G.dist w v + 1 := by
      have := hw.reachable.dist_triangle_left v;
      rw [ SimpleGraph.dist_eq_one_iff_adj.mpr hw ] at this ; linarith;
    have h_dist' : G.dist v w < G.dist v z := by
      exact Finset.mem_filter.mp hv |>.2;
    simp_all +decide [ SimpleGraph.dist_comm ];
    linarith;
  · intro h
    simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and];
    simp_all +decide [ SimpleGraph.dist_comm ]

theorem rootOf_spec (hG : G.IsTree) (v : V) (hv : v ≠ z) :
    G.Adj z (rootOf G z v) ∧ v ∈ branch G z (rootOf G z v) := by
  obtain ⟨w, hw⟩ := (Erdos550.exists_unique_root hG v hv).exists;
  convert! Classical.choose_spec ( Erdos550.exists_unique_root hG v hv |> ExistsUnique.exists ); all_goals unfold rootOf; aesop;

theorem rootOf_unique (hG : G.IsTree) (v : V) (hv : v ≠ z)
    {w : V} (hw : G.Adj z w) (hvw : v ∈ branch G z w) : w = rootOf G z v := by
  -- Apply the uniqueness part of `exists_unique_root` to conclude that $w = rootOf G z v$.
  apply (exists_unique_root hG v hv).unique ⟨hw, hvw⟩ (rootOf_spec hG v hv)

theorem rootOf_root (hG : G.IsTree) {w : V} (hw : G.Adj z w) :
    rootOf G z w = w := by
  exact Eq.symm ( rootOf_unique hG w ( by aesop ) hw ( by
    convert! mem_branch_iff_dist hw w |>.2 _;
    rw [ SimpleGraph.dist_self, zero_add, SimpleGraph.dist_eq_one_iff_adj.mpr hw ] ) )

/-- Moving towards `z` keeps the root unchanged. -/
theorem rootOf_toward (hG : G.IsTree) (v u : V) (hv : v ≠ z) (hu : u ≠ z)
    (huv : G.Adj v u) (hlt : G.dist z u < G.dist z v) :
    rootOf G z u = rootOf G z v := by
  obtain ⟨hadj', hmem'⟩ := rootOf_spec hG u hu
  have hub : G.dist u (rootOf G z u) < G.dist u z := by simpa [branch] using! hmem'
  have e1 : G.dist u (rootOf G z u) = G.dist (rootOf G z u) u := SimpleGraph.dist_comm
  have e2 : G.dist u z = G.dist z u := SimpleGraph.dist_comm
  have huv1 : G.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv.symm
  have htri : G.dist (rootOf G z u) v ≤ G.dist (rootOf G z u) u + G.dist u v :=
    (hG.1 (rootOf G z u) u).dist_triangle_left v
  have hmemv : v ∈ branch G z (rootOf G z u) := by
    simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]
    have f1 : G.dist v (rootOf G z u) = G.dist (rootOf G z u) v := SimpleGraph.dist_comm
    have f2 : G.dist v z = G.dist z v := SimpleGraph.dist_comm
    omega
  exact rootOf_unique hG v hv hadj' hmemv

/-! ## Counting identities relating `home = col ∘ rootOf` to branches. -/

/-
For `i`, the neighbours of `z` whose root-colour is `i` are exactly the
neighbours coloured `i` (since `rootOf` fixes neighbours of `z`).
-/
theorem card_root_eq [DecidableRel G.Adj] (hG : G.IsTree) (q : ℕ) (col : V → Fin q) (i : Fin q) :
    Fintype.card {w : V // G.Adj z w ∧ col (rootOf G z w) = i}
      = Fintype.card {w : V // G.Adj z w ∧ col w = i} := by
  have h_root_eq : ∀ w : V, G.Adj z w → rootOf G z w = w := fun _ hw => rootOf_root hG hw
  exact Fintype.card_congr ( Equiv.subtypeEquivRight fun w => by aesop )

/-
The non-`z` vertices coloured `i` (via their root) split into the branches
of the neighbours coloured `i`.
-/
theorem card_branch_eq [DecidableRel G.Adj] (hG : G.IsTree) (q : ℕ)
    (col : V → Fin q) (i : Fin q) :
    Fintype.card {v : V // v ≠ z ∧ col (rootOf G z v) = i}
      = ∑ w ∈ (G.neighborFinset z).filter (fun w => col w = i), branchSize G z w := by
  rw [ Fintype.card_subtype ];
  convert! Finset.card_biUnion _;
  all_goals try infer_instance;
  · ext v; simp [branch];
    grind +suggestions;
  · intro w hw w' hw' hww'; simp_all +decide [ Finset.disjoint_left ] ;
    intro v hv hv';
    have := rootOf_unique hG v (by
    intro h; simp_all +decide [ branch ] ;) hw.1 hv
    have := rootOf_unique hG v (by
    rintro rfl; simp_all +decide [ branch ]) hw'.1 hv'
    aesop

/-
Every branch of a neighbour of `z` is nonempty (it contains that neighbour).
-/
omit [DecidableEq V] in
theorem branchSize_pos {w : V} (hw : G.Adj z w) :
    0 < branchSize G z w := by
  refine' Finset.card_pos.mpr ⟨ w, _ ⟩;
  simp +decide [ branch ];
  rw [ SimpleGraph.dist_comm, SimpleGraph.dist_eq_one_iff_adj.mpr hw ] ; norm_num

/-! ## Count-and-load over an arbitrary finite index type. -/

/-
`count_and_load` transported to an arbitrary finite index type `ι`.
-/
theorem count_and_load' (q : ℕ) (hq : 2 ≤ q) (ω : ℝ) (hω : 0 < ω) :
    ∃ κ δ0 : ℝ, 0 < κ ∧ 0 < δ0 ∧
      ∀ {ι : Type} [Fintype ι] (n : ℕ) (s : ι → ℕ) (c : Fin q → ℕ),
        (∀ j, 0 < s j) → (∀ j, 2 * s j ≤ n) → (∑ j, s j = n - 1) →
        (∀ i, (c i : ℝ) ≤ (1 + δ0) * n) → ((1 + ω) * (n : ℝ) ≤ ∑ i, (c i : ℝ)) →
        ∃ I : ι → Fin q,
          (∀ i, #{j | I j = i} ≤ c i) ∧
          (∀ i, (∑ j ∈ {j | I j = i}, (s j : ℝ)) ≤ (1 - κ) * n) := by
  by_contra h_contra;
  obtain ⟨κ, δ0, hκ, hδ0, hCL⟩ : ∃ κ δ0 : ℝ, 0 < κ ∧ 0 < δ0 ∧ ∀ {ι : Type} [Fintype ι] (n : ℕ) (s : Fin (Fintype.card ι) → ℕ) (c : Fin q → ℕ),
    (∀ j, 0 < s j) → (∀ j, 2 * s j ≤ n) → (∑ j, s j = n - 1) → (∀ i, (c i : ℝ) ≤ (1 + δ0) * n) → ((1 + ω) * n ≤ ∑ i, (c i : ℝ)) →
    ∃ I : Fin (Fintype.card ι) → Fin q,
      (∀ i, #{j | I j = i} ≤ c i) ∧ (∀ i, (∑ j ∈ {j | I j = i}, (s j : ℝ)) ≤ (1 - κ) * n) := by
        have := @Erdos550.count_and_load q hq ω hω;
        exact ⟨ this.choose, this.choose_spec.choose, this.choose_spec.choose_spec.1, this.choose_spec.choose_spec.2.1, fun { ι } _ n s c hs hs' hs'' hs''' hs'''' => this.choose_spec.choose_spec.2.2 n ( Fintype.card ι ) s c hs hs' hs'' hs''' hs'''' ⟩;
  refine' h_contra ⟨ κ, δ0, hκ, hδ0, fun { ι } [ Fintype ι ] n s c hs hs' hs'' hc hc' => _ ⟩;
  obtain ⟨I', hI'⟩ := hCL n (fun j => s (Fintype.equivFin ι |>.symm j)) c (fun j => hs (Fintype.equivFin ι |>.symm j)) (fun j => hs' (Fintype.equivFin ι |>.symm j)) (by
  convert! hs'' using 1;
  exact Equiv.sum_comp ( Fintype.equivFin ι |> Equiv.symm ) s) hc hc';
  use fun j => I' (Fintype.equivFin ι j);
  refine' ⟨ fun i => _, fun i => _ ⟩;
  · convert! hI'.1 i using 1;
    rw [ Finset.card_filter, Finset.card_filter ];
    conv_rhs => rw [ ← Equiv.sum_comp ( Fintype.equivFin ι ) ] ;
  · convert! hI'.2 i using 1;
    refine' Finset.sum_bij ( fun j hj => Fintype.equivFin ι j ) _ _ _ _ <;> simp +decide only [mem_filter, mem_univ, true_and, exists_prop];
    exact fun j hj => ⟨ ( Fintype.equivFin ι ).symm j, by simpa using! hj, by simp +decide ⟩

/-! ## The profile lemma. -/

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Profile lemma** (Lemma `lem:profile` of the paper).

For `q ≥ 2` and `ω > 0` there are constants `κ, δ0 > 0` such that: if a blue graph
`Gb` has pairwise-disjoint reservoirs `W₁,…,W_q`, a vertex `x ∉ ⋃ Wᵢ` with blue
neighbourhoods of controlled size (`≤ (1+δ0)n` in each `Wᵢ`) and total demand
`∑ᵢ d_b(x,Wᵢ) ≥ (1+ω)n`, and each `Gb[Wᵢ]` has internal minimum degree
`≥ (1-κ)n`, then `Gb` contains every `n`-vertex tree `T` (with `n ≥ 2`). -/
theorem profile_lemma (q : ℕ) (hq : 2 ≤ q) (ω : ℝ) (hω : 0 < ω) :
    ∃ κ δ0 : ℝ, 0 < κ ∧ 0 < δ0 ∧
      ∀ {VT : Type} [Fintype VT] [DecidableEq VT]
        {Vb : Type} [Fintype Vb] [DecidableEq Vb]
        (T : SimpleGraph VT) [DecidableRel T.Adj]
        (Gb : SimpleGraph Vb) [DecidableRel Gb.Adj]
        (x : Vb) (W : Fin q → Finset Vb),
        T.IsTree → 2 ≤ Fintype.card VT →
        (∀ i, x ∉ W i) → (∀ i j, i ≠ j → Disjoint (W i) (W j)) →
        (∀ i, (((Gb.neighborFinset x) ∩ W i).card : ℝ) ≤ (1 + δ0) * Fintype.card VT) →
        ((1 + ω) * (Fintype.card VT : ℝ)
          ≤ ∑ i, (((Gb.neighborFinset x) ∩ W i).card : ℝ)) →
        (∀ i, ∀ v ∈ W i,
          (1 - κ) * (Fintype.card VT : ℝ) ≤ (((Gb.neighborFinset v) ∩ W i).card : ℝ)) →
        T ⊑ Gb := by
  obtain ⟨κ, δ0, hκ, hδ0, hCL⟩ := count_and_load' q hq ω hω;
  refine' ⟨ κ, δ0, hκ, hδ0, fun { VT } _ _ { Vb } _ _ T _ Gb _ x W hT hn hxW hWdisj hcap hdem hmindeg => _ ⟩;
  obtain ⟨z, hz⟩ : ∃ z : VT, ∀ w : VT, T.Adj z w → 2 * branchSize T z w ≤ Fintype.card VT := by
    have : Nonempty VT := Fintype.card_pos_iff.mp ( by linarith ) ; exact Erdos550.tree_centroid hT;
  obtain ⟨I, hI1, hI2⟩ : ∃ I : {w : VT // T.Adj z w} → Fin q, (∀ i, #{j | I j = i} ≤ ((Gb.neighborFinset x) ∩ W i).card) ∧ (∀ i, (∑ j ∈ {j | I j = i}, (branchSize T z j.1 : ℝ)) ≤ (1 - κ) * Fintype.card VT) := by
    apply hCL;
    · exact fun j => branchSize_pos j.2;
    · exact fun j => hz _ j.2;
    · convert! branchSize_sum_neighbors hT z using 1;
      refine' Finset.sum_bij ( fun w hw => w ) _ _ _ _ <;> simp +decide;
    · exact hcap;
    · convert! hdem using 1;
  -- Define the coloring function `col` and the home function `home`.
  set col : VT → Fin q := fun w => if h : T.Adj z w then I ⟨w, h⟩ else ⟨0, by linarith⟩
  set home : VT → Fin q := fun v => col (rootOf T z v);
  apply tree_embed_from_allocation T Gb q z x W home (parentT T z) (rankT T z) hxW hWdisj (parentT_ne) (parentT_rank) (parentT_root_adj hT) (parentT_nbr_none) (fun v u h => by
    have h_root_eq : rootOf T z u = rootOf T z v := by
      apply rootOf_toward hT v u;
      · rintro rfl; simp +decide [ parentT ] at h;
      · exact parentT_ne v u h;
      · exact parentT_adj v u h;
      · exact parentT_rank v u h
    simp [home, h_root_eq]) (fun u v huv hu hv => by
    exact parentT_edge hT u v huv hu hv) (fun i => by
    convert! hI1 i using 1;
    convert! card_root_eq hT q col i using 1;
    rw [ Fintype.subtype_card ];
    refine' Finset.card_bij ( fun j hj => j ) _ _ _ <;> simp +decide only [mem_filter, mem_univ, true_and, Subtype.forall, exists_prop, Subtype.exists,
    exists_and_right, exists_eq_right, and_imp];
    · exact fun a ha hi => ⟨ ha, by simpa [ ha ] using! hi ⟩;
    · exact fun w hw hi => ⟨ hw, by simpa [ hw ] using! hi ⟩) (fun i => by
    have h_card_branch : Fintype.card {v : VT // v ≠ z ∧ home v = i} = ∑ w ∈ (T.neighborFinset z).filter (fun w => col w = i), branchSize T z w := by
      convert! card_branch_eq hT q col i using 1;
    by_cases hi : W i = ∅;
    · specialize hI1 i; simp_all +decide [ Finset.ext_iff ] ;
      simp_all +decide [ show W i = ∅ from Finset.eq_empty_of_forall_notMem hi ];
      grind;
    · obtain ⟨ v, hv ⟩ := Finset.nonempty_of_ne_empty hi;
      have h_card_branch_le : (∑ w ∈ (T.neighborFinset z).filter (fun w => col w = i), branchSize T z w : ℝ) ≤ (1 - κ) * Fintype.card VT := by
        convert! hI2 i using 1;
        refine' Finset.sum_bij ( fun w hw => ⟨ w, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ col ]; all_goals grind;
      have h_card_branch_le : (∑ w ∈ (T.neighborFinset z).filter (fun w => col w = i), branchSize T z w : ℝ) ≤ ((Gb.neighborFinset v ∩ W i).card : ℝ) := by
        exact le_trans h_card_branch_le ( hmindeg i v hv );
      norm_cast at *;
      exact h_card_branch.symm ▸ h_card_branch_le.trans ( Finset.card_mono <| Finset.inter_subset_right )) (fun i v hv => by
    have h_card : Fintype.card {w : VT // w ≠ z ∧ home w = i} = ∑ w ∈ (T.neighborFinset z).filter (fun w => col w = i), branchSize T z w := by
      convert! card_branch_eq hT q col i using 1;
    have h_card_le : (∑ w ∈ (T.neighborFinset z).filter (fun w => col w = i), branchSize T z w : ℝ) ≤ (1 - κ) * Fintype.card VT := by
      convert! hI2 i using 1;
      refine' Finset.sum_bij ( fun w hw => ⟨ w, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ col ]; all_goals grind;
    exact Nat.sub_le_of_le_add <| by rw [ ← @Nat.cast_le ℝ ] ; push_cast [ h_card ] ; linarith [ hmindeg i v hv ] ;)

end Erdos550

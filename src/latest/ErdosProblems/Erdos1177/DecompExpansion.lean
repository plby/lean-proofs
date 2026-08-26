-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.DecompDichotomy

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The reconstruction step (§5): amalgamation and expansion cases

`decomp_step` (in `DecompReverse`) needs, for a `ReconOK` system with at least one
edge, to either split it at a one-point separation or recognise it as a bipartite
expansion.  This file provides the two geometric halves:

* `decomp_amalg` — if some edge has a bridge incidence at a vertex `w` that lies
  on another edge too, then cutting the edges into "reachable from `ed` avoiding
  `w`" and its complement is a one-point separation at `w`, exhibiting `F` as a
  one-point amalgamation of two strictly smaller `ReconOK` systems.  The
  separation property uses `bridge_ereach_false`.
* `exists_expansion_of_private` — if every edge has a private vertex, `F` is a
  bipartite expansion.
-/

open Cardinal

namespace Erdos1177

open Classical

universe u

set_option maxHeartbeats 2000000

variable {F : FTS}

/-
Split a walk at index `k`: `w = (prefix of length k) ++ (rest)`.
-/
theorem walk_split_at {V : Type*} {G : SimpleGraph V} {u v : V} (w : G.Walk u v)
    (k : ℕ) (hk : k ≤ w.length) :
    ∃ (w1 : G.Walk u (w.getVert k)) (w2 : G.Walk (w.getVert k) v),
      w = w1.append w2 ∧ w1.length = k := by
  exact ⟨w.take k, w.drop k, (w.append_take_drop_eq k).symm,
    by simpa only [SimpleGraph.Walk.take_length, Nat.min_eq_left hk]⟩

/-
A non-cycle closed walk of length `≥ 3` has a repeated vertex at two indices
`i < j < length`.
-/
theorem walk_vertex_repeat {V : Type*} {G : SimpleGraph V} {v : V} (w : G.Walk v v)
    (hcyc : ¬ w.IsCycle) (hlen : 3 ≤ w.length) :
    ∃ i j, i < j ∧ j < w.length ∧ w.getVert i = w.getVert j := by
  have h_not_path : ¬ w.tail.IsPath := by
    grind +suggestions;
  -- Since `w.tail` is not a path, there exist indices `a` and `b` such that `1 ≤ a < b ≤ w.length` and `w.getVert a = w.getVert b`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ b ≤ w.length ∧ w.getVert a = w.getVert b := by
    contrapose! h_not_path;
    have h_tail_nodup : List.Nodup (List.tail (w.support)) := by
      rw [ List.nodup_iff_getElem?_ne_getElem? ];
      grind +suggestions;
    convert! h_tail_nodup using 1;
    simp +decide [ SimpleGraph.Walk.isPath_def ];
    cases w <;> simp +decide [ SimpleGraph.Walk.support ];
  by_cases hb : b = w.length;
  · aesop;
  · exact ⟨ a, b, hab.2.1, lt_of_le_of_ne hab.2.2.1 hb, hab.2.2.2 ⟩

/-
**Odd closed walks contain odd cycles.**  From a closed walk of odd length
one can extract a cycle of odd length.
-/
theorem exists_odd_cycle_aux {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    ∀ (v : V) (w : G.Walk v v), w.length = n → Odd n →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ Odd c.length := by
  intro v w hw hn_odd
  induction' n using Nat.strong_induction_on with n ih generalizing v w;
  by_cases hw_cycle : w.IsCycle;
  · exact ⟨ v, w, hw_cycle, hw ▸ hn_odd ⟩;
  · -- Apply `walk_vertex_repeat` to find indices `i` and `j` such that `i < j < n` and `w.getVert i = w.getVert j =: x`.
    obtain ⟨i, j, hij, hjn, hx⟩ : ∃ i j, i < j ∧ j < n ∧ w.getVert i = w.getVert j := by
      convert! walk_vertex_repeat w hw_cycle _;
      · exact hw.symm;
      · rcases w with ( _ | ⟨ _, _, w ⟩ ) <;> simp_all +decide;
        · grind +extAll;
        · exact absurd ‹G.Adj v v› ( by simp +decide );
        · rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide;
    -- Split `w` into three parts: `w1`, `c₁`, and `w3`.
    obtain ⟨w1, w2, hw1, hw2⟩ : ∃ w1 : G.Walk v (w.getVert i), ∃ w2 : G.Walk (w.getVert i) v, w = w1.append w2 ∧ w1.length = i := by
      exact walk_split_at w i ( by linarith )
    obtain ⟨c₁, w3, hc₁, hw3⟩ : ∃ c₁ : G.Walk (w.getVert i) (w.getVert i), ∃ w3 : G.Walk (w.getVert i) v, w2 = c₁.append w3 ∧ c₁.length = j - i := by
      have := walk_split_at w2 ( j - i ) ( by
        have := congr_arg SimpleGraph.Walk.length hw1; norm_num at this; omega; );
      grind +suggestions;
    -- Consider the two closed walks `c₁` and `c₂ = w3.append w1`.
    set c₂ : G.Walk (w.getVert i) (w.getVert i) := w3.append w1
    have hc₂ : c₂.length = n - (j - i) := by
      simp +zetaDelta at *;
      simp_all +decide [ SimpleGraph.Walk.length_append ];
      omega
    have hc₁_odd : Odd c₁.length ∨ Odd c₂.length := by
      grind +qlia
    generalize_proofs at *;
    grind

/-- **No odd cycle implies 2-colorable.**  A simple graph in which every cycle
has even length is 2-colorable. -/
theorem colorable_two_of_cycle_even {V : Type*} (G : SimpleGraph V)
    (h : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length) : G.Colorable 2 := by
  rw [SimpleGraph.two_colorable_iff_forall_loop_even]
  intro u w
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨x, c, hc, hcodd⟩ := exists_odd_cycle_aux G w.length u w rfl hodd
  exact (Nat.not_odd_iff_even.mpr (h x c hc)) hcodd

/-
**Amalgamation case of the reconstruction step.**  If `(w, ed)` is a bridge
incidence and `w` also lies on another edge `f`, then `F` is a one-point
amalgamation of two strictly smaller `ReconOK` systems.
-/
theorem decomp_amalg (h : ReconOK F)
    (ed : {e : Finset F.V // e ∈ F.edges}) (w : F.V) (hbrid : IsBridgeInc F w ed)
    (f : {e : Finset F.V // e ∈ F.edges}) (hfne : f ≠ ed) (hwf : w ∈ f.1) :
    ∃ (F₁ F₂ : FTS) (x : F₁.V) (y : F₂.V),
        F₁.edges.card < F.edges.card ∧ F₂.edges.card < F.edges.card ∧
        ReconOK F₁ ∧ ReconOK F₂ ∧ FTS.Iso F (F₁.amalgamate F₂ x y) := by
  obtain ⟨hlin, hno_iso, hbrEx, hev⟩ := h;
  -- Let `S := Finset.univ.filter (fun e' => EReach w ed e')`.
  set S : Finset {e : Finset F.V // e ∈ F.edges} := Finset.univ.filter (fun e' => EReach w ed e');
  -- We need to show that `S` satisfies the conditions for `recon_amalg`.
  have hgS : IncS S w := by
    exact ⟨ ed, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Relation.ReflTransGen.refl ⟩, hbrid.1 ⟩
  have hgT : ∃ e ∈ Sᶜ, w ∈ e.1 := by
    use f;
    simp +zetaDelta at *;
    exact ⟨ bridge_ereach_false hlin w ed f hbrid.1 hwf ( Ne.symm hfne ) hbrid.2, hwf ⟩
  have hcov : ∀ v : F.V, IncS S v ∨ (∃ e ∈ Sᶜ, v ∈ e.1) := by
    intro v; specialize hno_iso v; simp_all +decide [ FTS.Isolated ] ;
    grind
  have hsep : ∀ v : F.V, IncS S v → (∃ e ∈ Sᶜ, v ∈ e.1) → v = w := by
    intro v hv hv'; obtain ⟨ a, ha, hv ⟩ := hv; obtain ⟨ b, hb, hv' ⟩ := hv'; simp_all +decide [ IncS ] ;
    contrapose! hb;
    exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Relation.ReflTransGen.tail ( Finset.mem_filter.mp ha |>.2 ) ⟨ v, hb, hv, hv' ⟩ ⟩;
  refine' ⟨ F.restrict S, F.restrict Sᶜ, ⟨ w, hgS ⟩, ⟨ w, hgT ⟩, _, _, _, _, recon_amalg S w hcov hsep hgS hgT ⟩;
  · rw [ FTS.restrict_edges_card ];
    refine' lt_of_lt_of_le ( Finset.card_lt_card ( Finset.filter_ssubset.mpr _ ) ) _;
    · exact ⟨ f, Finset.mem_univ _, fun h => bridge_ereach_false hlin w ed f hbrid.1 hwf ( Ne.symm hfne ) hbrid.2 h ⟩;
    · simp +decide;
  · rw [ FTS.restrict_edges_card ];
    rw [ Finset.card_compl ];
    rw [ Fintype.card_coe ];
    exact Nat.sub_lt ( Finset.card_pos.mpr ⟨ _, ed.2 ⟩ ) ( Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Relation.ReflTransGen.refl ⟩ ⟩ );
  · exact FTS.restrict_reconOK S hlin hbrEx hev;
  · apply FTS.restrict_reconOK;
    · assumption;
    · exact hbrEx;
    · exact hev

/-! ### The core graph of a private-vertex selection -/

/-- Core vertices for a private-vertex selection `pr`: vertices that are not the
chosen private vertex of any edge. -/
abbrev CoreV (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V) : Type :=
  {v : F.V // ∀ ed, pr ed ≠ v}

noncomputable instance instFintypeCoreV (F : FTS)
    (pr : {e : Finset F.V // e ∈ F.edges} → F.V) : Fintype (CoreV F pr) :=
  Fintype.ofFinite _

instance instDecEqCoreV (F : FTS)
    (pr : {e : Finset F.V // e ∈ F.edges} → F.V) : DecidableEq (CoreV F pr) :=
  Subtype.instDecidableEq

/-- The core graph: two core vertices are adjacent when they are distinct and both
lie on a common edge of `F`. -/
def coreGraph (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V) :
    SimpleGraph (CoreV F pr) where
  Adj a b := (a : F.V) ≠ (b : F.V) ∧
    ∃ ed : {e : Finset F.V // e ∈ F.edges}, (a : F.V) ∈ ed.1 ∧ (b : F.V) ∈ ed.1
  symm := by constructor; rintro a b ⟨h1, ed, h2, h3⟩; exact ⟨h1.symm, ed, h3, h2⟩
  loopless := ⟨fun a h => h.1 rfl⟩

noncomputable instance instDecRelCoreGraph (F : FTS)
    (pr : {e : Finset F.V // e ∈ F.edges} → F.V) :
    DecidableRel (coreGraph F pr).Adj :=
  fun _ _ => Classical.dec _

/-
In a cycle, `getVert` is injective on `[0, length)`.
-/
theorem cycle_getVert_inj {V : Type*} {G : SimpleGraph V} {x : V} {c : G.Walk x x}
    (hc : c.IsCycle) {i j : ℕ} (hi : i < c.length) (hj : j < c.length)
    (h : c.getVert i = c.getVert j) : i = j := by
  have h_tail_nodup : List.Nodup (c.support.tail) := by
    exact hc.support_nodup;
  have h_tail_nodup : ∀ i j, i < c.length → j < c.length → i ≠ j → c.getVert (i + 1) ≠ c.getVert (j + 1) := by
    intro i j hi hj hij;
    have := List.nodup_iff_injective_get.mp h_tail_nodup;
    have := @this ⟨ i, by
      grind ⟩ ⟨ j, by
      simp +decide [ hj ] ⟩ ; simp_all +decide
    generalize_proofs at *;
    grind +suggestions;
  rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide;
  · specialize h_tail_nodup j ( c.length - 1 ) ( by linarith ) ( by omega ) ( by omega ) ; simp_all +decide [ Nat.sub_add_cancel hi ];
  · grind +suggestions;
  · exact Classical.not_not.1 fun h' => h_tail_nodup i j ( Nat.lt_of_succ_lt hi ) ( Nat.lt_of_succ_lt hj ) h' h

/-
The core graph is 2-colorable, because a cycle of the core graph lifts to a
Berge cycle of `F` of the same length, which is even.
-/
theorem coreGraph_colorable (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hpm : ∀ ed, pr ed ∈ ed.1)
    (hev : ∀ c : BergeCycle F, Even c.m) : (coreGraph F pr).Colorable 2 := by
  apply colorable_two_of_cycle_even;
  intro v c hc
  set m := c.length with hm
  have hm3 : 3 ≤ m := by
    exact hc.three_le_length
  haveI : NeZero m := ⟨by omega⟩
  generalize_proofs at *;
  -- Build a Berge cycle of length `m` in `F`.
  obtain ⟨v', e', hv', he'⟩ : ∃ (v' : ZMod m → F.V) (e' : ZMod m → {e : Finset F.V // e ∈ F.edges}),
    (∀ i, v' i = (c.getVert i.val : F.V)) ∧
    (∀ i, v' i ∈ (e' i).1 ∧ v' (i + 1) ∈ (e' i).1) := by
      have h_adj : ∀ i : ZMod m, (coreGraph F pr).Adj (c.getVert i.val) (c.getVert ((i.val + 1) % m)) := by
        intro i
        have h_adj : (coreGraph F pr).Adj (c.getVert i.val) (c.getVert (i.val + 1)) := by
          convert! c.adj_getVert_succ _ using 1
          generalize_proofs at *;
          exact i.val_lt
        generalize_proofs at *;
        cases eq_or_ne ( i.val + 1 ) m <;> simp_all +decide;
        rwa [ Nat.mod_eq_of_lt ( lt_of_le_of_ne ( Nat.succ_le_of_lt ( show i.val < c.length from i.val_lt ) ) ‹_› ) ];
      choose e' he' using fun i => h_adj i |>.2;
      use fun i => (c.getVert i.val : F.V), e';
      simp_all +decide [ ZMod.val_add ];
      rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod.val ];
  -- Show that `v'` and `e'` satisfy the conditions of a Berge cycle.
  have hv'_inj : Function.Injective v' := by
    intro i j hij
    have h_eq : c.getVert i.val = c.getVert j.val := by
      exact Subtype.ext <| by simpa [ hv' ] using! hij;
    have h_eq' : i.val = j.val := by
      apply cycle_getVert_inj hc (ZMod.val_lt i) (ZMod.val_lt j) h_eq
    have h_eq'' : i = j := by
      exact ZMod.val_injective m h_eq'
    exact h_eq''
  have he'_inj : Function.Injective e' := by
    intro i j hij
    have h_core : (e' i).1.erase (pr (e' i)) = {v' i, v' (i + 1)} ∧ (e' j).1.erase (pr (e' j)) = {v' j, v' (j + 1)} := by
      have h_core : ∀ i, (e' i).1.erase (pr (e' i)) ⊇ {v' i, v' (i + 1)} := by
        grind +revert;
      have h_core_card : ∀ i, ((e' i).1.erase (pr (e' i))).card = 2 := by
        intro i; rw [ Finset.card_erase_of_mem ( hpm _ ) ] ; simp +decide [ F.card3 _ ( e' i |>.2 ) ] ;
      have h_core_eq : ∀ i, {v' i, v' (i + 1)} = (e' i).1.erase (pr (e' i)) := by
        intros i
        apply Finset.eq_of_subset_of_card_le (h_core i);
        rw [ h_core_card i, Finset.card_insert_of_notMem, Finset.card_singleton ] ; simp +decide [ hv'_inj.eq_iff ];
        exact by haveI := Fact.mk ( by linarith : 1 < m ) ; exact by simp +decide ;
      exact ⟨ h_core_eq i ▸ rfl, h_core_eq j ▸ rfl ⟩;
    have h_core_eq : v' j ∈ ({v' i, v' (i + 1)} : Finset F.V) ∧ v' (j + 1) ∈ ({v' i, v' (i + 1)} : Finset F.V) := by
      grind;
    simp_all +decide;
    cases h_core_eq.1 <;> cases h_core_eq.2 <;> simp_all +decide;
    · grind +suggestions;
    · grind;
    · have h_contra : (i + 1 + 1 : ZMod m) = i := by
        grind +suggestions;
      norm_num [ add_assoc ] at h_contra;
      erw [ ZMod.natCast_eq_zero_iff ] at h_contra ; have := Nat.le_of_dvd ( by linarith ) h_contra ; linarith;
    · grind +suggestions;
  exact hev ⟨ m, by linarith, v', e', hv'_inj, he'_inj, fun i => he' i |>.1, fun i => he' i |>.2 ⟩

/-
Structure of an edge: it consists of two distinct core vertices and its
private vertex.
-/
theorem edge_core_structure (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hpm : ∀ ed, pr ed ∈ ed.1)
    (hpu : ∀ ed, ∀ g ∈ F.edges, pr ed ∈ g → g = ed.1)
    (ed : {e : Finset F.V // e ∈ F.edges}) :
    ∃ a b : F.V, a ≠ b ∧ (∀ g, pr g ≠ a) ∧ (∀ g, pr g ≠ b) ∧
      ed.1 = {a, b, pr ed} := by
  obtain ⟨a, b, hab⟩ : ∃ a b : F.V, a ≠ b ∧ a ∈ ed.1 ∧ b ∈ ed.1 ∧ a ≠ pr ed ∧ b ≠ pr ed ∧ ed.1 = {a, b, pr ed} := by
    obtain ⟨a, b, hab⟩ : ∃ a b : F.V, a ≠ b ∧ a ∈ ed.1 ∧ b ∈ ed.1 ∧ a ≠ pr ed ∧ b ≠ pr ed := by
      have h_core : (ed.1.erase (pr ed)).card = 2 := by
        rw [ Finset.card_erase_of_mem ( hpm ed ), F.card3 _ ed.2 ];
      obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.1 ( by linarith ) ; use a, b; aesop;
    refine' ⟨ a, b, hab.1, hab.2.1, hab.2.2.1, hab.2.2.2.1, hab.2.2.2.2, _ ⟩;
    have h_card : ed.1.card = 3 := by
      exact F.card3 _ ed.2;
    rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hab.2.1, Finset.insert_subset_iff.mpr ⟨ hab.2.2.1, Finset.singleton_subset_iff.mpr ( hpm ed ) ⟩ ⟩ ) ] ; aesop;
  grind

/-
The private-vertex map is injective.
-/
theorem pr_injective (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hpm : ∀ ed, pr ed ∈ ed.1)
    (hpu : ∀ ed, ∀ g ∈ F.edges, pr ed ∈ g → g = ed.1) :
    Function.Injective pr := by
  intro ed1 ed2 h_eq;
  grind +suggestions

/-
Two distinct core vertices lying on a common edge are adjacent in the core
graph, so their `Sym2` is an edge of the core graph.
-/
theorem core_edge_mem (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (a b : CoreV F pr) (ed : {e : Finset F.V // e ∈ F.edges})
    (hab : a ≠ b) (hae : (a : F.V) ∈ ed.1) (hbe : (b : F.V) ∈ ed.1) :
    Sym2.mk (a) (b) ∈ (coreGraph F pr).edgeFinset := by
  simp +decide [ SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, coreGraph ];
  exact ⟨ Subtype.coe_injective.ne hab, ed.1, hae, ed.2, hbe ⟩

/-
An edge is determined by any two of its distinct vertices (linearity).
-/
theorem edge_unique_of_two (F : FTS) (hlin : F.Linear)
    {ed ed' : {e : Finset F.V // e ∈ F.edges}} {a b : F.V} (hab : a ≠ b)
    (h1 : a ∈ ed.1) (h2 : b ∈ ed.1) (h3 : a ∈ ed'.1) (h4 : b ∈ ed'.1) : ed = ed' := by
  exact Subtype.ext <| Classical.not_not.1 fun h => absurd ( hlin _ ed.2 _ ed'.2 h ) ( by exact Nat.not_le_of_gt ( Finset.one_lt_card.2 ⟨ a, by aesop, b, by aesop ⟩ ) )

/-
From an edge of the core graph, recover an `F`-edge containing both endpoints.
-/
theorem jedge_exists_edge (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (a b : CoreV F pr) (hx : Sym2.mk (a) (b) ∈ (coreGraph F pr).edgeFinset) :
    ∃ ed : {e : Finset F.V // e ∈ F.edges}, (a : F.V) ∈ ed.1 ∧ (b : F.V) ∈ ed.1 := by
  simp_all +decide [ coreGraph ]

/-- The vertex bijection `F.V ≃ (graphExpansion (coreGraph F pr)).V` with its
computation rules: core vertices go to `Sum.inl`, and the private vertex of an
edge goes to `Sum.inr` of the core-pair edge. -/
theorem exists_expEquiv (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hlin : F.Linear) (hpm : ∀ ed, pr ed ∈ ed.1)
    (hpu : ∀ ed, ∀ g ∈ F.edges, pr ed ∈ g → g = ed.1) :
    ∃ (φ : F.V ≃ (graphExpansion (coreGraph F pr)).V)
      (A B : {e : Finset F.V // e ∈ F.edges} → CoreV F pr),
      (∀ ed, A ed ≠ B ed) ∧
      (∀ ed, ed.1 = {(A ed : F.V), (B ed : F.V), pr ed}) ∧
      (∀ (v : F.V) (hv : ∀ ed, pr ed ≠ v), φ v = Sum.inl ⟨v, hv⟩) ∧
      (∀ ed, ∃ x : {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset},
          φ (pr ed) = Sum.inr x ∧ x.1 = Sym2.mk (A ed) (B ed)) ∧
      (∀ x : {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset},
          ∃ ed, φ (pr ed) = Sum.inr x) := by
  classical
  have hce : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ a b : CoreV F pr,
      a ≠ b ∧ ed.1 = {(a : F.V), (b : F.V), pr ed} := by
    intro ed
    obtain ⟨a, b, hne, hca, hcb, hs⟩ := edge_core_structure F pr hpm hpu ed
    exact ⟨⟨a, hca⟩, ⟨b, hcb⟩, by simpa [Subtype.ext_iff] using! hne, hs⟩
  choose A B hAB hset using hce
  have hmemA : ∀ ed, (A ed : F.V) ∈ ed.1 := by intro ed; rw [hset ed]; simp
  have hmemB : ∀ ed, (B ed : F.V) ∈ ed.1 := by intro ed; rw [hset ed]; simp
  have hmem : ∀ ed, Sym2.mk (A ed) (B ed) ∈ (coreGraph F pr).edgeFinset :=
    fun ed => core_edge_mem F pr (A ed) (B ed) ed (hAB ed) (hmemA ed) (hmemB ed)
  set jE : {e : Finset F.V // e ∈ F.edges} →
      {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset} :=
    fun ed => ⟨Sym2.mk (A ed) (B ed), hmem ed⟩ with hjEdef
  have hjE : ∀ ed, (jE ed).1 = Sym2.mk (A ed) (B ed) := fun ed => rfl
  have hjE_inj : Function.Injective jE := by
    intro ed1 ed2 h
    have h2 : Sym2.mk (A ed1) (B ed1) = Sym2.mk (A ed2) (B ed2) := by
      have := congrArg Subtype.val h; rwa [hjE, hjE] at this
    rw [Sym2.eq_iff] at h2
    have hane : (A ed1 : F.V) ≠ (B ed1 : F.V) := by simpa [Subtype.ext_iff] using! hAB ed1
    refine edge_unique_of_two F hlin hane (hmemA ed1) (hmemB ed1) ?_ ?_
    · rcases h2 with ⟨ha, _⟩ | ⟨ha, _⟩
      · rw [congrArg Subtype.val ha]; exact hmemA ed2
      · rw [congrArg Subtype.val ha]; exact hmemB ed2
    · rcases h2 with ⟨_, hb⟩ | ⟨_, hb⟩
      · rw [congrArg Subtype.val hb]; exact hmemB ed2
      · rw [congrArg Subtype.val hb]; exact hmemA ed2
  have hjE_surj : ∀ x : {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset},
      ∃ ed, jE ed = x := by
    intro x
    obtain ⟨P, Q, hPQ⟩ : ∃ P Q : CoreV F pr, x.1 = Sym2.mk (P) (Q) := by
      induction x.1 using Sym2.ind with | _ P Q => exact ⟨P, Q, rfl⟩
    have hxmem : Sym2.mk (P) (Q) ∈ (coreGraph F pr).edgeFinset := hPQ ▸ x.2
    obtain ⟨ed, hP, hQ⟩ := jedge_exists_edge F pr P Q hxmem
    have hadj := hxmem
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hadj
    have hPneQ : P ≠ Q := fun h => hadj.1 (by rw [h])
    have hPpr : (P : F.V) ≠ pr ed := (P.2 ed).symm
    have hQpr : (Q : F.V) ≠ pr ed := (Q.2 ed).symm
    have hPin : (P : F.V) = (A ed : F.V) ∨ (P : F.V) = (B ed : F.V) := by
      have := hP; rw [hset ed] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hPpr
    have hQin : (Q : F.V) = (A ed : F.V) ∨ (Q : F.V) = (B ed : F.V) := by
      have := hQ; rw [hset ed] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hQpr
    refine ⟨ed, ?_⟩
    apply Subtype.ext
    rw [hjE, hPQ, Sym2.eq_iff]
    have hPQne : (P:F.V) ≠ (Q:F.V) := fun h => hPneQ (Subtype.ext h)
    rcases hPin with hpA | hpB
    · rcases hQin with hqA | hqB
      · exact absurd (hpA.trans hqA.symm) hPQne
      · exact Or.inl ⟨(Subtype.ext hpA.symm), (Subtype.ext hqB.symm)⟩
    · rcases hQin with hqA | hqB
      · exact Or.inr ⟨Subtype.ext hqA.symm, Subtype.ext hpB.symm⟩
      · exact absurd (hpB.trans hqB.symm) hPQne
  set f : F.V → (graphExpansion (coreGraph F pr)).V :=
    fun v => if hv : (∀ ed, pr ed ≠ v) then Sum.inl ⟨v, hv⟩
      else Sum.inr (jE (Classical.choose (not_forall.mp hv))) with hfdef
  have hf_core : ∀ (v : F.V) (hv : ∀ ed, pr ed ≠ v), f v = Sum.inl ⟨v, hv⟩ := by
    intro v hv; rw [hfdef]; simp only [dif_pos hv]
  have hf_priv : ∀ ed, f (pr ed) = Sum.inr (jE ed) := by
    intro ed
    have hv : ¬ (∀ ed', pr ed' ≠ pr ed) := fun h => h ed rfl
    rw [hfdef]; simp only [dif_neg hv]
    have hchoose : pr (Classical.choose (not_forall.mp hv)) = pr ed :=
      not_not.mp (Classical.choose_spec (not_forall.mp hv))
    rw [pr_injective F pr hpm hpu hchoose]
  have hf_bij : Function.Bijective f := by
    constructor
    · intro v w hvw
      by_cases hv : (∀ ed, pr ed ≠ v) <;> by_cases hw : (∀ ed, pr ed ≠ w)
      · rw [hf_core v hv, hf_core w hw] at hvw
        exact congrArg Subtype.val (Sum.inl.inj hvw)
      · rw [hfdef] at hvw; simp only [dif_pos hv, dif_neg hw] at hvw
        exact (Sum.inl_ne_inr hvw).elim
      · rw [hfdef] at hvw; simp only [dif_neg hv, dif_pos hw] at hvw
        exact (Sum.inl_ne_inr hvw.symm).elim
      · rw [hfdef] at hvw; simp only [dif_neg hv, dif_neg hw] at hvw
        have hh := hjE_inj (Sum.inr.inj hvw)
        have h1 : pr (Classical.choose (not_forall.mp hv)) = v :=
          not_not.mp (Classical.choose_spec (not_forall.mp hv))
        have h2 : pr (Classical.choose (not_forall.mp hw)) = w :=
          not_not.mp (Classical.choose_spec (not_forall.mp hw))
        rw [← h1, ← h2, hh]
    · intro y
      rcases y with a | x
      · exact ⟨a.1, by rw [hf_core a.1 a.2]⟩
      · obtain ⟨ed, hed⟩ := hjE_surj x
        exact ⟨pr ed, by rw [hf_priv ed, hed]⟩
  refine ⟨Equiv.ofBijective f hf_bij, A, B, hAB, hset, ?_, ?_, ?_⟩
  · intro v hv; rw [Equiv.ofBijective_apply]; exact hf_core v hv
  · intro ed; refine ⟨jE ed, ?_, hjE ed⟩; rw [Equiv.ofBijective_apply]; exact hf_priv ed
  · intro x; obtain ⟨ed, hed⟩ := hjE_surj x
    exact ⟨ed, by rw [Equiv.ofBijective_apply, hf_priv ed, hed]⟩

/-- `F` is isomorphic to the private-vertex expansion of its core graph. -/
theorem F_iso_expansion (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hlin : F.Linear)
    (hpm : ∀ ed, pr ed ∈ ed.1)
    (hpu : ∀ ed, ∀ g ∈ F.edges, pr ed ∈ g → g = ed.1) :
    FTS.Iso F (graphExpansion (coreGraph F pr)) := by
  classical
  obtain ⟨φ, A, B, hAB, hset, hcore, hpr, hsurj⟩ := exists_expEquiv F pr hlin hpm hpu
  have key : ∀ (ed : {e : Finset F.V // e ∈ F.edges})
      (x : {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset}),
      φ (pr ed) = Sum.inr x → x.1 = Sym2.mk (A ed) (B ed) →
      ed.1.map φ.toEmbedding =
        ({Sum.inl (Quot.out x.1).1, Sum.inl (Quot.out x.1).2, Sum.inr x} :
          Finset (graphExpansion (coreGraph F pr)).V) := by
    intro ed x hx hxval
    have hφA : φ (A ed : F.V) = Sum.inl (A ed) := by
      have := hcore (A ed : F.V) (A ed).2; simpa using! this
    have hφB : φ (B ed : F.V) = Sum.inl (B ed) := by
      have := hcore (B ed : F.V) (B ed).2; simpa using! this
    have hmkout : Sym2.mk ((Quot.out x.1).1) ((Quot.out x.1).2) = x.1 := by
      exact Quot.out_eq x.1
    have hout : (Quot.out x.1).1 = A ed ∧ (Quot.out x.1).2 = B ed ∨
        (Quot.out x.1).1 = B ed ∧ (Quot.out x.1).2 = A ed := by
      have h : Sym2.mk ((Quot.out x.1).1) ((Quot.out x.1).2) = Sym2.mk (A ed) (B ed) := by
        rw [hmkout, hxval]
      rwa [Sym2.eq_iff] at h
    rw [hset ed, Finset.map_insert, Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding]
    rw [hφA, hφB, hx]
    rcases hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Finset.insert_comm]
  refine ⟨φ, fun e => ⟨fun he => ?_, fun he => ?_⟩⟩
  · obtain ⟨x, hx, hxval⟩ := hpr ⟨e, he⟩
    have hk := key ⟨e, he⟩ x hx hxval
    exact Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, hk.symm⟩
  · obtain ⟨x, hxeq⟩ := expansion_edge_cases (coreGraph F pr) he
    obtain ⟨ed, hed⟩ := hsurj x
    obtain ⟨x', hx', hx'val⟩ := hpr ed
    have hxx' : x = x' := Sum.inr.inj (hed.symm.trans hx')
    have hxval : x.1 = Sym2.mk (A ed) (B ed) := hxx' ▸ hx'val
    have hk := key ed x hed hxval
    have heq : e.map φ.toEmbedding = ed.1.map φ.toEmbedding := by rw [hxeq, ← hk]
    have he2 : e = ed.1 := Finset.map_injective φ.toEmbedding heq
    rw [he2]; exact ed.2

/-- **Expansion recognition.**  A linear finite triple system with no isolated
vertices, only even Berge cycles, and a private vertex on every edge, is
isomorphic to the private-vertex expansion of a finite bipartite graph. -/
theorem exists_expansion_of_private (hlin : F.Linear)
    (hpriv : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1,
      ∀ g ∈ F.edges, w ∈ g → g = ed.1)
    (hev : ∀ c : BergeCycle F, Even c.m) :
    ∃ (VJ : Type) (_ : Fintype VJ) (_ : DecidableEq VJ) (J : SimpleGraph VJ)
        (_ : DecidableRel J.Adj), J.Colorable 2 ∧ FTS.Iso F (graphExpansion J) := by
  choose pr hpm hpu using hpriv
  exact ⟨CoreV F pr, instFintypeCoreV F pr, instDecEqCoreV F pr, coreGraph F pr,
    instDecRelCoreGraph F pr, coreGraph_colorable F pr hpm hev,
    F_iso_expansion F pr hlin hpm hpu⟩

end Erdos1177

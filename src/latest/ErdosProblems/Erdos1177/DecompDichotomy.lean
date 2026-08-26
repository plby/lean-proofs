-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.DecompSep

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The separation dichotomy

For the reconstruction step we must, given a `ReconOK` finite triple system with
at least one edge, either exhibit a separation (a partition of the edges sharing
at most one vertex) or recognise the system as a bipartite expansion.

The key geometric input is that a bridge incidence blocks edge-connectivity: if
`(w, e₀)` lies on no Berge cycle, then no edge containing `w` (other than `e₀`)
is reachable from `e₀` through vertices other than `w`.
-/

open Cardinal

namespace Erdos1177

open Classical

universe u

set_option maxHeartbeats 2000000

variable {F : FTS}

/-- Two edges share a vertex different from `w`. -/
def ShareOff (w : F.V) (a b : {e : Finset F.V // e ∈ F.edges}) : Prop :=
  ∃ v, v ≠ w ∧ v ∈ a.1 ∧ v ∈ b.1

/-- Edge-reachability avoiding the vertex `w`. -/
def EReach (w : F.V) : {e : Finset F.V // e ∈ F.edges} → {e : Finset F.V // e ∈ F.edges} → Prop :=
  Relation.ReflTransGen (ShareOff w)

/-
**Generic chain shortcut.**  If two entries `L[i]`, `L[j]` (`i < j`) of an
`R`-chain are themselves `R`-related, then splicing the list at those positions
yields an `R`-chain with the same endpoints and length `i + 1 + (L.length - j)`.
-/
theorem chain_shortcut {α : Type*} {R : α → α → Prop} (L : List α)
    (hchain : List.IsChain R L) (i j : ℕ) (hi : i < L.length) (hj : j < L.length)
    (hij : i < j) (hR : R (L.get ⟨i, hi⟩) (L.get ⟨j, hj⟩)) :
    ∃ L' : List α, L'.head? = L.head? ∧ L'.getLast? = L.getLast? ∧
      List.IsChain R L' ∧ L'.length = i + 1 + (L.length - j) := by
  refine' ⟨ L.take ( i + 1 ) ++ L.drop j, _, _, _, _ ⟩ <;> simp_all +decide [ List.isChain_append ];
  · cases L <;> simp_all +decide [ List.take ];
    contradiction;
  · rw [ List.getLast?_drop ];
    grind;
  · refine' ⟨ hchain.take _, hchain.drop _, _ ⟩;
    grind

/-
A reachability witness as a chain-list of edges.
-/
theorem exists_chain_list (w : F.V) (a b : {e : Finset F.V // e ∈ F.edges})
    (hab : EReach w a b) :
    ∃ L : List {e : Finset F.V // e ∈ F.edges},
      L.head? = some a ∧ L.getLast? = some b ∧ List.IsChain (ShareOff w) L := by
  revert hab;
  intro hab
  induction' hab with c hc ih;
  · exact ⟨ [ a ], rfl, rfl, List.isChain_singleton _ ⟩;
  · obtain ⟨ L, hL₁, hL₂, hL₃ ⟩ := ‹_›; use L ++ [ hc ] ; simp_all +decide [ List.isChain_append ] ;

/-- **Assembling a Berge cycle from cyclic incidence data.**  Injective cyclic
sequences of vertices `v` and edges `g` (indexed by `ZMod m`, `m ≥ 2`) with the
two incidence conditions form a Berge cycle; if moreover `g 0 = e0` and `v 0 = w`
then `(w, e0)` lies on a Berge cycle. -/
theorem onBergeCycle_of_cycle_data (w : F.V) {m : ℕ} (hm : 2 ≤ m)
    (g : ZMod m → {e : Finset F.V // e ∈ F.edges})
    (v : ZMod m → F.V)
    (hg : Function.Injective g) (hv : Function.Injective v)
    (hmem1 : ∀ i, v i ∈ (g i).1)
    (hmem2 : ∀ i, v (i + 1) ∈ (g i).1)
    (e0 : {e : Finset F.V // e ∈ F.edges}) (hg0 : g 0 = e0) (hv0 : v 0 = w) :
    OnBergeCycle F w e0 :=
  ⟨{ m := m, hm := hm, v := v, e := g, vinj := hv, einj := hg,
      mem_left := hmem1, mem_right := hmem2 }, 0, hg0, Or.inl hv0⟩

/-
**A minimal reachability walk.**  A shortest chain-list from `e0` to `f`
(avoiding `w`) has length `≥ 2`, is nodup, and has no "chord": two entries at
list-distance `≥ 2` never share a vertex `≠ w`.
-/
theorem exists_minimal_chain (w : F.V)
    (e0 f : {e : Finset F.V // e ∈ F.edges})
    (hne : e0 ≠ f) (hreach : EReach w e0 f) :
    ∃ L : List {e : Finset F.V // e ∈ F.edges},
      L.head? = some e0 ∧ L.getLast? = some f ∧ List.IsChain (ShareOff w) L ∧
      2 ≤ L.length ∧ L.Nodup ∧
      (∀ i j (hi : i < L.length) (hj : j < L.length), i + 2 ≤ j →
        ¬ ShareOff w (L.get ⟨i, hi⟩) (L.get ⟨j, hj⟩)) := by
  obtain ⟨L, hL⟩ : ∃ L : List {e : Finset F.V // e ∈ F.edges},
    L.head? = some e0 ∧ L.getLast? = some f ∧ List.IsChain (ShareOff w) L ∧ ∀ L' : List {e : Finset F.V // e ∈ F.edges}, L'.head? = some e0 ∧ L'.getLast? = some f ∧ List.IsChain (ShareOff w) L' → L.length ≤ L'.length := by
      have h_exists_min : ∃ n, n ∈ {n : ℕ | ∃ L : List {e : Finset F.V // e ∈ F.edges}, L.head? = some e0 ∧ L.getLast? = some f ∧ List.IsChain (ShareOff w) L ∧ L.length = n} := by
        exact Exists.elim ( exists_chain_list w e0 f hreach ) fun L hL => ⟨ _, ⟨ L, hL.1, hL.2.1, hL.2.2, rfl ⟩ ⟩;
      obtain ⟨ n, hn ⟩ := Nat.findX h_exists_min;
      rcases hn.1 with ⟨ L, hL₁, hL₂, hL₃, rfl ⟩ ; exact ⟨ L, hL₁, hL₂, hL₃, fun L' hL' => not_lt.1 fun contra => hn.2 _ contra ⟨ L', hL'.1, hL'.2.1, hL'.2.2, rfl ⟩ ⟩ ;
  -- Let's choose the shortest such chain `L`.
  use L;
  refine' ⟨ hL.1, hL.2.1, hL.2.2.1, _, _, _ ⟩;
  · rcases L with ( _ | ⟨ x, _ | ⟨ y, L ⟩ ⟩ ) <;> simp_all +decide;
    grind;
  · by_contra h_dup;
    obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : Fin L.length, i < j ∧ L.get i = L.get j := by
      rw [ List.nodup_iff_injective_get ] at h_dup;
      obtain ⟨ i, j, hij, h ⟩ := Function.not_injective_iff.mp h_dup; cases lt_trichotomy i j <;> tauto;
    obtain ⟨v, hv⟩ : ∃ v : F.V, v ≠ w ∧ v ∈ (L.get i).1 ∧ v ∈ (L.get j).1 := by
      have := F.card3 ( L.get i |>.1 ) ( L.get i |>.2 );
      exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( L.get i |>.1 ) from by linarith ) w );
    by_cases h_cases : j.val = i.val + 1;
    · by_cases h_cases2 : j.val + 1 < L.length;
      · have h_chain : ShareOff w (L.get ⟨i.val, by
          exact i.2⟩) (L.get ⟨i.val + 2, by
          grind⟩) := by
          have := hL.2.2.1; simp_all +decide [ List.isChain_iff_getElem ] ;
        generalize_proofs at *;
        obtain ⟨ L', hL' ⟩ := chain_shortcut L hL.2.2.1 i ( i + 2 ) ( by linarith ) ( by linarith ) ( by linarith ) h_chain;
        grind;
      · have h_contra : L.take (L.length - 1) = L.take (i.val + 1) ∧ L.take (i.val + 1) ≠ L := by
          grind;
        have h_contra : L.take (L.length - 1) = L.take (i.val + 1) ∧ L.take (i.val + 1) ≠ L ∧ List.IsChain (ShareOff w) (L.take (i.val + 1)) ∧ (L.take (i.val + 1)).head? = some e0 ∧ (L.take (i.val + 1)).getLast? = some f := by
          refine' ⟨ h_contra.1, h_contra.2, _, _, _ ⟩;
          · exact hL.2.2.1.take _;
          · cases L <;> aesop;
          · grind;
        have := hL.2.2.2 ( List.take ( i.val + 1 ) L ) ⟨ h_contra.2.2.2.1, h_contra.2.2.2.2, h_contra.2.2.1 ⟩ ; simp_all +decide ;
    · have := chain_shortcut L hL.2.2.1 i j ( by simp ) ( by simp ) ( by simpa [ Fin.ext_iff ] using! hij ) ( by
        exact ⟨ v, hv.1, hv.2.1, hv.2.2 ⟩ );
      grind;
  · grind +suggestions

/-- Consecutive entries of an `IsChain (ShareOff w)` list share a vertex `≠ w`. -/
theorem chain_get_shareoff {w : F.V} {L : List {e : Finset F.V // e ∈ F.edges}}
    (hchain : List.IsChain (ShareOff w) L) {k : ℕ} (h : k + 1 < L.length) :
    ShareOff w (L.get ⟨k, by omega⟩) (L.get ⟨k + 1, h⟩) :=
  List.isChain_iff_getElem.mp hchain k h

/-
In `ZMod m` (`m ≠ 0`), the `val` of `i - 1` for `i ≠ 0` is `i.val - 1`.
-/
theorem zmod_val_sub_one {m : ℕ} [NeZero m] (i : ZMod m) (h : i ≠ 0) :
    (i - 1).val = i.val - 1 := by
  by_cases hi : i.val = 0;
  · exact False.elim <| h <| by rw [ ← ZMod.natCast_zmod_val i, hi ] ; norm_num;
  · have h_val : (i - 1 : ZMod m) = (i.val - 1 : ℕ) := by
      simp +decide [ Nat.cast_sub ( Nat.one_le_iff_ne_zero.mpr hi ) ];
    rw [ h_val, ZMod.val_cast_of_lt ];
    exact lt_of_le_of_lt ( Nat.pred_le _ ) ( ZMod.val_lt i )

/-
**Extraction of cyclic incidence data.**  If `w ∈ e0`, `w ∈ f`, `e0 ≠ f`,
and `f` is reachable from `e0` avoiding `w`, then there is injective cyclic
incidence data (`m ≥ 2`) closing up the reachability walk through `w`, with the
`0`-th edge equal to `e0` and the `0`-th vertex equal to `w`.
-/
theorem cycle_data_of_ereach (hlin : F.Linear) (w : F.V)
    (e0 f : {e : Finset F.V // e ∈ F.edges}) (hwe0 : w ∈ e0.1) (hwf : w ∈ f.1)
    (hne : e0 ≠ f) (hreach : EReach w e0 f) :
    ∃ (m : ℕ) (_ : 2 ≤ m)
      (g : ZMod m → {e : Finset F.V // e ∈ F.edges}) (v : ZMod m → F.V),
      Function.Injective g ∧ Function.Injective v ∧
      (∀ i, v i ∈ (g i).1) ∧ (∀ i, v (i + 1) ∈ (g i).1) ∧
      g 0 = e0 ∧ v 0 = w := by
  -- Set `m := L.length`, `haveI : NeZero m := ⟨by omega⟩`.
  obtain ⟨L, hhead, hlast, hchain, h2, hnodup, hnochord⟩ := exists_minimal_chain w e0 f hne hreach
  set m := L.length
  haveI : NeZero m := ⟨by omega⟩;
  -- Define `g : ZMod m → _ := fun i => L.get ⟨i.val, ZMod.val_lt i⟩`.
  set g : ZMod m → {e : Finset F.V // e ∈ F.edges} := fun i => L.get ⟨i.val, ZMod.val_lt i⟩
  have hg0 : g 0 = e0 := by
    cases L <;> aesop
  have g_last : g (0 - 1) = f := by
    convert! hlast using 1;
    rw [ List.getLast?_eq_getElem? ];
    simp +zetaDelta at *;
    rcases L with ( _ | ⟨ _, _ | L ⟩ ) <;> norm_num at *
  have hg_inj : Function.Injective g := by
    intro i j hij; have := List.nodup_iff_injective_get.mp hnodup; simp_all +decide ;
    exact ZMod.val_injective m <| by have := List.nodup_iff_injective_get.mp hnodup; have := @this ⟨ i.val, ZMod.val_lt i ⟩ ⟨ j.val, ZMod.val_lt j ⟩ ; aesop;
  -- Shared-vertex existence `hshare : ∀ i, ∃ x, x ∈ (g (i-1)).1 ∧ x ∈ (g i).1`.
  have hshare : ∀ i : ZMod m, ∃ x : F.V, x ∈ (g (i - 1)).1 ∧ x ∈ (g i).1 := by
    intro i
    by_cases hi : i = 0;
    · grind;
    · have hcons : ShareOff w (g (i - 1)) (g i) := by
        convert! chain_get_shareoff hchain _;
        · rw [ zmod_val_sub_one ];
          · rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using! hi ) ) ];
          · exact hi;
        · rw [ zmod_val_sub_one ];
          · rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using! hi ) ) ] ; exact ZMod.val_lt i;
          · exact hi;
      exact ⟨ hcons.choose, hcons.choose_spec.2.1, hcons.choose_spec.2.2 ⟩;
  choose v hv_prev hv_cur using hshare;
  -- Uniqueness `huniq i y : y ∈ (g (i-1)).1 → y ∈ (g i).1 → y = v i`.
  have huniq : ∀ i : ZMod m, ∀ y : F.V, y ∈ (g (i - 1)).1 → y ∈ (g i).1 → y = v i := by
    intros i y hy_prev hy_cur
    have h_inter : ((g (i - 1)).1 ∩ (g i).1).card ≤ 1 := by
      apply hlin;
      · exact g _ |>.2;
      · exact g i |>.2;
      · intro h; have := hg_inj ( Subtype.ext h ) ; simp_all +decide ;
    contrapose! h_inter;
    exact Finset.one_lt_card.mpr ⟨ y, by aesop, v i, by aesop ⟩;
  refine' ⟨ m, h2, g, v, hg_inj, _, hv_cur, _, hg0, _ ⟩;
  · -- Let `p := v i`.
    intro i j hij
    by_cases hp : v i = w;
    · -- If `v k = w`, then `k = 0` (as `v · = w` only at `0`, shown above).
      have hk_zero : ∀ k : ZMod m, v k = w → k = 0 := by
        intro k hk
        by_contra hk_ne_zero;
        obtain ⟨ x, hx ⟩ := chain_get_shareoff hchain ( show k.val - 1 + 1 < L.length from by
                                                          rw [ Nat.sub_add_cancel ];
                                                          · exact ZMod.val_lt k;
                                                          · exact Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using! hk_ne_zero ) );
        specialize huniq k x ; simp_all +decide [ Nat.sub_add_cancel ( show 1 ≤ k.val from Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using! hk_ne_zero ) ) ];
        grind +suggestions;
      rw [ hk_zero i hp, hk_zero j ( hij ▸ hp ) ];
    · -- WLOG `i.val < j.val` (else symmetric; `i.val = j.val → i = j` by `ZMod.val_injective`).
      wlog hij' : i.val < j.val generalizing i j;
      · by_cases hij'' : j.val < i.val;
        · exact Eq.symm ( this ( hij.symm ) ( by simpa [ hij ] using! hp ) hij'' );
        · exact ZMod.val_injective m ( le_antisymm ( le_of_not_gt hij'' ) ( le_of_not_gt hij' ) );
      · -- Set `a := i.val - 1`, `b := j.val`; `a + 2 ≤ b` (from `i.val < j.val`, `i.val ≥ 1`).
        set a := i.val - 1
        set b := j.val
        have hab : a + 2 ≤ b := by
          by_cases hi : i = 0;
          · grind +revert;
          · linarith [ Nat.sub_add_cancel ( show 1 ≤ i.val from Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using! hi ) ) ];
        -- `p ∈ g (i-1) = L.get ⟨a,_⟩` (`hv_prev i`, `zmod_val_sub_one`) and `p ∈ g j = L.get ⟨b,_⟩` (`hv_cur j`).
        have hp_a : v i ∈ (L.get ⟨a, by
          exact lt_of_le_of_lt ( Nat.sub_le _ _ ) ( ZMod.val_lt i )⟩).1 := by
          convert! hv_prev i using 1;
          congr! 2;
          simp +zetaDelta at *;
          rw [ zmod_val_sub_one ];
          rintro rfl; simp_all +decide;
          specialize huniq 0 w ; simp_all +decide [ ZMod.val ];
          exact hp ( huniq ( by cases L <;> aesop ) ▸ rfl )
        have hp_b : v i ∈ (L.get ⟨b, by
          grind⟩).1 := by
          grind
        generalize_proofs at *;
        exact False.elim <| hnochord a b ‹_› ‹_› hab ⟨ v i, hp, hp_a, hp_b ⟩;
  · intro i; specialize hv_prev ( i + 1 ) ; specialize hv_cur ( i + 1 ) ; aesop;
  · grind +suggestions

/-- **Bridge blocks reachability.**  If the incidence `(w, e₀)` lies on no Berge
cycle, then no other edge `f` containing `w` is reachable from `e₀` avoiding `w`. -/
theorem bridge_ereach_false (hlin : F.Linear) (w : F.V)
    (e0 f : {e : Finset F.V // e ∈ F.edges}) (hwe0 : w ∈ e0.1) (hwf : w ∈ f.1)
    (hne : e0 ≠ f) (hbr : ¬ OnBergeCycle F w e0) : ¬ EReach w e0 f := by
  intro hreach
  obtain ⟨m, hm, g, v, hg, hv, hmem1, hmem2, hg0, hv0⟩ :=
    cycle_data_of_ereach hlin w e0 f hwe0 hwf hne hreach
  exact hbr (onBergeCycle_of_cycle_data w hm g v hg hv hmem1 hmem2 e0 hg0 hv0)

end Erdos1177

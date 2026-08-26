-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Structures

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Cycle collapse (§4, `lem:cycle-collapse`)

This file formalizes the transfinite core of the paper's §4 "Finite linear
traces of the lift": the **cycle collapse** lemma.  If a finite linear triple
system `F` embeds into the lift `Lift(A,κ)` via `f`, and we write
`f v = (ν v, a v)` with `ν v : Node A κ` the *sequence node*, then on every
Berge cycle of `F` all sequence nodes `ν (c.v i)` are equal.

This is `lem:cycle-collapse` of arXiv:2606.24882, the linchpin of the necessity
direction of the bridge-trace theorem.
-/

open Cardinal Ordinal

namespace Erdos1177

universe u

variable {α : Type u} {A : SimpleGraph α} {κ : Cardinal.{u}}

/-! ### The prefix order on nodes -/

/-- Two nodes are *comparable* in the initial-segment (prefix) order: equal, or
one is a proper prefix of the other. -/
def Node.comparable (σ τ : Node A κ) : Prop :=
  σ = τ ∨ Node.pre A κ σ τ ∨ Node.pre A κ τ σ

/-- Weak prefix: `σ = τ` or `σ` is a proper prefix of `τ`. -/
def Node.wpre (σ τ : Node A κ) : Prop :=
  σ = τ ∨ Node.pre A κ σ τ

theorem Node.pre.pos_lt {σ τ : Node A κ} (h : Node.pre A κ σ τ) : σ.pos < τ.pos :=
  h.1

theorem Node.pre.agree {σ τ : Node A κ} (h : Node.pre A κ σ τ)
    (q : Idx κ) (hq : q < σ.pos) :
    τ.seq ⟨q, lt_trans hq h.1⟩ = σ.seq ⟨q, hq⟩ :=
  h.2 q hq

/-- If two nodes agree below `σ.pos` and have equal `pos` (with `σ.pos ≤ τ.pos`
and, symmetrically, agreement), they are equal. Concretely: a weak prefix with
equal position is equality. -/
theorem Node.wpre_pos_eq {σ τ : Node A κ} (h : Node.wpre σ τ) (hpos : τ.pos ≤ σ.pos) :
    σ = τ := by
  rcases h with h | h
  · exact h
  · exact absurd h.1 (not_lt.mpr hpos)

/-- `Node.pre` is transitive. -/
theorem Node.pre.trans {ρ σ τ : Node A κ} (h1 : Node.pre A κ ρ σ)
    (h2 : Node.pre A κ σ τ) : Node.pre A κ ρ τ := by
  refine ⟨lt_trans h1.1 h2.1, ?_⟩
  intro q hq
  rw [h2.2 q (lt_trans hq h1.1), h1.2 q hq]

/-- Weak-prefix / proper-prefix composition. -/
theorem Node.wpre.trans_pre {ρ σ τ : Node A κ} (h1 : Node.wpre ρ σ)
    (h2 : Node.pre A κ σ τ) : Node.wpre ρ τ := by
  rcases h1 with rfl | h1
  · exact Or.inr h2
  · exact Or.inr (h1.trans h2)

/-
**Prefix nesting.**  If `ρ` is a weak prefix of `a`, `b` is comparable with
`a`, and `ρ.pos ≤ b.pos`, then `ρ` is a weak prefix of `b`.  (Prefixes of a
common node are nested by position.)
-/
theorem Node.wpre_of_comparable {ρ a b : Node A κ} (hρa : Node.wpre ρ a)
    (hcomp : Node.comparable a b) (hpos : ρ.pos ≤ b.pos) :
    Node.wpre ρ b := by
  rcases hρa with ( rfl | hρa ) <;> rcases hcomp with ( rfl | hcomp | hcomp ) <;> simp_all +decide [ Node.wpre ];
  · exact absurd hpos ( not_le_of_gt hcomp.1 );
  · exact Or.inr ( Node.pre.trans hρa hcomp );
  · cases lt_or_eq_of_le hpos <;> simp_all +decide [ pre ];
    · grind +suggestions;
    · cases ρ ; cases b ; aesop

/-
If `p` and `q` are comparable and both strictly longer than a coordinate `d`,
their entries at `d` agree.
-/
theorem Node.seqAt_eq_of_comparable {p q : Node A κ} (hcomp : Node.comparable p q)
    {d : Idx κ} (hp : d < p.pos) (hq : d < q.pos) :
    p.seq ⟨d, hp⟩ = q.seq ⟨d, hq⟩ := by
  rcases hcomp with ( rfl | hcomp | hcomp );
  · grind;
  · exact hcomp.agree d hp ▸ rfl;
  · exact hcomp.agree d hq ▸ rfl

/-! ### Lift-edge structure -/

/-- The three first-coordinates of a lift edge `{(σ,x),(σ,y),(τ,z)}` lie in
`{σ, τ}`. -/
theorem liftEdge_fst_mem {σ τ : Node A κ} {x y z : α}
    {p : Node A κ × α} (hp : p ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α))) :
    p.1 = σ ∨ p.1 = τ := by
  rcases hp with rfl | rfl | rfl
  · left; rfl
  · left; rfl
  · right; rfl

/-- Any two vertices lying in a common edge of `F` whose `f`-image is a lift edge
have comparable sequence nodes. -/
theorem bergeEdge_nodes_comparable {F : FTS} {f : F.V → Node A κ × α}
    (e : Finset F.V) (he : (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    {u w : F.V} (hu : u ∈ e) (hw : w ∈ e) :
    Node.comparable (f u).1 (f w).1 := by
  obtain ⟨σ, τ, x, y, z, hpre, hseq, hset⟩ := he
  have hfu : f u ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α)) := by
    rw [← hset]; exact ⟨u, hu, rfl⟩
  have hfw : f w ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α)) := by
    rw [← hset]; exact ⟨w, hw, rfl⟩
  rcases liftEdge_fst_mem hfu with hu' | hu' <;> rcases liftEdge_fst_mem hfw with hw' | hw' <;>
    rw [Node.comparable, hu', hw']
  · left; rfl
  · right; left; exact hpre
  · right; right; exact hpre
  · left; rfl

/-
**Base pair of a rising edge.**  If an edge `e` of `F` has `f`-image a lift
edge, and `u, w ∈ e` with `(f u).1` a proper prefix of `(f w).1`, then the base
pair of the lift edge sits at node `(f u).1`: there are `x ≠ y` with
`(f w).1.seq ⟨(f u).1.pos, _⟩ = s(x, y)` and both `((f u).1, x)` and
`((f u).1, y)` lie in `f '' e`.
-/
theorem rising_base {F : FTS} {f : F.V → Node A κ × α}
    (e : Finset F.V) (he : (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    {u w : F.V} (hu : u ∈ e) (hw : w ∈ e) (hpre : Node.pre A κ (f u).1 (f w).1) :
    ∃ x y : α, x ≠ y ∧
      ((f w).1.seq ⟨(f u).1.pos, hpre.1⟩ : Sym2 α) = s(x, y) ∧
      ((f u).1, x) ∈ (f '' (↑e : Set F.V)) ∧ ((f u).1, y) ∈ (f '' (↑e : Set F.V)) := by
  obtain ⟨ σ', τ', a, b, cc, hpre', hseq', hset ⟩ := he;
  -- From `hpre`, we have `(f u).1 = σ'` and `(f w).1 = τ'`.
  have h_eq : (f u).1 = σ' ∧ (f w).1 = τ' := by
    have h_eq : (f u).1 ∈ ({σ', τ'} : Set (Node A κ)) ∧ (f w).1 ∈ ({σ', τ'} : Set (Node A κ)) := by
      exact ⟨ by simpa using! liftEdge_fst_mem ( hset ▸ Set.mem_image_of_mem f hu ), by simpa using! liftEdge_fst_mem ( hset ▸ Set.mem_image_of_mem f hw ) ⟩;
    cases h_eq.1 <;> cases h_eq.2 <;> simp_all +decide [ Node.pre ];
    exact absurd hpre.choose ( not_lt_of_gt hpre'.1 );
  have := ( τ'.seq ⟨ σ'.pos, hpre'.1 ⟩ ) |>.2; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
  exact ⟨ a, b, this.ne, by aesop ⟩

/-- Sym2-level version of `seqAt_eq_of_comparable`. -/
theorem Node.seqAt_Sym2_eq_of_comparable {p q : Node A κ} (hcomp : Node.comparable p q)
    {d : Idx κ} (hp : d < p.pos) (hq : d < q.pos) :
    ((p.seq ⟨d, hp⟩ : Sym2 α)) = ((q.seq ⟨d, hq⟩ : Sym2 α)) :=
  congrArg (fun e : A.edgeSet => (e : Sym2 α)) (Node.seqAt_eq_of_comparable hcomp hp hq)

/-
**Cyclic induction on `ZMod m`.**  A predicate holding at one point and
closed under `i ↦ i + 1` holds everywhere.
-/
theorem zmod_cyclic_induction {m : ℕ} [NeZero m] {P : ZMod m → Prop} (j0 : ZMod m)
    (hj0 : P j0) (hstep : ∀ i, P i → P (i + 1)) (i : ZMod m) : P i := by
  have h_ind : ∀ n : ℕ, P (j0 + n) := by
    intro n; induction n <;> simp_all +decide [ ← add_assoc ] ;
  convert! h_ind ( i - j0 |> ZMod.val ) ; aesop;

/-- Consecutive vertices on a Berge cycle have comparable sequence nodes. -/
theorem consecutive_comparable {F : FTS} {f : F.V → Node A κ × α}
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (c : BergeCycle F) (i : ZMod c.m) :
    Node.comparable (f (c.v i)).1 (f (c.v (i + 1))).1 :=
  bergeEdge_nodes_comparable (c.e i).1 (hfe _ (c.e i).2) (c.mem_left i) (c.mem_right i)

/-
**Value constant along a comparable walk.**  If consecutive nodes `g i, g (i+1)`
are comparable and every node `g (start + j)` (for `j ≤ n`) properly extends `σ`,
then the `Sym2`-value at coordinate `σ.pos` is the same at step `n` as at step
`0`.
-/
theorem seqAt_const_along {m : ℕ} (g : ZMod m → Node A κ)
    (hcomp : ∀ i : ZMod m, Node.comparable (g i) (g (i + 1)))
    (σ : Node A κ) (start : ZMod m) (n : ℕ)
    (hpre : ∀ j : ℕ, j ≤ n → Node.pre A κ σ (g (start + (j : ZMod m)))) :
    ((g (start + (n : ZMod m))).seq ⟨σ.pos, (hpre n le_rfl).1⟩ : Sym2 α)
      = ((g (start + ((0 : ℕ) : ZMod m))).seq ⟨σ.pos, (hpre 0 (Nat.zero_le n)).1⟩ : Sym2 α) := by
  induction' n with n ih;
  · rfl;
  · convert! ih ( fun j hj => hpre j ( Nat.le_succ_of_le hj ) ) using 1;
    convert! Node.seqAt_Sym2_eq_of_comparable _ _ _ using 1;
    convert! hcomp ( start + n ) |> fun h => h.symm using 1 ; push_cast ; ring;
    simp +decide [ add_comm, Node.comparable ];
    grind

/-
**First return.**  If `P` fails at `start` but holds at some `start + t`,
there is a least positive step `n0 ≤ m - 1` with `P (start + n0)` and `P` failing
at every earlier step.
-/
theorem exists_first_return {m : ℕ} [NeZero m] (P : ZMod m → Prop)
    (start : ZMod m) (hstart : ¬ P start)
    (hex : ∃ t : ℕ, P (start + (t : ZMod m))) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ n0 ≤ m - 1 ∧ P (start + (n0 : ZMod m)) ∧
      ∀ j : ℕ, j < n0 → ¬ P (start + (j : ZMod m)) := by
  obtain ⟨t, ht⟩ := hex
  have ht_lt : t % m < m := by
    exact Nat.mod_lt _ ( NeZero.pos m );
  have h_exists_n0 : ∃ n0, 1 ≤ n0 ∧ n0 ≤ m - 1 ∧ P (start + (n0 : ZMod m)) := by
    refine' ⟨ t % m, Nat.pos_of_ne_zero _, Nat.le_sub_one_of_lt ht_lt, _ ⟩;
    · contrapose! hstart; simp_all ;
      rw [ ← Nat.dvd_iff_mod_eq_zero ] at hstart; obtain ⟨ k, hk ⟩ := hstart; simp_all ;
    · simpa [ ZMod.natCast_mod ] using! ht;
  obtain ⟨n0, hn0⟩ : ∃ n0, n0 ∈ {n | 1 ≤ n ∧ n ≤ m - 1 ∧ P (start + (n : ZMod m))} ∧ ∀ n ∈ {n | 1 ≤ n ∧ n ≤ m - 1 ∧ P (start + (n : ZMod m))}, n0 ≤ n := by
    apply_rules [ Set.exists_min_image ];
    exact Set.finite_iff_bddAbove.mpr ⟨ m - 1, fun n hn => hn.2.1 ⟩;
  exact ⟨ n0, hn0.1.1, hn0.1.2.1, hn0.1.2.2, fun j hj hj' => not_lt_of_ge ( hn0.2 j ⟨ Nat.pos_of_ne_zero fun h => by aesop, Nat.le_trans ( Nat.le_of_lt hj ) hn0.1.2.1, hj' ⟩ ) hj ⟩

/-
**Base adjacency.**  If two distinct vertices `u, w` of an edge `e` of `F`
with `f`-image a lift edge have the *same* sequence node, then their second
coordinates are adjacent in `A` (they are the two base vertices of the lift
edge).
-/
theorem base_adj {F : FTS} {f : F.V → Node A κ × α} (hf : Function.Injective f)
    (e : Finset F.V) (he : (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    {u w : F.V} (hu : u ∈ e) (hw : w ∈ e) (huw : u ≠ w)
    (hnode : (f u).1 = (f w).1) :
    A.Adj (f u).2 (f w).2 := by
  obtain ⟨ σ, τ, x, y, z, hpre, hseq, hset ⟩ := he;
  -- From `hset`, the image of `e` contains these three nodes.
  have hfu : f u ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α)) := by
    exact hset ▸ Set.mem_image_of_mem _ hu
  have hfw : f w ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α)) := by
    grind;
  by_cases h : ( f u ).1 = τ <;> simp_all +decide [ Function.Injective.eq_iff hf ];
  · grind +suggestions;
  · rcases hfu with ( hfu | hfu | hfu ) <;> rcases hfw with ( hfw | hfw | hfw ) <;> simp_all +decide;
    · exact False.elim ( huw ( hf ( hfu.trans hfw.symm ) ) );
    · replace hseq := congr_arg ( fun s => s ∈ SimpleGraph.edgeSet A ) hseq ; simp_all +decide [ SimpleGraph.mem_edgeSet ];
    · convert! SimpleGraph.Adj.symm ( show A.Adj x y from ?_ ) using 1;
      convert! ( τ.seq ⟨ σ.pos, hpre.1 ⟩ ).2 using 1;
      simp +decide [ hseq, SimpleGraph.mem_edgeSet ];
    · exact False.elim ( huw ( hf ( hfu.trans hfw.symm ) ) )

/-! ### The collapse argument -/

/-- **Cycle collapse** (`lem:cycle-collapse`).  If a finite linear triple system
`F` embeds into `Lift(A,κ)` via an injective `f` sending each edge to a lift
edge, then on every Berge cycle all sequence nodes are equal. -/
theorem cycle_collapse {F : FTS} (hlin : F.Linear) (f : F.V → Node A κ × α)
    (hf : Function.Injective f)
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (c : BergeCycle F) (i j : ZMod c.m) :
    (f (c.v i)).1 = (f (c.v j)).1 := by
  haveI : NeZero c.m := ⟨by have := c.hm; omega⟩
  -- Step 1: minimal node
  obtain ⟨j0, -, hj0min⟩ := Finset.exists_min_image Finset.univ
    (fun t => (f (c.v t)).1.pos) ⟨i, Finset.mem_univ i⟩
  simp only [Finset.mem_univ, forall_true_left] at hj0min
  set σ := (f (c.v j0)).1 with hσdef
  -- Step 2: all weak-prefix σ
  have hwpre : ∀ t, Node.wpre σ (f (c.v t)).1 := fun t =>
    zmod_cyclic_induction j0 (Or.inl rfl)
      (fun i hi => Node.wpre_of_comparable hi (consecutive_comparable hfe c i) (hj0min (i+1))) t
  suffices hall : ∀ t, (f (c.v t)).1 = σ by rw [hall i, hall j]
  intro t
  by_contra hne
  -- Step 3: rising index
  obtain ⟨k, hk, hk1⟩ : ∃ k, (f (c.v k)).1 = σ ∧ (f (c.v (k+1))).1 ≠ σ := by
    by_contra hall2
    push_neg at hall2
    exact hne (zmod_cyclic_induction (P := fun s => (f (c.v s)).1 = σ) j0 rfl
      (fun s hs => hall2 s hs) t)
  have hkpre : Node.pre A κ σ (f (c.v (k+1))).1 :=
    (hwpre (k+1)).resolve_left (fun h => hk1 h.symm)
  -- Step 4: first return
  have hex : ∃ n : ℕ, (f (c.v (k+1+(n:ZMod c.m)))).1 = σ := by
    refine ⟨(j0-(k+1)).val, ?_⟩
    have he : k+1+(((j0-(k+1)).val : ℕ):ZMod c.m) = j0 := by
      rw [ZMod.natCast_zmod_val]; ring
    rw [he]
  obtain ⟨n0, h1n0, hn0m, hPn0, hbefore⟩ :=
    exists_first_return (fun s => (f (c.v s)).1 = σ) (k+1) hk1 hex
  -- Step 5: run pre and falling index
  have hrunpre : ∀ jj : ℕ, jj < n0 → Node.pre A κ σ (f (c.v (k+1+(jj:ZMod c.m)))).1 :=
    fun jj hjj => (hwpre _).resolve_left (fun h => hbefore jj hjj h.symm)
  set kf := k+1+((n0-1:ℕ):ZMod c.m) with hkfdef
  have hcast : (n0 : ZMod c.m) = ((n0 - 1 : ℕ) : ZMod c.m) + 1 := by
    have h1 : ((n0 - 1 : ℕ) : ZMod c.m) + 1 = (((n0 - 1) + 1 : ℕ) : ZMod c.m) := by norm_cast
    rw [h1, Nat.sub_add_cancel h1n0]
  have hkf1_eq : kf + 1 = k+1+(n0:ZMod c.m) := by rw [hkfdef, hcast]; ring
  have hνkf1 : (f (c.v (kf+1))).1 = σ := by rw [hkf1_eq]; exact hPn0
  have hνkf_pre : Node.pre A κ σ (f (c.v kf)).1 := by
    rw [hkfdef]; exact hrunpre (n0-1) (by omega)
  -- Step 6: base pairs at the two boundary edges
  obtain ⟨x1, y1, hxy1, hval1, hmx1, hmy1⟩ :=
    rising_base (c.e k).1 (hfe _ (c.e k).2) (c.mem_left k) (c.mem_right k) (hk.symm ▸ hkpre)
  obtain ⟨x2, y2, hxy2, hval2, hmx2, hmy2⟩ :=
    rising_base (c.e kf).1 (hfe _ (c.e kf).2) (c.mem_right kf) (c.mem_left kf) (hνkf1.symm ▸ hνkf_pre)
  -- rewrite the memberships and base-pair values to base node σ
  simp only [hk] at hval1 hmx1 hmy1
  simp only [hνkf1] at hval2 hmx2 hmy2
  -- Step 7: the two base pairs are equal Sym2 values (constant along the run)
  have hpre' : ∀ jj : ℕ, jj ≤ n0 - 1 →
      Node.pre A κ σ ((fun s => (f (c.v s)).1) (k+1+(jj:ZMod c.m))) :=
    fun jj hjj => hrunpre jj (by omega)
  have hca := seqAt_const_along (fun s => (f (c.v s)).1)
    (consecutive_comparable hfe c) σ (k+1) (n0-1) hpre'
  have hnode_val : ∀ {p q : Node A κ} {hp : σ.pos < p.pos} {hq : σ.pos < q.pos},
      p = q → ((p.seq ⟨σ.pos, hp⟩ : Sym2 α)) = ((q.seq ⟨σ.pos, hq⟩ : Sym2 α)) := by
    rintro p q hp hq rfl; rfl
  have hsym2 : s(x1, y1) = s(x2, y2) := by
    rw [← hval1, ← hval2]
    refine (hnode_val (p := (f (c.v (k+1))).1) (q := (f (c.v (k+1+((0:ℕ):ZMod c.m)))).1)
      (hq := (hpre' 0 (Nat.zero_le _)).1) (by simp)).trans ?_
    exact hca.symm.trans (hnode_val (p := (f (c.v (k+1+((n0-1:ℕ):ZMod c.m)))).1)
      (q := (f (c.v kf)).1) (hp := (hpre' (n0-1) le_rfl).1) (by rw [hkfdef]))
  -- Step 8: same base pair as a set
  have hmemx1kf : (σ, x1) ∈ (f '' (↑(c.e kf).1 : Set F.V)) := by
    rw [Sym2.eq_iff] at hsym2
    rcases hsym2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmx2
    · exact hmy2
  have hmemy1kf : (σ, y1) ∈ (f '' (↑(c.e kf).1 : Set F.V)) := by
    rw [Sym2.eq_iff] at hsym2
    rcases hsym2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmy2
    · exact hmx2
  -- Step 9: linearity contradiction
  obtain ⟨ux, huxk, hfux⟩ := hmx1
  obtain ⟨ux', huxkf, hfux'⟩ := hmemx1kf
  obtain ⟨uy, huyk, hfuy⟩ := hmy1
  obtain ⟨uy', huykf, hfuy'⟩ := hmemy1kf
  have huxeq : ux = ux' := hf (by rw [hfux, hfux'])
  have huyeq : uy = uy' := hf (by rw [hfuy, hfuy'])
  have huxy : ux ≠ uy := by
    intro h; apply hxy1
    have hfeq : f ux = f uy := by rw [h]
    rw [hfux, hfuy] at hfeq
    exact (Prod.ext_iff.mp hfeq).2
  have hkne : k ≠ kf := by
    intro h
    rw [hkfdef] at h
    have hz : (n0 : ZMod c.m) = 0 := by rw [hcast]; linear_combination -h
    have hdvd : c.m ∣ n0 := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hedgene : (c.e k).1 ≠ (c.e kf).1 := by
    intro h
    exact hkne (c.einj (Subtype.ext h))
  have hcard : 1 < ((c.e k).1 ∩ (c.e kf).1).card := by
    refine Finset.one_lt_card.mpr ⟨ux, ?_, uy, ?_, huxy⟩
    · exact Finset.mem_inter.mpr ⟨huxk, huxeq ▸ huxkf⟩
    · exact Finset.mem_inter.mpr ⟨huyk, huyeq ▸ huykf⟩
  have hle := hlin (c.e k).1 (c.e k).2 (c.e kf).1 (c.e kf).2 hedgene
  omega

/-- **Bridge incidence from an embedding** (necessity part of the bridge-trace
theorem).  If a finite linear triple system `F` embeds into `Lift(A,κ)` via an
injective `f`, then every edge `ed` of `F` is incident with a *bridge*: the
incidence at the apex vertex (whose image is the apex `(τ,z)` of the lift edge)
lies on no Berge cycle.  This is one of the three intrinsic conditions of the
classification, and the key use of `cycle_collapse`. -/
theorem exists_bridge_incidence {F : FTS} (hlin : F.Linear) (f : F.V → Node A κ × α)
    (hf : Function.Injective f)
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (ed : {e : Finset F.V // e ∈ F.edges}) :
    ∃ w ∈ ed.1, IsBridgeInc F w ed := by
  obtain ⟨σ, τ, x, y, z, hpre, hseq, hset⟩ := hfe ed.1 ed.2
  -- the apex host vertex (τ,z) has a preimage `w ∈ ed.1`
  have hmem : ((τ, z) : Node A κ × α) ∈ f '' (↑ed.1 : Set F.V) := by
    rw [hset]; right; right; rfl
  obtain ⟨w, hw, hfw⟩ := hmem
  refine ⟨w, hw, hw, ?_⟩
  rintro ⟨c, i, hei, hvi⟩
  haveI : Fact (1 < c.m) := ⟨by have := c.hm; omega⟩
  -- the other displayed vertex `w'` of the Berge cycle at edge `ed`
  have hcc := cycle_collapse hlin f hf hfe c i (i + 1)
  have hvne : c.v i ≠ c.v (i + 1) := by
    intro h
    have hii : i = i + 1 := c.vinj h
    exact zero_ne_one (by linear_combination hii : (0 : ZMod c.m) = 1)
  -- `w` has apex node `τ`
  have hwnode : (f w).1 = τ := by rw [hfw]
  -- identify the other vertex `w'` in `ed.1`, distinct from `w`, with base node `σ`
  have hbase : ∀ v : F.V, v ∈ ed.1 → v ≠ w → (f v).1 = σ := by
    intro v hv hvw
    have hfv : f v ∈ f '' (↑ed.1 : Set F.V) := ⟨v, hv, rfl⟩
    rw [hset] at hfv
    rcases hfv with h | h | h
    · rw [h]
    · rw [h]
    · exact absurd (hf (by rw [h, hfw])) hvw
  -- both displayed vertices lie in `ed.1` and one of them is `w`
  have hi_mem : c.v i ∈ ed.1 := by rw [← hei]; exact c.mem_left i
  have hi1_mem : c.v (i + 1) ∈ ed.1 := by rw [← hei]; exact c.mem_right i
  -- derive σ = τ, contradicting the strict prefix
  have hστ : σ = τ := by
    rcases hvi with hvi | hvi
    · -- w = c.v i, so w' = c.v (i+1)
      have hw' : (f (c.v (i + 1))).1 = σ :=
        hbase _ hi1_mem (fun h => hvne (hvi.trans h.symm))
      rw [← hw', ← hcc, hvi, hwnode]
    · -- w = c.v (i+1), so w' = c.v i
      have hw' : (f (c.v i)).1 = σ :=
        hbase _ hi_mem (fun h => hvne (h.trans hvi.symm))
      rw [← hw', hcc, hvi, hwnode]
  exact absurd hpre.1 (by rw [hστ]; exact lt_irrefl _)

/-
**Berge cycle to graph cycle** (`lem:cycle-selector`, host form).  If a finite
linear triple system `F` embeds into `Lift(A,κ)` and has a Berge cycle of length
`m`, then `A` contains an `m`-cycle: an injective `v : ZMod m → α` with consecutive
vertices adjacent.  (Follows from `cycle_collapse`: all cycle vertices share a
node `σ`, and each cycle edge's base pair is an actual edge of `A`.)  This is the
case-(iii) input of the spectrum construction.
-/
theorem lift_bergeCycle_graphCycle {F : FTS} (hlin : F.Linear) (f : F.V → Node A κ × α)
    (hf : Function.Injective f)
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (c : BergeCycle F) :
    ∃ v : ZMod c.m → α, Function.Injective v ∧ ∀ i, A.Adj (v i) (v (i + 1)) := by
  -- Show that `v` is injective.
  have hv_inj : Function.Injective (fun i => (f (c.v i)).2) := by
    intro i j hij
    have hnode : (f (c.v i)).1 = (f (c.v j)).1 := by
      convert! cycle_collapse hlin f hf hfe c i j using 1;
    have := hf ( Prod.ext hnode hij ) ; simp_all +decide [ c.vinj.eq_iff ] ;
  refine' ⟨ _, hv_inj, _ ⟩;
  intro i
  have h_edge : (f '' (↑(c.e i).1 : Set F.V)) ∈ (liftHG A κ).edges := by
    exact hfe _ ( c.e i |>.2 )
  have h_nodes : (f (c.v i)).1 = (f (c.v (i + 1))).1 := by
    exact cycle_collapse hlin f hf hfe c i ( i + 1 )
  exact base_adj hf (c.e i).1 h_edge (c.mem_left i) (c.mem_right i) (by
  intro h_eq
  have h_contra : i = i + 1 := by
    exact c.vinj h_eq
  have h_contra' : (0 : ZMod c.m) = 1 := by
    linear_combination' h_contra
  have h_contra'' : ¬(0 : ZMod c.m) = 1 := by
    haveI : Fact (1 < c.m) := ⟨by linarith [c.hm]⟩; exact zero_ne_one;
  exact h_contra'' h_contra') h_nodes

/-- **A lift embedding yields a bridge selector.**  If a finite linear triple
system `F` embeds into `Lift(A,κ)`, then `F` has a bridge selector.  Hence, by
contraposition, a finite linear system with *no* bridge selector cannot embed
into any lift `Lift(A,κ)` — this is the case-(ii) input of the spectrum
construction (`thm:classification`, `thm:spectrum`). -/
theorem bridgeSelector_of_embeds_lift {F : FTS} (hlin : F.Linear)
    (h : F.Embeds (liftHG A κ)) : Nonempty (BridgeSelector F) := by
  obtain ⟨f, hf, hfe⟩ := h
  refine ⟨⟨fun ed => (exists_bridge_incidence hlin f hf hfe ed).choose, fun ed => ?_⟩⟩
  exact (exists_bridge_incidence hlin f hf hfe ed).choose_spec.2

/-- **Case (ii) omission** (`thm:classification`, `thm:spectrum`).  A finite
linear triple system with *no* bridge selector is omitted by every lift
`Lift(A,κ)`.  (Contrapositive of `bridgeSelector_of_embeds_lift`.) -/
theorem lift_omits_of_no_bridgeSelector {F : FTS} (hlin : F.Linear)
    (hns : ¬ Nonempty (BridgeSelector F)) : ¬ F.Embeds (liftHG A κ) :=
  fun h => hns (bridgeSelector_of_embeds_lift hlin h)

/-- **Case (iii) omission** (`thm:classification`, `thm:spectrum`).  If a finite
linear triple system `F` has a Berge cycle of length `m` and the graph `A`
contains no `m`-cycle, then `Lift(A,κ)` omits `F`.  Combined with a graph of
high odd girth (`E2`) this handles the odd-Berge-cycle case. -/
theorem lift_omits_of_bergeCycle {F : FTS} (hlin : F.Linear) (c : BergeCycle F)
    (hA : ¬ ∃ v : ZMod c.m → α, Function.Injective v ∧ ∀ i, A.Adj (v i) (v (i + 1))) :
    ¬ F.Embeds (liftHG A κ) := by
  rintro ⟨f, hf, hfe⟩
  exact hA (lift_bergeCycle_graphCycle hlin f hf hfe c)

end Erdos1177

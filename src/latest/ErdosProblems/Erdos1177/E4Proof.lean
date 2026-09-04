-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.EHBase
import ErdosProblems.Erdos1177.External

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# E4 (Reiher's Theorem 1.2, case `k = 3`): `K^{(3)}_{n,n}` is obligatory

This file discharges the literature input `E4_Reiher`: for every `n`, the
private-vertex expansion `K^{(3)}_{n,n}` of the complete bipartite graph is
obligatory, i.e. it occurs in every triple system of uncountable chromatic
number.

Reference: C. Reiher, *Obligatory hypergraphs*, arXiv:2403.11223, Theorem 1.2
(the `k = 3` case, whose `k = 2` base case `K_{n,n}` is the Erdős–Hajnal theorem
proved in `ErdosProblems.Erdos1177.EHBase` as `eh_hasKmm`).

## Strategy

`HasK3nn H n` records a copy of `K^{(3)}_{n,n}` inside a host `H` (left cores
`L`, right cores `R`, private vertices `P`, all distinct, with each triple
`{L i, R j, P i j}` an edge).  We prove:

* `hasK3nn_embeds` : `HasK3nn H n → (graphExpansion K_{n,n}).Embeds H` (bookkeeping).
* `hasK3nn_of_uncountable` : every uncountably-chromatic triple system has a
  `K^{(3)}_{n,n}` (Reiher's delta-system argument, using `eh_hasKmm`).
* `e4_Reiher` : hence `E4_Reiher`.
-/

open Cardinal

namespace Erdos1177

universe u

variable {W : Type u}

/-- A copy of `K^{(3)}_{n,n}` inside a host hypergraph `H`: `n` left cores, `n`
right cores, and `n²` private vertices, all distinct, with each triple
`{L i, R j, P i j}` an edge of `H`. -/
def HasK3nn (H : Hypergraph W) (n : ℕ) : Prop :=
  ∃ f : (Fin n ⊕ Fin n) ⊕ (Fin n × Fin n) → W, Function.Injective f ∧
    ∀ i j : Fin n,
      ({f (Sum.inl (Sum.inl i)), f (Sum.inl (Sum.inr j)), f (Sum.inr (i, j))} : Set W)
        ∈ H.edges

/-
Every edge of `K_{n,n} = completeBipartiteGraph (Fin n) (Fin n)` joins a
left vertex `Sum.inl i` to a right vertex `Sum.inr j`.
-/
open Classical in
theorem cb_edge_exists {n : ℕ} (e : Sym2 (Fin n ⊕ Fin n))
    (he : e ∈ (completeBipartiteGraph (Fin n) (Fin n)).edgeFinset) :
    ∃ i j : Fin n, e = s(Sum.inl i, Sum.inr j) := by
  rcases e with ⟨ ⟨ a, b ⟩ ⟩;
  cases a <;> cases b <;> simp_all +decide [ completeBipartiteGraph ]

open Classical in
/-- **Packaging.**  A `K^{(3)}_{n,n}` copy yields an embedding of the graph
expansion `graphExpansion K_{n,n}` into `H`. -/
theorem hasK3nn_embeds (H : Hypergraph W) (n : ℕ) (h : HasK3nn H n) :
    (graphExpansion (completeBipartiteGraph (Fin n) (Fin n))).Embeds H := by
  obtain ⟨ f, hf, hedge ⟩ := h;
  -- Define the embedding `g` by extending `f` to the new vertices.
  obtain ⟨g, hg⟩ : ∃ g : (Fin n ⊕ Fin n) ⊕ {e : Sym2 (Fin n ⊕ Fin n) // e ∈ (completeBipartiteGraph (Fin n) (Fin n)).edgeFinset} → W, Function.Injective g ∧ ∀ e : Fin n, ∀ f' : Fin n, g (Sum.inl (Sum.inl e)) = f (Sum.inl (Sum.inl e)) ∧ g (Sum.inl (Sum.inr f')) = f (Sum.inl (Sum.inr f')) ∧ g (Sum.inr ⟨s(Sum.inl e, Sum.inr f'), by
    simp +decide [ completeBipartiteGraph ]⟩) = f (Sum.inr (e, f')) := by
    refine' ⟨ fun x => Sum.elim ( fun x => Sum.elim ( fun x => f ( Sum.inl ( Sum.inl x ) ) ) ( fun x => f ( Sum.inl ( Sum.inr x ) ) ) x ) ( fun x => f ( Sum.inr ( x.val |> fun x => if h : ∃ i j, x = s(Sum.inl i, Sum.inr j) then ( h.choose, h.choose_spec.choose ) else ( ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩, ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩ ) ) ) ) x, _, _ ⟩;
    · intro x y hxy;
      grind +suggestions;
    · simp +decide [ hf.eq_iff ]
  generalize_proofs at *;
  refine' ⟨ g, hg.1, _ ⟩;
  intro e he; simp_all +decide [ graphExpansion ] ;
  obtain ⟨ a, ha, rfl ⟩ := he; simp +decide [ ← hg.2, Set.image_insert_eq, Set.image_singleton ] ;
  obtain ⟨ i, j, hi, hj, rfl ⟩ := cb_edge_exists a ( by simpa using! ha ) ; simp +decide [ hg.2 i j ] ;
  convert! hedge i j using 1;
  rw [ ← hg.2 i j |>.1, ← hg.2 i j |>.2.1 ];
  have := Quot.out_eq ( s(Sum.inl i, Sum.inr j) : Sym2 (Fin n ⊕ Fin n) ) ; rw [ Sym2.eq_iff ] at this; aesop;

/-! ### Colourability bridge for hypergraphs -/

/-- A hypergraph is *countably colourable* if it has a proper `ℕ`-colouring. -/
def HGCountColorable (H : Hypergraph W) : Prop :=
  ∃ c : W → ℕ, H.ProperColoring c

/-
`HGCountColorable` is exactly `ℵ₀`-colourability.
-/
theorem hgCountColorable_iff (H : Hypergraph W) :
    HGCountColorable H ↔ H.ColorableBy ℵ₀ := by
  constructor;
  · intro h;
    convert! colorableBy_aleph0_of_countable H _ _;
    exact ULift ℕ;
    exact Cardinal.mk_le_aleph0;
    exact fun x => ⟨ h.choose x ⟩;
    intro e he; obtain ⟨ u, hu, v, hv, huv ⟩ := h.choose_spec e he; use u, hu, v, hv; aesop;
  · intro h;
    convert! h using 1;
    constructor <;> intro h <;> rcases h with ⟨ c, hc ⟩;
    · grind;
    · obtain ⟨ f, hf ⟩ := Cardinal.eq.1 ( Cardinal.mk_out ℵ₀ );
      use fun x => ( f ( c x ) ).down;
      intro e he; obtain ⟨ u, hu, v, hv, huv ⟩ := hc e he; use u, hu, v, hv; simp_all +decide [ Function.LeftInverse, Function.RightInverse ] ;
      grind

/-! ### Delta systems -/

/-- `f` is the *root* of a delta system of size `≥ t`: there are `≥ t` edges, all
containing `f`, pairwise meeting exactly in `f`. -/
def IsDeltaRoot (H : Hypergraph W) (t : ℕ) (f : Set W) : Prop :=
  ∃ D : Set (Set W), D ⊆ H.edges ∧ (t : Cardinal) ≤ #D ∧ (∀ e ∈ D, f ⊆ e) ∧
    (∀ e₁ ∈ D, ∀ e₂ ∈ D, e₁ ≠ e₂ → e₁ ∩ e₂ = f)

/-- The *roots graph* `H^{(2)}`: `x, y` are adjacent iff `{x, y}` is a delta-system
root. -/
def rootsGraph (H : Hypergraph W) (t : ℕ) : SimpleGraph W :=
  SimpleGraph.fromRel (fun x y => IsDeltaRoot H t ({x, y} : Set W))

/-
**Single delta-root extension.**  If `f` is a delta-system root (size `≥ t`)
and `g` is a set with fewer than `t` elements containing `f`, then some edge `e`
contains `f` and meets `g` exactly in `f`.
-/
theorem deltaRoot_extend (H : Hypergraph W) (t : ℕ) (f g : Set W)
    (hf : IsDeltaRoot H t f) (hg : #g < (t : Cardinal)) (hfg : f ⊆ g) :
    ∃ e ∈ H.edges, f ⊆ e ∧ e ∩ g = f := by
  obtain ⟨ D, hDsub, hDcard, hDf, hDpair ⟩ := hf;
  contrapose! hg;
  -- For each edge `e ∈ D`, define a vertex `v e ∈ (e ∩ g) \ f`.
  have hv : ∀ e ∈ D, ∃ v : W, v ∈ (e ∩ g) \ f := by
    exact fun e he => Set.exists_of_ssubset ( lt_of_le_of_ne ( by aesop_cat ) ( Ne.symm ( hg e ( hDsub he ) ( hDf e he ) ) ) );
  choose! v hv₁ hv₂ using hv;
  refine' le_trans hDcard _;
  refine' ⟨ fun x => ⟨ v x.1 x.2, _ ⟩, fun x y hxy => _ ⟩;
  grind;
  grind +extAll

/-
**Greedy private-vertex assignment.**  Given cores `a, b` inside a small
`Core` set, all of whose `n²` pairs are delta roots of size `≥ 3n²+1`, one can
choose an injective family of private vertices `P`, avoiding `Core`, so that each
`{a i, b j, P (i,j)}` is an edge.  Proof: greedily extend one pair at a time by
`deltaRoot_extend`; the accumulated used set always has `< 3n²+1` elements.
-/
set_option maxHeartbeats 2000000 in
theorem exists_private_assignment (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (a b : Fin n → W) (Core : Finset W)
    (hCa : ∀ i, a i ∈ Core) (hCb : ∀ j, b j ∈ Core) (hCard : Core.card ≤ 2 * n)
    (hab : ∀ i j, a i ≠ b j)
    (hroot : ∀ i j, IsDeltaRoot H (3 * n ^ 2 + 1) ({a i, b j} : Set W)) :
    ∃ P : Fin n × Fin n → W, Function.Injective P ∧ (∀ p, P p ∉ Core) ∧
      ∀ p, ({a p.1, b p.2, P p} : Set W) ∈ H.edges := by
  rcases n with ( _ | n ) <;> simp_all +decide only [IsEmpty.forall_iff, and_self, and_true, Prod.forall];
  · exact ⟨ fun _ => by aesop, by aesop_cat ⟩;
  · have hkey : ∀ s : Finset (Fin (n + 1) × Fin (n + 1)), ∃ P : Fin (n + 1) × Fin (n + 1) → W, Set.InjOn P s ∧ (∀ p ∈ s, P p ∉ Core) ∧ (∀ p ∈ s, ({a p.1, b p.2, P p} : Set W) ∈ H.edges) := by
      intro s
      induction' s using Finset.induction with p s ih;
      · exact ⟨ fun _ => a 0, by simp +decide [ Set.InjOn ] ⟩;
      · obtain ⟨ P, hP₁, hP₂, hP₃ ⟩ := ‹_›;
        -- Let's choose a new vertex $w$ for $p$ that is not in $Core$ and not in the image of $P$ on $s$.
        obtain ⟨w, hw⟩ : ∃ w : W, w ∉ Core ∧ w ∉ Set.image P s ∧ ({a p.1, b p.2, w} : Set W) ∈ H.edges := by
          have := deltaRoot_extend H ( 3 * ( n + 1 ) ^ 2 + 1 ) { a p.1, b p.2 } ( Core ∪ P '' s ) ( hroot p.1 p.2 ) ?_ ?_ <;> simp_all +decide only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one,
    Set.mem_image, SetLike.mem_coe, Prod.exists, not_exists, not_and];
          · obtain ⟨ e, he₁, he₂, he₃ ⟩ := this; simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
            obtain ⟨w, hw⟩ : ∃ w : W, w ∈ e ∧ w ≠ a p.1 ∧ w ≠ b p.2 := by
              have := hts e he₁; simp_all +decide only [ne_eq] ;
              contrapose! this;
              rw [ show e = { a p.1, b p.2 } from Set.ext fun x => by by_cases hx : x = a p.1 <;> specialize this x <;> aesop ] ; simp +decide [ Set.ncard_pair, hab ];
            refine' ⟨ w, _, _, _ ⟩;
            · grind;
            · grind +ring;
            · convert! he₁ using 1;
              have := hts e he₁; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
              rw [ Set.ncard_eq_three ] at this;
              grind;
          · refine' lt_of_le_of_lt ( Cardinal.mk_le_mk_of_subset _ ) _;
            exact ↑Core ∪ P '' ↑s;
            · exact Set.Subset.rfl;
            · refine' lt_of_le_of_lt ( Cardinal.mk_le_mk_of_subset _ ) _;
              exact Set.range ( fun x : Core ⊕ s => x.elim ( fun x => x.val ) fun x => P x.val );
              · rintro x ( hx | ⟨ y, hy, rfl ⟩ ) <;> [ exact ⟨ Sum.inl ⟨ x, hx ⟩, rfl ⟩ ; exact ⟨ Sum.inr ⟨ y, hy ⟩, rfl ⟩ ];
              · refine' lt_of_le_of_lt ( Cardinal.mk_range_le ) _;
                simp +decide [ Cardinal.mk_sum ];
                norm_cast ; nlinarith [ show s.card ≤ ( n + 1 ) * ( n + 1 ) - 1 from Nat.le_sub_one_of_lt ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ _, by aesop_cat ⟩ ) ) ( by simp +decide [ Finset.card_univ ] ) ), Nat.sub_add_cancel ( show 1 ≤ ( n + 1 ) * ( n + 1 ) from Nat.mul_pos ( Nat.succ_pos _ ) ( Nat.succ_pos _ ) ) ];
        use fun q => if q = p then w else P q;
        simp_all +decide [ Set.InjOn ];
        grind +splitImp;
    specialize hkey Finset.univ ; aesop;

/-- **Claim 2.1 (extension step).**  If the roots graph `H^{(2)}` (with
`t = 3n²+1`) contains `K_{n,n}`, then `H` contains a copy of `K^{(3)}_{n,n}`. -/
theorem hasK3nn_of_rootsKmm (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (hK : HasKmm (rootsGraph H (3 * n ^ 2 + 1)) n) : HasK3nn H n := by
  classical
  obtain ⟨a, b, ha, hb, hab, hadj⟩ := hK
  have hroot : ∀ i j, IsDeltaRoot H (3 * n ^ 2 + 1) ({a i, b j} : Set W) := by
    intro i j
    have h := hadj i j
    rw [rootsGraph, SimpleGraph.fromRel_adj] at h
    rcases h.2 with h' | h'
    · exact h'
    · rwa [Set.pair_comm] at h'
  set Core : Finset W := Finset.univ.image a ∪ Finset.univ.image b with hCoreDef
  have hCa : ∀ i, a i ∈ Core :=
    fun i => Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hCb : ∀ j, b j ∈ Core :=
    fun j => Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
  have hCard : Core.card ≤ 2 * n := by
    have h0 : Core.card ≤ (Finset.univ.image a).card + (Finset.univ.image b).card :=
      Finset.card_union_le _ _
    have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := a)
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := b)
    simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
    omega
  obtain ⟨P, hPinj, hPcore, hPedge⟩ :=
    exists_private_assignment H hts n a b Core hCa hCb hCard hab hroot
  have hPa : ∀ p i, P p ≠ a i := fun p i h => hPcore p (h ▸ hCa i)
  have hPb : ∀ p j, P p ≠ b j := fun p j h => hPcore p (h ▸ hCb j)
  refine ⟨Sum.elim (Sum.elim a b) P, ?_, fun i j => hPedge (i, j)⟩
  rintro ((i | i) | p) ((j | j) | q) hxy <;>
    simp only [Sum.elim_inl, Sum.elim_inr] at hxy <;>
    first
      | rw [ha hxy] | rw [hb hxy] | rw [hPinj hxy]
      | exact absurd hxy (hab _ _) | exact absurd hxy.symm (hab _ _)
      | exact absurd hxy (hPa _ _) | exact absurd hxy.symm (hPa _ _)
      | exact absurd hxy (hPb _ _) | exact absurd hxy.symm (hPb _ _)

/-- **Claim 2.1.**  If `H` has no `K^{(3)}_{n,n}`, then its roots graph `H^{(2)}`
is countably colourable.  (Otherwise, by Erdős–Hajnal `eh_hasKmm` the roots graph
would contain `K_{n,n}`, and `hasK3nn_of_rootsKmm` would build a `K^{(3)}_{n,n}`.) -/
theorem rootsGraph_countColorable (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (hfree : ¬ HasK3nn H n) : GCountColorable (rootsGraph H (3 * n ^ 2 + 1)) := by
  by_contra hnc
  rw [gCountColorable_iff_colorableBy] at hnc
  exact hfree (hasK3nn_of_rootsKmm H hts n (eh_hasKmm (rootsGraph H (3 * n ^ 2 + 1)) hnc n))

/-! ### Part A: maximal delta systems and the finitary delta-closure

The remainder of the file discharges Reiher's `k = 3` delta-system reduction
(`hasK3nn_of_uncountable`).  For each pair `{x,y}` that is *not* a size-`t`
delta-root we build a *maximal* finite delta system with root `{x,y}`; its
vertex set `witnessVerts` is finite.  Closing a set under all these witness
sets produces a *delta-closed* set, replacing the elementary submodels of
Reiher's proof.  This mirrors the finitary-closure filtration proved in
`EHBase` (`cl`, `nclosed_cl`, `cl_card_le`, `countColorable_of_smaller`). -/

/-- A finite delta system with prescribed root `f`: all edges of `H`, each
containing `f`, pairwise meeting exactly in `f`. -/
def IsRootDS (H : Hypergraph W) (f : Set W) (D : Finset (Set W)) : Prop :=
  (∀ e ∈ D, e ∈ H.edges ∧ f ⊆ e) ∧
    (∀ e₁ ∈ D, ∀ e₂ ∈ D, e₁ ≠ e₂ → e₁ ∩ e₂ = f)

/-
If `f` is not the root of a size-`t` delta system, every finite delta system
with root `f` has fewer than `t` edges.
-/
theorem rootDS_card_lt (H : Hypergraph W) (t : ℕ) (f : Set W)
    (hf : ¬ IsDeltaRoot H t f) (D : Finset (Set W)) (hD : IsRootDS H f D) :
    D.card < t := by
  contrapose! hf;
  use D;
  simp_all +decide only [SetLike.coe_sort_coe, mk_fintype, Fintype.card_coe, Nat.cast_le, SetLike.mem_coe,
    ne_eq];
  exact fun x hx => hD.1 x hx |>.1

open Classical in
/-- Inserting an edge that meets every member of a root-`f` delta system exactly
in `f` yields another root-`f` delta system. -/
theorem IsRootDS_insert (H : Hypergraph W) (f : Set W) (D : Finset (Set W))
    (hD : IsRootDS H f D) (e : Set W) (he : e ∈ H.edges) (hfe : f ⊆ e)
    (hint : ∀ e' ∈ D, e ∩ e' = f) (hnew : e ∉ D) :
    IsRootDS H f (insert e D) := by
  refine ⟨?_, ?_⟩
  · intro e'' he''
    rcases Finset.mem_insert.mp he'' with h | h
    · subst h; exact ⟨he, hfe⟩
    · exact hD.1 e'' h
  · intro e₁ h₁ e₂ h₂ hne
    rcases Finset.mem_insert.mp h₁ with h₁' | h₁' <;>
      rcases Finset.mem_insert.mp h₂ with h₂' | h₂'
    · exact absurd (h₁'.trans h₂'.symm) hne
    · subst h₁'; exact hint e₂ h₂'
    · subst h₂'; rw [Set.inter_comm]; exact hint e₁ h₁'
    · exact hD.2 e₁ h₁' e₂ h₂' hne

open Classical in
/-- A *maximal* finite delta system with root `f` exists when `f` is not a
size-`t` root: one that no further edge of `H` can extend. -/
theorem exists_maximal_rootDS (H : Hypergraph W) (t : ℕ) (f : Set W)
    (hf : ¬ IsDeltaRoot H t f) :
    ∃ D : Finset (Set W), IsRootDS H f D ∧
      ∀ e ∈ H.edges, f ⊆ e → (∀ e' ∈ D, e ∩ e' = f) → e ∈ D := by
  obtain ⟨D, hD⟩ : ∃ D : Finset (Set W), IsRootDS H f D ∧
      ∀ D' : Finset (Set W), IsRootDS H f D' → D'.card ≤ D.card := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (∃ D : Finset (Set W), IsRootDS H f D ∧ D.card = m) ∧
        ∀ k, (∃ D : Finset (Set W), IsRootDS H f D ∧ D.card = k) → k ≤ m := by
      apply_rules [Set.exists_max_image]
      · exact Set.finite_iff_bddAbove.mpr ⟨t, fun n hn => by
          obtain ⟨D, hD₁, rfl⟩ := hn; exact le_of_lt (rootDS_card_lt H t f hf D hD₁)⟩
      · exact ⟨0, ⟨∅, by simp +decide [IsRootDS]⟩⟩
    obtain ⟨⟨D, hD₁, hD₂⟩, hD₃⟩ := hm
    exact ⟨D, hD₁, fun D' hD' => by linarith [hD₃ _ ⟨D', hD', rfl⟩]⟩
  refine ⟨D, hD.1, fun e he hfe hint => ?_⟩
  by_contra hnew
  have hins : IsRootDS H f (insert e D) := IsRootDS_insert H f D hD.1 e he hfe hint hnew
  have hcard : (insert e D).card = D.card + 1 := Finset.card_insert_of_notMem hnew
  have := hD.2 _ hins
  omega

open Classical in
/-- A chosen maximal delta system with root `f` (junk `∅` when `f` is a root). -/
noncomputable def maxDS (H : Hypergraph W) (t : ℕ) (f : Set W) : Finset (Set W) :=
  if h : ¬ IsDeltaRoot H t f then (exists_maximal_rootDS H t f h).choose else ∅

/-- The vertex set of the chosen maximal delta system with root `f`. -/
def witnessVerts (H : Hypergraph W) (t : ℕ) (f : Set W) : Set W :=
  ⋃ e ∈ maxDS H t f, e

/-- Specification of `maxDS` when `f` is not a root. -/
theorem maxDS_spec (H : Hypergraph W) (t : ℕ) (f : Set W) (hf : ¬ IsDeltaRoot H t f) :
    IsRootDS H f (maxDS H t f) ∧
      ∀ e ∈ H.edges, f ⊆ e → (∀ e' ∈ maxDS H t f, e ∩ e' = f) →
        e ∈ maxDS H t f := by
  rw [maxDS, dif_pos hf]
  exact (exists_maximal_rootDS H t f hf).choose_spec

/-
The witness vertex set is finite (a maximal delta system has `< t` edges,
each a triple).
-/
theorem witnessVerts_finite (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (f : Set W) : (witnessVerts H t f).Finite := by
  by_cases h : IsDeltaRoot H t f;
  · unfold witnessVerts maxDS; aesop;
  · convert! Set.Finite.biUnion ( Finset.finite_toSet ( maxDS H t f ) ) ( fun e he => ?_ ) using 1;
    have := maxDS_spec H t f h;
    exact Set.finite_of_ncard_pos ( by rw [ hts e ( this.1.1 e he |>.1 ) ] ; norm_num )

/-- The witness vertex set is at most countable. -/
theorem witnessVerts_card_le (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (f : Set W) : #(witnessVerts H t f) ≤ ℵ₀ := by
  have h := (witnessVerts_finite H hts t f)
  exact le_of_lt h.lt_aleph0

/-- One delta-closure step: add the witness vertices of every pair in `X`. -/
def DCloseStep (H : Hypergraph W) (t : ℕ) (X : Set W) : Set W :=
  X ∪ {v | ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ v ∈ witnessVerts H t {x, y}}

/-- The `k`-fold delta-closure step. -/
def DCloseIter (H : Hypergraph W) (t : ℕ) (X : Set W) : ℕ → Set W
  | 0 => X
  | k + 1 => DCloseStep H t (DCloseIter H t X k)

/-- The finitary delta-closure of `X`. -/
def Dcl (H : Hypergraph W) (t : ℕ) (X : Set W) : Set W := ⋃ k, DCloseIter H t X k

/-- `X` is *delta-closed*: it contains the witness vertices of each of its
pairs. -/
def DClosed (H : Hypergraph W) (t : ℕ) (X : Set W) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → witnessVerts H t {x, y} ⊆ X

theorem subset_DCloseIter (H : Hypergraph W) (t : ℕ) (X : Set W) (k : ℕ) :
    X ⊆ DCloseIter H t X k := by
  induction' k with k ih
  · rfl
  · exact Set.Subset.trans ih Set.subset_union_left

theorem DCloseIter_mono_index (H : Hypergraph W) (t : ℕ) (X : Set W) {k l : ℕ}
    (h : k ≤ l) : DCloseIter H t X k ⊆ DCloseIter H t X l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact Set.Subset.trans ih Set.subset_union_left

theorem subset_Dcl (H : Hypergraph W) (t : ℕ) (X : Set W) : X ⊆ Dcl H t X :=
  Set.subset_iUnion_of_subset 0 (by rfl)

theorem Dcl_mono (H : Hypergraph W) (t : ℕ) {X Y : Set W} (h : X ⊆ Y) :
    Dcl H t X ⊆ Dcl H t Y := by
  apply Set.iUnion_mono;
  intro k;
  induction' k with k ih;
  · exact h;
  · refine' Set.union_subset_union ih _;
    exact fun v hv => by obtain ⟨ x, hx, y, hy, hxy, hv ⟩ := hv; exact ⟨ x, ih hx, y, ih hy, hxy, hv ⟩ ;

/-
The delta-closure is delta-closed.
-/
theorem DClosed_Dcl (H : Hypergraph W) (t : ℕ) (X : Set W) :
    DClosed H t (Dcl H t X) := by
  intro x hx y hy hxy v hv; simp_all +decide [ DClosed, Dcl ] ;
  obtain ⟨ kx, hkx ⟩ := hx; obtain ⟨ ky, hky ⟩ := hy; use Max.max kx ky + 1; simp_all +decide [ DCloseIter ] ;
  exact Set.mem_union_right _ ⟨ x, DCloseIter_mono_index _ _ _ ( le_max_left _ _ ) hkx, y, DCloseIter_mono_index _ _ _ ( le_max_right _ _ ) hky, hxy, hv ⟩

/-
The delta-closure step increases cardinality by at most `ℵ₀`.
-/
theorem DCloseStep_card_le (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (X : Set W) : #(DCloseStep H t X) ≤ #X + ℵ₀ := by
  -- By definition of `DCloseStep`, we have `DCloseStep H t X = X ∪ {v | ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ v ∈ witnessVerts H t {x, y}}`.
  set A := {v : W | ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ v ∈ witnessVerts H t {x, y}} with hA_def
  have hDCloseStep : DCloseStep H t X = X ∪ A := by
    grind +locals
  generalize_proofs at *; (
  -- It suffices to show that $|A| \leq |X|^2 \cdot \aleph_0$.
  suffices hA_card : #(A) ≤ #(X × X) * Cardinal.aleph0 by
    by_cases hX : Infinite X <;> simp_all +decide only [ge_iff_le];
    · refine' le_trans ( Cardinal.mk_union_le _ _ ) _ ; aesop;
    · refine' le_trans ( Cardinal.mk_union_le _ _ ) _;
      refine' add_le_add le_rfl _;
      exact Cardinal.mk_le_aleph0_iff.mpr ( Set.Finite.countable <| Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_coe_iff.mp hX ) fun x hx => Set.Finite.biUnion ( Set.finite_coe_iff.mp hX ) fun y hy => Set.Finite.subset ( witnessVerts_finite H hts t { x, y } ) fun z => by aesop ) fun x hx => by aesop );
  -- By definition of $A$, we have $A \subseteq \bigcup_{p : ↥X × ↥X} witnessVerts H t {(p.1 : W), (p.2 : W)}$.
  have hA_subset : A ⊆ ⋃ p : ↥X × ↥X, witnessVerts H t {(p.1 : W), (p.2 : W)} := by
    intro v hv; obtain ⟨ x, hx, y, hy, hxy, hv ⟩ := hv; exact Set.mem_iUnion.2 ⟨ ⟨ ⟨ x, hx ⟩, ⟨ y, hy ⟩ ⟩, hv ⟩ ;
  refine' le_trans ( Cardinal.mk_le_mk_of_subset hA_subset ) _;
  refine' le_trans ( Cardinal.mk_iUnion_le _ ) _;
  refine' mul_le_mul_right _ _;
  exact ciSup_le' fun p => witnessVerts_card_le H hts t _)

/-
The delta-closure has size at most `#X + ℵ₀`.
-/
theorem Dcl_card_le (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (X : Set W) : #(Dcl H t X) ≤ #X + ℵ₀ := by
  convert! Cardinal.mk_iUnion_le _ |> le_trans <| _;
  rotate_left;
  exact ULift ℕ;
  exact fun i => DCloseIter H t X i.down;
  · refine' le_trans ( mul_le_mul_right ( ciSup_le _ ) _ ) _;
    exact #X + ℵ₀;
    · intro x; induction' x.down with k ih <;> simp_all +decide [ DCloseIter ] ;
      refine' le_trans ( DCloseStep_card_le H hts t _ ) _;
      convert! add_le_add_right ih ℵ₀ using 1;
      · rw [ add_comm ];
      · rw [ add_comm, Cardinal.add_eq_max ];
        · rw [ Cardinal.add_eq_max ];
          · grind;
          · norm_num;
        · norm_num;
    · simp +decide [ Cardinal.mk_nat ];
  · ext; simp [Dcl]

/-
A monotone union of delta-closed sets over an initial segment stays
delta-closed.
-/
theorem DClosed_biUnion_lt {σ : Type u} [LinearOrder σ] (H : Hypergraph W) (t : ℕ)
    (M : σ → Set W) (hmono : Monotone M) (hcl : ∀ b, DClosed H t (M b)) (a : σ) :
    DClosed H t (⋃ b ∈ {b : σ | b < a}, M b) := by
  intro x hx y hy hxy;
  simp_all +decide only [Set.mem_ofPred_eq];
  obtain ⟨ i, hi, hx ⟩ := hx; obtain ⟨ j, hj, hy ⟩ := hy; use fun z hz => ⟨ Max.max i j, max_lt hi hj, hcl ( Max.max i j ) _ ( hmono ( le_max_left _ _ ) hx ) _ ( hmono ( le_max_right _ _ ) hy ) hxy hz ⟩ ;

/-! ### Part B: Claim 2.2 and the colourability ingredients -/

/-- An edge `e` *contains a delta-root*: two distinct vertices `u, v` with
`{u,v} ⊆ e` that form a size-`t` delta-root.  `E'` is the set of edges with a
root; `E''` its complement inside `H.edges`. -/
def hasRoot (H : Hypergraph W) (t : ℕ) (e : Set W) : Prop :=
  ∃ u v, u ≠ v ∧ ({u, v} : Set W) ⊆ e ∧ IsDeltaRoot H t {u, v}

/-
**Claim 2.2 (core step).**  Let `U` be delta-closed, `x, y ∈ U`, `z ∉ U`, and
`e = {x,y,z}` an edge whose lower pair `{x,y}` is not a delta-root.  This is
impossible: the maximal delta system with root `{x,y}` lives inside `U` (by
delta-closedness), yet `e` extends it (since `z ∉ U`), contradicting maximality.
-/
theorem claim22_abstract (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (U : Set W) (hU : DClosed H t U) (x y z : W)
    (hxU : x ∈ U) (hyU : y ∈ U) (hzU : z ∉ U)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (e : Set W) (he : e ∈ H.edges) (hxe : x ∈ e) (hye : y ∈ e) (hze : z ∈ e)
    (hnr : ¬ IsDeltaRoot H t ({x, y} : Set W)) : False := by
  -- Apply the maximality condition hmax to e.
  have h_e_in_maxDS : e ∈ maxDS H t {x, y} := by
    obtain ⟨hDS, hmax⟩ := maxDS_spec H t {x, y} hnr;
    refine' hmax e he ( by aesop_cat ) _;
    intro e' he';
    apply Set.Subset.antisymm;
    · intro w hw;
      have h_w_in_U : w ∈ U := by
        have h_w_in_U : e' ⊆ U := by
          exact Set.subset_biUnion_of_mem he' |> Set.Subset.trans <| hU x hxU y hyU hxy;
        exact h_w_in_U hw.2;
      have := hts e he;
      rw [ Set.ncard_eq_three ] at this;
      grind;
    · simp_all +decide [ Set.subset_def ];
      have := hDS.1 e' he'; aesop;
  exact hzU ( hU x hxU y hyU hxy |> fun h => h ( Set.mem_iUnion₂.mpr ⟨ e, h_e_in_maxDS, hze ⟩ ) )

/-
**Combining per-level colourings.**  If every edge of `E₀` has two vertices of
a common `rank` value `a` that a level-`a` colouring `d a` separates, then
`(W, E₀)` is `ℵ₀`-colourable (colour `v` by `d (rank v) v`).
-/
theorem colorable_combine {Idx : Type*} (rank : W → Idx) (E₀ : Set (Set W))
    (d : Idx → W → ℕ)
    (hsep : ∀ e ∈ E₀, ∃ a, ∃ u ∈ e, ∃ w ∈ e, rank u = a ∧ rank w = a ∧ d a u ≠ d a w) :
    (⟨E₀⟩ : Hypergraph W).ColorableBy ℵ₀ := by
  convert! colorableBy_aleph0_of_countable _ _ _ using 1;
  exact ULift ℕ;
  exact Cardinal.mk_le_aleph0;
  exact fun v => ⟨ d ( rank v ) v ⟩;
  intro e he; obtain ⟨ a, u, hu, w, hw, hru, hrw, hne ⟩ := hsep e he; use u, hu, w, hw; aesop;

/-
**`E'` is `ℵ₀`-colourable.**  A proper `ℕ`-colouring of the roots graph
`H^{(2)}` (which exists by `rootsGraph_countColorable`) is proper for `(W, E')`,
since each `e ∈ E'` contains an adjacent pair `{u,v}` of the roots graph.
-/
theorem E'_colorable (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (hfree : ¬ HasK3nn H n) :
    (⟨{e | e ∈ H.edges ∧ hasRoot H (3 * n ^ 2 + 1) e}⟩ : Hypergraph W).ColorableBy ℵ₀ := by
  obtain ⟨c, hc⟩ := rootsGraph_countColorable H hts n hfree;
  convert! colorableBy_aleph0_of_countable _ _ _ using 1;
  exact ULift ℕ;
  exact Cardinal.mk_le_aleph0;
  exact fun x => ⟨ c x ⟩;
  intro e he; obtain ⟨ u, v, huv, huv', huv'' ⟩ := he.2; simp_all +decide only [ne_eq, ULift.up.injEq] ;
  exact ⟨ u, huv' ( Set.mem_insert _ _ ), v, huv' ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ), hc u v huv ( Or.inl huv'' ) ⟩

/-- The triple system induced by `H` on a subset `S`, living on the subtype `↑S`. -/
def Hsub (H : Hypergraph W) (S : Set W) : Hypergraph ↑S :=
  ⟨{s | Subtype.val '' s ∈ H.edges}⟩

/-
The induced system on `S` is a triple system.
-/
theorem Hsub_isTripleSystem (H : Hypergraph W) (hts : H.IsTripleSystem) (S : Set W) :
    (Hsub H S).IsTripleSystem := by
  intro s hs; specialize hts ( Subtype.val '' s ) ; simp_all +decide [ Set.ncard_image_of_injective, Function.Injective ] ;
  exact hts hs

/-
A `K^{(3)}_{n,n}` in the induced system on `S` lifts to one in `H`.
-/
theorem Hsub_hasK3nn (H : Hypergraph W) (S : Set W) (n : ℕ)
    (h : HasK3nn (Hsub H S) n) : HasK3nn H n := by
  obtain ⟨ g, hg_inj, hg_edge ⟩ := h;
  refine' ⟨ fun x => g x, _, _ ⟩;
  · exact Subtype.coe_injective.comp hg_inj;
  · convert! hg_edge using 1;
    simp +decide [ Hsub, Set.image_insert_eq, Set.image_singleton ]

/-
For an edge `e ⊆ S`, its preimage in `↑S` is an edge of the induced system
with image `e`.
-/
theorem Hsub_edge_of_subset (H : Hypergraph W) (S : Set W) (e : Set W)
    (he : e ∈ H.edges) (hsub : e ⊆ S) :
    ∃ s : Set ↑S, Subtype.val '' s = e ∧ s ∈ (Hsub H S).edges := by
  -- Let $s$ be the preimage of $e$ under the inclusion map from $S$ to $W$.
  use {x : S | x.val ∈ e};
  -- By definition of `Hsub`, we know that `{x | x.val ∈ e}` is an edge in `Hsub H S` if and only if `e` is an edge in `H`.
  unfold Hsub;
  aesop

/-- **Minimality gives level colourings.**  Any subset `S` of size `< #W` carries
a `ℕ`-colouring proper for the edges of `H` contained in `S` (the induced triple
system on `S` is `K^{(3)}_{n,n}`-free and smaller, hence `ℵ₀`-colourable). -/
theorem sub_colorable_gives (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (hfree : ¬ HasK3nn H n)
    (minim : ∀ (W' : Type u) (H' : Hypergraph W'), #W' < #W → H'.IsTripleSystem →
       ¬ HasK3nn H' n → H'.ColorableBy ℵ₀)
    (S : Set W) (hS : #S < #W) :
    ∃ d : W → ℕ, ∀ e ∈ H.edges, e ⊆ S → ∃ u ∈ e, ∃ w ∈ e, d u ≠ d w := by
  classical
  have htri : (Hsub H S).IsTripleSystem := Hsub_isTripleSystem H hts S
  have hfree' : ¬ HasK3nn (Hsub H S) n := fun h => hfree (Hsub_hasK3nn H S n h)
  obtain ⟨c, hc⟩ := minim (↑S) (Hsub H S) hS htri hfree'
  have hcnt : Countable (ℵ₀ : Cardinal.{u}).out :=
    Cardinal.mk_le_aleph0_iff.mp (le_of_eq (Cardinal.mk_out _))
  obtain ⟨g, hg⟩ : ∃ g : (ℵ₀ : Cardinal.{u}).out → ℕ, Function.Injective g :=
    ⟨_, (exists_injective_nat _).choose_spec⟩
  set d : W → ℕ := fun v => if h : v ∈ S then g (c ⟨v, h⟩) else 0 with hd
  have hval : ∀ a : ↑S, d (a : W) = g (c a) := by
    intro a; simp only [hd, dif_pos a.2, Subtype.coe_eta]
  refine ⟨d, fun e he hsub => ?_⟩
  obtain ⟨s, hsimg, hsedge⟩ := Hsub_edge_of_subset H S e he hsub
  obtain ⟨u, hu, w, hw, huw⟩ := hc s hsedge
  refine ⟨(u : W), by rw [← hsimg]; exact ⟨u, hu, rfl⟩, (w : W),
    by rw [← hsimg]; exact ⟨w, hw, rfl⟩, ?_⟩
  rw [hval u, hval w]
  exact fun h => huw (hg h)

/-
A triple system on an at-most-countable vertex type is `ℵ₀`-colourable
(colour vertices injectively).
-/
theorem tripleSystem_colorable_of_le_aleph0 (H : Hypergraph W)
    (hts : H.IsTripleSystem) (h : #W ≤ ℵ₀) : H.ColorableBy ℵ₀ := by
  obtain ⟨c, hc⟩ : ∃ c : W → ℕ, ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v := by
    cases' Cardinal.le_mk_iff_exists_set.mp h with S hS;
    cases' Cardinal.eq.1 hS.symm with f hf;
    use fun w => (f w).val.down;
    intro e he; have := hts e he; rw [ Set.ncard_eq_three ] at this; obtain ⟨ a, b, c, hab, hac, hbc, rfl ⟩ := this; use a, by simp +decide, b, by simp +decide; ; simp +decide only [ne_eq, ULift.down_inj] ;
    exact fun h => hab <| f.injective <| Subtype.ext h;
  exact hgCountColorable_iff H |>.1 ⟨ c, hc ⟩

/-! ### Part C: the rainbow grid and grid-to-`K^{(3)}_{n,n}` -/

/-
Assembling a `K^{(3)}_{n,n}` from an injective grid of left cores `X`, right
cores `Y`, and private vertices `P`.
-/
theorem hasK3nn_from_grid (H : Hypergraph W) (n : ℕ) (X Y : Fin n → W)
    (P : Fin n → Fin n → W)
    (hInj : Function.Injective
      (Sum.elim (Sum.elim X Y) (fun p : Fin n × Fin n => P p.1 p.2)))
    (hedge : ∀ i j, ({X i, Y j, P i j} : Set W) ∈ H.edges) : HasK3nn H n := by
  use Sum.elim (Sum.elim X Y) (fun p => P p.1 p.2);
  grind

/-
**Generic greedy selection.**  Build `n` distinct elements, each satisfying a
unary predicate `Q` and pairwise related by `R`, from a one-step extension
property.
-/
theorem exists_finset_pairwise {α : Type*} [Fintype α] [DecidableEq α]
    (Q : α → Prop) (R : α → α → Prop) (n : ℕ)
    (hstep : ∀ D : Finset α, D.card < n → (∀ x ∈ D, Q x) →
      ∃ z, z ∉ D ∧ Q z ∧ ∀ x ∈ D, R x z ∧ R z x) :
    ∃ C : Finset α, C.card = n ∧ (∀ x ∈ C, Q x) ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → R x y := by
  induction' n with n ih;
  · exact ⟨ ∅, rfl, by simp +decide ⟩;
  · -- Apply the induction hypothesis with hstep modified to use n instead of n+1.
    obtain ⟨C, hC⟩ := ih (fun D hD hQ => hstep D (Nat.lt_succ_of_lt hD) hQ);
    obtain ⟨z, hz⟩ := hstep C (by linarith) hC.2.1;
    use Insert.insert z C;
    grind

open Classical in
/-- **Double counting of column agreement.**  For a fixed column `b`, the total
number of `(a, z)` with `P a b = P a z` is `≤ q*(t-1)` (each row `a` has `< t`
columns of any given value). -/
theorem sum_agree_le {V : Type*} (t q : ℕ) (P : Fin q → Fin q → V)
    (hrow : ∀ (a : Fin q) (v : V), (Finset.univ.filter (fun b => P a b = v)).card < t)
    (b : Fin q) :
    ∑ z : Fin q, (Finset.univ.filter (fun a => P a b = P a z)).card ≤ q * (t - 1) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ z : Fin q, (Finset.univ.filter (fun a => P a b = P a z)).card = ∑ a : Fin q, (Finset.univ.filter (fun z => P a b = P a z)).card := by
    simp +decide only [Finset.card_filter];
    exact Finset.sum_comm;
  exact h_fubini.symm ▸ le_trans ( Finset.sum_le_sum fun i _ => show Finset.card ( Finset.filter ( fun z => P i b = P i z ) Finset.univ ) ≤ t - 1 from Nat.le_sub_one_of_lt ( by simpa [ eq_comm ] using! hrow i ( P i b ) ) ) ( by simp +decide [ mul_comm ] ) ;

open Classical in
/-- **Column step.**  Given `< n` chosen columns, there is a new column agreeing
with each on `< n*t` rows (few columns are `n*t`-twins of any fixed column, by
`sum_agree_le`). -/
theorem cols_step {V : Type*} (n t q : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n) (hq : n ^ 2 * t ≤ q)
    (P : Fin q → Fin q → V)
    (hrow : ∀ (a : Fin q) (v : V), (Finset.univ.filter (fun b => P a b = v)).card < t)
    (D : Finset (Fin q)) (hD : D.card < n) :
    ∃ z, z ∉ D ∧ ∀ x ∈ D,
      (Finset.univ.filter (fun a => P a x = P a z)).card < n * t := by
  -- By `sum_agree_le` and `bad union bound`, we can find such a $z$.
  have h_bad_card : ∑ x ∈ D, ∑ z : Fin q, (Finset.univ.filter (fun a => P a x = P a z)).card ≤ D.card * q * (t - 1) := by
    convert! Finset.sum_le_sum fun x hx => sum_agree_le t q P hrow x using 1;
    simp +decide [ mul_assoc ];
  -- By `bad union bound`, we can find such a $z$.
  have h_bad_card : ∑ z : Fin q, ∑ x ∈ D, (Finset.univ.filter (fun a => P a x = P a z)).card < (q - D.card) * n * t := by
    rw [ Finset.sum_comm ];
    nlinarith [ Nat.sub_add_cancel ( show 1 ≤ t from ht ), Nat.sub_add_cancel ( show D.card ≤ q from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ), mul_le_mul_right hD.le q, mul_le_mul_right hn q, mul_le_mul_right ht q, mul_le_mul_right hD.le t, mul_le_mul_right hn t, mul_le_mul_right ht t ];
  contrapose! h_bad_card;
  have h_bad_card : ∑ z ∈ Finset.univ \ D, ∑ x ∈ D, (Finset.univ.filter (fun a => P a x = P a z)).card ≥ (q - D.card) * n * t := by
    have h_bad_card : ∀ z ∈ Finset.univ \ D, ∑ x ∈ D, (Finset.univ.filter (fun a => P a x = P a z)).card ≥ n * t := by
      exact fun z hz => by obtain ⟨ x, hx, hx' ⟩ := h_bad_card z ( Finset.mem_sdiff.mp hz |>.2 ) ; exact le_trans hx' ( Finset.single_le_sum ( fun x _ => Nat.zero_le ( Finset.card ( Finset.filter ( fun a => P a x = P a z ) Finset.univ ) ) ) hx ) ;
    simpa [ mul_assoc, Finset.card_sdiff ] using! Finset.sum_le_sum h_bad_card;
  exact h_bad_card.trans ( Finset.sum_le_sum_of_subset ( Finset.sdiff_subset ) )

open Classical in
/-- **Row step.**  Given `< n` chosen rows, all internally rainbow on the fixed
columns `B` and pairwise non-crossing, there is a new such row (internal
collisions bounded by `hpair`, cross collisions by the column bound). -/
theorem rows_step {V : Type*} (n t q : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n)
    (hq : 3 * n ^ 3 * t + n ≤ q) (P : Fin q → Fin q → V) (B : Fin n → Fin q)
    (hcol : ∀ (b : Fin q) (v : V), (Finset.univ.filter (fun a => P a b = v)).card < t)
    (hpair : ∀ i i' : Fin n, i ≠ i' →
      (Finset.univ.filter (fun a => P a (B i) = P a (B i'))).card < n * t)
    (D : Finset (Fin q)) (hD : D.card < n)
    (hDQ : ∀ x ∈ D, ∀ k l : Fin n, k ≠ l → P x (B k) ≠ P x (B l)) :
    ∃ z, z ∉ D ∧ (∀ k l : Fin n, k ≠ l → P z (B k) ≠ P z (B l)) ∧
      ∀ x ∈ D, (∀ k l : Fin n, P x (B k) ≠ P z (B l)) ∧
        (∀ k l : Fin n, P z (B k) ≠ P x (B l)) := by
  -- Define the "bad" rows: `I := Finset.univ.filter (fun z => ∃ k l : Fin n, k ≠ l ∧ P z (B k) = P z (B l))` (internally non-rainbow), `C := Finset.univ.filter (fun z => ∃ x ∈ D, ∃ k l : Fin n, P x (B k) = P z (B l) ∨ P z (B k) = P x (B l))` (crossing some chosen row)
  set I := Finset.biUnion (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)) (fun p => Finset.univ.filter (fun z => P z (B p.1) = P z (B p.2)))
  set C := Finset.biUnion D (fun x => Finset.biUnion (Finset.univ ×ˢ Finset.univ) (fun p : Fin n × Fin n => Finset.univ.filter (fun z => P z (B p.2) = P x (B p.1)) ∪ Finset.univ.filter (fun z => P z (B p.1) = P x (B p.2))));
  -- Bound `I.card ≤ n ^ 3 * t` and `C.card ≤ 2 * n ^ 3 * t`.
  have hI : I.card ≤ n ^ 3 * t := by
    refine' le_trans ( Finset.card_biUnion_le ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => Nat.le_of_lt ( hpair _ _ <| Finset.mem_filter.mp hx |>.2 ) ) _;
    rw [ show ( Finset.univ.filter fun p : Fin n × Fin n => ¬p.1 = p.2 ) = Finset.univ \ Finset.diag ( Finset.univ : Finset ( Fin n ) ) by ext ⟨ i, j ⟩ ; simp +decide [ Finset.mem_sdiff, Finset.mem_diag ] ] ; simp +decide [ Finset.card_sdiff, Finset.card_singleton, Finset.card_univ ] ; ring_nf;
    exact Nat.mul_le_mul_right _ ( by nlinarith only [ Nat.sub_le ( n ^ 2 ) n ] )
  have hC : C.card ≤ 2 * n ^ 3 * t := by
    refine' le_trans ( Finset.card_biUnion_le ) ( le_trans ( Finset.sum_le_sum fun x hx => Finset.card_biUnion_le ) _ );
    refine' le_trans ( Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => Finset.card_union_le _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => add_le_add ( Nat.le_of_lt ( hcol _ _ ) ) ( Nat.le_of_lt ( hcol _ _ ) ) ) _ ; norm_num ; ring_nf ; norm_num;
    nlinarith [ mul_le_mul_right hn t ];
  -- Then `Bad.card ≤ D.card + I.card + C.card ≤ (n-1) + n^3*t + 2*n^3*t < 3*n^3*t + n ≤ q`.
  have hBad : (D ∪ I ∪ C).card < q := by
    grind +qlia;
  obtain ⟨ z, hz ⟩ := Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ ( D ∪ I ∪ C ), by aesop_cat ⟩ );
  simp +zetaDelta only [ne_eq] at *;
  exact ⟨ z, hz.1, hz.2.1, fun x hx => ⟨ fun k l => Ne.symm ( hz.2.2 x hx k l |>.1 ), fun k l => hz.2.2 x hx k l |>.2 ⟩ ⟩

open Classical in
/-- **Rainbow grid lemma.**  A `q × q` matrix `P` in which every value occurs
fewer than `t` times in each row and in each column contains an `n × n` rainbow
subgrid (an injective `A × B` block).  Proof: choose `n` columns pairwise
agreeing on `< n*t` rows (possible by the row bound), then greedily choose `n`
rows keeping all grid entries distinct (possible by the column bound and the
small column-agreement). -/
theorem greedy_rainbow {V : Type*} (n t q : ℕ) (ht : 1 ≤ t)
    (hq : 4 * t * n ^ 3 + n ^ 2 + n ≤ q) (P : Fin q → Fin q → V)
    (hrow : ∀ (a : Fin q) (v : V), (Finset.univ.filter (fun b => P a b = v)).card < t)
    (hcol : ∀ (b : Fin q) (v : V), (Finset.univ.filter (fun a => P a b = v)).card < t) :
    ∃ A B : Fin n → Fin q, Function.Injective A ∧ Function.Injective B ∧
      ∀ i j i' j', P (A i) (B j) = P (A i') (B j') → i = i' ∧ j = j' := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  -- Stage 1: choose `n` pairwise-`< n*t`-agreeing columns.
  obtain ⟨Ccol, hCcard, -, hCpair⟩ :=
    exists_finset_pairwise (α := Fin q) (fun _ => True)
      (fun b b' => (Finset.univ.filter (fun a => P a b = P a b')).card < n * t) n
      (fun D hD _ => by
        obtain ⟨z, hz, hzD⟩ := cols_step n t q ht hn (by nlinarith [hq]) P hrow D hD
        refine ⟨z, hz, trivial, fun x hx => ⟨hzD x hx, ?_⟩⟩
        show (Finset.univ.filter (fun a => P a z = P a x)).card < n * t
        rw [show (Finset.univ.filter (fun a => P a z = P a x)) =
            (Finset.univ.filter (fun a => P a x = P a z)) from
          Finset.filter_congr (fun a _ => by rw [eq_comm])]
        exact hzD x hx)
  -- Extract the injective column map `B`.
  set B : Fin n → Fin q := ⇑(Ccol.orderEmbOfFin hCcard) with hBdef
  have hBinj : Function.Injective B := (Ccol.orderEmbOfFin hCcard).injective
  have hBmem : ∀ i, B i ∈ Ccol := fun i => Ccol.orderEmbOfFin_mem hCcard i
  have hpairB : ∀ i i' : Fin n, i ≠ i' →
      (Finset.univ.filter (fun a => P a (B i) = P a (B i'))).card < n * t :=
    fun i i' hii => hCpair (B i) (hBmem i) (B i') (hBmem i') (fun h => hii (hBinj h))
  -- Stage 2: choose `n` rows, internally rainbow on `B` and pairwise non-crossing.
  obtain ⟨Crow, hRcard, hRQ, hRpair⟩ :=
    exists_finset_pairwise (α := Fin q)
      (fun a => ∀ k l : Fin n, k ≠ l → P a (B k) ≠ P a (B l))
      (fun a a' => ∀ k l : Fin n, P a (B k) ≠ P a' (B l)) n
      (fun D hD hDQ => by
        obtain ⟨z, hz, hzQ, hzcross⟩ := rows_step n t q ht hn (by nlinarith [hq]) P B hcol hpairB D hD hDQ
        exact ⟨z, hz, hzQ, fun x hx => ⟨(hzcross x hx).1, (hzcross x hx).2⟩⟩)
  set A : Fin n → Fin q := ⇑(Crow.orderEmbOfFin hRcard) with hAdef
  have hAinj : Function.Injective A := (Crow.orderEmbOfFin hRcard).injective
  have hAmem : ∀ i, A i ∈ Crow := fun i => Crow.orderEmbOfFin_mem hRcard i
  refine ⟨A, B, hAinj, hBinj, fun i j i' j' hgrid => ?_⟩
  by_cases hAA : A i = A i'
  · refine ⟨hAinj hAA, ?_⟩
    by_contra hjj
    have hcol' : P (A i) (B j) = P (A i) (B j') := by rw [hgrid, hAA]
    exact hRQ (A i) (hAmem i) j j' hjj hcol'
  · exact absurd hgrid (hRpair (A i) (hAmem i) (A i') (hAmem i') hAA j j')

/-- The *layer graph* at level `i`: `x ~ y` iff both have rank `i` and there is a
lower vertex `z` with `{x,y,z}` an `E''`-edge. -/
def layerGraph {Idx : Type*} [LT Idx] (H : Hypergraph W) (t : ℕ) (rank : W → Idx)
    (i : Idx) : SimpleGraph W :=
  SimpleGraph.fromRel (fun x y =>
    rank x = i ∧ rank y = i ∧ ∃ z, rank z < i ∧ ({x, y, z} : Set W) ∈ H.edges ∧
      ¬ hasRoot H t ({x, y, z} : Set W))

/-
**The delta-closed filtration and Claim 2.2, packaged.**  For an uncountable
triple system there is a rank function into a well-order such that (A) every rank
level is smaller than the whole, and (B) no `E''`-edge has a unique top vertex:
if `x, y` both have rank `< rank z`, `x ≠ y`, `{x,y}` is not a delta-root, and
`{x,y,z}` is an edge, that is impossible (Claim 2.2).
-/
theorem exists_delta_filtration (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (hbig : ℵ₀ < #W) :
    ∃ (Idx : Type u) (_ : LinearOrder Idx) (_ : WellFoundedLT Idx) (rank : W → Idx),
      (∀ a : Idx, #({v | rank v = a} : Set W) < #W) ∧
      (∀ (x y z : W), rank x < rank z → rank y < rank z → x ≠ y →
        ¬ IsDeltaRoot H t ({x, y} : Set W) →
        ∀ e ∈ H.edges, x ∈ e → y ∈ e → z ∈ e → False) := by
  -- Let `Idx := (#W).ord.ToType`.
  set Idx := (#W).ord.ToType;
  -- Set `M : Idx → Set W := fun a => Dcl H t (e '' {b | b ≤ a})`.
  obtain ⟨e, he⟩ : ∃ e : Idx ≃ W, True := by
    refine' ⟨ _, trivial ⟩;
    exact Classical.choice ( Cardinal.eq.1 <| by simp +decide [ Idx ] )
  set M : Idx → Set W := fun a => Dcl H t (Set.image e {b | b ≤ a});
  -- Show that `M` satisfies the required properties.
  have hM_mono : Monotone M := by
    intro a b hab; apply Dcl_mono; exact Set.image_mono (fun x hx => le_trans hx.out hab) ;
  have hM_DClosed : ∀ a, DClosed H t (M a) := by
    exact fun a => DClosed_Dcl H t _
  have hM_small : ∀ a, #(M a) < #W := by
    intro a
    have h_card_image : #(Set.image e {b | b ≤ a}) ≤ Cardinal.mk (Set.Iic a) := by
      exact Cardinal.mk_image_le.trans ( by simp +decide [ Set.Iic_def ] )
    have h_card_Iic : Cardinal.mk (Set.Iic a) < #W := by
      have h_card_Iic : Cardinal.mk (Set.Iio a) < #W := by
        convert! Cardinal.mk_Iio_ord_toType a using 1;
      have h_card_Iic : Cardinal.mk (Set.Iic a) = Cardinal.mk (Set.Iio a) + 1 := by
        rw [ ← Cardinal.mk_singleton ( a : Idx ), ← Cardinal.mk_union_of_disjoint ];
        · congr with x ; simp +decide [ le_iff_lt_or_eq, eq_comm ];
        · exact Set.disjoint_singleton_right.mpr (lt_irrefl a)
      convert! Cardinal.add_lt_of_lt _ ‹_› _ using 1;
      · exact le_of_lt hbig;
      · exact lt_of_le_of_lt ( by norm_num ) hbig
    have h_card_M : #(M a) ≤ #(Set.image e {b | b ≤ a}) + ℵ₀ := by
      convert! Dcl_card_le H hts t ( Set.image e { b | b ≤ a } ) using 1
    have h_card_M_lt : #(M a) < #W := by
      refine' lt_of_le_of_lt h_card_M _;
      refine' lt_of_le_of_lt ( add_le_add h_card_image le_rfl ) _;
      convert! Cardinal.add_lt_of_lt _ _ _ using 1;
      · exact le_of_lt hbig;
      · exact h_card_Iic;
      · exact hbig
    exact h_card_M_lt
  have hM_cover : ∀ x, x ∈ M (e.symm x) := by
    intro x
    simp [M, subset_Dcl];
    exact subset_Dcl _ _ _ ⟨ e.symm x, by simp +decide, by simp +decide ⟩;
  -- Define `rank : W → Idx` as the least index such that `x ∈ M a`.
  obtain ⟨rank, hrank⟩ : ∃ rank : W → Idx, ∀ x, x ∈ M (rank x) ∧ ∀ b, b < rank x → x ∉ M b := by
    have h_wellFounded : WellFounded (fun x y : Idx => x < y) := by
      exact wellFounded_lt;
    have h_least : ∀ x, ∃ a, x ∈ M a ∧ ∀ b, b < a → x ∉ M b := by
      intro x;
      have := h_wellFounded.has_min { a | x ∈ M a } ⟨ e.symm x, hM_cover x ⟩;
      exact ⟨ this.choose, this.choose_spec.1, fun b hb hb' => this.choose_spec.2 b hb' hb ⟩;
    exact ⟨ fun x => Classical.choose ( h_least x ), fun x => Classical.choose_spec ( h_least x ) ⟩;
  refine' ⟨ Idx, inferInstance, inferInstance, rank, _, _ ⟩;
  · intro a
    have h_subset : {v | rank v = a} ⊆ M a := by
      intro v hv; specialize hrank v; aesop;
    exact lt_of_le_of_lt ( Cardinal.mk_le_mk_of_subset h_subset ) ( hM_small a );
  · intros x y z hxz hyz hxy hnr e he hx hy hz;
    apply claim22_abstract H hts t (⋃ b ∈ {b | b < rank z}, M b) (DClosed_biUnion_lt H t M hM_mono hM_DClosed (rank z)) x y z (by
    exact Set.mem_iUnion₂.mpr ⟨ rank x, hxz, hrank x |>.1 ⟩) (by
    exact Set.mem_iUnion₂.mpr ⟨ rank y, hyz, hrank y |>.1 ⟩) (by
    simp +zetaDelta only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, not_exists, not_and] at *;
    exact fun x hx => hrank z |>.2 x hx) hxy (by
    exact fun h => hxz.ne <| h ▸ rfl) (by
    exact fun h => by have := hrank z; aesop;) e he hx hy hz hnr

/-
**A monochromatic column/row of size `t` is a delta-root.**  If `t` distinct
vertices `x` all form an edge `{x, u, w}` (with `u ≠ w`, `x ∉ {u,w}`), then
`{u,w}` is a size-`t` delta-root, so each such edge `hasRoot` — contradicting the
assumption that none does.
-/
theorem delta_root_contra (H : Hypergraph W) (t : ℕ) (ht : 0 < t) (u w : W) (huw : u ≠ w)
    (S : Finset W) (hScard : t ≤ S.card) (hSne : ∀ x ∈ S, x ≠ u ∧ x ≠ w)
    (hedge : ∀ x ∈ S, ({x, u, w} : Set W) ∈ H.edges)
    (hnr : ∀ x ∈ S, ¬ hasRoot H t ({x, u, w} : Set W)) : False := by
  -- By assumption, $D := \{e \mid e \in H.edges \land \{u, w\} \subseteq e\}$ has size at least $t$, so $\{u, w\}$ is a delta-root.
  have h_delta_root : IsDeltaRoot H t ({u, w} : Set W) := by
    -- By assumption, $D := \{ {x, u, w} \mid x \in S \}$ has size at least $t$, so $\{u, w\}$ is a delta-root.
    use { {x, u, w} | x ∈ S };
    refine' ⟨ _, _, _, _ ⟩;
    · exact fun x hx => by obtain ⟨ y, hy, rfl ⟩ := hx; exact hedge y hy;
    · refine' le_trans _ ( show _ ≤ _ from Cardinal.mk_le_mk_of_subset _ );
      rotate_left;
      exact Set.image ( fun x => { x, u, w } ) S;
      · exact Set.image_subset_iff.mpr fun x hx => ⟨ x, hx, rfl ⟩;
      · rw [ Set.image_eq_range ];
        rw [ Cardinal.mk_range_eq ];
        · simp +decide [ Cardinal.mk_coe_finset, hScard ];
        · intro x y; simp +decide only [SetLike.coe_sort_coe] ;
          intro h; specialize h x; aesop;
    · aesop_cat;
    · grind;
  obtain ⟨ x, hx ⟩ := Finset.card_pos.mp ( pos_of_gt ( lt_of_lt_of_le ht hScard ) ) ; specialize hnr x hx; unfold hasRoot at hnr; simp_all +decide ;

/-
**Layer adjacency for an `E''`-edge that is not level-flat.**  An `E''`-edge
whose vertices do not all share a rank has (by Claim 2.2) exactly two top vertices
`x, y` of some rank `i`, adjacent in the layer graph `layerGraph .. i`.
-/
theorem Ess_adj {Idx : Type u} [LinearOrder Idx] (H : Hypergraph W)
    (hts : H.IsTripleSystem) (t : ℕ) (rank : W → Idx)
    (hclaim : ∀ (x y z : W), rank x < rank z → rank y < rank z → x ≠ y →
        ¬ IsDeltaRoot H t ({x, y} : Set W) →
        ∀ e ∈ H.edges, x ∈ e → y ∈ e → z ∈ e → False)
    (e : Set W) (heE : e ∈ H.edges) (hnr : ¬ hasRoot H t e)
    (hne : ¬ ∃ a, ∀ v ∈ e, rank v = a) :
    ∃ (i : Idx) (x y : W), x ∈ e ∧ y ∈ e ∧ rank x = i ∧ rank y = i ∧
      (layerGraph H t rank i).Adj x y := by
  obtain ⟨ p, q, r, hpq, hpr, hqr, he ⟩ := Set.ncard_eq_three.mp ( hts e heE );
  -- By `key`, no vertex is a strict maximum over the other two.
  have h_no_max : ¬(rank p > rank q ∧ rank p > rank r) ∧ ¬(rank q > rank p ∧ rank q > rank r) ∧ ¬(rank r > rank p ∧ rank r > rank q) := by
    refine' ⟨ _, _, _ ⟩ <;> intro h <;> simp_all +decide [ hasRoot ];
    · exact hclaim q r p h.1 h.2 ( by tauto ) ( hnr q r ( by tauto ) ( by simp +decide [ Set.insert_subset_iff ] ) ) _ heE ( by simp +decide ) ( by simp +decide ) ( by simp +decide );
    · exact hclaim p r q h.1 h.2 ( by tauto ) ( hnr p r ( by tauto ) ( by simp +decide [ Set.insert_subset_iff ] ) ) _ heE ( by simp +decide ) ( by simp +decide ) ( by simp +decide );
    · exact hclaim p q r h.1 h.2 ( by tauto ) ( hnr p q ( by tauto ) ( by simp +decide [ Set.insert_subset_iff ] ) ) _ heE ( by simp +decide ) ( by simp +decide ) ( by simp +decide );
  -- By `hne`, the ranks are not all equal.
  obtain ⟨i, hi⟩ : ∃ i : Idx, (rank p = i ∧ rank q = i ∧ rank r ≠ i) ∨ (rank p = i ∧ rank r = i ∧ rank q ≠ i) ∨ (rank q = i ∧ rank r = i ∧ rank p ≠ i) := by
    contrapose! hne; simp_all +decide ;
    grind +splitImp;
  rcases hi with ( ⟨ hp, hq, hr ⟩ | ⟨ hp, hr, hq ⟩ | ⟨ hq, hr, hp ⟩ ) <;> simp_all +decide only [↓existsAndEq, true_and, exists_and_left];
  · grind +splitImp;
  · refine' Or.inl ( Or.inl ⟨ q, lt_of_le_of_ne h_no_max hq, _, _ ⟩ );
    · convert! heE using 1 ; ext ; simp +decide [ *, or_comm, or_left_comm, or_assoc ];
    · convert! hnr using 1;
      simp +decide [ Set.insert_comm, Set.pair_comm ];
  · refine' Or.inr ⟨ Ne.symm hqr, Or.inl ⟨ p, lt_of_le_of_ne h_no_max hp, _, _ ⟩ ⟩;
    · convert! heE using 1 ; ext ; simp +decide [ *, or_comm, or_left_comm, or_assoc ];
    · convert! hnr using 1;
      simp +decide [ Set.Subset.antisymm_iff, Set.subset_def, hasRoot ];
      grind

/-
Injectivity of the assembled `K^{(3)}_{n,n}` grid: cores have rank `i₀`,
privates have rank `< i₀`, and the grid privates are distinct.
-/
theorem grid_injective {Idx : Type u} [LinearOrder Idx] (rank : W → Idx) (n q : ℕ)
    (i₀ : Idx) (a b : Fin q → W) (A B : Fin n → Fin q) (P : Fin q → Fin q → W)
    (hainj : Function.Injective a) (hbinj : Function.Injective b)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hab : ∀ i j, a i ≠ b j)
    (hgrid : ∀ i j i' j', P (A i) (B j) = P (A i') (B j') → i = i' ∧ j = j')
    (hra : ∀ k, rank (a k) = i₀) (hrb : ∀ k, rank (b k) = i₀)
    (hrP : ∀ i j, rank (P (A i) (B j)) < i₀) :
    Function.Injective
      (Sum.elim (Sum.elim (fun i => a (A i)) (fun j => b (B j)))
        (fun p : Fin n × Fin n => P (A p.1) (B p.2))) := by
  intro x y hxy;
  grind +revert

/-- `K^{(3)}_{n,n}` is trivially present for `n = 0`. -/
theorem hasK3nn_zero (H : Hypergraph W) : HasK3nn H 0 := by
  refine ⟨fun x => (by rcases x with (i | i) | ⟨i, _⟩ <;> exact i.elim0), ?_, ?_⟩
  · rintro ((i | i) | ⟨i, _⟩) _ _ <;> exact i.elim0
  · rintro i; exact i.elim0

/-! ### Part D: the delta-system reduction and E4 -/

/-- **The inductive step of Reiher's `k = 3` argument.**  A `K^{(3)}_{n,n}`-free
triple system of uncountable chromatic number, minimal in cardinality, yields a
contradiction.  This is the delta-closed filtration (Part A), Claim 2.2, and the
final rainbow counting. -/
theorem hasK3nn_step (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (hbig : ℵ₀ < #W) (huc : H.UncountablyChromatic) (hfree : ¬ HasK3nn H n)
    (minim : ∀ (W' : Type u) (H' : Hypergraph W'), #W' < #W → H'.IsTripleSystem →
       ¬ HasK3nn H' n → H'.ColorableBy ℵ₀) : False := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (hasK3nn_zero H) hfree
    · exact hn
  -- E' colourable, E'' uncountably chromatic
  have hE'col := E'_colorable H hts n hfree
  have hE''uc := uncountablyChromatic_diff H.edges
      {e | e ∈ H.edges ∧ hasRoot H (3 * n ^ 2 + 1) e} huc hE'col
  obtain ⟨Idx, instLO, instWF, rank, hlevel, hclaim⟩ :=
    exists_delta_filtration H hts (3 * n ^ 2 + 1) hbig
  let := instLO
  let := instWF
  -- level colourings
  have hlc : ∀ a : Idx, ∃ d : W → ℕ, ∀ e ∈ H.edges, e ⊆ {v | rank v = a} →
      ∃ u ∈ e, ∃ w ∈ e, d u ≠ d w :=
    fun a => sub_colorable_gives H hts n hfree minim {v | rank v = a} (hlevel a)
  choose dstar hdstar using hlc
  set E'' : Set (Set W) := {e | e ∈ H.edges ∧ ¬ hasRoot H (3 * n ^ 2 + 1) e} with hE''def
  have hE''eq :
      (H.edges \ {e | e ∈ H.edges ∧ hasRoot H (3 * n ^ 2 + 1) e}) = E'' := by
    ext e; constructor
    · rintro ⟨he, hne⟩; exact ⟨he, fun hr => hne ⟨he, hr⟩⟩
    · rintro ⟨he, hnr⟩; exact ⟨he, fun h => hnr h.2⟩
  rw [hE''eq] at hE''uc
  -- level-flat part is colourable
  have hEstarcol :
      (⟨{e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}⟩ : Hypergraph W).ColorableBy ℵ₀ := by
    apply colorable_combine rank _ dstar
    rintro e ⟨heE'', a, ha⟩
    obtain ⟨u, hu, w, hw, huw⟩ := hdstar a e heE''.1 (fun v hv => ha v hv)
    exact ⟨a, u, hu, w, hw, ha u hu, ha w hw, huw⟩
  -- some layer is uncountably chromatic
  have hExists : ∃ i₀ : Idx,
      ¬ (SimpleGraph.toHG (layerGraph H (3 * n ^ 2 + 1) rank i₀)).ColorableBy ℵ₀ := by
    by_contra hall
    push_neg at hall
    have hlayerc : ∀ i : Idx, ∃ c : W → ℕ,
        ∀ x y, (layerGraph H (3 * n ^ 2 + 1) rank i).Adj x y → c x ≠ c y :=
      fun i => (gCountColorable_iff_colorableBy _).2 (hall i)
    choose dlayer hdlayer using hlayerc
    have hEsscol :
        (⟨E'' \ {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}⟩ : Hypergraph W).ColorableBy ℵ₀ := by
      apply colorable_combine rank _ dlayer
      rintro e ⟨heE'', hne⟩
      have hne' : ¬ ∃ a, ∀ v ∈ e, rank v = a := fun h => hne ⟨heE'', h⟩
      obtain ⟨i, x, y, hxe, hye, hrx, hry, hadj⟩ :=
        Ess_adj H hts (3 * n ^ 2 + 1) rank hclaim e heE''.1 heE''.2 hne'
      exact ⟨i, x, hxe, y, hye, hrx, hry, hdlayer i x y hadj⟩
    have hunion := colorableBy_aleph0_union
      {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}
      (E'' \ {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}) hEstarcol hEsscol
    have hcov : {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a} ∪
        (E'' \ {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}) = E'' := by
      rw [Set.union_diff_cancel]; intro e he; exact he.1
    rw [hcov] at hunion
    exact hE''uc hunion
  obtain ⟨i₀, hi₀⟩ := hExists
  -- Erdős–Hajnal: the layer graph contains `K_{q,q}`
  set q := 4 * (3 * n ^ 2 + 1) * n ^ 3 + n ^ 2 + n with hqdef
  obtain ⟨a, b, hainj, hbinj, hab, hadj⟩ :=
    eh_hasKmm (layerGraph H (3 * n ^ 2 + 1) rank i₀) hi₀ q
  have hqpos : 0 < q := by positivity
  -- extract private vertices
  have hP : ∀ i j : Fin q, ∃ z, rank (a i) = i₀ ∧ rank (b j) = i₀ ∧ rank z < i₀ ∧
      ({a i, b j, z} : Set W) ∈ H.edges ∧
      ¬ hasRoot H (3 * n ^ 2 + 1) ({a i, b j, z} : Set W) := by
    intro i j
    have hh := hadj i j
    rw [layerGraph, SimpleGraph.fromRel_adj] at hh
    obtain ⟨_, hr⟩ := hh
    rcases hr with ⟨r1, r2, z, hz1, hz2, hz3⟩ | ⟨r1, r2, z, hz1, hz2, hz3⟩
    · exact ⟨z, r1, r2, hz1, hz2, hz3⟩
    · refine ⟨z, r2, r1, hz1, ?_, ?_⟩
      · rw [Set.insert_comm]; exact hz2
      · rw [Set.insert_comm]; exact hz3
  choose P hPra hPrb hPrz hPedge hPnr using hP
  -- column bound
  have hcol : ∀ (j : Fin q) (v : W),
      (Finset.univ.filter (fun i => P i j = v)).card < (3 * n ^ 2 + 1) := by
    intro j v
    by_contra hge
    push_neg at hge
    have hpos : 0 < (Finset.univ.filter (fun i => P i j = v)).card :=
      lt_of_lt_of_le (by positivity) hge
    obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hpos
    have hi0v : P i0 j = v := (Finset.mem_filter.mp hi0).2
    have hbv : b j ≠ v := by
      intro h; have := hPrz i0 j; rw [hi0v, ← h, hPrb i0 j] at this; exact lt_irrefl _ this
    refine delta_root_contra H (3 * n ^ 2 + 1) (by positivity) (b j) v hbv
      ((Finset.univ.filter (fun i => P i j = v)).image a) ?_ ?_ ?_ ?_
    · rw [Finset.card_image_of_injective _ hainj]; exact hge
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨i, ⟨_, hiv⟩, rfl⟩ := hx
      refine ⟨hab i j, ?_⟩
      intro h; have := hPrz i j; rw [hiv, ← h, hPra i j] at this; exact lt_irrefl _ this
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨i, ⟨_, hiv⟩, rfl⟩ := hx
      have := hPedge i j; rw [hiv] at this; exact this
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨i, ⟨_, hiv⟩, rfl⟩ := hx
      have := hPnr i j; rw [hiv] at this; exact this
  -- row bound
  have hrow : ∀ (i : Fin q) (v : W),
      (Finset.univ.filter (fun j => P i j = v)).card < (3 * n ^ 2 + 1) := by
    intro i v
    by_contra hge
    push_neg at hge
    have hpos : 0 < (Finset.univ.filter (fun j => P i j = v)).card :=
      lt_of_lt_of_le (by positivity) hge
    obtain ⟨j0, hj0⟩ := Finset.card_pos.mp hpos
    have hj0v : P i j0 = v := (Finset.mem_filter.mp hj0).2
    have hav : a i ≠ v := by
      intro h; have := hPrz i j0; rw [hj0v, ← h, hPra i j0] at this; exact lt_irrefl _ this
    refine delta_root_contra H (3 * n ^ 2 + 1) (by positivity) (a i) v hav
      ((Finset.univ.filter (fun j => P i j = v)).image b) ?_ ?_ ?_ ?_
    · rw [Finset.card_image_of_injective _ hbinj]; exact hge
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨j, ⟨_, hjv⟩, rfl⟩ := hx
      refine ⟨(hab i j).symm, ?_⟩
      intro h; have := hPrz i j; rw [hjv, ← h, hPrb i j] at this; exact lt_irrefl _ this
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨j, ⟨_, hjv⟩, rfl⟩ := hx
      have := hPedge i j; rw [hjv] at this
      rw [Set.insert_comm]; exact this
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨j, ⟨_, hjv⟩, rfl⟩ := hx
      have := hPnr i j; rw [hjv] at this
      rw [Set.insert_comm]; exact this
  -- rainbow grid
  obtain ⟨A, B, hAinj, hBinj, hgrid⟩ :=
    greedy_rainbow n (3 * n ^ 2 + 1) q (by omega) (le_of_eq hqdef.symm) P hrow hcol
  -- assemble `K^{(3)}_{n,n}`, contradiction
  refine hfree (hasK3nn_from_grid H n (fun i => a (A i)) (fun j => b (B j))
    (fun i j => P (A i) (B j)) ?_ ?_)
  · exact grid_injective rank n q i₀ a b A B P hainj hbinj hAinj hBinj hab hgrid
      (fun k => hPra k ⟨0, hqpos⟩) (fun k => hPrb ⟨0, hqpos⟩ k)
      (fun i j => hPrz (A i) (B j))
  · intro i j; exact hPedge (A i) (B j)

/-- **The delta-system theorem.**  Every triple system of uncountable chromatic
number contains a copy of `K^{(3)}_{n,n}` (Reiher's Theorem 1.2, `k = 3`). -/
theorem hasK3nn_of_uncountable (H : Hypergraph W) (hts : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) (n : ℕ) : HasK3nn H n := by
  have key : ∀ κ : Cardinal.{u}, ∀ (W : Type u) (H : Hypergraph W),
      #W = κ → H.IsTripleSystem → H.UncountablyChromatic → HasK3nn H n := by
    refine fun κ => Cardinal.lt_wf.induction
      (C := fun κ => ∀ (W : Type u) (H : Hypergraph W),
        #W = κ → H.IsTripleSystem → H.UncountablyChromatic → HasK3nn H n) κ ?_
    intro κ IH W H hcard hts huc
    by_contra hfree
    have hbig : ℵ₀ < #W := by
      by_contra hle
      exact huc (tripleSystem_colorable_of_le_aleph0 H hts (not_lt.mp hle))
    refine hasK3nn_step H hts n hbig huc hfree (fun W' H' hlt hts' hfree' => ?_)
    by_contra hcc'
    exact hfree' (IH (#W') (hcard ▸ hlt) W' H' rfl hts' hcc')
  exact key (#W) W H rfl hts huc

open Classical in
/-- **E4 (Reiher, `k = 3`).**  `K^{(3)}_{n,n}` is obligatory for every `n`. -/
theorem e4_Reiher : E4_Reiher.{u} := by
  intro n W H hts huc
  exact hasK3nn_embeds H n (hasK3nn_of_uncountable H hts huc n)

end Erdos1177

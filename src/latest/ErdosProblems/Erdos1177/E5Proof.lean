-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.External
import ErdosProblems.Erdos1177.AmalgHelpers

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Verified infrastructure toward E5 (Hajnal–Komjáth: the loose 7-cycle)

E5 states that the loose `7`-cycle `C₇^{(3)}` is *linearly obligatory*: it embeds
into every linear triple system of uncountable chromatic number.  This file
formalizes reductions and the finite embedding bookkeeping used by that theorem.
-/

open Cardinal

namespace Erdos1177

universe u

variable {W : Type u}

/-- The **shadow graph** of a hypergraph `H`: two vertices are adjacent iff they
are distinct and lie in a common edge of `H`. -/
def shadowGraph (H : Hypergraph W) : SimpleGraph W :=
  SimpleGraph.fromRel (fun u v => ∃ e ∈ H.edges, u ∈ e ∧ v ∈ e)

/-- If a triple system is uncountably chromatic, then so is its shadow graph. -/
theorem shadow_uncountablyChromatic (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic) :
    (SimpleGraph.toHG (shadowGraph H)).UncountablyChromatic := by
  contrapose! huc
  obtain ⟨c, hc⟩ := Classical.not_not.1 huc
  simp_all +decide [Hypergraph.UncountablyChromatic]
  use c
  intro e he
  specialize htri e he
  obtain ⟨a, b, d, hab, hbd, had⟩ := Set.ncard_eq_three.mp htri
  simp_all +decide [SimpleGraph.toHG]
  have := hc {a, b}
  simp_all +decide [shadowGraph]
  grind

/-- Any two distinct vertices of an edge are adjacent in the shadow graph. -/
theorem shadowGraph_adj_of_mem_edge (H : Hypergraph W) {e : Set W} (he : e ∈ H.edges)
    {u v : W} (hu : u ∈ e) (hv : v ∈ e) (huv : u ≠ v) :
    (shadowGraph H).Adj u v := by
  rw [shadowGraph, SimpleGraph.fromRel_adj]
  exact ⟨huv, Or.inl ⟨e, he, hu, hv⟩⟩

/-- In a linear hypergraph, a pair of distinct vertices lies in at most one edge. -/
theorem linear_edge_unique_of_pair (H : Hypergraph W) (hlin : H.Linear)
    {e₁ e₂ : Set W} (he₁ : e₁ ∈ H.edges) (he₂ : e₂ ∈ H.edges)
    {u v : W} (huv : u ≠ v)
    (hu₁ : u ∈ e₁) (hv₁ : v ∈ e₁) (hu₂ : u ∈ e₂) (hv₂ : v ∈ e₂) :
    e₁ = e₂ := by
  by_contra hne
  exact huv (hlin e₁ he₁ e₂ he₂ hne ⟨hu₁, hu₂⟩ ⟨hv₁, hv₂⟩)

/-- Countably many edges implies countable colourability for a triple system. -/
theorem colorable_of_countable_edges (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hcnt : H.edges.Countable) :
    H.ColorableBy ℵ₀ := by
  classical
  set S : Set W := ⋃₀ H.edges with hS
  have hScnt : S.Countable := by
    apply Set.Countable.sUnion hcnt
    intro e he
    have h3 := htri e he
    rw [Set.ncard_eq_three] at h3
    obtain ⟨a, b, c, -, -, -, rfl⟩ := h3
    exact (Set.toFinite _).countable
  obtain ⟨ι, hι⟩ := hScnt.exists_injective_nat
  have hInf : Infinite ((ℵ₀ : Cardinal).out) :=
    Cardinal.infinite_iff.mpr (by rw [Cardinal.mk_out])
  set g : ℕ ↪ (ℵ₀ : Cardinal).out := Infinite.natEmbedding _ with hg
  refine ⟨fun w => if h : w ∈ S then g (ι ⟨w, h⟩) else g 0, ?_⟩
  intro e he
  have h3 := htri e he
  rw [Set.ncard_eq_three] at h3
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := h3
  have hxS : x ∈ S := Set.subset_sUnion_of_mem he (by simp)
  have hyS : y ∈ S := Set.subset_sUnion_of_mem he (by simp)
  refine ⟨x, by simp, y, by simp, ?_⟩
  simp only [dif_pos hxS, dif_pos hyS]
  intro hcontra
  exact hxy (congrArg Subtype.val (hι (g.injective hcontra)))

/-- An uncountably chromatic triple system has uncountably many edges. -/
theorem uncountable_edges_of_uncountablyChromatic (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic) :
    ¬ H.edges.Countable :=
  fun hcnt => huc (colorable_of_countable_edges H htri hcnt)

/-! ## Private-third-vertex infrastructure -/

/-
A three-element edge containing distinct `a,b` has a unique third vertex.
-/
theorem triple_edge_private_vertex (H : Hypergraph W) (htri : H.IsTripleSystem)
    {e : Set W} (he : e ∈ H.edges) {a b : W} (hab : a ≠ b)
    (ha : a ∈ e) (hb : b ∈ e) :
    ∃! y, y ∈ e ∧ y ≠ a ∧ y ≠ b := by
  obtain ⟨c, hc⟩ : ∃ c : W, c ∈ e ∧ c ≠ a ∧ c ≠ b := by
    contrapose! htri;
    exact fun h => by have := h e he; rw [ show e = { a, b } by ext x; by_cases hx : x = a <;> aesop ] at this; simp +decide [ hab ] at this;
  refine' ⟨ c, hc, fun y hy => _ ⟩;
  have := htri e he; rw [ Set.ncard_eq_three ] at this; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; simp_all +decide ;
  grind

/-
The edge is exactly the pair together with its private third vertex.
-/
theorem triple_edge_eq_pair_insert (H : Hypergraph W) (htri : H.IsTripleSystem)
    {e : Set W} (he : e ∈ H.edges) {a b y : W} (hab : a ≠ b)
    (ha : a ∈ e) (hb : b ∈ e) (hy : y ∈ e) (hya : y ≠ a) (hyb : y ≠ b) :
    e = {a, b, y} := by
  have h_card : e.ncard = 3 := by
    exact htri e he;
  rw [ @Set.ncard_eq_three ] at h_card;
  grind

/-- Data that directly witnesses a loose seven-cycle in a host.  Packaging the
single injectivity condition on the sum is convenient because it simultaneously
asserts that all core and private vertices are distinct. -/
structure Loose7Witness (H : Hypergraph W) where
  core : Fin 7 → W
  priv : Fin 7 → W
  injective : Function.Injective (Sum.elim core priv)
  edge_mem : ∀ i : Fin 7,
    ({core i, core (i + 1), priv i} : Set W) ∈ H.edges

/-
A loose-seven witness gives precisely an embedding of `looseCycle7`.
-/
theorem looseCycle7_embeds_of_witness (H : Hypergraph W) (w : Loose7Witness H) :
    looseCycle7.Embeds H := by
  use fun x => Sum.elim w.core w.priv x;
  refine' ⟨ _, _ ⟩;
  · exact w.injective;
  · simp +decide [ looseCycle7 ];
    simp +decide [ Set.image_insert_eq, Set.image_singleton ];
    exact fun i => w.edge_mem i

/-
Conversely, an embedding of `looseCycle7` supplies a witness with named
core and private vertices.
-/
theorem loose7Witness_of_embeds (H : Hypergraph W) (h : looseCycle7.Embeds H) :
    Nonempty (Loose7Witness H) := by
  obtain ⟨ f, hf ⟩ := h;
  refine' ⟨ ⟨ fun i => f ( Sum.inl i ), fun i => f ( Sum.inr i ), _, _ ⟩ ⟩;
  · intro x y hxy;
    cases x <;> cases y <;> simp_all +decide [ hf.1.eq_iff ];
  · intro i;
    convert! hf.2 _ _;
    rotate_left;
    exact { Sum.inl i, Sum.inl ( i + 1 ), Sum.inr i };
    · fin_cases i <;> simp +decide [ looseCycle7 ];
    · simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.image_insert_eq, Set.image_singleton]

/-
The bundled witness and the original embedding predicate are equivalent.
-/
theorem looseCycle7_embeds_iff_witness (H : Hypergraph W) :
    looseCycle7.Embeds H ↔ Nonempty (Loose7Witness H) := by
  exact ⟨ fun h => loose7Witness_of_embeds H h, fun h => looseCycle7_embeds_of_witness H ( Classical.choice h ) ⟩

/-
A more elementary criterion for the injectivity field of `Loose7Witness`.
-/
theorem sum_elim_injective_of_disjoint
    {x y : Fin 7 → W} (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i ≠ y j) : Function.Injective (Sum.elim x y) := by
  intro a b; cases a <;> cases b <;> simp_all +decide [ hx.eq_iff, hy.eq_iff ] ;
  exact Ne.symm ( hxy _ _ )

/-
Construct a loose-seven embedding from separately stated distinctness and
edge conditions.  This is the finite endpoint needed from the infinitary
Hajnal–Komjáth argument.
-/
theorem looseCycle7_embeds_of_core_private
    (H : Hypergraph W) (x y : Fin 7 → W)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i ≠ y j)
    (hedge : ∀ i : Fin 7, ({x i, x (i + 1), y i} : Set W) ∈ H.edges) :
    looseCycle7.Embeds H := by
  apply looseCycle7_embeds_of_witness;
  exact ⟨ x, y, sum_elim_injective_of_disjoint hx hy hxy, hedge ⟩

/-! ## Deleting a countable set of vertices -/

/-- The family of edges meeting `S`. -/
def edgesMeeting (H : Hypergraph W) (S : Set W) : Set (Set W) :=
  {e | e ∈ H.edges ∧ (e ∩ S).Nonempty}

/-
Every vertex of a three-element edge has another vertex beside it.
-/
theorem triple_edge_has_other (H : Hypergraph W) (htri : H.IsTripleSystem)
    {e : Set W} (he : e ∈ H.edges) (u : W) :
    ∃ v ∈ e, v ≠ u := by
  have h_card : e.ncard = 3 := by
    exact htri e he;
  exact Set.exists_ne_of_one_lt_ncard ( by linarith ) u

/-- If `S` is countable, all edges meeting `S` form a countably colourable
subhypergraph.  The colouring separates every point of `S` from all points
outside `S`, and is injective on `S`. -/
theorem colorable_edgesMeeting (H : Hypergraph W) (htri : H.IsTripleSystem)
    {S : Set W} (hS : S.Countable) :
    (⟨edgesMeeting H S⟩ : Hypergraph W).ColorableBy ℵ₀ := by
  classical
  letI : Countable S := hS.to_subtype
  let c : W → S ⊕ Unit := fun w =>
    if hw : w ∈ S then Sum.inl ⟨w, hw⟩ else Sum.inr ()
  apply colorableBy_aleph0_of_countable (T := S ⊕ Unit)
      (⟨edgesMeeting H S⟩ : Hypergraph W) Cardinal.mk_le_aleph0
  show (⟨edgesMeeting H S⟩ : Hypergraph W).ProperColoring c
  intro e he
  rcases he.2 with ⟨u, hue, huS⟩
  obtain ⟨v, hve, hvu⟩ := triple_edge_has_other H htri he.1 u
  refine ⟨u, hue, v, hve, ?_⟩
  by_cases hvS : v ∈ S
  · simp only [c, dif_pos huS, dif_pos hvS]
    intro huv
    have huv' : (⟨u, huS⟩ : S) = ⟨v, hvS⟩ := Sum.inl.inj huv
    exact hvu (congrArg Subtype.val huv').symm
  · simp [c, huS, hvS]

/-
Removing every edge that meets a countable vertex set preserves
uncountable chromatic number.
-/
theorem uncountablyChromatic_avoid_countable (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    {S : Set W} (hS : S.Countable) :
    (⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩ : Hypergraph W).UncountablyChromatic := by
  have h_diff : (⟨H.edges \ edgesMeeting H S⟩ : Hypergraph W).UncountablyChromatic := by
    convert! uncountablyChromatic_diff H.edges ( edgesMeeting H S ) huc ( colorable_edgesMeeting H htri hS ) using 1;
  convert! h_diff using 2 ; ext ; simp +decide [ edgesMeeting ];
  simp +contextual [ Set.subset_def, Set.Nonempty ]

/-
Consequently an uncountably chromatic triple system has an edge disjoint
from every prescribed countable set.
-/
theorem exists_edge_disjoint_countable (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    {S : Set W} (hS : S.Countable) :
    ∃ e ∈ H.edges, e ⊆ Sᶜ := by
  contrapose! huc;
  convert! colorable_edgesMeeting H htri hS using 1;
  constructor <;> intro h <;> simp_all +decide [ Hypergraph.UncountablyChromatic ];
  · convert! colorable_edgesMeeting H htri hS using 1;
  · obtain ⟨ c, hc ⟩ := h;
    use c;
    intro e he; specialize hc e; simp_all +decide [ edgesMeeting ] ;
    exact hc ( by simpa [ Set.not_subset ] using! huc e he )

/-! ## Clean edge cycles

The infinitary part of the Hajnal–Komjáth argument naturally produces edges
rather than already named private vertices.  The following criterion packages
the exact finite ``clean cycle'' endpoint: each edge contains its two consecutive
core vertices, contains no other core vertex, and two distinct cycle edges can
intersect only in the core. -/

/-- A clean cyclic family of seven host edges. -/
structure CleanLoose7EdgeCycle (H : Hypergraph W) where
  core : Fin 7 → W
  edge : Fin 7 → Set W
  core_injective : Function.Injective core
  edge_mem : ∀ i, edge i ∈ H.edges
  left_mem : ∀ i, core i ∈ edge i
  right_mem : ∀ i, core (i + 1) ∈ edge i
  core_mem_iff : ∀ i j, core j ∈ edge i ↔ j = i ∨ j = i + 1
  inter_subset_core : ∀ ⦃i j⦄, i ≠ j → edge i ∩ edge j ⊆ Set.range core

/-
Every clean seven-edge cycle in a triple system is a copy of the loose
seven-cycle.  This removes all private-vertex bookkeeping from the remaining
infinitary argument.
-/
theorem looseCycle7_embeds_of_cleanEdgeCycle (H : Hypergraph W)
    (htri : H.IsTripleSystem) (c : CleanLoose7EdgeCycle H) :
    looseCycle7.Embeds H := by
      obtain ⟨core, edge, core_injective, edge_mem, left_mem, right_mem, core_mem_iff, inter_subset_core⟩ := c;
      obtain ⟨p, hp⟩ : ∃ p : Fin 7 → W, (∀ i, p i ∈ edge i ∧ p i ≠ core i ∧ p i ≠ core (i + 1)) ∧ (∀ i j, i ≠ j → p i ≠ p j) ∧ (∀ i j, p i ≠ core j) := by
        obtain ⟨p, hp⟩ : ∃ p : Fin 7 → W, (∀ i, p i ∈ edge i ∧ p i ≠ core i ∧ p i ≠ core (i + 1)) := by
          have hp_exists : ∀ i, ∃ p : W, p ∈ edge i ∧ p ≠ core i ∧ p ≠ core (i + 1) := by
            intro i
            have h_card : (edge i).ncard = 3 := by
              exact htri _ ( edge_mem i )
            have h_core : core i ∈ edge i ∧ core (i + 1) ∈ edge i := by
              exact ⟨ left_mem i, right_mem i ⟩
            have h_distinct : core i ≠ core (i + 1) := by
              exact core_injective.ne ( by fin_cases i <;> trivial )
            have h_card_core : (edge i \ {core i, core (i + 1)}).ncard = 1 := by
              rw [ Set.ncard_diff _ _ ] <;> simp_all +decide [ Set.ncard_eq_toFinset_card' ];
              simp_all +decide [ Set.insert_subset_iff ]
            obtain ⟨p, hp⟩ : ∃ p, p ∈ edge i \ {core i, core (i + 1)} := by
              exact Set.nonempty_of_ncard_ne_zero ( h_card_core.symm ▸ by decide )
            use p
            simp [hp];
            exact ⟨ hp.1, by rintro rfl; exact hp.2 ( by simp +decide ), by rintro rfl; exact hp.2 ( by simp +decide ) ⟩;
          exact ⟨ fun i => Classical.choose ( hp_exists i ), fun i => Classical.choose_spec ( hp_exists i ) ⟩;
        refine' ⟨ p, hp, _, _ ⟩;
        · intro i j hij h_eq
          have h_common : p i ∈ edge i ∩ edge j := by
            grind;
          grind;
        · intro i j hij; specialize hp i; specialize core_mem_iff i j; aesop;
      convert! looseCycle7_embeds_of_core_private H core p _ _ _ _ using 1;
      · assumption;
      · exact fun i j hij => Classical.not_not.1 fun hi => hp.2.1 i j hi hij;
      · exact fun i j => Ne.symm ( hp.2.2 j i );
      · intro i
        have h_edge : edge i = {core i, core (i + 1), p i} := by
          apply triple_edge_eq_pair_insert H htri (edge_mem i) (core_injective.ne (by
          fin_cases i <;> decide)) (left_mem i) (right_mem i) (hp.left i).left (hp.left i).right.left (hp.left i).right.right;
        exact h_edge ▸ edge_mem i

/-
The exact core-incidence condition forces the seven cycle edges to be pairwise
distinct.
-/
theorem cleanEdgeCycle_edge_injective (H : Hypergraph W)
    (c : CleanLoose7EdgeCycle H) : Function.Injective c.edge := by
      intro i j hij; have := c.core_mem_iff i i; have := c.core_mem_iff j j; simp_all +decide ;
      grind +suggestions

/-
The entire E5 theorem reduces to producing a clean seven-edge cycle in
each linear uncountably chromatic triple system.
-/
theorem e5_HK_loose7_of_cleanEdgeCycle
    (hclean : ∀ {W : Type u} (H : Hypergraph W), H.IsTripleSystem → H.Linear →
      H.UncountablyChromatic → Nonempty (CleanLoose7EdgeCycle H)) :
    E5_HK_loose7.{u} := by
      intro W H htri hlin huc;
      exact looseCycle7_embeds_of_cleanEdgeCycle H htri (hclean H htri hlin huc).some

/-! ## Arbitrarily large finite matchings away from countable sets -/

/-
An uncountably chromatic triple system contains arbitrarily large finite
matchings disjoint from any prescribed countable set.  This is a useful
reservoir fact for recursive clean-cycle constructions.
-/
theorem exists_finite_edge_matching_avoid_countable (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    {S : Set W} (hS : S.Countable) (n : ℕ) :
    ∃ es : Fin n → Set W,
      (∀ i, es i ∈ H.edges ∧ es i ⊆ Sᶜ) ∧
      (∀ ⦃i j⦄, i ≠ j → Disjoint (es i) (es j)) := by
        induction' n with n ih;
        · exact ⟨ fun _ => ∅, by simp +decide ⟩;
        · obtain ⟨es, hes⟩ := ih
          obtain ⟨e, he⟩ : ∃ e ∈ H.edges, e ⊆ (S ∪ (⋃ i : Fin n, es i))ᶜ := by
            apply exists_edge_disjoint_countable H htri huc;
            refine' Set.Countable.union hS _;
            exact Set.countable_iUnion fun i => Set.Finite.countable <| Set.finite_coe_iff.mp <| by have := htri ( es i ) ( hes.1 i |>.1 ) ; exact Set.finite_of_ncard_pos ( by linarith ) ;
          refine' ⟨ Fin.cons e es, _, _ ⟩ <;> simp_all +decide [ Fin.forall_fin_succ, Set.subset_def ];
          · exact fun i x hx => hes.1 i |>.2 x hx;
          · exact ⟨ fun i hi => Set.disjoint_left.mpr fun x hx hx' => he.2 x hx |>.2 i hx', fun i => Set.disjoint_left.mpr fun x hx hx' => he.2 x hx' |>.2 i hx ⟩

/-
An uncountably chromatic triple system contains a countably infinite
matching avoiding any prescribed countable set.
-/
theorem exists_countable_edge_matching_avoid_countable (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    {S : Set W} (hS : S.Countable) :
    ∃ es : ℕ → Set W,
      (∀ i, es i ∈ H.edges ∧ es i ⊆ Sᶜ) ∧
      (∀ ⦃i j⦄, i ≠ j → Disjoint (es i) (es j)) := by
        obtain ⟨es, hes⟩ : ∃ es : ℕ → Set W, (∀ i, es i ∈ H.edges ∧ es i ⊆ Sᶜ) ∧ (∀ i j, i < j → Disjoint (es i) (es j)) := by
          obtain ⟨es, hes⟩ : ∃ es : ℕ → Set W, (∀ i, es i ∈ H.edges ∧ es i ⊆ Sᶜ) ∧ (∀ i, es i ⊆ Sᶜ) ∧ (∀ i j, i < j → Disjoint (es i) (es j)) := by
            have h_rec : ∀ (S' : Set W), S'.Countable → ∃ e ∈ H.edges, e ⊆ S'ᶜ := by
              exact fun S' hS' => exists_edge_disjoint_countable H htri huc hS'
            choose! f hf using h_rec;
            -- Define the sequence of sets $S_n$ recursively.
            have h_seq : ∃ S_n : ℕ → Set W, S_n 0 = S ∧ ∀ n, S_n (n + 1) = S_n n ∪ f (S_n n) := by
              exact ⟨ fun n => Nat.recOn n S fun n ih => ih ∪ f ih, rfl, fun n => rfl ⟩;
            obtain ⟨S_n, hS_n₀, hS_n⟩ := h_seq
            have hS_n_countable : ∀ n, (S_n n).Countable := by
              intro n; induction' n with n ih <;> simp_all +decide [ Set.countable_union ] ;
              have := htri ( f ( S_n n ) ) ( hf ( S_n n ) ih |>.1 );
              exact Set.finite_of_ncard_pos ( by linarith ) |> Set.Finite.countable;
            refine' ⟨ fun n => f ( S_n n ), _, _, _ ⟩ <;> simp_all +decide [ Set.disjoint_left ];
            · intro n; specialize hf ( S_n n ) ( hS_n_countable n ) ; simp_all +decide [ Set.subset_def ] ;
              exact fun x hx hx' => hf.2 x hx ( show x ∈ S_n n from by exact Nat.recOn n ( by aesop ) fun n ihn => by aesop );
            · intro n; specialize hf ( S_n n ) ( hS_n_countable n ) ; simp_all +decide [ Set.subset_def ] ;
              exact fun x hx hx' => hf.2 x hx ( by exact Nat.recOn n ( by aesop ) fun n ihn => by aesop );
            · intro i j hij a ha hb; have := hf ( S_n j ) ( hS_n_countable j ) ; simp_all +decide [ Set.subset_def ] ;
              have h_seq : ∀ n ≥ i + 1, a ∈ S_n n := by
                intro n hn; induction hn <;> aesop;
              exact hf ( S_n j ) ( hS_n_countable j ) |>.2 a hb ( h_seq j ( by linarith ) );
          exact ⟨ es, hes.1, hes.2.2 ⟩;
        exact ⟨ es, hes.1, fun i j hij => by cases lt_or_gt_of_ne hij <;> [ exact hes.2 _ _ ‹_› ; exact Disjoint.symm ( hes.2 _ _ ‹_› ) ] ⟩

/-! ## Deleting countably many edges -/

/-
Deleting a countable family of edges from an uncountably chromatic triple
system preserves uncountable chromaticity.
-/
theorem uncountablyChromatic_delete_countable_edges (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    {D : Set (Set W)} (hD : D.Countable) :
    (⟨H.edges \ D⟩ : Hypergraph W).UncountablyChromatic := by
      -- Since H.edges ∩ D is countable, the hypergraph with edges H.edges ∩ D is countably colorable by colorable_of_countable_edges.
      have h_countable_colorable : (⟨H.edges ∩ D⟩ : Hypergraph W).ColorableBy ℵ₀ := by
        apply Erdos1177.colorable_of_countable_edges;
        · exact fun e he => htri e he.1;
        · exact hD.mono fun x hx => hx.2;
      convert! uncountablyChromatic_diff H.edges ( H.edges ∩ D ) huc h_countable_colorable using 1;
      aesop

/-
In particular, no countable list exhausts the edge set of an uncountably
chromatic triple system.
-/
theorem exists_edge_outside_countable (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    {D : Set (Set W)} (hD : D.Countable) :
    ∃ e ∈ H.edges, e ∉ D := by
      by_contra! h;
      -- If `∀ e ∈ H.edges, e ∈ D`, then `D` would contain all edges of `H`, contradicting `huc`.
      have h_all_edges_in_D : H.edges ⊆ D := by
        exact h;
      apply uncountable_edges_of_uncountablyChromatic H htri huc;
      exact hD.mono h_all_edges_in_D

/-! ## A local-intersection criterion for clean cycles -/

/-
A convenient weakening of `CleanLoose7EdgeCycle`: it suffices to know that
any vertex shared by two distinct cycle edges is one of the two designated core
vertices of the first edge.  Linearity is not needed for this finite conversion.
-/
theorem cleanLoose7EdgeCycle_of_local_intersections (H : Hypergraph W)
    (core : Fin 7 → W) (edge : Fin 7 → Set W)
    (hcore : Function.Injective core)
    (hedge : ∀ i, edge i ∈ H.edges)
    (hleft : ∀ i, core i ∈ edge i)
    (hright : ∀ i, core (i + 1) ∈ edge i)
    (hinter : ∀ ⦃i j : Fin 7⦄, i ≠ j →
      edge i ∩ edge j ⊆ ({core i, core (i + 1)} : Set W)) :
    Nonempty (CleanLoose7EdgeCycle H) := by
  refine' ⟨ ⟨ core, edge, hcore, hedge, hleft, hright, _, _ ⟩ ⟩;
  · intro i j;
    by_cases hij : i = j;
    · aesop;
    · specialize @hinter i j hij;
      by_cases h : core j ∈ edge i <;> simp_all +decide [ Set.subset_def ];
      · cases hinter _ h ( show core j ∈ edge j from hleft _ ) <;> simp_all +decide [ hcore.eq_iff ];
      · grind;
  · exact fun i j hij => Set.Subset.trans ( hinter hij ) ( Set.insert_subset_iff.mpr ⟨ Set.mem_range_self _, Set.singleton_subset_iff.mpr ( Set.mem_range_self _ ) ⟩ )

/-
The local-intersection criterion already gives a loose seven-cycle in every
triple system.  This is the form most directly usable after a recursive edge
selection argument.
-/
theorem looseCycle7_embeds_of_local_intersections (H : Hypergraph W)
    (htri : H.IsTripleSystem)
    (core : Fin 7 → W) (edge : Fin 7 → Set W)
    (hcore : Function.Injective core)
    (hedge : ∀ i, edge i ∈ H.edges)
    (hleft : ∀ i, core i ∈ edge i)
    (hright : ∀ i, core (i + 1) ∈ edge i)
    (hinter : ∀ ⦃i j : Fin 7⦄, i ≠ j →
      edge i ∩ edge j ⊆ ({core i, core (i + 1)} : Set W)) :
    looseCycle7.Embeds H := by
  have h_clean_cycle : ∃ c : CleanLoose7EdgeCycle H, True := by
    exact ⟨ cleanLoose7EdgeCycle_of_local_intersections H core edge hcore hedge hleft hright hinter |> Classical.choice, trivial ⟩;
  exact looseCycle7_embeds_of_cleanEdgeCycle H htri h_clean_cycle.choose

/-
A pairwise-disjoint family of nonempty edges is automatically indexed
injectively.
-/
theorem edge_family_injective_of_pairwise_disjoint
    {ι : Type*} (es : ι → Set W)
    (hne : ∀ i, (es i).Nonempty)
    (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (es i) (es j)) :
    Function.Injective es := by
  intro i j hij; specialize hdisj; by_contra hneq; simp_all +decide [ Set.disjoint_left ] ;
  exact hdisj hneq ( hne i |> Classical.choose_spec ) ( hij ▸ ( hne i |> Classical.choose_spec ) )

/-
The countable matching produced above consists of pairwise distinct host
edges.
-/
theorem exists_countable_injective_edge_matching_avoid_countable
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable) :
    ∃ es : ℕ → Set W,
      Function.Injective es ∧
      (∀ i, es i ∈ H.edges ∧ es i ⊆ Sᶜ) ∧
      (∀ ⦃i j⦄, i ≠ j → Disjoint (es i) (es j)) := by
  convert! exists_countable_edge_matching_avoid_countable H htri huc hS using 1;
  ext;
  exact ⟨ fun h => ⟨ h.2.1, h.2.2 ⟩, fun h => ⟨ edge_family_injective_of_pairwise_disjoint _ ( fun i => Set.nonempty_of_ncard_ne_zero ( by rw [ htri _ ( h.1 i |>.1 ) ] ; norm_num ) ) h.2, h.1, h.2 ⟩ ⟩

/-! ## Countable edge reservoirs and their residual hypergraph -/

/-
The vertices covered by a countable family of edges in a triple system form
 a countable set.
-/
theorem countable_edge_family_vertex_union (H : Hypergraph W)
    (htri : H.IsTripleSystem) {D : Set (Set W)} (hD : D.Countable)
    (hsub : D ⊆ H.edges) : (⋃₀ D).Countable := by
  have h_countable : ∀ e ∈ D, e.Countable := by
    exact fun e he => Set.Finite.countable <| Set.Finite.subset ( Set.finite_of_ncard_ne_zero <| by have := htri e ( hsub he ) ; aesop ) <| Set.Subset.refl _;
  exact Set.Countable.sUnion hD h_countable

/-
After removing every vertex covered by a countable family of host edges,
uncountable chromaticity remains.
-/
theorem uncountablyChromatic_avoid_countable_edge_union (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    {D : Set (Set W)} (hD : D.Countable) (hsub : D ⊆ H.edges) :
    (⟨{e | e ∈ H.edges ∧ e ⊆ (⋃₀ D)ᶜ}⟩ : Hypergraph W).UncountablyChromatic := by
  convert! uncountablyChromatic_avoid_countable H htri huc ( countable_edge_family_vertex_union H htri hD hsub ) using 1

/-
One can choose a countably infinite matching away from `S` while retaining
an uncountably chromatic residual triple system disjoint from every selected
edge.  This packages the reservoir needed for subsequent recursive arguments.
-/
theorem exists_countable_matching_and_uncountable_residual
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable) :
    ∃ es : ℕ → Set W,
      Function.Injective es ∧
      (∀ i, es i ∈ H.edges ∧ es i ⊆ Sᶜ) ∧
      (∀ ⦃i j⦄, i ≠ j → Disjoint (es i) (es j)) ∧
      (⟨{e | e ∈ H.edges ∧ e ⊆ (S ∪ ⋃ i, es i)ᶜ}⟩ : Hypergraph W).UncountablyChromatic := by
  obtain ⟨es, hes⟩ := exists_countable_injective_edge_matching_avoid_countable H htri huc hS;
  refine' ⟨ es, hes.1, hes.2.1, hes.2.2, _ ⟩;
  convert! uncountablyChromatic_avoid_countable H htri huc ( hS.union ?_ ) using 1;
  exact Set.countable_iUnion fun i => Set.Finite.countable ( show Set.Finite ( es i ) from by
                                                              exact Set.finite_of_ncard_pos ( by rw [ htri _ ( hes.2.1 i |>.1 ) ] ; norm_num ) )

/-! ## Finite high-chromatic cores in the shadow graph

The next compactness consequences isolate finite obstructions inside every
uncountably chromatic triple system.  They are useful when the infinitary E5
argument is organized by finite approximations.
-/

/-
A proper finite colouring of the shadow graph gives a countable proper
colouring of the original triple system.
-/
theorem colorableBy_aleph0_of_shadow_fin_coloring (H : Hypergraph W)
    (htri : H.IsTripleSystem) (k : ℕ) [NeZero k]
    (c : W → Fin k) (hc : ∀ a b, (shadowGraph H).Adj a b → c a ≠ c b) :
    H.ColorableBy ℵ₀ := by
  -- Since the shadow graph is colorable by ℵ₀, the original hypergraph is colorable by ℵ₀.
  apply colorableBy_aleph0_of_countable;
  convert! Cardinal.mk_le_aleph0;
  exact ULift ( Fin k );
  exact inferInstance;
  swap;
  exact fun x => ⟨ c x ⟩;
  intro e he;
  obtain ⟨ u, hu, v, hv, huv ⟩ := htri e he |> fun h => Set.ncard_eq_three.mp h;
  grind +suggestions

/-
For every positive finite number of colours, some finite vertex set already
witnesses failure of that many colours in the shadow graph.
-/
theorem exists_finite_shadow_coloring_obstruction (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    (k : ℕ) [NeZero k] :
    ∃ s : Finset W, ∀ c : W → Fin k,
      ∃ a ∈ s, ∃ b ∈ s, (shadowGraph H).Adj a b ∧ c a = c b := by
  by_contra! h;
  obtain ⟨c, hc⟩ := colorable_of_forall_finite ( shadowGraph H ) k h;
  exact huc <| colorableBy_aleph0_of_shadow_fin_coloring H htri k c hc

/-
All shadow adjacencies within a finite vertex set can be covered by a
finite family of actual host edges.
-/
theorem exists_finite_edges_cover_shadow_on (H : Hypergraph W)
    (s : Finset W) :
    ∃ D : Finset (Set W),
      (∀ e ∈ D, e ∈ H.edges) ∧
      ∀ a ∈ s, ∀ b ∈ s, (shadowGraph H).Adj a b →
        ∃ e ∈ D, a ∈ e ∧ b ∈ e := by
  by_contra! h_contra;
  -- Define the set of all adjacency pairs in the finite vertex set s.
  set pairs := {p : W × W | p.1 ∈ s ∧ p.2 ∈ s ∧ (shadowGraph H).Adj p.1 p.2} with hpairs_def;
  -- By definition of pairs, for each pair (a, b) in pairs, there exists an edge e in H.edges such that a ∈ e and b ∈ e.
  have h_pairs_edges : ∀ p ∈ pairs, ∃ e ∈ H.edges, p.1 ∈ e ∧ p.2 ∈ e := by
    simp +zetaDelta at *;
    intro a b ha hb hab; rcases hab with ⟨ hab, ⟨ e, he, ha, hb ⟩ ⟩ ; use e; aesop;
  choose! f hf₁ hf₂ hf₃ using h_pairs_edges;
  -- Since pairs is finite, the image of f over pairs is also finite.
  have h_image_finite : Set.Finite (Set.image f pairs) := by
    exact Set.Finite.image f ( Set.Finite.subset ( s.finite_toSet.prod s.finite_toSet ) fun p hp => ⟨ hp.1, hp.2.1 ⟩ );
  obtain ⟨ D, hD ⟩ := h_image_finite.exists_finset_coe;
  obtain ⟨ a, ha, b, hb, hab, h ⟩ := h_contra D ( fun e he => by rw [ Set.ext_iff ] at hD; specialize hD e; aesop ) ; specialize h ( f ( a, b ) ) ; simp_all +decide ;
  exact h ( hD.symm.subset ⟨ ( a, b ), ⟨ ha, hb, hab ⟩, rfl ⟩ )

/-
For a finite edge, the set of colourings that are nonconstant on that
edge is closed in the product topology.
-/
theorem isClosed_edgeProperColorings (k : ℕ) (e : Set W) (he : e.Finite) :
    IsClosed {c : W → Fin k |
      ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ c u ≠ c v} := by
  convert! isClosed_biUnion_finset ( s := ( he.toFinset : Finset W ) ) ( fun u hu => isClosed_biUnion_finset ( s := ( he.toFinset : Finset W ) ) ( fun v hv => ?_ ) ) using 1;
  rotate_left;
  use fun u v => { c : W → Fin k | c u ≠ c v };
  · exact isClosed_compl_iff.mpr ( isOpen_discrete { x : Fin k × Fin k | x.1 = x.2 } |> IsOpen.preimage ( show Continuous fun c : W → Fin k => ( c u, c v ) from Continuous.prodMk ( continuous_apply _ ) ( continuous_apply _ ) ) );
  · ext; aesop

/-- Compactness for weak hypergraph colourings, formulated using finite edge
subfamilies. -/
theorem hypergraph_coloring_compactness (H : Hypergraph W)
    (htri : H.IsTripleSystem) (k : ℕ) [NeZero k]
    (hfin : ∀ D : Finset (Set W), (∀ e ∈ D, e ∈ H.edges) →
      ∃ c : W → Fin k, (⟨(D : Set (Set W))⟩ : Hypergraph W).ProperColoring c) :
    ∃ c : W → Fin k, H.ProperColoring c := by
  classical
  let T : H.edges → Set (W → Fin k) := fun e =>
    {c | ∃ u ∈ e.1, ∃ v ∈ e.1, c u ≠ c v}
  have hclosed : ∀ e, IsClosed (T e) := by
    intro e
    have hfin_e : e.1.Finite :=
      Set.finite_of_ncard_pos (by rw [htri e.1 e.2]; norm_num)
    convert! isClosed_edgeProperColorings k e.1 hfin_e using 1
    ext c
    constructor
    · rintro ⟨u, hu, v, hv, huv⟩
      exact ⟨u, hu, v, hv, fun h => huv (congrArg c h), huv⟩
    · rintro ⟨u, hu, v, hv, huv, hcolor⟩
      exact ⟨u, hu, v, hv, hcolor⟩
  have hfinite : ∀ D : Finset H.edges,
      ((Set.univ : Set (W → Fin k)) ∩ ⋂ e ∈ D, T e).Nonempty := by
    intro D
    let E : Finset (Set W) := D.image Subtype.val
    have hE : ∀ e ∈ E, e ∈ H.edges := by
      intro e he
      simp only [E, Finset.mem_image] at he
      obtain ⟨d, hd, rfl⟩ := he
      exact d.2
    obtain ⟨c, hc⟩ := hfin E hE
    refine ⟨c, ⟨Set.mem_univ c, ?_⟩⟩
    simp only [Set.mem_iInter]
    intro e heD
    have heE : e.1 ∈ E := Finset.mem_image_of_mem Subtype.val heD
    show ∃ u ∈ e.1, ∃ v ∈ e.1, c u ≠ c v
    exact hc e.1 heE
  obtain ⟨c, hcuniv, hc⟩ := isCompact_univ.inter_iInter_nonempty T hclosed hfinite
  refine ⟨c, ?_⟩
  intro e he
  have hce : c ∈ T ⟨e, he⟩ := Set.mem_iInter.mp hc ⟨e, he⟩
  exact hce

/-
Every finite number of colours already fails on a finite edge subhypergraph
of an uncountably chromatic triple system.
-/
theorem exists_finite_edge_coloring_obstruction (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    (k : ℕ) [NeZero k] :
    ∃ D : Finset (Set W),
      (∀ e ∈ D, e ∈ H.edges) ∧
      ¬ ∃ c : W → Fin k, (⟨(D : Set (Set W))⟩ : Hypergraph W).ProperColoring c := by
  contrapose! huc;
  obtain ⟨c, hc⟩ := hypergraph_coloring_compactness H htri k huc;
  refine' fun h => h _;
  convert! colorableBy_aleph0_of_countable H _ _;
  exact ULift ( Fin k );
  exact Cardinal.mk_le_aleph0;
  exact fun x => ⟨ c x ⟩;
  intro e he; specialize hc e he; aesop;

/-
The finite shadow obstruction may be chosen wholly outside any prescribed
countable vertex set.
-/
theorem exists_finite_shadow_coloring_obstruction_avoid_countable
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    (k : ℕ) [NeZero k] :
    ∃ s : Finset W, (∀ x ∈ s, x ∉ S) ∧ ∀ c : W → Fin k,
      ∃ a ∈ s, ∃ b ∈ s, (shadowGraph H).Adj a b ∧ c a = c b := by
  by_contra h_contra;
  -- By `exists_finite_edge_coloring_obstruction_avoid_countable`, there exists a finite set D of H-edges disjoint S with no proper Fin k coloring.
  obtain ⟨D, hD⟩ : ∃ D : Finset (Set W), (∀ e ∈ D, e ∈ H.edges) ∧ (∀ e ∈ D, e ⊆ Sᶜ) ∧ ¬∃ c : W → Fin k, (⟨(D : Set (Set W))⟩ : Hypergraph W).ProperColoring c := by
    obtain ⟨D, hD⟩ : ∃ D : Finset (Set W), (∀ e ∈ D, e ∈ H.edges ∧ e ⊆ Sᶜ) ∧ ¬∃ c : W → Fin k, (⟨(D : Set (Set W))⟩ : Hypergraph W).ProperColoring c := by
      have h_uncountablyChromatic_avoid_countable : (⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩ : Hypergraph W).UncountablyChromatic := by
        convert! uncountablyChromatic_avoid_countable H htri huc hS using 1;
      have := exists_finite_edge_coloring_obstruction ⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩ (by
      exact fun e he => htri e he.1) h_uncountablyChromatic_avoid_countable k
      generalize_proofs at *;
      exact this;
    exact ⟨ D, fun e he => hD.1 e he |>.1, fun e he => hD.1 e he |>.2, hD.2 ⟩;
  obtain ⟨s, hs⟩ : ∃ s : Finset W, (∀ x ∈ s, x ∉ S) ∧ ∀ e ∈ D, e ⊆ s := by
    have h_finite_union : ∀ e ∈ D, e.Finite := by
      exact fun e he => Set.Finite.subset ( Set.finite_of_ncard_pos ( by linarith [ htri e ( hD.1 e he ) ] ) ) ( Set.Subset.refl _ );
    have h_finite_union : (⋃ e ∈ D, e).Finite := by
      exact Set.Finite.biUnion ( Finset.finite_toSet D ) h_finite_union;
    exact ⟨ h_finite_union.toFinset, fun x hx => by aesop, fun e he => fun x hx => h_finite_union.mem_toFinset.mpr <| Set.mem_iUnion₂.mpr ⟨ e, he, hx ⟩ ⟩;
  refine' h_contra ⟨ s, hs.1, fun c => _ ⟩;
  simp_all +decide [ Hypergraph.ProperColoring ];
  obtain ⟨ e, he₁, he₂ ⟩ := hD.2.2 c;
  obtain ⟨ a, ha, b, hb, hab ⟩ := Set.ncard_eq_three.mp ( htri e ( hD.1 e he₁ ) );
  exact ⟨ a, hs.2 e he₁ ( by simp +decide [ hab ] ), ha, hs.2 e he₁ ( by simp +decide [ hab ] ), shadowGraph_adj_of_mem_edge H ( hD.1 e he₁ ) ( by simp +decide [ hab ] ) ( by simp +decide [ hab ] ) hb, he₂ a ( by simp +decide [ hab ] ) ha ( by simp +decide [ hab ] ) ⟩

/-
Likewise, the finite edge obstruction may be chosen with every selected
edge disjoint from a prescribed countable set.
-/
theorem exists_finite_edge_coloring_obstruction_avoid_countable
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    (k : ℕ) [NeZero k] :
    ∃ D : Finset (Set W),
      (∀ e ∈ D, e ∈ H.edges ∧ e ⊆ Sᶜ) ∧
      ¬ ∃ c : W → Fin k, (⟨(D : Set (Set W))⟩ : Hypergraph W).ProperColoring c := by
  convert! exists_finite_edge_coloring_obstruction ( ⟨ { e | e ∈ H.edges ∧ e ⊆ Sᶜ } ⟩ : Hypergraph W ) ?_ ?_ k;
  · intro e he;
    exact htri e he.1;
  · convert! uncountablyChromatic_avoid_countable H htri huc hS using 1

/-
Deleting any countable family of edges still leaves a finite obstruction
to every prescribed finite colouring.
-/
theorem exists_finite_edge_coloring_obstruction_avoid_countable_edges
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {A : Set (Set W)} (hA : A.Countable)
    (k : ℕ) [NeZero k] :
    ∃ D : Finset (Set W),
      (∀ e ∈ D, e ∈ H.edges ∧ e ∉ A) ∧
      ¬ ∃ c : W → Fin k, (⟨(D : Set (Set W))⟩ : Hypergraph W).ProperColoring c := by
  have hres : (⟨H.edges \ A⟩ : Hypergraph W).UncountablyChromatic :=
    uncountablyChromatic_delete_countable_edges H htri huc hA
  exact exists_finite_edge_coloring_obstruction
    (⟨H.edges \ A⟩ : Hypergraph W) (fun e he => htri e he.1) hres k

end Erdos1177

-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.External
import ErdosProblems.Erdos1177.CardinalArith

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The §6 reservoir recursion: setup and construction

This file formalizes the construction of the exact-chromatic linear triple
system `L_κ` of §6 of arXiv:2606.24882 (the "transfinite reservoir recursion"),
following `lem:calibration-construction` and its supporting lemmas.

The construction depends only on the Erdős–Galvin–Hajnal simultaneous-labelling
input (`E3_EGH_P`), which supplies a graph `S` with an edge labelling having
property `P`.  Everything else — the levels, ranks, reservoirs, copies and apex
maps — is a self-contained ZFC construction assembled here.

We bundle all the fixed choices of the construction into a structure
`CalibData μ` (for an infinite base cardinal `μ`), and prove that the associated
triple system `CalibData.L` is a linear triple system of chromatic number
exactly `κ = μ⁺`.  The existence of a `CalibData μ` from `E3` is
`exists_calibData` (the capacity/allocation part of the recursion).
-/

open Cardinal Ordinal

set_option maxHeartbeats 4000000

namespace Erdos1177

universe u

/-! ### Geometry of the construction -/

/-- The "reservoir" base cardinal `ρ = 2^μ`. -/
abbrev rhoC (μ : Cardinal.{u}) : Cardinal.{u} := (2 : Cardinal.{u}) ^ μ

/-- The number of levels `R = ρ⁺`. -/
noncomputable def Rord (ρ : Cardinal.{u}) : Ordinal.{u} := (Order.succ ρ).ord

/-- Levels of the construction: `R = ρ⁺` many, well-ordered. -/
abbrev Lev (ρ : Cardinal.{u}) : Type u := (Rord ρ).ToType

/-- Each level has a fiber of size `Λ = 2^ρ`. -/
abbrev Fib (ρ : Cardinal.{u}) : Type u := ((2 : Cardinal.{u}) ^ ρ).out

/-- Vertices: a level together with a point of its fiber. -/
abbrev Vtx (ρ : Cardinal.{u}) : Type u := Lev ρ × Fib ρ

/-- Rank of a level as an ordinal below `R.ord`. -/
noncomputable def lrank {ρ : Cardinal.{u}} (a : Lev ρ) : Ordinal.{u} :=
  Ordinal.typein (α := Lev ρ) (· < ·) a

/-- The set of vertices strictly below level `a`. -/
def Vbelow {ρ : Cardinal.{u}} (a : Lev ρ) : Set (Vtx ρ) := {v | v.1 < a}

/-- **Admissible reservoir at level `a`** (conditions (R1)–(R4)).  An `Ilab`-indexed
family `X` of subsets of the vertices below `a`, each empty or of size `ρ`, the
nonempty ones pairwise disjoint, and all of whose points have a `q`-colour
different from `q`'s value at level `a`. -/
def IsReservoir {ρ : Cardinal.{u}} {Ilab : Type u} (q : Ordinal.{u} → Ordinal.{u})
    (a : Lev ρ) (X : Ilab → Set (Vtx ρ)) : Prop :=
  (∀ i, X i ⊆ Vbelow a) ∧
  (∀ i, X i = ∅ ∨ #(X i) = ρ) ∧
  (∀ i j, i ≠ j → (X i).Nonempty → (X j).Nonempty → Disjoint (X i) (X j)) ∧
  (∀ i, ∀ v ∈ X i, q (lrank v.1) ≠ q (lrank a))

/-! ### The bundled construction data -/

/-- **All data fixed by the §6 successor construction** for base cardinal `μ`.
This packages the Erdős–Galvin–Hajnal graph and labelling (`S`, `G`, `lbl`, `hP`),
the fibre colouring `q` with cofinal fibres, and the allocation of copies
(`copy`) and apex maps (`phi`) fixed by the recursion. -/
structure CalibData (μ : Cardinal.{u}) where
  /-- `μ` is infinite. -/
  hμ : ℵ₀ ≤ μ
  /-- The Erdős–Galvin–Hajnal graph. -/
  S : Type u
  /-- Its adjacency. -/
  G : SimpleGraph S
  /-- The label type, of size `ρ = 2^μ`. -/
  Ilab : Type u
  /-- `|I| = ρ`. -/
  hIlab : #Ilab = rhoC μ
  /-- `|V(S)| ≤ ρ`. -/
  hS : #S ≤ rhoC μ
  /-- The edge labelling. -/
  lbl : G.edgeSet → Ilab
  /-- Property `P` at `κ = μ⁺`. -/
  hP : SimpleGraph.PropertyP G lbl (Order.succ μ)
  /-- The fibre colouring `q : R → κ`. -/
  q : Ordinal.{u} → Ordinal.{u}
  /-- `q` lands in `κ`. -/
  hq1 : ∀ a, a < Rord (rhoC μ) → q a < (Order.succ μ).ord
  /-- Every `q`-fibre is cofinal in `R`. -/
  hq2 : ∀ ξ, ξ < (Order.succ μ).ord → ∀ β, β < Rord (rhoC μ) →
          ∃ α, β ≤ α ∧ α < Rord (rhoC μ) ∧ q α = ξ
  /-- The copy of `S` installed for reservoir `X` (subtype element) and `η < ρ`
  at level `a`; an injection `S → Vtx` landing in the fiber of `a`. -/
  copy : ∀ a : Lev (rhoC μ),
    {X : Ilab → Set (Vtx (rhoC μ)) // IsReservoir q a X} → Fib (rhoC μ) → S → Vtx (rhoC μ)
  /-- Copies are installed at their own level. -/
  copy_lev : ∀ a X η s, (copy a X η s).1 = a
  /-- Distinct copies (over reservoir, `η`, vertex) are placed injectively. -/
  copy_inj : ∀ a : Lev (rhoC μ),
    Function.Injective
      (fun p : ({X : Ilab → Set (Vtx (rhoC μ)) // IsReservoir q a X} × Fib (rhoC μ) × S) =>
        copy a p.1 p.2.1 p.2.2)
  /-- The apex map for reservoir `X` at level `a`. -/
  phi : ∀ a : Lev (rhoC μ),
    {X : Ilab → Set (Vtx (rhoC μ)) // IsReservoir q a X} → G.edgeSet → Vtx (rhoC μ)
  /-- The apex of an active edge lies in the reservoir set of its label. -/
  phi_mem : ∀ a X e, (X.val (lbl e)).Nonempty → phi a X e ∈ X.val (lbl e)
  /-- The apex map is injective on active edges. -/
  phi_inj : ∀ a X, Set.InjOn (phi a X) {e | (X.val (lbl e)).Nonempty}

namespace CalibData

variable {μ : Cardinal.{u}} (D : CalibData μ)

/-- The base set of an edge `e` of `S`, as a set of vertices of `S`. -/
def edgeBase (e : D.G.edgeSet) : Set D.S := {x | x ∈ (e : Sym2 D.S)}

/-- **The triple system `L_κ`.**  Its edges are the triples `copy(e) ∪ {phi(e)}`
for installed copies `B_{X,η}` at level `a` and active edges `e` of `S`. -/
def edgeSetL : Set (Set (Vtx (rhoC μ))) :=
  {t | ∃ (a : Lev (rhoC μ))
        (X : {X : D.Ilab → Set (Vtx (rhoC μ)) // IsReservoir D.q a X})
        (η : Fib (rhoC μ)) (e : D.G.edgeSet),
      (X.val (D.lbl e)).Nonempty ∧
      t = (fun s => D.copy a X η s) '' (D.edgeBase e) ∪ {D.phi a X e} }

/-- The host hypergraph `L_κ`. -/
def L : Hypergraph (Vtx (rhoC μ)) := ⟨D.edgeSetL⟩

end CalibData

/-! ### A colouring into a small type gives colourability -/

/-- If a hypergraph has a proper colouring into a type `T` of cardinality at most
`θ`, then it is `θ`-colourable. -/
theorem colorableBy_of_proper_le {V : Type u} {H : Hypergraph V} {T : Type u} (c : V → T)
    (hc : H.ProperColoring c) {θ : Cardinal.{u}} (hT : #T ≤ θ) : H.ColorableBy θ := by
  have : #T ≤ #θ.out := by simpa [Cardinal.mk_out] using! hT
  obtain ⟨g, hg⟩ := this
  refine ⟨fun v => g (c v), ?_⟩
  intro e he
  obtain ⟨u, hu, v, hv, huv⟩ := hc e he
  exact ⟨u, hu, v, hv, fun h => huv (hg h)⟩

namespace CalibData

variable {μ : Cardinal.{u}} (D : CalibData μ)

/-- Membership in the edge set of `L`. -/
theorem mem_edgeSetL {t : Set (Vtx (rhoC μ))} :
    t ∈ D.edgeSetL ↔ ∃ (a : Lev (rhoC μ))
        (X : {X : D.Ilab → Set (Vtx (rhoC μ)) // IsReservoir D.q a X})
        (η : Fib (rhoC μ)) (e : D.G.edgeSet),
      (X.val (D.lbl e)).Nonempty ∧
      t = (fun s => D.copy a X η s) '' (D.edgeBase e) ∪ {D.phi a X e} := Iff.rfl

/-
The base of an edge of `S` has exactly two vertices.
-/
theorem edgeBase_ncard (e : D.G.edgeSet) : (D.edgeBase e).ncard = 2 := by
  unfold CalibData.edgeBase;
  convert! Set.ncard_eq_two.mpr _;
  rcases e with ⟨ e, he ⟩;
  rcases e with ⟨ x, y ⟩;
  exact ⟨ x, y, by rintro rfl; exact absurd he ( by simp +decide ), by ext; simp +decide ⟩

/-
**`L` is a triple system**: every installed edge has exactly three vertices.
-/
theorem L_isTripleSystem : (D.L).IsTripleSystem := by
  intro t ht
  obtain ⟨a, X, η, e, hX, ht⟩ := (D.mem_edgeSetL).mp ht;
  rw [ ht, @Set.ncard_union_eq ];
  · rw [ Set.ncard_image_of_injective, Set.ncard_singleton ];
    · exact D.edgeBase_ncard e ▸ rfl;
    · exact fun x y hxy => by have := D.copy_inj a; have := @this ( X, η, x ) ( X, η, y ) ; aesop;
  · simp +decide [ Set.disjoint_left ];
    intro s hs h_eq
    have h_level : (D.copy a X η s).1 = a := by
      exact D.copy_lev a X η s
    have h_level_phi : (D.phi a X e).1 < a := by
      exact X.2.1 _ ( D.phi_mem _ _ _ hX )
    exact absurd h_level (by
    exact ne_of_lt ( h_eq ▸ h_level_phi ));
  · exact Set.Finite.image _ ( Set.finite_of_ncard_pos ( by rw [ D.edgeBase_ncard ] ; positivity ) );
  · exact Set.finite_singleton _

/-
Two distinct edges of `S` share at most one vertex (their bases meet in at
most one point).
-/
theorem edgeBase_inter_subsingleton {e₁ e₂ : D.G.edgeSet} (h : e₁ ≠ e₂) :
    (D.edgeBase e₁ ∩ D.edgeBase e₂).Subsingleton := by
  unfold CalibData.edgeBase;
  rcases e₁ with ⟨ ⟨ x, y ⟩, hxy ⟩ ; rcases e₂ with ⟨ ⟨ u, v ⟩, huv ⟩ ; simp_all +decide [ Set.Subsingleton ];
  grind

/-- The apex of an active edge lies strictly below the level of its copy. -/
theorem phi_level_lt {a : Lev (rhoC μ)}
    {X : {X : D.Ilab → Set (Vtx (rhoC μ)) // IsReservoir D.q a X}} {e : D.G.edgeSet}
    (hX : (X.val (D.lbl e)).Nonempty) : (D.phi a X e).1 < a :=
  X.property.1 (D.lbl e) (D.phi_mem a X e hX)

/-
**`L` is linear** (`lem:calibration-linearity`): any two distinct edges meet
in at most one vertex.
-/
theorem L_linear : (D.L).Linear := by
  intro t₁ ht₁ t₂ ht₂ hne
  obtain ⟨a₁, X₁, η₁, e₁, hX₁, rfl⟩ := D.mem_edgeSetL.mp ht₁
  obtain ⟨a₂, X₂, η₂, e₂, hX₂, rfl⟩ := D.mem_edgeSetL.mp ht₂;
  by_cases h_cases : a₁ < a₂;
  · have h_level : ∀ p ∈ (fun s => D.copy a₁ X₁ η₁ s) '' D.edgeBase e₁ ∪ {D.phi a₁ X₁ e₁}, p.1 < a₂ := by
      simp +zetaDelta at *;
      exact ⟨ lt_trans ( D.phi_level_lt hX₁ ) h_cases, fun x hx => lt_of_le_of_lt ( by simp +decide [ D.copy_lev ] ) h_cases ⟩;
    intro p hp q hq; have := h_level p hp.1; have := h_level q hq.1; simp_all +decide [ D.copy_lev ] ;
    grind +suggestions;
  · by_cases h_cases : a₂ < a₁;
    · have h_inter : ∀ p ∈ (fun s => D.copy a₂ X₂ η₂ s) '' D.edgeBase e₂ ∪ {D.phi a₂ X₂ e₂}, p.1 < a₁ := by
        simp [D.copy_lev];
        exact ⟨ lt_of_lt_of_le ( D.phi_level_lt hX₂ ) h_cases.le, fun _ _ => h_cases ⟩;
      intro p hp q hq; have := h_inter p hp.2; have := h_inter q hq.2; simp_all +decide [ D.copy_lev ] ;
      rcases hp.1 with ( rfl | ⟨ x, hx, rfl ⟩ ) <;> rcases hq.1 with ( rfl | ⟨ y, hy, rfl ⟩ ) <;> simp_all +decide [ D.copy_lev ];
    · cases lt_or_eq_of_le ( le_of_not_gt h_cases ) <;> simp_all +decide;
      by_cases h_cases : X₁.val = X₂.val ∧ η₁ = η₂;
      · have h_base_inter : (D.copy a₁ X₁ η₁ '' D.edgeBase e₁ ∩ D.copy a₁ X₁ η₁ '' D.edgeBase e₂).Subsingleton := by
          have h_base_inter : (D.edgeBase e₁ ∩ D.edgeBase e₂).Subsingleton := by
            apply D.edgeBase_inter_subsingleton;
            lia;
          have h_base_inter : (D.copy a₁ X₁ η₁ '' (D.edgeBase e₁ ∩ D.edgeBase e₂)).Subsingleton := by
            exact Set.Subsingleton.image h_base_inter _;
          convert! h_base_inter using 1;
          rw [ Set.image_inter ];
          exact fun x y hxy => by have := D.copy_inj a₁; have := @this ( X₁, η₁, x ) ( X₁, η₁, y ) ; aesop;
        have h_apex_inter : ¬(D.phi a₁ X₁ e₁ = D.phi a₂ X₂ e₂) := by
          have := D.phi_inj a₁ X₁; simp_all +decide [ Set.InjOn ] ;
          specialize this _ e₁.2 hX₁ _ e₂.2 hX₂ ; aesop;
        have h_apex_not_in_base : D.phi a₁ X₁ e₁ ∉ D.copy a₁ X₁ η₁ '' D.edgeBase e₂ ∧ D.phi a₂ X₂ e₂ ∉ D.copy a₁ X₁ η₁ '' D.edgeBase e₁ := by
          constructor <;> intro h <;> obtain ⟨ s, hs, hs' ⟩ := h <;> have := D.copy_lev a₁ X₁ η₁ s <;> simp_all +decide;
          · have := D.phi_level_lt ( show ( X₁.val ( D.lbl e₁ ) ).Nonempty from by aesop ) ; aesop;
          · exact absurd this ( ne_of_lt ( by simpa [ * ] using! phi_level_lt D hX₂ ) );
        intro x hx y hy; simp_all +decide [ Set.Subsingleton ] ;
        grind;
      · have h_disjoint : Disjoint ((fun s => D.copy a₁ X₁ η₁ s) '' D.edgeBase e₁) ((fun s => D.copy a₂ X₂ η₂ s) '' D.edgeBase e₂) := by
          have := D.copy_inj a₁;
          simp_all +decide [ Set.disjoint_left, Function.Injective ];
          grind;
        have h_disjoint : D.phi a₁ X₁ e₁ ∉ (fun s => D.copy a₂ X₂ η₂ s) '' D.edgeBase e₂ ∧ D.phi a₂ X₂ e₂ ∉ (fun s => D.copy a₁ X₁ η₁ s) '' D.edgeBase e₁ := by
          constructor <;> intro h <;> obtain ⟨ s, hs, hs' ⟩ := h <;> have := D.copy_lev a₂ X₂ η₂ s <;> simp_all +decide;
          · have := D.phi_level_lt hX₁; aesop;
          · have := D.copy_lev a₁ X₁ η₁ s; simp_all +decide ;
            exact absurd this ( ne_of_lt ( D.phi_level_lt hX₂ ) );
        simp_all +decide [ Set.Subsingleton ];
        simp_all +decide [ Set.disjoint_left ]

/-
**Canonical upper colouring** (`lem:calibration-upper`): `x ↦ q(rk x)` is a
proper `κ`-colouring, so `χ(L) ≤ κ`.
-/
theorem L_colorable : (D.L).ColorableBy (Order.succ μ) := by
  set c : Vtx (rhoC μ) → {o : Ordinal // o < (Order.succ μ).ord} := fun v => ⟨D.q (lrank v.1), by
    exact D.hq1 _ ( by exact Ordinal.typein_lt_self _ )⟩
  generalize_proofs at *;
  -- Show that c is a proper coloring of L.
  have hc_proper : (D.L).ProperColoring c := by
    intro t ht
    obtain ⟨a, X, η, e, hX, rfl⟩ := D.mem_edgeSetL.mp ht;
    obtain ⟨ s, hs ⟩ := Set.nonempty_of_ncard_ne_zero ( by rw [ D.edgeBase_ncard e ] ; norm_num );
    refine' ⟨ _, Or.inl ⟨ s, hs, rfl ⟩, _, Or.inr rfl, _ ⟩ ; simp +decide [ c ];
    convert! X.2.2.2.2 ( D.lbl e ) _ ( D.phi_mem a X e hX ) using 1;
    rw [ D.copy_lev ] ; aesop;
  refine' ⟨ _, _ ⟩;
  exact fun v => Classical.choice ( Cardinal.mk_out ( Order.succ μ ) |> fun h => Cardinal.lift_mk_eq'.mp <| by
    change Cardinal.lift #(Set.Iio (Order.succ μ).ord) = _
    simp [Cardinal.mk_Iio_ordinal] ) ( c v );
  intro e he; specialize hc_proper e he; aesop;

end CalibData

end Erdos1177

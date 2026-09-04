-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib
import ErdosProblems.Erdos1177.E2Construction

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The Erdős–Rado / Erdős–Hajnal triangle-free graph with `|V| = χ = κ`

This file formalizes the base case (`n = 1`) of the Erdős–Hajnal high-odd-girth
construction (Erdős–Hajnal, Acta Math. Hungar. 17 (1966), Theorem 7.4; the
`n = 1` instance is Erdős–Rado 1960, restated in Reiher's girth survey
arXiv:2403.13571 as Theorem `er60`).

**Construction.**  Fix an infinite cardinal `κ` and let `Pt = κ.ord.ToType` be a
well-ordered set of order type `κ.ord` (so `|Pt| = κ`).  The vertices are the
strictly increasing triples `a₀ < a₁ < a₂` of `Pt`.  Two triples
`a = (a₀,a₁,a₂)` and `b = (b₀,b₁,b₂)` are joined when the six coordinates
interleave as
```
      a₀ < a₁ < b₀ < a₂ < b₁ < b₂
```
(or symmetrically with the roles of `a` and `b` swapped).  This is exactly the
Erdős–Rado edge rule: the edge is assigned to the increasing six-tuple
`α₀<α₁<α₂<α₃<α₄<α₅` by `a = (α₀,α₁,α₃)`, `b = (α₂,α₄,α₅)`.

We prove:
* `card_le` — `|V| ≤ κ`;
* `triangleFree` / `noShortOddCycle_one` — the graph has no triangle, i.e. no odd
  cycle of length `≤ 3`;
* `not_colorableBy` — the graph is not `θ`-colourable for any `θ < κ` (the
  Erdős–Rado chromatic lower bound, via the iterated cofinal-colour argument at a
  regular cardinal together with the reduction to `θ⁺`).

Together these give the `s ≤ 1` slice of `Erdos1177.E2Core` (`e2Core_oddGirth_one`).
-/

open Cardinal Ordinal

namespace Erdos1177
namespace ER60

universe u

/-- The ordered point set: order type `κ.ord`, cardinality `κ`. -/
abbrev Pt (κ : Cardinal.{u}) : Type u := κ.ord.ToType

/-- Vertices: strictly increasing triples of `Pt κ`. -/
abbrev Vtx (κ : Cardinal.{u}) : Type u := {t : Fin 3 → Pt κ // StrictMono t}

variable {κ : Cardinal.{u}}

/-- The oriented Erdős–Rado edge relation:
`a₀ < a₁ < b₀ < a₂ < b₁ < b₂`. -/
def IsEdge (a b : Fin 3 → Pt κ) : Prop :=
  a 0 < a 1 ∧ a 1 < b 0 ∧ b 0 < a 2 ∧ a 2 < b 1 ∧ b 1 < b 2

/-- Symmetric adjacency. -/
def Adjr (a b : Vtx κ) : Prop := IsEdge a.1 b.1 ∨ IsEdge b.1 a.1

theorem isEdge_irrefl (a : Fin 3 → Pt κ) : ¬ IsEdge a a := by
  rintro ⟨h01, h1, -, -, -⟩
  exact absurd (lt_trans h01 h1) (lt_irrefl _)

/-- The Erdős–Rado graph on increasing triples of `Pt κ`. -/
def graph (κ : Cardinal.{u}) : SimpleGraph (Vtx κ) where
  Adj a b := Adjr a b
  symm := by constructor; intro a b h; exact h.symm
  loopless := ⟨by rintro a (h | h) <;> exact isEdge_irrefl _ h⟩

/-! ### Cardinality -/

theorem card_le (hκ : ℵ₀ ≤ κ) : Cardinal.mk (Vtx κ) ≤ κ := by
  -- The set of all functions from Fin 3 to Pt κ has cardinality κ^3.
  have h_card : #(Fin 3 → Pt κ) = κ ^ (3 : ℕ) := by
    simp +decide [ Cardinal.mk_toType, Cardinal.card_ord ];
    norm_cast;
  refine' le_trans ( Cardinal.mk_subtype_le _ ) _;
  rw [ h_card, Cardinal.power_nat_eq ];
  · exact hκ;
  · norm_num

/-! ### Triangle-freeness

The key observation: `IsEdge a b` forces `a 0 < b 0` (since `a 0 < a 1 < b 0`).
So an oriented edge points from the triple with the smaller first coordinate to
the one with the larger.  In a putative triangle `a, b, c` we may therefore
assume `a 0 < b 0 < c 0`, whence all three edges are oriented `a→b`, `b→c`,
`a→c`; then `a 2 < b 1` (from `a→b`), `b 1 < c 0` (from `b→c`), and `c 0 < a 2`
(from `a→c`), a contradiction. -/

theorem isEdge_fst_lt {a b : Fin 3 → Pt κ} (h : IsEdge a b) : a 0 < b 0 :=
  lt_trans h.1 h.2.1

theorem triangleFree :
    ∀ a b c : Vtx κ, (graph κ).Adj a b → (graph κ).Adj b c → (graph κ).Adj a c → False := by
  intro a b c hab hbc hac
  simp only [graph, Adjr, IsEdge] at hab hbc hac
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc <;>
    rcases hac with hac | hac <;> rcases hab with ⟨_, _, _, _, _⟩ <;>
    rcases hbc with ⟨_, _, _, _, _⟩ <;> rcases hac with ⟨_, _, _, _, _⟩ <;> order

/-
No odd cycle of length `≤ 3` (i.e. `NoShortOddCycle (graph κ) 1`).
-/
theorem noShortOddCycle_one : NoShortOddCycle (graph κ) 1 := by
  intro m hm₁ hm₂ hm₃;
  interval_cases m ; simp_all +decide only [not_exists, not_and, not_forall];
  intro x hx_inj
  by_contra h_contra
  push_neg at h_contra;
  convert! triangleFree _ _ _ ( h_contra 0 ) ( h_contra 1 ) ( h_contra 2 |> SimpleGraph.Adj.symm ) using 1

/-! ### The chromatic lower bound

`not_colorableBy_regular` is the core: at a *regular* `κ`, the graph is not
`θ`-colourable for `θ < κ`, by the iterated "cofinally-many equal colours"
argument.  `not_colorableBy` removes the regularity assumption by restricting a
hypothetical `θ`-colouring to an initial segment of order type `θ⁺` (regular). -/

/-- A subset `S` of the point order is *cofinal* (unbounded): above every point
there is a larger point of `S`. -/
def Cofinal (S : Set (Pt κ)) : Prop := ∀ x : Pt κ, ∃ y ∈ S, x < y

/-
The whole order is cofinal: `κ.ord` is a limit ordinal (for `ℵ₀ ≤ κ`), so
`Pt κ` has no maximum.
-/
theorem cofinal_univ (hκ : ℵ₀ ≤ κ) : Cofinal (Set.univ : Set (Pt κ)) := by
  intro x
  obtain ⟨y, hy⟩ : ∃ y : Pt κ, x < y := by
    convert! exists_gt x;
    have h_no_max : NoMaxOrder (κ.ord.ToType) := by
      have h_limit : Order.IsSuccLimit κ.ord := by
        apply_rules [ Cardinal.isSuccLimit_ord, hκ ]
      grind +suggestions;
    exact h_no_max
  use y
  simp [hy]

/-- Every tail `{z | y < z}` is cofinal. -/
theorem cofinal_Ioi (hκ : ℵ₀ ≤ κ) (y : Pt κ) : Cofinal {z | y < z} := by
  intro x
  obtain ⟨z, -, hz⟩ := cofinal_univ hκ (max x y)
  exact ⟨z, lt_of_le_of_lt (le_max_right _ _) hz, lt_of_le_of_lt (le_max_left _ _) hz⟩

/-
**Regularity boundedness.**  A `θ`-indexed family of points, with `θ < κ`
(`κ` regular), has a strict upper bound: the supremum of `θ`-many ordinals below
`κ.ord` stays below `κ.ord`, because `cof κ.ord = κ > θ`.
-/
theorem exists_ub (hreg : κ.IsRegular) {θ : Cardinal.{u}} (hθ : θ < κ)
    (b : θ.out → Pt κ) : ∃ B : Pt κ, ∀ v, b v < B := by
      obtain ⟨c, hc⟩ : ∃ c : Ordinal, c < κ.ord ∧ ∀ v : Cardinal.ord κ |> Ordinal.ToType, (∃ w : (Quotient.out θ), b w = v) → v < c := by
        use Ordinal.lsub (fun w : (Quotient.out θ) => (b w).toOrd);
        refine' ⟨ _, _ ⟩;
        · convert! Ordinal.lsub_lt_ord_lift _ _;
          · simp +decide only [mk_out, Cardinal.lift_id];
            exact hθ.trans_le hreg.cof_eq.ge;
          · grind +suggestions;
        · rintro v ⟨ w, rfl ⟩;
          exact Ordinal.lt_lsub ( fun w => ToType.toOrd ( b w ) ) w;
      have h_enum : ∃ w : Ordinal.ToType κ.ord, w.toOrd = c := by
        obtain ⟨w, hw⟩ : ∃ w : Ordinal.ToType κ.ord, w.toOrd = c := by
          have h_enum : ∀ x : Ordinal, x < κ.ord → ∃ w : Ordinal.ToType κ.ord, w.toOrd = x := by
            intro x hx;
            obtain ⟨w, hw⟩ : ∃ w : Ordinal.ToType κ.ord, w.toOrd = x := by
              have h_enum : ∀ x : Ordinal, x < κ.ord → ∃ w : Ordinal.ToType κ.ord, w.toOrd = x := by
                intro x hx
                have h_enum : x < Ordinal.type (· < · : Ordinal.ToType κ.ord → Ordinal.ToType κ.ord → Prop) := by
                  convert! hx using 1;
                  convert! Ordinal.type_toType κ.ord using 1
                obtain ⟨ w, hw ⟩ := typein_surj ( fun x1 x2 : Ordinal.ToType κ.ord => x1 < x2 ) h_enum; use w; aesop;
              exact h_enum x hx;
            use w
          exact h_enum c hc.1;
        use w;
      cases' h_enum with w hw; use w; intro v; specialize hc; have := hc.2 ( b v ) ⟨ v, rfl ⟩ ; aesop;

/-
**The pigeonhole step.**  If `S` is cofinal and `f : Pt κ → θ.out` with
`θ < κ` (`κ` regular), then some colour `v` has a cofinal fibre inside `S`.
Proof: otherwise every colour class in `S` is bounded; a strict upper bound `B`
of the `θ`-many bounds (`exists_ub`) then bounds `S`, contradicting cofinality.
-/
theorem cofinal_fiber (hreg : κ.IsRegular) {θ : Cardinal.{u}} (hθ : θ < κ)
    {S : Set (Pt κ)} (hS : Cofinal S) (f : Pt κ → θ.out) :
    ∃ v : θ.out, Cofinal {y | y ∈ S ∧ f y = v} := by
      contrapose! hS; simp_all +decide [ Cofinal ] ;
      choose b hb using hS; have := exists_ub hreg hθ b; obtain ⟨ B, hB ⟩ := this; use B; intros x hx; specialize hb ( f x ) x hx rfl; exact le_trans hb ( le_of_lt ( hB _ ) ) ;

/-- The vertex given by three strictly increasing points `a < b < c`. -/
def mk3 (a b c : Pt κ) (h1 : a < b) (h2 : b < c) : Vtx κ :=
  ⟨![a, b, c], by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all (config := {decide := true}) [lt_trans h1 h2]⟩

@[simp] theorem mk3_zero (a b c : Pt κ) (h1 : a < b) (h2 : b < c) :
    (mk3 a b c h1 h2).1 0 = a := rfl
@[simp] theorem mk3_one (a b c : Pt κ) (h1 : a < b) (h2 : b < c) :
    (mk3 a b c h1 h2).1 1 = b := rfl
@[simp] theorem mk3_two (a b c : Pt κ) (h1 : a < b) (h2 : b < c) :
    (mk3 a b c h1 h2).1 2 = c := rfl

/-- Two increasing triples `(α₀,α₁,α₃)` and `(α₂,α₄,α₅)` extracted from an
increasing 6-chain form an Erdős–Rado edge. -/
theorem adj_of_chain {a0 a1 a2 a3 a4 a5 : Pt κ}
    (h01 : a0 < a1) (h12 : a1 < a2) (h23 : a2 < a3) (h34 : a3 < a4) (h45 : a4 < a5) :
    (graph κ).Adj (mk3 a0 a1 a3 h01 (lt_trans h12 h23))
      (mk3 a2 a4 a5 (lt_trans h23 h34) h45) :=
  Or.inl ⟨h01, h12, h23, h34, h45⟩

/-
**The chromatic lower bound at a regular cardinal.**  The Erdős–Rado graph on
`Pt κ` (`κ` regular) is not `θ`-colourable for `θ < κ`, by the iterated cofinal
colour argument (three peeling levels `triple → pair → point → constant`).
-/
theorem not_colorableBy_regular (hreg : κ.IsRegular) {θ : Cardinal.{u}} (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (graph κ)).ColorableBy θ := by
  have h_card : ∃ v0 v1 v2 : Pt κ, v0 < v1 ∧ v1 < v2 := by
    have := cofinal_univ hreg.1;
    by_cases h : Nonempty ( Pt κ ) <;> simp_all +decide [ Cofinal ];
  obtain ⟨ v0, v1, v2, hv0, hv1 ⟩ := h_card;
  intro h
  obtain ⟨c, hc⟩ := h
  have hadj : ∀ a b, (graph κ).Adj a b → c a ≠ c b := by
    grind +suggestions;
  -- Define the function F1
  set F1 : Pt κ → Pt κ → (Pt κ → θ.out) := fun x y z => if h : x < y ∧ y < z then c (mk3 x y z h.1 h.2) else c (mk3 v0 v1 v2 hv0 hv1);
  -- Apply `cofinal_fiber` to get a colour `g x y` and a proof `hg x y : Cofinal {z | z ∈ {z | y < z} ∧ F1 x y z = g x y}`.
  obtain ⟨g, hg⟩ : ∃ g : Pt κ → Pt κ → θ.out, ∀ x y, x < y → Cofinal {z | z ∈ {z | y < z} ∧ F1 x y z = g x y} := by
    have h_cofinal_fiber : ∀ x y, x < y → ∃ v : θ.out, Cofinal {z | z ∈ {z | y < z} ∧ F1 x y z = v} := by
      intros x y hxy
      apply cofinal_fiber hreg hθ (cofinal_Ioi hreg.1 y) (F1 x y);
    exact ⟨ fun x y => if h : x < y then Classical.choose ( h_cofinal_fiber x y h ) else c ( mk3 v0 v1 v2 hv0 hv1 ), fun x y hxy => by simpa [ hxy ] using Classical.choose_spec ( h_cofinal_fiber x y hxy ) ⟩;
  -- Define the function F2
  set F2 : Pt κ → (Pt κ → θ.out) := fun x y => if h : x < y then g x y else c (mk3 v0 v1 v2 hv0 hv1);
  -- Apply `cofinal_fiber` to get a colour `hcol x` and a proof `hcol x : Cofinal {y | y ∈ {y | x < y} ∧ F2 x y = hcol x}`.
  obtain ⟨hcol, hhcol⟩ : ∃ hcol : Pt κ → θ.out, ∀ x, Cofinal {y | y ∈ {y | x < y} ∧ F2 x y = hcol x} := by
    have h_cofinal_fiber : ∀ x : Pt κ, ∃ v : θ.out, Cofinal {y | y ∈ {y | x < y} ∧ F2 x y = v} := by
      intro x
      apply cofinal_fiber hreg hθ (cofinal_Ioi hreg.1 x) (F2 x);
    exact ⟨ fun x => Classical.choose ( h_cofinal_fiber x ), fun x => Classical.choose_spec ( h_cofinal_fiber x ) ⟩;
  -- Apply `cofinal_fiber` to get a colour `star` and a proof `star : Cofinal {x | hcol x = star}`.
  obtain ⟨star, hstar⟩ : ∃ star : θ.out, Cofinal {x | hcol x = star} := by
    have := cofinal_fiber hreg hθ ( cofinal_univ hreg.1 ) hcol; aesop;
  obtain ⟨ α0, hα0 ⟩ := hstar v0;
  obtain ⟨ α1, hα1 ⟩ := hhcol α0 α0;
  obtain ⟨ α2, hα2 ⟩ := hstar α1;
  obtain ⟨ α3, hα3 ⟩ := hg α0 α1 hα1.2 α2;
  obtain ⟨ α4, hα4 ⟩ := hhcol α2 α3;
  obtain ⟨ α5, hα5 ⟩ := hg α2 α4 ( by
    exact hα4.1.1 ) α4;
  grind +suggestions

/-
If `μ ≤ κ` then `Pt μ` order-embeds into `Pt κ` as an initial segment
(`μ.ord ≤ κ.ord`).
-/
theorem exists_pt_orderEmbedding {μ : Cardinal.{u}} (hμκ : μ ≤ κ) :
    Nonempty (Pt μ ↪o Pt κ) := by
      convert! Nonempty.intro ?_;
      convert! OrderEmbedding.ofStrictMono ( fun x => Ordinal.enum ( fun x1 x2 : κ.ord.ToType => x1 < x2 ) ⟨ Ordinal.typein ( fun x1 x2 : μ.ord.ToType => x1 < x2 ) x, ?_ ⟩ ) fun x y hxy => ?_;
      all_goals norm_num [ typein_lt_type ];
      all_goals norm_num [ typein_lt_type, enum_lt_enum ];
      · exact lt_of_lt_of_le ( Ordinal.typein_lt_self x ) ( Cardinal.ord_le_ord.mpr hμκ );
      · exact hxy

/-
**Colourability transfers down initial segments.**  If `μ ≤ κ` and the
Erdős–Rado graph on `κ` is `θ`-colourable, then so is the one on `μ`: an order
embedding `Pt μ ↪o Pt κ` induces a graph embedding `graph μ → graph κ`
(mapping each increasing triple coordinatewise), and a proper colouring pulls
back along it.
-/
theorem colorableBy_of_le {μ : Cardinal.{u}} (hμκ : μ ≤ κ) {θ : Cardinal.{u}}
    (h : (SimpleGraph.toHG (graph κ)).ColorableBy θ) :
    (SimpleGraph.toHG (graph μ)).ColorableBy θ := by
      revert h;
      intro h
      obtain ⟨e, he⟩ : ∃ e : Pt μ ↪o Pt κ, True := by
        exact ⟨ Classical.choice ( exists_pt_orderEmbedding hμκ ), trivial ⟩;
      obtain ⟨c, hc⟩ := h
      have hadjκ : ∀ a b, (graph κ).Adj a b → c a ≠ c b := by
        grind +suggestions;
      refine' ⟨ fun a => c ⟨ fun i => e ( a.1 i ), _ ⟩, _ ⟩;
      exact e.strictMono.comp a.2;
      convert! toHG_proper_iff ( graph μ ) _ |>.2 _;
      intro x y hxy; specialize hadjκ ⟨ fun i => e ( x.1 i ), e.strictMono.comp x.2 ⟩ ⟨ fun i => e ( y.1 i ), e.strictMono.comp y.2 ⟩ ; simp_all +decide [ graph, Adjr, IsEdge ] ;

/-- **The chromatic lower bound (no regularity assumption).**  For `ℵ₀ < κ` the
Erdős–Rado graph on `Pt κ` is not `θ`-colourable for any `θ < κ`.  Reduce to the
regular cardinal `μ = (max θ ℵ₀)⁺ ≤ κ`: a `θ`-colouring of `graph κ` restricts to
one of `graph μ`, impossible by `not_colorableBy_regular`. -/
theorem not_colorableBy (hκ : ℵ₀ < κ) {θ : Cardinal.{u}} (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (graph κ)).ColorableBy θ := by
  intro h
  have hνκ : max θ ℵ₀ < κ := max_lt hθ hκ
  have hμκ : Order.succ (max θ ℵ₀) ≤ κ := Order.succ_le_of_lt hνκ
  have hμreg : (Order.succ (max θ ℵ₀)).IsRegular := Cardinal.isRegular_succ (le_max_right _ _)
  have hθμ : θ < Order.succ (max θ ℵ₀) := lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)
  exact not_colorableBy_regular hμreg hθμ (colorableBy_of_le hμκ h)

/-! ### Assembling the `s ≤ 1` slice of `E2Core` -/

/-- The Erdős–Rado triangle-free graph realizes the `s = 1` case of the
Erdős–Hajnal core: a graph on `≤ κ` vertices, not `θ`-colourable for `θ < κ`,
with no odd cycle of length `≤ 3`. -/
theorem e2Core_oddGirth_one (hκ : ℵ₀ < κ) :
    ∃ (W : Type u) (G : SimpleGraph W),
      Cardinal.mk W ≤ κ ∧
      (∀ θ, θ < κ → ¬ (SimpleGraph.toHG G).ColorableBy θ) ∧
      NoShortOddCycle G 1 :=
  ⟨Vtx κ, graph κ, card_le hκ.le, fun _ hθ => not_colorableBy hκ hθ, noShortOddCycle_one⟩

end ER60
end Erdos1177

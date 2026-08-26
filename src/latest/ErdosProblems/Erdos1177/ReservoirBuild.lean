-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.ReservoirSetup
import ErdosProblems.Erdos1177.DeltaRho

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The §6 reservoir recursion: existence of the construction data

This file discharges the *allocation* part of the recursion
(`lem:stage-capacity` and `lem:calibration-construction`): from the
Erdős–Galvin–Hajnal input `E3` we can choose, for every infinite base cardinal
`μ`, all the data of a `CalibData μ` — in particular the injective placement of
copies (using that each level fiber has size `Λ = 2^ρ ≥ |R_α| · ρ · |S|`) and
the apex maps (using `|X_i| = ρ ≥ |E(S)|`).
-/

open Cardinal Ordinal

set_option maxHeartbeats 4000000

namespace Erdos1177

universe u

/-
`#(Vtx ρ) = 2^ρ` for infinite `ρ` (`|R · Λ| = Λ`).
-/
theorem mk_Vtx (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ) : #(Vtx ρ) = (2 : Cardinal.{u}) ^ ρ := by
  -- By definition of Lev, we have #Lev ρ = (Order.succ ρ).ord.card.
  have h_lev : #(Lev ρ) = (Order.succ ρ).ord.card := by
    convert! Cardinal.mk_toType ( Order.succ ρ |> Cardinal.ord ) using 1;
  convert! congr_arg₂ ( · * · ) h_lev ( Cardinal.mk_out _ ) using 1;
  rw [ Cardinal.mul_eq_max ];
  · simp +zetaDelta at *;
    exact Cardinal.cantor _;
  · exact le_trans hρ ( le_trans ( le_of_lt ( Order.lt_succ ρ ) ) ( by simp +decide [ Cardinal.card_ord ] ) );
  · exact le_trans hρ ( Cardinal.cantor ρ |> le_of_lt )

/-
**Stage capacity** (`lem:stage-capacity`): there are at most `Λ = 2^ρ`
admissible reservoirs at any level.
-/
theorem stage_capacity {ρ : Cardinal.{u}} (hρ : ℵ₀ ≤ ρ) {Ilab : Type u}
    (hI : #Ilab ≤ ρ) (q : Ordinal.{u} → Ordinal.{u}) (a : Lev ρ) :
    #{X : Ilab → Set (Vtx ρ) // IsReservoir q a X} ≤ (2 : Cardinal.{u}) ^ ρ := by
  refine' le_trans ( Cardinal.mk_le_mk_of_subset _ ) _;
  exact { X : Ilab → Set ( Vtx ρ ) | ∀ i, X i ⊆ Vbelow a ∧ ( X i = ∅ ∨ # ( X i ) ≤ ρ ) };
  · exact fun X hX i => ⟨ hX.1 i, Or.imp id ( fun h => h.le ) ( hX.2.1 i ) ⟩;
  · -- The cardinality of the set of functions from Ilab to the set of subsets of Vtx ρ with cardinality at most ρ is at most (2^ρ)^#Ilab.
    have h_card : #(Ilab → {t : Set (Vtx ρ) | t ⊆ Vbelow a ∧ (t = ∅ ∨ #t ≤ ρ)}) ≤ (2 ^ ρ) ^ #Ilab := by
      have h_card_pi : Cardinal.mk {t : Set (Vtx ρ) | t ⊆ Vbelow a ∧ (t = ∅ ∨ #t ≤ ρ)} ≤ 2 ^ ρ := by
        refine' le_trans ( Cardinal.mk_le_mk_of_subset _ ) _;
        exact { t : Set ( Vtx ρ ) | #t ≤ ρ };
        · aesop;
        · convert! Cardinal.mk_bounded_set_le ( Vtx ρ ) ρ using 1;
          rw [ mk_Vtx ρ hρ ];
          rw [ max_eq_left ( by exact le_trans ( by exact Cardinal.aleph0_le_continuum ) ( Cardinal.power_le_power_left two_ne_zero hρ ) ), Erdos1177.pow_two_pow_self ρ hρ ];
      exact le_trans ( by simp +decide ) ( Cardinal.power_le_power_right h_card_pi );
    convert! h_card.trans _ using 1;
    · fapply Cardinal.mk_congr;
      exact ⟨ fun X => fun i => ⟨ X.val i, X.property i ⟩, fun X => ⟨ fun i => X i, fun i => X i |>.2 ⟩, fun X => rfl, fun X => rfl ⟩;
    · convert! Cardinal.power_le_power_left _ hI using 1;
      · rw [ Erdos1177.pow_two_pow_self ρ hρ ];
      · exact ne_of_gt ( Cardinal.power_pos _ ( by norm_num ) )

/-
`S` has at most `ρ` edges when `|V(S)| ≤ ρ` (`ρ` infinite).
-/
theorem mk_edgeSet_le {S : Type u} (G : SimpleGraph S) {ρ : Cardinal.{u}}
    (hρ : ℵ₀ ≤ ρ) (hS : #S ≤ ρ) : #G.edgeSet ≤ ρ := by
  refine' le_trans _ ( show ρ * ρ ≤ ρ from _ );
  · refine' le_trans ( Cardinal.mk_subtype_le _ ) _;
    refine' le_trans _ ( mul_le_mul hS hS ( by positivity ) ( by positivity ) );
    convert! Cardinal.mk_le_of_surjective ( Sym2.mk_surjective ) using 1;
  · rw [ Cardinal.mul_eq_self ] ; aesop

/-
**Copy allocation** (`lem:calibration-construction`, placement of copies):
at each level `a` the fiber `Λ = 2^ρ` is large enough to place, injectively over
all `(reservoir, η, vertex)` triples, one copy of `S` per pair `(X, η)`.
-/
theorem exists_copy {ρ : Cardinal.{u}} (hρ : ℵ₀ ≤ ρ) {Ilab : Type u} (hI : #Ilab ≤ ρ)
    {S : Type u} (hS : #S ≤ ρ) (q : Ordinal.{u} → Ordinal.{u}) (a : Lev ρ) :
    ∃ f : {X : Ilab → Set (Vtx ρ) // IsReservoir q a X} → Fib ρ → S → Vtx ρ,
      (∀ X η s, (f X η s).1 = a) ∧
      Function.Injective
        (fun p : ({X : Ilab → Set (Vtx ρ) // IsReservoir q a X} × Fib ρ × S) =>
          f p.1 p.2.1 p.2.2) := by
  obtain ⟨e, he⟩ : ∃ e : ({X : Ilab → Set (Vtx ρ) // IsReservoir q a X} × Fib ρ × S) ↪ Fib ρ, True := by
    refine' ⟨ _, trivial ⟩;
    refine' ( Cardinal.lift_mk_le'.mp _ ) |> Classical.choice;
    simp +zetaDelta at *;
    refine' le_trans ( mul_le_mul' ( stage_capacity hρ hI q a ) ( mul_le_mul' le_rfl hS ) ) _;
    rw [ ← mul_assoc, Cardinal.mul_eq_self ];
    · rw [ Cardinal.mul_eq_left ];
      · exact le_trans hρ ( le_of_lt ( Cardinal.cantor _ ) );
      · exact le_of_lt ( Cardinal.cantor ρ );
      · exact ne_of_gt ( lt_of_lt_of_le ( Cardinal.aleph0_pos ) hρ );
    · exact le_trans hρ ( le_of_lt ( Cardinal.cantor _ ) );
  refine' ⟨ fun X η s => ⟨ a, e ⟨ X, η, s ⟩ ⟩, _, _ ⟩ <;> simp +decide [ Function.Injective ]

/-
**Apex allocation** (`lem:calibration-construction`, the maps `φ_B`):
for an admissible reservoir `X`, the active edges of a copy inject into
`⋃ᵢ Xᵢ` respecting labels (each active `Xᵢ` has size `ρ ≥ |E(S)|`).
-/
theorem exists_phi {ρ : Cardinal.{u}} (hρ : ℵ₀ ≤ ρ) {S : Type u} {Ilab : Type u}
    {G : SimpleGraph S} (lbl : G.edgeSet → Ilab) (hE : #G.edgeSet ≤ ρ)
    (q : Ordinal.{u} → Ordinal.{u}) (a : Lev ρ)
    (X : {X : Ilab → Set (Vtx ρ) // IsReservoir q a X}) :
    ∃ φ : G.edgeSet → Vtx ρ,
      (∀ e, (X.val (lbl e)).Nonempty → φ e ∈ X.val (lbl e)) ∧
      Set.InjOn φ {e | (X.val (lbl e)).Nonempty} := by
  have h_card_le : ∀ i : Ilab, ∃ (f : {e : G.edgeSet // lbl e = i} → Vtx ρ), (∀ (ee : {e : G.edgeSet // lbl e = i}), (X.val i).Nonempty → f ee ∈ X.val i) ∧ Function.Injective f := by
    intro i
    by_cases hX : (X.val i).Nonempty;
    · obtain ⟨f, hf⟩ : ∃ f : {e : G.edgeSet // lbl e = i} ↪ ↥(X.val i), True := by
        have h_card_le : #(X.val i) = ρ := by
          exact X.2.2.1 i |> Or.resolve_left <| by aesop;
        have h_card_le : #{e : G.edgeSet // lbl e = i} ≤ ρ := by
          exact le_trans ( Cardinal.mk_subtype_le _ ) hE;
        exact ⟨ Classical.choice <| Cardinal.lift_mk_le'.mp <| by aesop, trivial ⟩;
      exact ⟨ fun ee => f ee, fun ee _ => f ee |>.2, Subtype.val_injective.comp f.injective ⟩;
    · have h_card_le : #{e : G.edgeSet // lbl e = i} ≤ Cardinal.mk (Vtx ρ) := by
        refine' le_trans _ ( le_trans hE _ );
        · exact Cardinal.mk_subtype_le _;
        · rw [ Erdos1177.mk_Vtx ρ hρ ];
          exact le_of_lt ( Cardinal.cantor _ );
      have := Cardinal.le_mk_iff_exists_set.mp h_card_le;
      obtain ⟨ p, hp ⟩ := this;
      have := Cardinal.eq.1 hp.symm;
      exact ⟨ fun x => this.some x |>.1, by tauto, fun x y hxy => by simpa [ Subtype.ext_iff ] using! this.some.injective <| Subtype.ext hxy ⟩;
  choose f hf₁ hf₂ using h_card_le;
  refine' ⟨ fun e => f ( lbl e ) ⟨ e, rfl ⟩, _, _ ⟩ <;> simp_all +decide [ Set.InjOn ];
  intro e₁ he₁ he₁' e₂ he₂ he₂' h; have := X.2.2.2.1; simp_all +decide [ Set.disjoint_left ] ;
  grind

/-- **Stage capacity + allocation** (`lem:stage-capacity`, `lem:calibration-construction`).
From the Erdős–Galvin–Hajnal property-`P` input `E3`, for every infinite base
cardinal `μ` there is a full set of construction data `CalibData μ`. -/
theorem exists_calibData (h3 : E3_EGH_P.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    Nonempty (CalibData μ) := by
  -- `ρ = 2^μ` is infinite
  have hρ : ℵ₀ ≤ rhoC μ := le_trans hμ (le_of_lt (Cardinal.cantor μ))
  -- E3 supplies the Specker graph, labels and property P
  obtain ⟨S, G, Ilab, hSρ, hIρ, lbl, hP0⟩ := h3 (rhoC μ) hρ
  -- property P at `κ = μ⁺` via monotonicity and `κ ≤ δ(ρ)`
  have hP : SimpleGraph.PropertyP G lbl (Order.succ μ) :=
    hP0.mono (succ_le_deltaRho hμ)
  -- the fibre colouring `q`
  obtain ⟨q, hq1, hq2⟩ := cofinal_fibres (Order.succ μ) (rhoC μ)
    (le_trans hμ (le_of_lt (Order.lt_succ μ))) (succ_le_two_pow μ)
  -- copies
  have hIle : #Ilab ≤ rhoC μ := le_of_eq hIρ
  have hSle : #S ≤ rhoC μ := le_of_eq hSρ
  choose cf cf_lev cf_inj using
    (fun a => exists_copy hρ hIle hSle q a :
      ∀ a : Lev (rhoC μ), ∃ f : _ → Fib (rhoC μ) → S → Vtx (rhoC μ),
        (∀ X η s, (f X η s).1 = a) ∧ _)
  -- apex maps
  have hE : #G.edgeSet ≤ rhoC μ := mk_edgeSet_le G hρ hSle
  choose pf pf_mem pf_inj using
    (fun a X => exists_phi hρ lbl hE q a X :
      ∀ (a : Lev (rhoC μ)) (X : {X : Ilab → Set (Vtx (rhoC μ)) // IsReservoir q a X}),
        ∃ φ : G.edgeSet → Vtx (rhoC μ), _ ∧ _)
  exact ⟨{
    hμ := hμ
    S := S
    G := G
    Ilab := Ilab
    hIlab := hIρ
    hS := hSle
    lbl := lbl
    hP := hP
    q := q
    hq1 := hq1
    hq2 := hq2
    copy := cf
    copy_lev := fun a X η s => cf_lev a X η s
    copy_inj := cf_inj
    phi := pf
    phi_mem := pf_mem
    phi_inj := pf_inj }⟩

end Erdos1177

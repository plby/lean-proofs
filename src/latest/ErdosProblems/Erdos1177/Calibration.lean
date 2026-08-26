-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Reservoir
import ErdosProblems.Erdos1177.Results

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The calibration cardinality bound and Erdős Problem #1177, part (1)

This file records the *calibration cardinality bound* of arXiv:2606.24882 and
uses it to formalize part (1) of Erdős Problem #1177: if `F_G(ℵ₁) ≠ ∅` then it
already contains a witness of cardinality at most `2^{2^{ℵ₀}}`.

The key quantitative fact is that all of the negative-direction constructions at
`λ = ℵ₁` live on a vertex set of cardinality at most `2^{2^{ℵ₀}}`:

* the §6 calibration `L_κ` for `κ = μ⁺` lives on `Vtx (2^μ)`, of cardinality
  exactly `2^{2^μ}` (`Vtx_card`), so `≤ 2^{2^{ℵ₀}}` at `μ = ℵ₀`
  (`successor_linear_bounded`);
* the one-apex lift `Lift(A, ℵ₁)` of any graph `A` with `|V(A)| ≤ ℵ₁` lives on a
  vertex set of cardinality `≤ 2^{ℵ₁} ≤ 2^{2^{ℵ₀}}` (`lift_card_le_aleph1`).

Threading these bounds through the three cases of the obstruction trichotomy
gives the bounded negative core at `ℵ₁` (`negativeCore_bounded_aleph1`), and
hence part (1) (`problem_1177_part1`).

Everything is proved from the same carried external inputs as the headline
results — `ReiherExpansion` (E4), `E3_EGH_P` (E3) and `E2_EH_oddgirth` (E2) —
and is otherwise `sorry`-free.
-/

open Cardinal Ordinal

namespace Erdos1177

universe u

/-! ### The calibration cardinality bound -/

/-- **Cardinality of the calibration vertex set.**  The vertex set
`Vtx (2^μ) = Lev (2^μ) × Fib (2^μ)` of the §6 calibration has cardinality
`|(2^μ)⁺| · 2^{2^μ} = 2^{2^μ}`. -/
theorem Vtx_card (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    #(Vtx (rhoC μ)) = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) := by
  have hρ : ℵ₀ ≤ (2 : Cardinal.{u}) ^ μ := le_trans hμ (le_of_lt (Cardinal.cantor μ))
  have h1 : Order.succ ((2 : Cardinal.{u}) ^ μ) ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) :=
    Order.succ_le_of_lt (Cardinal.cantor _)
  have h2 : ℵ₀ ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) :=
    le_trans hρ (le_of_lt (Cardinal.cantor _))
  have h3 : Order.succ ((2 : Cardinal.{u}) ^ μ) ≠ 0 :=
    (lt_of_le_of_lt zero_le (Order.lt_succ _)).ne'
  show #((Rord (rhoC μ)).ToType × ((2 : Cardinal.{u}) ^ (rhoC μ)).out) = _
  rw [Cardinal.mk_prod, Cardinal.mk_out]
  show Cardinal.lift.{u,u} (#(((Order.succ (rhoC μ)).ord).ToType)) * _ = _
  rw [mk_ord_toType, Cardinal.lift_id, Cardinal.lift_id]
  show Order.succ ((2 : Cardinal.{u}) ^ μ) * (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) = _
  rw [Cardinal.mul_eq_right h2 h1 h3]

/-- **The §6 successor calibration, with the cardinality bound**
(`thm:successor-linear` together with the calibration cardinality bound): for
infinite `μ` there is a linear triple system of chromatic number exactly `μ⁺`
living on a vertex set of cardinality `≤ 2^{2^μ}`. -/
theorem successor_linear_bounded (h3 : E3_EGH_P.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧ H.Linear ∧ H.HasChromatic (Order.succ μ) ∧
        #W ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) := by
  obtain ⟨D⟩ := exists_calibData h3 μ hμ
  exact ⟨_, D.L, D.L_isTripleSystem, D.L_linear, ⟨D.L_colorable, D.L_lower⟩,
    le_of_eq (Vtx_card μ hμ)⟩

/-! ### The lift cardinality bound -/

/-
**Cardinality of the lift vertex set at `κ`.**  For infinite `κ` and any
graph `A` with `|V(A)| ≤ κ`, the lift `Lift(A, κ)` lives on a vertex set of
cardinality `≤ 2^κ`.
-/
theorem lift_card_le {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hα : #α ≤ κ) :
    #(Node A κ × α) ≤ (2 : Cardinal.{u}) ^ κ := by
  -- Since `Node A κ` is a structure with fields `pos : Idx κ` and `seq : {q : Idx κ // q < pos} → A.edgeSet`.
  -- We can bound `#(Node A κ)` by considering the cardinality of the product of these fields.
  have h_node_card : #(Node A κ) ≤ κ * κ ^ κ := by
    have h_node_card : #(Node A κ) ≤ κ * κ ^ κ := by
      have h_card_seq : ∀ pos : Idx κ, #( {q : Idx κ // q < pos} → A.edgeSet ) ≤ κ ^ κ := by
        intro pos
        have h_seq_card : #({q : Idx κ // q < pos} → A.edgeSet) ≤ κ ^ #( {q : Idx κ // q < pos} ) := by
          refine' le_trans ( Cardinal.mk_le_of_injective _ ) _;
          exact ( { q : Idx κ // q < pos } → α × α );
          exact fun f q => f q |>.1.out;
          · intro f g hfg;
            ext q; replace hfg := congr_fun hfg q; simp_all +decide [ funext_iff, Quot.out ] ;
            grind +suggestions;
          · simp +decide [ Cardinal.mk_pi, Cardinal.mk_prod ];
            exact Cardinal.power_le_power_right ( by simpa using! mul_le_mul' hα hα |> le_trans <| by simp +decide [ Cardinal.mul_eq_self hκ ] );
        refine' le_trans h_seq_card ( Cardinal.power_le_power_left _ _ );
        · exact ne_of_gt ( lt_of_lt_of_le ( Cardinal.aleph0_pos ) hκ );
        · refine' le_trans ( Cardinal.mk_le_mk_of_subset _ ) _;
          exact Set.univ;
          · exact Set.subset_univ _;
          · simp +decide [ Cardinal.mk_univ ]
      have h_card_node : #(Node A κ) ≤ Cardinal.mk (Σ pos : Idx κ, {q : Idx κ // q < pos} → A.edgeSet) := by
        refine' ⟨ fun x => ⟨ x.pos, x.seq ⟩, fun x y hxy => _ ⟩ ; cases x ; cases y ; aesop;
      refine' le_trans h_card_node _;
      convert! Cardinal.sum_le_sum _ _ h_card_seq using 1;
      · convert! Cardinal.mk_sigma _;
      · simp +decide [ Cardinal.mk_ord_toType ];
    exact h_node_card;
  refine' le_trans ( Cardinal.mk_prod _ _ |> le_of_eq ) _;
  refine' le_trans ( mul_le_mul' ( Cardinal.lift_le.mpr h_node_card ) ( Cardinal.lift_le.mpr hα ) ) _;
  simp +decide [ Cardinal.power_self_eq hκ ];
  rw [ mul_right_comm, Cardinal.mul_eq_max ];
  · simp +decide [ Cardinal.mul_eq_self hκ ];
    exact le_of_lt ( Cardinal.cantor _ );
  · exact le_trans hκ ( le_mul_of_one_le_right' ( Cardinal.one_le_iff_ne_zero.mpr ( ne_of_gt ( lt_of_lt_of_le ( Cardinal.aleph0_pos ) hκ ) ) ) );
  · exact le_trans hκ ( le_of_lt ( Cardinal.cantor _ ) )

/-- **Cardinality of the lift vertex set at `ℵ₁`.**  For any graph `A` with
`|V(A)| ≤ ℵ₁`, the lift `Lift(A, ℵ₁)` lives on a vertex set of cardinality
`≤ 2^{2^{ℵ₀}}`. -/
theorem lift_card_le_aleph1 {α : Type u} (A : SimpleGraph α)
    (hα : #α ≤ Order.succ (ℵ₀ : Cardinal.{u})) :
    #(Node A (Order.succ (ℵ₀ : Cardinal.{u})) × α) ≤
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u})) := by
  have hℵ₁ : ℵ₀ ≤ Order.succ (ℵ₀ : Cardinal.{u}) := le_of_lt (Order.lt_succ _)
  have hbound : #(Node A (Order.succ (ℵ₀ : Cardinal.{u})) × α) ≤
      (2 : Cardinal.{u}) ^ (Order.succ (ℵ₀ : Cardinal.{u})) :=
    lift_card_le A (Order.succ ℵ₀) hℵ₁ hα
  refine le_trans hbound ?_
  apply Cardinal.power_le_power_left (by norm_num)
  exact Order.succ_le_of_lt (Cardinal.cantor _)

/-! ### The bounded negative core at `ℵ₁` -/

/-
**Bounded negative core at `ℵ₁`.**  If `F ∉ B` then there is an
exact-`ℵ₁`-chromatic `F`-free triple system living on a vertex set of cardinality
`≤ 2^{2^{ℵ₀}}`.  This is the negative direction (`negativeCore_of`) with the
cardinality of each of the three cases tracked, using the calibration bound
(`successor_linear_bounded`, case (i)) and the lift bound (`lift_card_le_aleph1`,
cases (ii) and (iii)).
-/
theorem negativeCore_bounded_aleph1 (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u})
    (F : FTS) (hnb : ¬ Bclass F) :
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧ H.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
        ¬ F.Embeds H ∧ #W ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u})) := by
  by_cases hLin : F.reduce.Linear;
  · have hni : ¬ F.reduce.IntrinsicObligatory := by
      contrapose! hnb; exact (finiteDecomposition_holds F).mpr hnb;
    by_cases hBr : ∀ ed : {e : Finset F.reduce.V // e ∈ F.reduce.edges}, ∃ w ∈ ed.1, IsBridgeInc F.reduce w ed;
    · obtain ⟨c, hc_odd, hc_cycle⟩ : ∃ c : BergeCycle F.reduce, Odd c.m := by
        contrapose! hni;
        exact ⟨ hLin, fun ed => hBr ed, fun c => by simpa using! hni c ⟩;
      obtain ⟨V, A, hcard, hAchr, hAgirth⟩ := hE2 (Order.succ (ℵ₀ : Cardinal)) (Order.lt_succ _) (2 * hc_odd + 1);
      have h_lift_omits : ¬ F.reduce.Embeds (liftHG A (Order.succ ℵ₀)) := by
        apply lift_omits_of_bergeCycle;
        exact hLin;
        convert! hAgirth ( 2 * hc_odd + 1 ) _ _ _ using 1;
        any_goals tauto;
        · rw [ hc_cycle ];
        · rcases hc_odd with ( _ | _ | hc_odd ) <;> simp_all +arith +decide;
          exact absurd hc_cycle ( by linarith [ c.hm ] );
        · grobner;
      grind +suggestions;
    · have hno_bridgeSelector : ¬ Nonempty (BridgeSelector F.reduce) := by
        exact no_bridgeSelector_of ( by push_neg at hBr; exact hBr );
      refine' ⟨ Node ( ⊤ : SimpleGraph ( Order.succ ℵ₀ ).out ) ( Order.succ ℵ₀ ) × ( Order.succ ℵ₀ ).out, liftHG ( ⊤ : SimpleGraph ( Order.succ ℵ₀ ).out ) ( Order.succ ℵ₀ ), _, _, _, _ ⟩;
      · exact Erdos1177.liftHG_tripleSystem _ _;
      · convert! Erdos1177.lift_hasChromatic ( ⊤ : SimpleGraph ( Order.succ ℵ₀ ).out ) ( Order.succ ℵ₀ ) ( Erdos1177.completeGraph_hasChromatic ( Order.succ ℵ₀ ) ) using 1;
      · intro h;
        apply hno_bridgeSelector;
        apply bridgeSelector_of_embeds_lift;
        exact hLin;
        exact F.reduce_embeds_of_embeds h;
      · convert! lift_card_le_aleph1 _ _;
        simp +decide [ Cardinal.mk_out ];
  · obtain ⟨W, H, htri, hHlin, hchr, hcard⟩ := successor_linear_bounded h3 ℵ₀ le_rfl
    use W, H
    refine ⟨ htri, hchr, ?_, hcard ⟩
    intro hF
    have hFreduce : F.reduce.Embeds H := by
      exact F.reduce_embeds_of_embeds hF
    exact absurd (nonlinear_not_embeds_linear hLin hHlin hFreduce) (by
    grind)

/-! ### Erdős Problem #1177, part (1) -/

/-- **Erdős Problem #1177, part (1)** (the calibration cardinality bound).  If
`F_G(ℵ₁) ≠ ∅` — i.e. there is *some* exact-`ℵ₁`-chromatic `G`-free triple
system — then there is already one living on a vertex set of cardinality
`≤ 2^{2^{ℵ₀}}`.  Proved from the same carried external inputs as the headline
theorems (E4, E3, E2). -/
theorem problem_1177_part1 (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (G : FTS) (h : G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u}))) :
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧ H.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
        ¬ G.Embeds H ∧ #W ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u})) := by
  have hnb : ¬ Bclass G :=
    ((spectrum_dichotomy_of_E3 hexp h3 hE2 G (Order.succ ℵ₀)).mp
      ⟨Order.lt_succ _, h⟩).1
  exact negativeCore_bounded_aleph1 h3 hE2 G hnb

end Erdos1177

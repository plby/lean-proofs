-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Structures
import ErdosProblems.Erdos1177.Compactness

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Helper lemmas for closure of obligatory triple systems under amalgamation

Reusable framework lemmas used in the proof of `lem:obligatory-closure`
(closure of the obligatory finite triple systems under one-point amalgamation).
-/

open Cardinal SimpleGraph

namespace Erdos1177

universe u

/-- The restriction of a host hypergraph to a vertex subset `S`. -/
def Hypergraph.restrict {W : Type u} (H : Hypergraph W) (S : Set W) : Hypergraph W :=
  ⟨{e | e ∈ H.edges ∧ e ⊆ S}⟩

/-
A proper colouring into any countable colour type witnesses `ℵ₀`-colourability.
-/
theorem colorableBy_aleph0_of_countable {W : Type u} (H : Hypergraph W) {T : Type u}
    (hT : #T ≤ ℵ₀) {c : W → T} (hc : H.ProperColoring c) : H.ColorableBy ℵ₀ := by
  obtain ⟨ f, hf ⟩ := Cardinal.mk_le_aleph0_iff.mp hT;
  obtain ⟨ g, hg ⟩ := Cardinal.eq.1 ( Cardinal.mk_out ℵ₀ );
  refine' ⟨ fun w => hg ⟨ f ( c w ) ⟩, _ ⟩;
  intro e he; obtain ⟨ u, hu, v, hv, huv ⟩ := hc e he; use u, hu, v, hv; simp +decide [ * ] ;
  grind +qlia

/-
Any type of cardinality `≤ ℵ₀` embeds into `(ℵ₀).out`; a `Countable` product
of finite by `(ℵ₀).out` is countable.
-/
theorem countable_prod_out {I : Type} [Fintype I] : #(I × (ℵ₀ : Cardinal.{u}).out) ≤ ℵ₀ := by
  convert! Cardinal.mk_le_aleph0;
  convert! instCountableProd;
  · infer_instance;
  · convert! Cardinal.mk_le_aleph0_iff.mp ( le_of_eq ( Cardinal.mk_out ℵ₀ ) )

/-
If `F` is obligatory and does not embed into the restriction of a triple
system `H` to `S`, then that restriction is `ℵ₀`-colourable.
-/
theorem restrict_colorable_of_obligatory {W : Type u} {H : Hypergraph W}
    (htri : H.IsTripleSystem) {F : FTS} (hF : FTS.Obligatory.{u} F)
    {S : Set W} (hfree : ¬ F.Embeds (H.restrict S)) :
    (H.restrict S).ColorableBy ℵ₀ := by
  contrapose! hfree;
  apply hF;
  · exact fun e he => htri e he.1;
  · exact hfree

/-
If the vertex set is partitioned into finitely many parts, each inducing an
`ℵ₀`-colourable restriction, then the whole host is `ℵ₀`-colourable.
-/
theorem colorableBy_of_finite_parts {W : Type u} (H : Hypergraph W) {I : Type}
    [Fintype I] [Nonempty I] (part : W → I)
    (hcol : ∀ i : I, (H.restrict (part ⁻¹' {i})).ColorableBy ℵ₀) :
    H.ColorableBy ℵ₀ := by
  choose f hf using hcol;
  refine' colorableBy_aleph0_of_countable H _ _;
  exact I × Quotient.out ℵ₀;
  apply countable_prod_out;
  exact fun w => ( part w, f ( part w ) w );
  intro e he; by_cases h : ∃ i, e ⊆ part ⁻¹' { i } <;> simp_all +decide [ Set.subset_def ] ;
  · obtain ⟨ i, hi ⟩ := h;
    have := hf i;
    obtain ⟨ u, hu, v, hv, huv ⟩ := this e ⟨ he, fun x hx => by aesop ⟩ ; use u, hu, v, hv; aesop;
  · obtain ⟨ u, hu, hu' ⟩ := h ( part ( Classical.choose ( Set.nonempty_iff_ne_empty.mpr ( show e ≠ ∅ from by rintro rfl; simpa using! h ( Classical.arbitrary I ) ) ) ) ) ; obtain ⟨ v, hv, hv' ⟩ := h ( part u ) ; use u, hu, v, hv; aesop;

/-- Averaging / degeneracy: in a graph with an out-orientation of out-degree
`≤ d`, every nonempty finite vertex set contains a vertex of degree `≤ 2d`
inside the set. -/
theorem exists_low_degree_vertex {B : Type u} (D : SimpleGraph B) (d : ℕ)
    (out : B → Finset B) (hout : ∀ v, (out v).card ≤ d)
    (hcov : ∀ v w, D.Adj v w → w ∈ out v ∨ v ∈ out w) [DecidableRel D.Adj]
    (s : Finset B) (hs : s.Nonempty) :
    ∃ v₀ ∈ s, (s.filter (fun w => D.Adj v₀ w)).card ≤ 2 * d := by
  classical
  by_contra h_contra
  push_neg at h_contra
  have h_sum_ge : (2 * d + 1) * s.card ≤ ∑ v ∈ s, (s.filter (fun w => D.Adj v w)).card := by
    calc (2 * d + 1) * s.card = ∑ _v ∈ s, (2 * d + 1) := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ s, (s.filter (fun w => D.Adj v w)).card :=
            Finset.sum_le_sum (fun v hv => h_contra v hv)
  have h_eq : ∑ v ∈ s, (s.filter (fun w => D.Adj v w)).card
      = ((s ×ˢ s).filter (fun p => D.Adj p.1 p.2)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl (fun a _ => (Finset.card_filter _ _))
  have h_sub : (s ×ˢ s).filter (fun p => D.Adj p.1 p.2) ⊆
      ((s ×ˢ s).filter (fun p => p.2 ∈ out p.1)) ∪
      ((s ×ˢ s).filter (fun p => p.1 ∈ out p.2)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rcases hcov p.1 p.2 hp.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp.1, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp.1, h⟩)
  have hc1 : ((s ×ˢ s).filter (fun p => p.2 ∈ out p.1)).card ≤ d * s.card := by
    rw [Finset.card_filter, Finset.sum_product]
    calc ∑ a ∈ s, ∑ b ∈ s, (if b ∈ out a then 1 else 0)
        = ∑ a ∈ s, (s.filter (fun b => b ∈ out a)).card :=
          Finset.sum_congr rfl (fun a _ => (Finset.card_filter _ _).symm)
      _ ≤ ∑ a ∈ s, (out a).card :=
          Finset.sum_le_sum (fun a _ => Finset.card_le_card
            (fun b hb => (Finset.mem_filter.mp hb).2))
      _ ≤ ∑ _a ∈ s, d := Finset.sum_le_sum (fun a _ => hout a)
      _ = d * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hc2 : ((s ×ˢ s).filter (fun p => p.1 ∈ out p.2)).card ≤ d * s.card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    calc ∑ b ∈ s, ∑ a ∈ s, (if a ∈ out b then 1 else 0)
        = ∑ b ∈ s, (s.filter (fun a => a ∈ out b)).card :=
          Finset.sum_congr rfl (fun b _ => (Finset.card_filter _ _).symm)
      _ ≤ ∑ b ∈ s, (out b).card :=
          Finset.sum_le_sum (fun b _ => Finset.card_le_card
            (fun a ha => (Finset.mem_filter.mp ha).2))
      _ ≤ ∑ _b ∈ s, d := Finset.sum_le_sum (fun b _ => hout b)
      _ = d * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have h_sum_le : ∑ v ∈ s, (s.filter (fun w => D.Adj v w)).card ≤ 2 * d * s.card := by
    rw [h_eq]
    calc ((s ×ˢ s).filter (fun p => D.Adj p.1 p.2)).card
        ≤ (((s ×ˢ s).filter (fun p => p.2 ∈ out p.1)) ∪
            ((s ×ˢ s).filter (fun p => p.1 ∈ out p.2))).card := Finset.card_le_card h_sub
      _ ≤ ((s ×ˢ s).filter (fun p => p.2 ∈ out p.1)).card +
            ((s ×ˢ s).filter (fun p => p.1 ∈ out p.2)).card := Finset.card_union_le _ _
      _ ≤ d * s.card + d * s.card := Nat.add_le_add hc1 hc2
      _ = 2 * d * s.card := by ring
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  nlinarith [h_sum_ge, h_sum_le, hpos]

/-- A finite-graph degeneracy colouring: if `D` has an orientation `out` with all
out-degrees `≤ d`, then any finite vertex set admits a proper `(2d+1)`-colouring
(restricted to that set). -/
theorem finite_degenerate_coloring {B : Type u} (D : SimpleGraph B) (d : ℕ)
    (out : B → Finset B) (hout : ∀ v, (out v).card ≤ d)
    (hcov : ∀ v w, D.Adj v w → w ∈ out v ∨ v ∈ out w) [DecidableRel D.Adj]
    (s : Finset B) :
    ∃ c : B → Fin (2 * d + 1), ∀ a ∈ s, ∀ b ∈ s, D.Adj a b → c a ≠ c b := by
  classical
  suffices H : ∀ n (s : Finset B), s.card = n →
      ∃ c : B → Fin (2 * d + 1), ∀ a ∈ s, ∀ b ∈ s, D.Adj a b → c a ≠ c b by
    exact H s.card s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp⟩
    · obtain ⟨v₀, hv₀, hdeg⟩ := exists_low_degree_vertex D d out hout hcov s hne
      have hcard' : (s.erase v₀).card < n := by
        rw [← hs]; exact Finset.card_erase_lt_of_mem hv₀
      obtain ⟨c', hc'⟩ := ih (s.erase v₀).card hcard' (s.erase v₀) rfl
      set Bad := (s.filter (fun w => D.Adj v₀ w)).image c' with hBad
      have hBadcard : Bad.card ≤ 2 * d := le_trans (Finset.card_image_le) hdeg
      obtain ⟨col, hcolBad⟩ : ∃ col : Fin (2 * d + 1), col ∉ Bad := by
        by_contra hcon
        push_neg at hcon
        have hsub : (Finset.univ : Finset (Fin (2 * d + 1))) ⊆ Bad := fun x _ => hcon x
        have := Finset.card_le_card hsub
        rw [Finset.card_univ, Fintype.card_fin] at this
        omega
      refine ⟨Function.update c' v₀ col, ?_⟩
      intro a ha b hb hab
      have hane : a ≠ b := hab.ne
      by_cases haeq : a = v₀
      · subst haeq
        have hbne : b ≠ a := fun h => hane h.symm
        have hc'bBad : c' b ∈ Bad :=
          Finset.mem_image_of_mem c' (Finset.mem_filter.mpr ⟨hb, hab⟩)
        rw [Function.update_self, Function.update_of_ne hbne]
        exact fun h => hcolBad (h ▸ hc'bBad)
      · by_cases hbeq : b = v₀
        · subst hbeq
          have hc'aBad : c' a ∈ Bad :=
            Finset.mem_image_of_mem c' (Finset.mem_filter.mpr ⟨ha, hab.symm⟩)
          rw [Function.update_of_ne haeq, Function.update_self]
          exact fun h => hcolBad (h ▸ hc'aBad)
        · rw [Function.update_of_ne haeq, Function.update_of_ne hbeq]
          exact hc' a (Finset.mem_erase.mpr ⟨haeq, ha⟩) b (Finset.mem_erase.mpr ⟨hbeq, hb⟩) hab

/-- **Degeneracy colouring via de Bruijn–Erdős.**  If `D` has an orientation with
all out-degrees `≤ d`, then `D` is `(2d+1)`-colourable. -/
theorem colorable_of_out {B : Type u} (D : SimpleGraph B) (d : ℕ)
    (out : B → Finset B) (hout : ∀ v, (out v).card ≤ d)
    (hcov : ∀ v w, D.Adj v w → w ∈ out v ∨ v ∈ out w) [DecidableRel D.Adj] :
    ∃ c : B → Fin (2 * d + 1), ∀ a b, D.Adj a b → c a ≠ c b := by
  have : NeZero (2 * d + 1) := ⟨by omega⟩
  exact colorable_of_forall_finite D (2 * d + 1)
    (finite_degenerate_coloring D d out hout hcov)

/-- Restricting an uncountably chromatic triple system to the complement of a
finite vertex set stays uncountably chromatic (and a triple system): recolour the
finitely many deleted vertices with a disjoint copy of the countable palette. -/
theorem restrict_uc {W : Type u} {H : Hypergraph W} (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Finite) :
    (⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩ : Hypergraph W).UncountablyChromatic := by
  rintro ⟨c, hc⟩
  apply huc
  have hSfin : Finite ↥S := hS
  have hle : (#((ℵ₀ : Cardinal.{u}).out ⊕ ↥S)) ≤ (#((ℵ₀ : Cardinal.{u}).out)) := by
    rw [Cardinal.mk_sum, Cardinal.mk_out]
    have h2 : Cardinal.lift.{u,u} (#(↥S)) ≤ ℵ₀ := by
      rw [Cardinal.lift_le_aleph0]; exact le_of_lt (Cardinal.lt_aleph0_of_finite _)
    calc Cardinal.lift.{u,u} ℵ₀ + Cardinal.lift.{u,u} (#(↥S))
        ≤ ℵ₀ + ℵ₀ := add_le_add (by simp) h2
      _ = ℵ₀ := by simp
  obtain ⟨j, hj⟩ := (Cardinal.le_def _ _).mp hle
  classical
  refine ⟨fun w => if h : w ∈ S then j (Sum.inr ⟨w, h⟩) else j (Sum.inl (c w)), ?_⟩
  intro e he
  by_cases heS : e ⊆ Sᶜ
  · obtain ⟨u, hu, v, hv, huv⟩ := hc e ⟨he, heS⟩
    have hus : u ∉ S := fun h => (heS hu) h
    have hvs : v ∉ S := fun h => (heS hv) h
    refine ⟨u, hu, v, hv, ?_⟩
    simp only [dif_neg hus, dif_neg hvs]
    exact fun h => huv (by have := hj h; simpa using! this)
  · rw [Set.not_subset] at heS
    obtain ⟨w, hwe, hwS⟩ := heS
    have hwS' : w ∈ S := by simpa [Set.mem_compl_iff, not_not] using! hwS
    obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Set.ncard_eq_three.mp (htri e he)
    have : ∃ v ∈ ({a, b, d} : Set W), v ≠ w := by
      rcases hwe with rfl | rfl | rfl
      · exact ⟨b, by simp, hab.symm⟩
      · exact ⟨a, by simp, hab⟩
      · exact ⟨a, by simp, had⟩
    obtain ⟨v, hv, hvw⟩ := this
    refine ⟨w, hwe, v, hv, ?_⟩
    simp only [dif_pos hwS']
    by_cases hvS : v ∈ S
    · simp only [dif_pos hvS]
      exact fun h => hvw (by have := hj h; simp at this; exact this.symm)
    · simp only [dif_neg hvS]
      exact fun h => by have := hj h; simp at this

end Erdos1177

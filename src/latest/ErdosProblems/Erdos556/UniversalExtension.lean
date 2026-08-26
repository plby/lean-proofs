import ErdosProblems.Erdos556.MatchingInterface
import Mathlib.Combinatorics.SimpleGraph.Tutte

/-!
# Universal vertices for the Tutte--Berge reduction

The extension retains the original graph and joins a new clique to it.
-/

namespace Erdos556

open SimpleGraph

def universalExtension {V W : Type*} (G : SimpleGraph V) : SimpleGraph (V ⊕ W) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | _, _ => x ≠ y
  symm := ⟨by intro x y; cases x <;> cases y <;> simp [G.adj_comm, ne_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

theorem universalExtension_inl_adj {V W : Type*} (G : SimpleGraph V) (u v : V) :
    (universalExtension (W := W) G).Adj (Sum.inl u) (Sum.inl v) ↔ G.Adj u v := Iff.rfl

theorem universalExtension_inr_universal {V W : Type*} (G : SimpleGraph V) (w : W) :
    (universalExtension G).IsUniversal (Sum.inr w) := by
  intro x hx
  cases x <;> exact hx

theorem connected_deleteVerts_of_universal {V : Type*} (G : SimpleGraph V)
    {u : V} (hu : G.IsUniversal u) (X : Set V) (huX : u ∉ X) :
    ((⊤ : G.Subgraph).deleteVerts X).coe.Connected := by
  let u' : ((⊤ : G.Subgraph).deleteVerts X).verts := ⟨u, ⟨trivial, huX⟩⟩
  apply SimpleGraph.Connected.of_isUniversal (v := u')
  intro y hy
  exact ⟨u'.property, y.property, hu (fun h => hy (Subtype.ext h))⟩

theorem connected_oddComponents_card_le_one {V : Type*} [Finite V]
    (G : SimpleGraph V) (hG : G.Connected) : G.oddComponents.ncard ≤ 1 := by
  let : Subsingleton G.ConnectedComponent := hG.preconnected.subsingleton_connectedComponent
  apply Set.ncard_le_one_iff_subsingleton.mpr
  intro a _ b _
  exact Subsingleton.elim a b

theorem connected_even_oddComponents_card_zero {V : Type*} [Finite V]
    (G : SimpleGraph V) (hG : G.Connected) (hN : Even (Nat.card V)) :
    G.oddComponents.ncard = 0 := by
  have hle := connected_oddComponents_card_le_one G hG
  have heven : Even G.oddComponents.ncard := by
    apply Nat.not_odd_iff_even.mp
    intro hodd
    exact (Nat.not_odd_iff_even.mpr hN) ((SimpleGraph.odd_ncard_oddComponents G).mp hodd)
  obtain ⟨k, hk⟩ := heven
  omega

theorem isTutteViolator_contains_universal {V : Type*} [Finite V]
    (G : SimpleGraph V) (hN : Even (Nat.card V)) {X : Set V}
    (hX : G.IsTutteViolator X) {u : V} (hu : G.IsUniversal u) : u ∈ X := by
  by_contra huX
  have hc := connected_deleteVerts_of_universal G hu X huX
  have hle := connected_oddComponents_card_le_one _ hc
  have hcardX : X.ncard = 0 := by
    unfold SimpleGraph.IsTutteViolator at hX
    omega
  have hXe : X = ∅ := (Set.ncard_eq_zero (Set.toFinite X)).mp hcardX
  have heven : Even (Nat.card ((⊤ : G.Subgraph).deleteVerts X).verts) := by
    simpa [Subgraph.deleteVerts_verts, hXe, Subgraph.verts_top, Nat.card_coe_set_eq] using hN
  have hz := connected_even_oddComponents_card_zero _ hc heven
  unfold SimpleGraph.IsTutteViolator at hX
  omega

theorem isomorphic_oddComponents_ncard {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) : G.oddComponents.ncard = H.oddComponents.ncard := by
  have hcard (c : G.ConnectedComponent) :
      c.supp.ncard = (e.connectedComponentEquiv c).supp.ncard := by
    simpa only [Nat.card_coe_set_eq] using Nat.card_congr (ConnectedComponent.isoEquivSupp e c)
  let f : G.oddComponents ≃ H.oddComponents := e.connectedComponentEquiv.subtypeEquiv
    (fun c => by change Odd c.supp.ncard ↔ Odd (e.connectedComponentEquiv c).supp.ncard; rw [hcard])
  simpa only [Nat.card_coe_set_eq] using Nat.card_congr f

theorem universalExtension_violator_inr {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (hN : Even (Nat.card V + Nat.card W)) {X : Set (V ⊕ W)}
    (hX : (universalExtension G).IsTutteViolator X) (w : W) : Sum.inr w ∈ X := by
  apply isTutteViolator_contains_universal (universalExtension G) _ hX
    (universalExtension_inr_universal G w)
  simpa only [Nat.card_sum] using hN

noncomputable def universalExtension_deleteIso {V W : Type*} (G : SimpleGraph V)
    (X : Set (V ⊕ W)) (hX : ∀ w, Sum.inr w ∈ X) :
    ((⊤ : G.Subgraph).deleteVerts (Sum.inl ⁻¹' X)).coe ≃g
      ((⊤ : (universalExtension G).Subgraph).deleteVerts X).coe := by
  let f : ((⊤ : G.Subgraph).deleteVerts (Sum.inl ⁻¹' X)).verts →
      ((⊤ : (universalExtension G).Subgraph).deleteVerts X).verts :=
    fun v => ⟨Sum.inl v.val, ⟨trivial, v.property.2⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val huv))
    · intro z
      rcases z with ⟨v | w, hv⟩
      · exact ⟨⟨v, ⟨trivial, hv.2⟩⟩, rfl⟩
      · exact (hv.2 (hX w)).elim
  refine ⟨Equiv.ofBijective f hf, ?_⟩
  intro u v
  change (_ ∧ _ ∧ G.Adj u.val v.val) ↔ (_ ∧ _ ∧ G.Adj u.val v.val)
  rfl

open scoped Classical in
theorem matching_of_perfect_universalExtension {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (M : (universalExtension (W := W) G).Subgraph)
    (hM : M.IsPerfectMatching) :
    ∃ F, EdgeMatching G F ∧ Nat.card V ≤ 2 * F.card + Nat.card W := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype W := Fintype.ofFinite W
  let K : G.Subgraph := {
    verts := {u | ∃ v, M.Adj (Sum.inl u) (Sum.inl v)}
    Adj u v := M.Adj (Sum.inl u) (Sum.inl v)
    adj_sub := fun h => M.adj_sub h
    edge_vert := fun h => ⟨_, h⟩
    symm := ⟨fun _ _ h => h.symm⟩ }
  have hK : K.IsMatching := by
    intro u hu
    obtain ⟨v, huv⟩ := hu
    refine ⟨v, huv, ?_⟩
    intro w huw
    exact Sum.inl.inj (hM.1.eq_of_adj_left huw huv)
  have hpartner : ∀ u : ↥(K.vertsᶜ), ∃ w : W, M.Adj (Sum.inl u.val) (Sum.inr w) := by
    intro u
    obtain ⟨z, hz, _⟩ := hM.1 (hM.2 (Sum.inl u.val))
    cases z with
    | inl v => exact (u.property ⟨v, hz⟩).elim
    | inr w => exact ⟨w, hz⟩
  choose f hf using hpartner
  have hfinj : Function.Injective f := by
    intro u v huv
    have hh := hM.1.eq_of_adj_right (hf u) (huv.symm ▸ hf v)
    exact Subtype.ext (Sum.inl.inj hh)
  have hcompl : K.vertsᶜ.ncard ≤ Nat.card W := by
    simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hfinj
  let F := K.spanningCoe.edgeFinset
  have hF : EdgeMatching G F := edgeMatching_of_subgraphMatching K hK
  have hsupport : K.verts.ncard = 2 * F.card := by
    rw [← matchingSupport_of_subgraphMatching K hK, Set.ncard_coe_finset]
    exact hF.card_support
  have hsum := Set.ncard_add_ncard_compl K.verts
  refine ⟨F, hF, ?_⟩
  omega

theorem ncard_sum_set_of_all_inr {V W : Type*} [Finite V] [Finite W]
    (X : Set (V ⊕ W)) (hX : ∀ w, Sum.inr w ∈ X) :
    X.ncard = (Sum.inl ⁻¹' X).ncard + Nat.card W := by
  have hr : Nat.card {w : W // Sum.inr w ∈ X} = Nat.card W :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hX)
  have hsum := Nat.card_congr (Equiv.subtypeSum (p := fun z => z ∈ X))
  rw [Nat.card_sum, hr] at hsum
  change Nat.card ↥X = Nat.card ↥(Sum.inl ⁻¹' X) + Nat.card W at hsum
  simpa only [Nat.card_coe_set_eq] using hsum

end Erdos556

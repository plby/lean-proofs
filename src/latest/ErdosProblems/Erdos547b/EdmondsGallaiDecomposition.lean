import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Set.Card

variable {V : Type*} {G : SimpleGraph V} {S T : Set V} {v w : V}

namespace SimpleGraph

lemma exists_crossing_edge {v w : V}
  {X : Set V} (h₀ : v ∈ X) (h₁ : w ∉ X) (h : G.Reachable v w) : ∃ x ∈ X, ∃ y ∈ Xᶜ, G.Adj x y := by
  rcases h with ⟨p⟩
  induction p with
   | nil => contradiction
   | @cons u x _ ux _ ih =>
     by_cases h: x ∈ X
     · exact ih h h₁
     · exact ⟨u, h₀, x, h, ux⟩


def IsClosed (G : SimpleGraph V) (S : Set V) : Prop :=
    ¬∃ x ∈ S, ∃y ∈ Sᶜ, G.Adj x y


lemma IsClosed.compl (h : G.IsClosed S) : G.IsClosed Sᶜ := by
    rintro ⟨x, hx, y, hy, xy⟩
    have: S = Sᶜᶜ := by simp
    rw[← this] at hy
    exact h ⟨y, hy, x, hx, G.adj_symm xy⟩


lemma IsClosed.union (h₀ : G.IsClosed S) (h₁ : G.IsClosed T) : G.IsClosed (S ∪ T) := by
  rintro ⟨x, (hx | hx), y, hy, xy⟩
  · rw[Set.mem_compl_iff, Set.mem_union] at hy
    push_neg at hy
    exact h₀ ⟨x, hx, y, hy.1, xy⟩
  · rw[Set.mem_compl_iff, Set.mem_union] at hy
    push_neg at hy
    exact h₁ ⟨x, hx, y, hy.2, xy⟩

lemma IsClosed.biUnion {α : Type*} (S : Set α) (f : α → Set V)
 (hS : ∀ s ∈ S, G.IsClosed (f s)) :
  G.IsClosed (⋃ s ∈ S, (f s)) := by
  rintro ⟨x, hx, y, hy, xy⟩
  simp at hx hy
  obtain ⟨s, hs⟩ := hx
  exact (hS s hs.1) ⟨x, hs.2, y, hy s hs.1, xy⟩

lemma IsClosed.iUnion {ι : Type*} (s : ι → Set V) (hS : (i : ι) → G.IsClosed (s i))
  : G.IsClosed (⋃ (i : ι), s i) := by
  rintro ⟨x, hx , y, hy, xy⟩
  rw[Set.compl_iUnion, Set.mem_iInter] at hy
  rcases Set.mem_iUnion.1 hx with ⟨w, hw⟩
  exact (hS w) ⟨x, hw, y, hy w, xy⟩

lemma ConnectedComponent.isClosed_supp (C : G.ConnectedComponent) : G.IsClosed C.supp := by
  rintro ⟨x, hx, y, hy, xy⟩
  apply hy
  rw[← hx]
  exact ConnectedComponent.connectedComponentMk_eq_of_adj xy.symm


lemma IsClosed.val_preimage_closed (B : Set V) (h₁ : G.IsClosed S) :
  (G.induce B).IsClosed ((↑) ⁻¹' S) :=
  fun ⟨⟨x, _⟩, hx, ⟨y, _⟩, hy, xy⟩ ↦ h₁ ⟨x, hx, y, hy, xy⟩


lemma IsClosed.induce_of_not_adj {B : Set {x // x ∈ S}}
  (hc : (G.induce S).IsClosed B) (he : ¬(∃ x ∈ T \ S, ∃ y ∈ B, G.Adj x y)) :
  (G.induce T).IsClosed (Subtype.val ⁻¹' (↑B)) := by
  rintro ⟨⟨x, xt⟩, hx, ⟨y, yt⟩, hy, xy⟩
  simp at hx hy
  rcases hx with ⟨x', hx'⟩
  by_cases hy': y ∈ S
  · exact hc ⟨⟨x, x'⟩, hx', ⟨y, hy'⟩, hy hy', xy⟩
  · exact he ⟨y, ⟨yt, hy'⟩, ⟨x, x'⟩, hx', xy.symm⟩


lemma IsClosed.mem_of_reachable
  (vs : v ∈ S) (h₀ : G.IsClosed S) (h₁ : G.Reachable v w) : w ∈ S := by
  by_contra! wns
  exact h₀ <| exists_crossing_edge vs wns h₁


lemma IsClosed.reachable_induce (vs : v ∈ S) (h₀ : G.IsClosed S) (h₁ : G.Reachable v w) :
  ∃(ws : w ∈ S), (G.induce S).Reachable ⟨v, vs⟩ ⟨w, ws⟩ := by
  obtain ⟨p⟩ := h₁
  induction p with
    | nil =>
      use vs
    | @cons u v w uv p ih =>
      have h': v ∈ S := IsClosed.mem_of_reachable vs h₀ ⟨uv.toWalk⟩
      have adj: (G.induce S).Adj ⟨u, vs⟩ ⟨v, h'⟩ := uv
      rcases ih h' with ⟨ws, ⟨p⟩⟩
      exact ⟨ws, ⟨Walk.cons adj p⟩⟩

lemma IsClosed.connectedComponent_map_induce_injective (h : G.IsClosed S) :
  Function.Injective (ConnectedComponent.map (Embedding.induce S : G.induce S ↪g G).toHom) := by
  intro C C' h'
  obtain ⟨⟨v, vs⟩, rfl⟩ := C.nonempty_supp
  obtain ⟨w, rfl⟩ := C'.nonempty_supp
  simp only [ConnectedComponent.map_mk, ConnectedComponent.eq] at h'
  exact ConnectedComponent.sound (h.reachable_induce vs h').2


lemma IsClosed.connectedComponent_map_induce_supp_subset
  (h : G.IsClosed S) (C : (G.induce S).ConnectedComponent) :
  (C.map (Embedding.induce S).toHom).supp ⊆ S := by
  intro _ h'
  obtain ⟨⟨_, vs⟩, rfl⟩ := C.nonempty_supp
  rw[ConnectedComponent.map_mk, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at h'
  exact h.mem_of_reachable vs h'.symm


lemma IsClosed.connectedComponent_eq_map_induce_iff
  (h : G.IsClosed S) {C : (G.induce S).ConnectedComponent} {v : {x // x ∈ S}} :
  (G.connectedComponentMk ↑v) = C.map (Embedding.induce S).toHom ↔
  (G.induce S).connectedComponentMk v = C := by
  refine C.ind fun u => ?_
  simp only [← h.connectedComponent_map_induce_injective.eq_iff, ConnectedComponent.map_mk]
  rfl


lemma IsClosed.connectedComponent_map_induce_supp_eq {S : Set V} (h : G.IsClosed S)
  (C : (G.induce S).ConnectedComponent) :
  (C.map (Embedding.induce S).toHom).supp = ↑C.supp := by
  ext x; simp[← h.connectedComponent_eq_map_induce_iff]
  exact fun hx ↦
        h.connectedComponent_map_induce_supp_subset C
        <| (ConnectedComponent.mem_supp_iff _ _).2 hx


lemma IsClosed.connectedComponent_ncard_eq
  (h : G.IsClosed S) (C : (G.induce S).ConnectedComponent) :
  (C.map (Embedding.induce S).toHom).supp.ncard = C.supp.ncard := by
  rw[h.connectedComponent_map_induce_supp_eq,
     Set.ncard_image_of_injective _ Subtype.val_injective]


theorem IsClosed.oddComponents_ncard_add_compl_eq [Fintype V] (h : G.IsClosed S) :
  (G.induce S).oddComponents.ncard + (G.induce Sᶜ).oddComponents.ncard = G.oddComponents.ncard := by
  rw[← Set.ncard_image_of_injective _ h.connectedComponent_map_induce_injective,
     ← Set.ncard_image_of_injective _ h.compl.connectedComponent_map_induce_injective,
     ← Set.ncard_union_eq]
  · congr; ext x
    refine x.ind (fun u ↦ ?_)
    simp only [Set.mem_union, Set.mem_image, Set.mem_setOf]
    constructor
    · rintro (⟨c, ⟨_, h'⟩⟩ | ⟨c, ⟨_, h'⟩⟩)
      · rwa[← h', h.connectedComponent_ncard_eq c]
      · rwa[← h', h.compl.connectedComponent_ncard_eq c]
    rintro h'
    by_cases us: u ∈ S
    · left
      refine ⟨(G.induce S).connectedComponentMk ⟨u, us⟩, ⟨?_ , rfl⟩⟩
      rwa[← h.connectedComponent_ncard_eq]
    · right
      refine ⟨(G.induce Sᶜ).connectedComponentMk ⟨u, us⟩ , ⟨?_ , rfl⟩⟩
      rwa[← h.compl.connectedComponent_ncard_eq]

  rw[Set.disjoint_iff]
  rintro x ⟨⟨xs, ⟨_, xim⟩⟩, ⟨xsc, ⟨_, ximsc⟩⟩⟩
  let ⟨x', hx'⟩ := x.nonempty_supp
  exact (ximsc ▸ h.compl.connectedComponent_map_induce_supp_subset xsc) hx' <|
        (xim ▸ h.connectedComponent_map_induce_supp_subset xs) hx'


end SimpleGraph


variable {V V' : Type*}
variable {G H : SimpleGraph V}
variable {G' H' : SimpleGraph V'}
variable {S B T : Set V}
variable {S' : Set V'}
variable {C : G.ConnectedComponent}


namespace SimpleGraph

abbrev ι : G.induce S ↪g G := Embedding.induce S

def IsFactorCriticalArea (G : SimpleGraph V) (S : Set V) : Prop :=
  S.Nonempty ∧ ∀ v ∈ S, ∃ M : G.Subgraph, M.IsMatching ∧ M.support = S \ {v}

def IsMatchableToComponents (S : Set V) : Prop :=
  ∃ (f : S → (G.induce Sᶜ).ConnectedComponent),
  Function.Injective f ∧ (∀ s : S, ∃ y ∈ (f s), G.Adj ↑s ↑y)

open Classical in
open Fintype in
lemma IsMatchableToComps.card_le [Fintype V] (h : G.IsMatchableToComponents S) :
  card S ≤ card (G.induce Sᶜ).ConnectedComponent := by
  obtain ⟨f, finj, _⟩ := h
  exact Fintype.card_le_of_injective f finj

def connectedComponentsNeighbors (s : S) : Set (G.induce Sᶜ).ConnectedComponent :=
  {C : (G.induce Sᶜ).ConnectedComponent | ∃ y ∈ C.supp, G.Adj s y}

open Fintype in
lemma not_matchable_exists_hall_violator [Fintype V] (h : ¬ G.IsMatchableToComponents S) :
  ∃ (A : Set S),
     A.ncard > (⋃ a ∈ A, G.connectedComponentsNeighbors a).ncard  := by
     classical
     let r := fun (s : S) (C : (G.induce Sᶜ).ConnectedComponent) ↦ ∃ y ∈ C.supp, G.Adj s y
     apply (Iff.not (all_card_le_filter_rel_iff_exists_injective r)).2 at h
     push_neg at h
     rcases h with ⟨A, hA⟩
     use A
     rw[Set.ncard_coe_finset, Finset.set_biUnion_coe, gt_iff_lt, Set.ncard_eq_toFinset_card']
     convert hA using 1
     all_goals try rfl
     congr 1
     ext C
     simp [connectedComponentsNeighbors, r]

lemma IsMatching.exists_of_disjoint_sets_of_injective {A B : Set V} (f : A → B) (hd : Disjoint A B)
  (hf : ∀ a : A, G.Adj a (f a)) (hinj : Function.Injective f) :
  ∃ M : G.Subgraph, M.verts = A ∪ (↑(Set.range f)) ∧ M.IsMatching := by
  have: ↑(Set.range f) ⊆ B := by simp
  let hd' := (Set.disjoint_of_subset_right this hd)
  let f' := (Equiv.ofInjective f hinj).trans (Equiv.Set.image _ (Set.range f) Subtype.val_injective)
  exact Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hd' f' hf


open Subgraph in
lemma IsFactorCriticalArea.odd_ncard [Fintype V]
  (h : G.IsFactorCriticalArea S) : Odd S.ncard := by
  classical
  obtain ⟨v, vs⟩ := h.1
  rcases (h.2 v vs) with ⟨M, hM⟩
  rw[← Set.ncard_diff_singleton_add_one vs, ← Nat.not_even_iff_odd, Nat.even_add_one,
      not_not, ← hM.2, Set.ncard_eq_toFinset_card', hM.1.support_eq_verts]
  exact hM.1.even_card

lemma Iso.ncard_supp_map_eq (φ : G ≃g G') (C : G.ConnectedComponent) :
  C.supp.ncard = (C.map φ.toHom).supp.ncard := by
  rw[Set.ncard, Set.encard_congr (C.isoEquivSupp φ), ← Set.ncard]
  rfl

lemma Iso.oddComponents_ncard_eq (φ : G ≃g G') :
  G.oddComponents.ncard = G'.oddComponents.ncard := by
  have: G.oddComponents ≃ G'.oddComponents := by
    refine φ.connectedComponentEquiv.subtypeEquiv fun u ↦ ?_
    simp only [oddComponents, Set.mem_setOf, Iso.ncard_supp_map_eq φ]
    rfl
  rw[Set.ncard, Set.encard_congr this, Set.ncard]

def induce_congr (h : B = S) : G.induce B ≃g G.induce S where
  toFun := by subst h; exact id
  invFun := by subst h; exact id
  map_rel_iff' := by
    intro a b
    subst h
    rfl

  left_inv := by intro x; subst h; rfl
  right_inv := by intro x; subst h; rfl


variable [Fintype V] [Fintype V']

def induce_induce_iso (G : SimpleGraph V) (T : Set {x // x ∈ S}) :
  (G.induce S).induce T ≃g (G.induce (↑T : Set V)) where
  toFun := by
    rintro ⟨⟨s, hs⟩, hc⟩
    use s
    use ⟨s, hs⟩

  invFun := by
    rintro ⟨s, hs⟩
    have: s ∈ S := by rcases hs with ⟨⟨_, hs'⟩, ⟨_, rfl⟩⟩; exact hs'
    use ⟨s, this⟩
    have: ⟨s, this⟩ ∈ T := by
      rcases hs with ⟨x, hx, rfl⟩; exact hx
    assumption

  map_rel_iff' := by rfl

lemma odd_comp_eq_zero_induce_even_comp
  (C : G.ConnectedComponent) (h : Even C.supp.ncard) :
  (G.induce C.supp).oddComponents.ncard = 0 := by
  rw[Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
  intro C'
  obtain ⟨⟨x, xc⟩, rfl⟩ := C'.nonempty_supp
  rw[Set.mem_setOf, ← C.isClosed_supp.connectedComponent_ncard_eq,
    ConnectedComponent.map_mk]
  dsimp
  rwa[xc, Nat.not_odd_iff_even]


omit [Fintype V] in
lemma odd_comp_eq_one_induce_odd_comp
  (C : G.ConnectedComponent) (h : Odd C.supp.ncard) :
  (G.induce C.supp).oddComponents.ncard = 1 := by
  rw[Set.ncard_eq_one]
  obtain ⟨u, uc⟩ := C.nonempty_supp
  use (G.induce C.supp).connectedComponentMk ⟨u, uc⟩
  ext x
  refine x.ind fun ⟨v, vc⟩ ↦ ?_
  rw[Set.mem_setOf, Set.mem_singleton_iff, eq_comm,
     ← C.isClosed_supp.connectedComponent_eq_map_induce_iff, uc,
     ConnectedComponent.map_mk, eq_comm, ← C.mem_supp_iff,
     ← C.isClosed_supp.connectedComponent_ncard_eq, ConnectedComponent.map_mk]
  dsimp
  rw[vc]
  exact iff_of_true h vc

noncomputable
def d (G : SimpleGraph V) (S : Set V) : ℤ :=
    (G.induce Sᶜ).oddComponents.ncard - S.ncard

noncomputable
def score (G : SimpleGraph V) (B : Set V) : Lex (ℤ × ℕ) :=
  (d G B, B.ncard)

def exists_maximal_score (G : SimpleGraph V) :
  ∃ (B : Set V), ∀ (S : Set V), score G S ≤ score G B := by
  let ps : (Set (Set V)) := Set.univ
  have psnonempty: ps.Nonempty := by simp[ps]
  have psfinite: ps.Finite := by simp[Set.toFinite]
  rcases Set.exists_max_image ps (score G) psfinite psnonempty with ⟨B', _, h⟩
  exact ⟨B', fun S ↦  Set.mem_univ S |> h S⟩

noncomputable
def edmonds_gallai_set (G : SimpleGraph V) : Set V := (exists_maximal_score G).choose

lemma edmonds_gallai_is_maximal_d (G : SimpleGraph V) :
  ∀ (B : Set V), d G B ≤ d G (edmonds_gallai_set G) := by
  intro B
  have h := (exists_maximal_score G).choose_spec B
  apply Prod.Lex.monotone_fst at h
  rwa[edmonds_gallai_set]

lemma edmonds_gallai_is_maximal_card (G : SimpleGraph V) (h : d G S = d G (edmonds_gallai_set G)) :
  S.ncard ≤ (edmonds_gallai_set G).ncard := by
  have h' := (exists_maximal_score G).choose_spec S
  change toLex (d G S, S.ncard) ≤
    toLex (d G (edmonds_gallai_set G), (edmonds_gallai_set G).ncard) at h'
  simp only [Prod.Lex.le_iff, ofLex_toLex] at h'
  rcases h' with h_lt | ⟨_ , h'⟩
  · rw[h] at h_lt
    apply lt_irrefl at h_lt
    contradiction
  · exact h'

lemma ncard_ge_induce_iUnion_oddComponents (Cs : Set G.ConnectedComponent) :
  Cs.ncard ≥ (G.induce (⋃ c ∈ Cs, c.supp)).oddComponents.ncard := by
  let comps_closed := IsClosed.biUnion Cs (fun c ↦ c.supp) (fun c _ ↦ c.isClosed_supp)
  rw[← Set.ncard_image_of_injective _ comps_closed.connectedComponent_map_induce_injective]
  apply Set.ncard_le_ncard _
  intro _ ⟨c, ⟨_, h⟩⟩
  obtain ⟨⟨v, vc⟩, rfl⟩ := c.nonempty_supp
  simp only [Set.mem_iUnion, exists_prop, ConnectedComponent.mem_supp_iff, exists_eq_right'] at vc
  rwa[← h, ConnectedComponent.map_mk]


lemma deficiency_remove_hall_violator_lt
  (T : Set S) (hT : T.ncard > (⋃ x ∈ T, G.connectedComponentsNeighbors x).ncard) :
  d G S < d G (S \ ↑T) := by
  classical
  let I := ⋃ x ∈ T, G.connectedComponentsNeighbors x
  let comps := ⋃ x ∈ I, x.supp
  let comps_closed := IsClosed.biUnion I (fun c ↦ c.supp) (fun c _ ↦ c.isClosed_supp)
  let compsST : Set ↑(S \ ↑T)ᶜ := Subtype.val ⁻¹' ↑compsᶜ

  have: Subtype.val '' compsST = Subtype.val '' compsᶜ := by
     simp[compsST]
     tauto_set

  have T_subset: ↑T ⊆ S := fun _ ⟨⟨_, xs⟩, ⟨_, hx⟩⟩ ↦ hx ▸ xs

  have he': ¬(∃ x ∈ (Subtype.val '' T), ∃ y ∈ compsᶜ, G.Adj x y) := by
    rintro ⟨x, ⟨x', ⟨hx, hx'⟩⟩, y, hy, xy⟩
    simp only [Set.mem_compl_iff, comps, Set.mem_iUnion, exists_prop, I] at hy
    apply hy
    --refine ⟨(G.induce Sᶜ).connectedComponentMk y, ⟨⟨x, ⟨hx, ⟨y, ⟨rfl, xy⟩⟩⟩⟩, rfl⟩⟩
    use ((G.induce Sᶜ).connectedComponentMk y)
    constructor
    · use x'
      exact ⟨hx, ⟨y, ⟨rfl, hx' ▸ xy⟩⟩⟩
    · rfl

  have compsST_closed : (G.induce (S \ T)ᶜ).IsClosed compsST := by
    have: Subtype.val '' T = (S \ T)ᶜ \ Sᶜ := by
      tauto_set

    exact IsClosed.induce_of_not_adj (comps_closed.compl) (this ▸ he')

  have: (G.induce (S \ ↑T)ᶜ).oddComponents.ncard ≥
        ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard := by
    let ψ := (G.induce_induce_iso compsᶜ).symm.comp <|
             (G.induce_congr this).comp <|
             (G.induce_induce_iso compsST)
    rw[← compsST_closed.oddComponents_ncard_add_compl_eq, Iso.oddComponents_ncard_eq ψ]
    linarith

  have S_diff_T_ncard: - ((S \ ↑T).ncard : ℤ) = -S.ncard + ↑T.ncard := by
    rw[Set.ncard_diff T_subset, Nat.cast_sub (Set.ncard_le_ncard T_subset),
       Set.ncard_image_of_injective _ Subtype.val_injective]
    linarith

  calc
    d G (S \ ↑T) = (G.induce (S \ ↑T)ᶜ).oddComponents.ncard - (S \ ↑T).ncard := rfl
    _ ≥ ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard - (S \ ↑T).ncard := by linarith[this]
    _ > (G.induce Sᶜ).oddComponents.ncard - S.ncard := by
        linarith[S_diff_T_ncard,
                 lt_of_le_of_lt ((G.induce Sᶜ).ncard_ge_induce_iUnion_oddComponents I) hT,
                 comps_closed.oddComponents_ncard_add_compl_eq]
    _ = d G S := rfl



open Subgraph
open Fintype

open Classical in
lemma exists_isPerfectMatching_iff_card_eq (h₀ : G.IsMatchableToComponents S)
  (h₁ : ∀ (C : (G.induce Sᶜ).ConnectedComponent), (G.induce Sᶜ).IsFactorCriticalArea C.supp) :
  card S = card (G.induce Sᶜ).ConnectedComponent ↔ ∃ M : Subgraph G, M.IsPerfectMatching := by
  obtain ⟨f, finj, hf⟩ := h₀
  choose c c_mem c_adj using hf
  choose M hM hM' using fun s ↦ (h₁ (f s)).2 (c s) (c_mem s)
  constructor
  · intro card_eq

    have fbij := (Fintype.bijective_iff_injective_and_card f).2 ⟨finj, card_eq⟩

    have hd: Pairwise fun s s' ↦ Disjoint (M s).support (M s').support := by
      intro s s' h
      rw[hM', hM']
      exact Disjoint.mono (by simp) (by simp) <|
            ((G.induce Sᶜ).pairwise_disjoint_supp_connectedComponent (finj.ne h))


    have cinj: Function.Injective c := by
      intro s s' h
      by_contra! ts
      have cinfs': c s ∈ (f s') := by rw[h]; exact c_mem s'
      exact ((G.induce Sᶜ).pairwise_disjoint_supp_connectedComponent (finj.ne ts)).le_bot <|
            ⟨c_mem s, cinfs'⟩

    have dj: Disjoint S Sᶜ := by rw[Set.disjoint_compl_right_iff_subset]


    obtain ⟨P, ⟨hP, hP'⟩⟩ := IsMatching.exists_of_disjoint_sets_of_injective c dj c_adj cinj
    let cM' := ⨆ s : S, (M s)
    let hcM' := Subgraph.IsMatching.iSup hM hd
    let hcM := hcM'.map (G.ι.toHom) (G.ι.injective)
    let cM := cM'.map G.ι.toHom

    have P_D_cM: Disjoint P.support cM.support := by
      rw[IsMatching.support_eq_verts, IsMatching.support_eq_verts, Set.disjoint_iff]
      · rintro x ⟨hl , ⟨⟨v, vc⟩, ⟨hC, hv⟩⟩⟩
        rcases hP ▸ hl with (hs | ⟨⟨y, yc⟩, ⟨⟨w, h⟩, hw⟩ ⟩)
        · rw[← hv] at hs
          exact vc hs
        rw[verts_iSup] at hC
        rcases hC with ⟨C, ⟨⟨s, hs'⟩, vC⟩⟩
        dsimp at hs'
        rw[← IsMatching.support_eq_verts, hM' s] at hs'
        · rw[← hs'] at vC
          have: G.ι.toHom ⟨v, vc⟩ = (⟨v, vc⟩ : ↑(Sᶜ)) := rfl
          rw[← hw, this, Subtype.val_inj] at hv
          rw[hv, ← h] at vC
          rcases vC with ⟨h1, h2⟩
          by_cases ws : w = s
          · rw[ws] at h2
            exact h2 rfl
          · exact ((G.induce Sᶜ).pairwise_disjoint_supp_connectedComponent (finj.ne ws)).le_bot <|
                  ⟨c_mem w, h1⟩
        exact hM s
      · exact hcM
      exact hP'

    let pMatch := P ⊔ cM

    have: pMatch.IsSpanning := by
      intro v
      rw[verts_sup]
      by_cases hv: v ∈ S
      · left
        rw[hP]
        exact Or.inl hv

      · have: ⟨v, hv⟩ ∈ (Set.univ : Set ↑(Sᶜ)) := by trivial
        rw[← (G.induce Sᶜ).iUnion_connectedComponentSupp] at this
        rcases this with ⟨Csupp, ⟨⟨C, rfl⟩, vC⟩⟩
        obtain ⟨s, hs⟩ := fbij.existsUnique C
        by_cases hv' : ⟨v, hv⟩ = (c s)
        · left
          rw[hP]
          right
          refine ⟨c s, ⟨Set.mem_range_self s, Subtype.val_inj.2 hv'.symm⟩⟩
        · right
          rw[map_verts, verts_iSup]
          refine ⟨⟨v, hv⟩, ⟨?_, rfl⟩⟩
          rw[Set.mem_iUnion]
          use s
          rw[← IsMatching.support_eq_verts <| hM s, hM' s, hs.1]
          exact ⟨vC, hv'⟩

    exact ⟨pMatch, ⟨IsMatching.sup hP' hcM P_D_cM, this⟩⟩

  intro h
  let nonviolator := tutte.1 h S


  have iso: G.induce Sᶜ ≃g ((⊤ : G.Subgraph).deleteVerts S).coe := by
    rw[deleteVerts, Subgraph.verts_top, ← Set.compl_eq_univ_diff, G.induce_eq_coe_induce_top Sᶜ]
    rfl

  have Sleq: S.ncard ≥ (G.induce Sᶜ).oddComponents.ncard := by -- ≤ wg. tutte
    by_contra!
    apply nonviolator
    rwa[IsTutteViolator, ← Iso.oddComponents_ncard_eq iso]

  have oddeq: card (induce Sᶜ G).ConnectedComponent = (induce Sᶜ G).oddComponents.ncard := by
    rw[Fintype.card_eq_nat_card, ← Nat.card_congr (Equiv.Set.univ _)]
    congr
    symm
    rw[Set.eq_univ_iff_forall]
    intro C
    exact IsFactorCriticalArea.odd_ncard (h₁ C)

  have Seq: card S = S.ncard := by rw[← Nat.card_coe_set_eq, Fintype.card_eq_nat_card]

  have Sgeq: S.ncard ≤ (G.induce Sᶜ).oddComponents.ncard := by -- ≥ wg. h₀
    rw[← Seq, ← oddeq]
    exact Fintype.card_le_of_injective f finj

  rw[Seq, oddeq, le_antisymm Sgeq Sleq]


lemma oddComponents_sub_ncard_le_two
  (h₀ : Even (Nat.card V)) (h₁ : S.ncard < (G.induce Sᶜ).oddComponents.ncard) :
  (G.induce Sᶜ).oddComponents.ncard - S.ncard ≥ 2 := by

  by_cases hS : Odd (S.ncard)
  · have: Odd (Nat.card ↑Sᶜ) := by
      rw[Nat.card_coe_set_eq, Set.odd_ncard_compl_iff]
      assumption'

    rcases (G.induce Sᶜ).odd_ncard_oddComponents.2 this with ⟨n₀, hn₀⟩
    rcases hS with ⟨n₁, hn₁⟩
    omega
  · have: ¬ Odd (Nat.card ↑Sᶜ) := by
      rw[Nat.not_odd_iff_even] at *
      rw[Nat.card_coe_set_eq, Set.even_ncard_compl_iff]
      assumption'

    rw[← (G.induce Sᶜ).odd_ncard_oddComponents] at this
    rcases Nat.not_odd_iff_even.1 this with ⟨n₀, hn₀⟩
    rcases Nat.not_odd_iff_even.1 hS with ⟨n₁, hn₁⟩
    omega



lemma ncard_oddComponents_induce_compl_eq_add
  {C : G.ConnectedComponent} (h : S ⊆ C.supp) :
  (G.induce Sᶜ).oddComponents.ncard = (G.induce C.suppᶜ).oddComponents.ncard +
                                      (G.induce (C.supp \ S)).oddComponents.ncard := by
  classical
  let C' : Set ↑Sᶜ := Subtype.val ⁻¹' C.supp
  have hc: ↑C' = C.supp \ S := by
    simp only [C', Set.diff_eq, Set.inter_comm, Subtype.image_preimage_coe]
  have hcc: (Subtype.val '' C'ᶜ) = C.suppᶜ := by
    simp only [C', Set.image_compl_preimage, Subtype.range_coe, Set.diff_eq,
    ← Set.compl_union, Set.union_eq_right.2 h]

  let ψ₀ := (G.induce_congr hc).comp <| G.induce_induce_iso C' -- G[Sᶜ][C] ≃g G[C \ S]
  let ψ₁ := (G.induce_congr hcc).comp <| G.induce_induce_iso C'ᶜ -- G[Sᶜ][Cᶜ] ≃g G[Cᶜ]
  rw[← IsClosed.oddComponents_ncard_add_compl_eq <|
     IsClosed.val_preimage_closed Sᶜ (ConnectedComponent.isClosed_supp C),
     Iso.oddComponents_ncard_eq ψ₀, Iso.oddComponents_ncard_eq ψ₁]
  ring


lemma ncard_oddComponents_induce_compl_eq_add'
  (h : S ⊆ T) (hT : G.IsClosed T) :
  (G.induce Sᶜ).oddComponents.ncard = (G.induce Tᶜ).oddComponents.ncard +
                                      (G.induce (T \ S)).oddComponents.ncard := by
  classical
  let T' : Set ↑Sᶜ := Subtype.val ⁻¹' T
  have hc: ↑T' = T \ S := by
    simp only [T', Set.diff_eq, Set.inter_comm, Subtype.image_preimage_coe]
  have hcc: (Subtype.val '' T'ᶜ) = Tᶜ := by
    simp only [T', Set.image_compl_preimage, Subtype.range_coe, Set.diff_eq,
    ← Set.compl_union, Set.union_eq_right.2 h]

  let ψ₀ := (G.induce_congr hc).comp <| G.induce_induce_iso T' -- G[Sᶜ][T] ≃g G[T \ S]
  let ψ₁ := (G.induce_congr hcc).comp <| G.induce_induce_iso T'ᶜ -- G[Sᶜ][Tᶜ] ≃g G[Tᶜ]
  rw[← IsClosed.oddComponents_ncard_add_compl_eq <|
     IsClosed.val_preimage_closed Sᶜ hT,
     Iso.oddComponents_ncard_eq ψ₀, Iso.oddComponents_ncard_eq ψ₁]
  ring

lemma odd_ncard_geq_one_oddComponents (G : SimpleGraph V) (h : Odd (card V)) :
  G.oddComponents.ncard ≥ 1 :=  by
  simp only [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
  apply Odd.pos
  rwa[odd_ncard_oddComponents, Nat.card_eq_fintype_card]


def IsEdmondsGallai (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ B : Set V, (d G S ≥ d G B) ∧ (d G S = d G B → S.ncard ≥ B.ncard)

lemma exists_isEdmondsGallai (G : SimpleGraph V) :
  ∃ (S : Set V) , G.IsEdmondsGallai S := by
  use G.edmonds_gallai_set
  intro B
  constructor
  · exact G.edmonds_gallai_is_maximal_d B
  · intro d_eq
    exact G.edmonds_gallai_is_maximal_card d_eq.symm


omit [Fintype V] in
lemma IsTutteViolator.lt_oddComponents_induce_compl (h : G.IsTutteViolator S) :
  (G.induce Sᶜ).oddComponents.ncard > S.ncard := by
  have iso: G.induce Sᶜ ≃g ((⊤ : G.Subgraph).deleteVerts S).coe := by
    rw[deleteVerts, Subgraph.verts_top, ← Set.compl_eq_univ_diff, G.induce_eq_coe_induce_top Sᶜ]
    rfl
  rwa[Iso.oddComponents_ncard_eq iso]


lemma IsEdmondsGallai.odd_ncard_supp (h : G.IsEdmondsGallai S) :
  ∀ C : (G.induce Sᶜ).ConnectedComponent, Odd C.supp.ncard := by
  classical
  intro C
  by_contra! h_even
  rw[Nat.not_odd_iff_even] at h_even
  obtain ⟨c, hC⟩ := C.nonempty_supp
  let T  := S ∪ {↑c}
  let C' := C.supp \ {c}

  have T_c : Tᶜ = Subtype.val '' {c}ᶜ := by simp[Set.diff_eq, ← Set.compl_union, T]

  have τ: (G.induce Sᶜ).induce {c}ᶜ ≃g G.induce Tᶜ :=
    (G.induce_congr T_c.symm).comp <| G.induce_induce_iso {c}ᶜ

  have T_ncard : T.ncard = S.ncard + 1 := by
    have: ↑c ∉ S := c.property
    rw[Set.ncard_union_eq (Set.disjoint_singleton_right.2 this), Set.ncard_singleton]

  have odd_C' : Odd (card C') := by
    rwa[Fintype.card_eq_nat_card, Nat.card_coe_set_eq, ← Nat.not_even_iff_odd,
       ← Nat.even_add_one, Set.ncard_diff_singleton_add_one hC]

  suffices d G S = d G T by linarith[(h T).2 this]

  apply le_antisymm ?_ (h T).1
  simp only [d, ← C.isClosed_supp.oddComponents_ncard_add_compl_eq,
             odd_comp_eq_zero_induce_even_comp C h_even, zero_add,
             ← Iso.oddComponents_ncard_eq τ,
             ncard_oddComponents_induce_compl_eq_add (Set.singleton_subset_iff.2 hC), T_ncard,
             Nat.cast_add, Nat.cast_one]

  linarith[((G.induce Sᶜ).induce C').odd_ncard_geq_one_oddComponents odd_C']


lemma IsEdmondsGallai.isFactorCriticalArea_supp (h : G.IsEdmondsGallai S) :
  ∀ C : (G.induce Sᶜ).ConnectedComponent, (G.induce Sᶜ).IsFactorCriticalArea C.supp := by
  classical
  intro C
  rw[IsFactorCriticalArea]
  by_contra! hC
  rcases hC C.nonempty_supp with ⟨c, hC⟩

  let P' := C.supp \ {c}

  have noP': ¬ ∃ M : ((G.induce Sᶜ).induce P').Subgraph, M.IsPerfectMatching := by
    rintro ⟨M, ⟨hM₀, hM₁⟩⟩
    let M' := M.map (G.induce Sᶜ).ι.toHom
    let hM' := hM₀.map (G.induce Sᶜ).ι.toHom (G.induce Sᶜ).ι.injective
    apply hC.2 M' hM'
    rw[IsMatching.support_eq_verts hM', map_verts, isSpanning_iff.1 hM₁]
    ext x; constructor
    · rintro ⟨⟨_, ha⟩, ⟨_, rfl⟩⟩
      exact ha
    · exact fun hx ↦ ⟨⟨x, hx⟩, ⟨Set.mem_univ (⟨x, hx⟩ : ↑P'), rfl⟩⟩

  have even_P' : Even (Nat.card P') := by
    rw[Nat.card_coe_set_eq, Set.ncard_diff_singleton_of_mem hC.1,
       ← Nat.not_odd_iff_even, ← Nat.odd_add_one, Nat.sub_add_cancel]
    · exact h.odd_ncard_supp C
    · apply Nat.one_le_of_lt
      rw[Set.ncard_pos]
      exact C.nonempty_supp


  have exists_tutte_violator := (Iff.not tutte).1 noP'
  push_neg at exists_tutte_violator
  rcases exists_tutte_violator with ⟨Q, hQ⟩

  let T := S ∪ ↑((Subtype.val '' Q) ∪ {c})
  let deficency := IsTutteViolator.lt_oddComponents_induce_compl hQ

  have Q_union_c_subset_C: ↑Q ∪ {c} ⊆ C.supp := by
    rw[Set.union_subset_iff]
    refine ⟨?_, Set.singleton_subset_iff.2 hC.1⟩
    apply Set.Subset.trans (Set.image_subset_range _ _)
    rw[Subtype.range_coe]
    exact Set.diff_subset

  have T_ncard : T.ncard = S.ncard + Q.ncard + 1 := by
    repeat rw[Set.ncard_union_eq, Set.ncard_image_of_injective _ Subtype.val_injective]
    · rw[Set.ncard_singleton, add_assoc]
    · apply Set.disjoint_of_subset_left (Set.image_subset_range _ _)
      rw[Subtype.range_coe]
      exact Set.disjoint_sdiff_left
    · exact Set.disjoint_right.2 fun _ ⟨⟨_, ha⟩ , ⟨_, rfl⟩⟩ ↦ ha

  have ψ: (G.induce Sᶜ).induce ((Subtype.val '' Q) ∪ {c})ᶜ ≃g G.induce Tᶜ := by
    have T_c : Subtype.val '' (Subtype.val '' Q ∪ {c})ᶜ = Tᶜ := by
      rw[Set.image_compl_eq_range_diff_image Subtype.val_injective, Subtype.range_coe,
        Set.compl_union, Set.diff_eq]
    exact (G.induce_congr T_c).comp <| G.induce_induce_iso (Subtype.val '' Q ∪ {c})ᶜ

  have Q_c: ↑Qᶜ = C.supp \ (↑Q ∪ {c}) := by
        simp only [P', Set.image_compl_eq_range_diff_image Subtype.val_injective,
          Subtype.range_coe, Set.diff_diff, Set.union_comm]

  let τ := ((G.induce Sᶜ).induce_congr Q_c).comp <| (G.induce Sᶜ).induce_induce_iso Qᶜ
  suffices d G S = d G T by linarith[(h T).2 this]
  apply le_antisymm ?_ (h T).1
  simp only [d, ← C.isClosed_supp.oddComponents_ncard_add_compl_eq,
            odd_comp_eq_one_induce_odd_comp C (h.odd_ncard_supp C), Nat.cast_add,
            Nat.cast_one, ← Iso.oddComponents_ncard_eq ψ,
            ncard_oddComponents_induce_compl_eq_add Q_union_c_subset_C,
            ← Iso.oddComponents_ncard_eq τ, T_ncard]
  ring_nf
  have htwo := oddComponents_sub_ncard_le_two even_P' deficency
  have htwo' : (2 : ℤ) ≤
      (((((G.induce Sᶜ).induce P').induce Qᶜ).oddComponents.ncard - Q.ncard : ℕ) : ℤ) := by
    exact_mod_cast htwo
  rw [Nat.cast_sub deficency.le] at htwo'
  linarith


theorem aux (G : SimpleGraph V) : ∃ (S : Set V),
  (G.IsMatchableToComponents S) ∧
  (∀ (C : (G.induce Sᶜ).ConnectedComponent), (G.induce Sᶜ).IsFactorCriticalArea C.supp) := by
  classical
  rcases G.exists_isEdmondsGallai with ⟨S, hS⟩
  refine ⟨S, ⟨?_, hS.isFactorCriticalArea_supp⟩⟩
  by_contra! h
  rcases not_matchable_exists_hall_violator h with ⟨T, hT⟩
  linarith[G.deficiency_remove_hall_violator_lt T hT, hS (S \ T)]

end SimpleGraph

#print axioms SimpleGraph.IsClosed.oddComponents_ncard_add_compl_eq
#print axioms SimpleGraph.exists_isPerfectMatching_iff_card_eq
#print axioms SimpleGraph.exists_isEdmondsGallai
#print axioms SimpleGraph.IsEdmondsGallai.isFactorCriticalArea_supp
#print axioms SimpleGraph.aux
#check SimpleGraph.exists_isPerfectMatching_iff_card_eq
#check SimpleGraph.exists_isEdmondsGallai
#check SimpleGraph.IsEdmondsGallai.isFactorCriticalArea_supp
#check SimpleGraph.aux
namespace GallaiEdmonds547Port

open SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The exact finite Gallai--Edmonds package used in Zhao's Section 6:
the separator is matched injectively into distinct components of its
complement, and every complementary component is factor-critical. -/
structure ZhaoGallaiEdmondsWitness where
  separator : Set W
  targetComponent : separator → (H.induce separatorᶜ).ConnectedComponent
  targetComponent_injective : Function.Injective targetComponent
  bridgeVertex : (s : separator) → (targetComponent s).supp
  bridge_adj : ∀ s : separator, H.Adj s.1 (bridgeVertex s).1.1
  component_factorCritical : ∀ C : (H.induce separatorᶜ).ConnectedComponent,
    (H.induce separatorᶜ).IsFactorCriticalArea C.supp

/-- The assumption-free finite Gallai--Edmonds decomposition, packaged in the
form directly consumed by Zhao's forest-matching argument. -/
theorem exists_zhaoGallaiEdmondsWitness :
    Nonempty (ZhaoGallaiEdmondsWitness H) := by
  classical
  obtain ⟨S, hmatch, hcritical⟩ := SimpleGraph.aux H
  obtain ⟨f, hf_inj, hf_adj⟩ := hmatch
  choose y hy_mem hy_adj using hf_adj
  exact ⟨{
    separator := S
    targetComponent := f
    targetComponent_injective := hf_inj
    bridgeVertex := fun s ↦ ⟨y s, hy_mem s⟩
    bridge_adj := hy_adj
    component_factorCritical := hcritical }⟩

theorem ZhaoGallaiEdmondsWitness.component_odd
    (Z : ZhaoGallaiEdmondsWitness H)
    (C : (H.induce Z.separatorᶜ).ConnectedComponent) :
    Odd C.supp.ncard := by
  classical
  exact (Z.component_factorCritical C).odd_ncard

/-- The near-perfect matching in the component targeted by a separator
vertex, chosen to miss precisely the endpoint of the bridge edge. -/
theorem ZhaoGallaiEdmondsWitness.nearPerfectAtBridge
    (Z : ZhaoGallaiEdmondsWitness H) (s : Z.separator) :
    ∃ M : (H.induce Z.separatorᶜ).Subgraph,
      M.IsMatching ∧
      M.support = (Z.targetComponent s).supp \ {(Z.bridgeVertex s).1} :=
  (Z.component_factorCritical (Z.targetComponent s)).2
    (Z.bridgeVertex s).1 (Z.bridgeVertex s).2

/-- Bridge endpoints are distinct because their target components are
distinct. -/
theorem ZhaoGallaiEdmondsWitness.bridgeVertex_injective
    (Z : ZhaoGallaiEdmondsWitness H) :
    Function.Injective (fun s : Z.separator ↦ (Z.bridgeVertex s).1.1) := by
  intro s t hst
  apply Z.targetComponent_injective
  apply ConnectedComponent.eq_of_common_vertex (v := (Z.bridgeVertex s).1)
  · exact (Z.bridgeVertex s).2
  · have hsub : (Z.bridgeVertex s).1 = (Z.bridgeVertex t).1 :=
      Subtype.ext hst
    rw [hsub]
    exact (Z.bridgeVertex t).2

/-- The bridge edges themselves form an ambient matching saturating the
separator. -/
theorem ZhaoGallaiEdmondsWitness.exists_bridgeMatching
    (Z : ZhaoGallaiEdmondsWitness H) :
    ∃ M : H.Subgraph,
      Z.separator ⊆ M.verts ∧ M.IsMatching := by
  classical
  let f : Z.separator → ↑(Z.separatorᶜ : Set W) :=
    fun s ↦ (Z.bridgeVertex s).1
  have hf : Function.Injective f := by
    intro s t hst
    apply Z.targetComponent_injective
    apply ConnectedComponent.eq_of_common_vertex (v := f s)
    · exact (Z.bridgeVertex s).2
    · have hval : (f s).1 = (f t).1 := congrArg Subtype.val hst
      have hsub : f s = f t := Subtype.ext hval
      rw [hsub]
      exact (Z.bridgeVertex t).2
  have hadj : ∀ s : Z.separator, H.Adj s (f s) := Z.bridge_adj
  obtain ⟨M, hverts, hmatching⟩ :=
    IsMatching.exists_of_disjoint_sets_of_injective f
      (by rw [Set.disjoint_compl_right_iff_subset]) hadj hf
  exact ⟨M, fun v hv ↦ hverts.symm ▸ Or.inl hv, hmatching⟩

end GallaiEdmonds547Port

#print axioms GallaiEdmonds547Port.exists_zhaoGallaiEdmondsWitness

import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Dynamic sequential embedding with route-local retirement

This file gives the finite combinatorial core of a sequential matching-cluster
embedding. Candidate pools may depend on the entire partial embedding, so a
caller may delete retired vertices, atypical vertices, rounded slice errors, and
vertices already used on the current route. The pool only has to beat the
current route load; it need not reserve the final size of the forest.

Arbitrary finite anchor families are supported at every source vertex, covering
pendant, internal, and two-ended shrubs once their endpoint obligations have
been put into the dynamic pool.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

/-- A finite parent forest has a not-yet-embedded vertex whose parent is already
embedded, provided ranks strictly decrease along parent links. -/
lemma exists_ready_vertex
    {α : Type*} [Fintype α] [DecidableEq α]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (S : Finset α) (hS : S ≠ univ) :
    ∃ a ∉ S, ∀ b, parent a = some b → b ∈ S := by
  have hnon : (univ \ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hS
    ext a
    have ha : a ∉ univ \ S := by simp [h]
    simpa using! ha
  obtain ⟨a, ha, hmin⟩ := (univ \ S).exists_min_image rank hnon
  refine ⟨a, (mem_sdiff.mp ha).2, ?_⟩
  intro b hab
  by_contra hb
  have hbu : b ∈ univ \ S := mem_sdiff.mpr ⟨mem_univ b, hb⟩
  exact (not_lt_of_ge (hmin b hbu)) (hrank a b hab)

/-- Generic dynamic extension engine. At every downward-closed partial
embedding, it is enough to supply one fresh legal image for every ready vertex.
The legal set can depend on the partial embedding. -/
theorem dynamic_sequential_embedding
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [Fintype α] [DecidableEq α]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (cand : α → Finset V) (anchors : α → Finset V)
    (hext : ∀ (S : Finset α) (f : α → V),
      (∀ a ∈ S, ∀ b, parent a = some b → b ∈ S) →
      Set.InjOn f S →
      (∀ a ∈ S, f a ∈ cand a) →
      (∀ a ∈ S, ∀ b, parent a = some b → G.Adj (f a) (f b)) →
      (∀ a ∈ S, ∀ z ∈ anchors a, G.Adj z (f a)) →
      ∀ a ∉ S, (∀ b, parent a = some b → b ∈ S) →
        ∃ v ∈ cand a, v ∉ S.image f ∧
          (∀ b, parent a = some b → G.Adj v (f b)) ∧
          (∀ z ∈ anchors a, G.Adj z v)) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ cand a) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) ∧
      (∀ a z, z ∈ anchors a → G.Adj z (f a)) := by
  let Good : Finset α → Prop := fun S =>
    (∀ a ∈ S, ∀ b, parent a = some b → b ∈ S) ∧
    ∃ f : α → V, Set.InjOn f S ∧
      (∀ a ∈ S, f a ∈ cand a) ∧
      (∀ a ∈ S, ∀ b, parent a = some b → G.Adj (f a) (f b)) ∧
      (∀ a ∈ S, ∀ z ∈ anchors a, G.Adj z (f a))
  have hzero : Good ∅ := by
    refine ⟨by simp, fun _ => Classical.arbitrary V, ?_⟩
    simp [Set.InjOn]
  let P : Finset (Finset α) := univ.filter Good
  have hP : P.Nonempty := ⟨∅, by simp [P, hzero]⟩
  obtain ⟨S, hSP, hmax⟩ := P.exists_max_image Finset.card hP
  have hgood : Good S := (mem_filter.mp hSP).2
  obtain ⟨hclosed, f, hinj, hmem, hadj, hanchor⟩ := hgood
  have hfull : S = univ := by
    by_contra hne
    obtain ⟨a, haS, hready⟩ := exists_ready_vertex parent rank hrank S hne
    obtain ⟨v, hvcand, hvfresh, hvpar, hvanchor⟩ :=
      hext S f hclosed hinj hmem hadj hanchor a haS hready
    let f' := Function.update f a v
    have hnew : Good (insert a S) := by
      refine ⟨?_, f', ?_, ?_, ?_, ?_⟩
      · intro x hx b hxb
        rcases mem_insert.mp hx with rfl | hxS
        · exact mem_insert_of_mem (hready b hxb)
        · exact mem_insert_of_mem (hclosed x hxS b hxb)
      · intro x hx y hy hxy
        rcases mem_insert.mp hx with rfl | hxS <;>
          rcases mem_insert.mp hy with rfl | hyS
        · rfl
        · simp only [f', Function.update_self,
              Function.update_apply, (ne_of_mem_of_not_mem hyS haS)] at hxy
          exact False.elim (hvfresh (mem_image.mpr ⟨y, hyS, hxy.symm⟩))
        · simp only [f', Function.update_self,
              Function.update_apply, (ne_of_mem_of_not_mem hxS haS)] at hxy
          exact False.elim (hvfresh (mem_image.mpr ⟨x, hxS, hxy⟩))
        · apply hinj hxS hyS
          simpa [f', Function.update_apply, (ne_of_mem_of_not_mem hxS haS),
            Function.update_apply, (ne_of_mem_of_not_mem hyS haS)] using! hxy
      · intro x hx
        rcases mem_insert.mp hx with rfl | hxS
        · simpa [f'] using! hvcand
        · simpa [f', Function.update_apply, (ne_of_mem_of_not_mem hxS haS)] using! hmem x hxS
      · intro x hx b hxb
        rcases mem_insert.mp hx with rfl | hxS
        · have hbS := hready b hxb
          simpa [f', Function.update_apply, (ne_of_mem_of_not_mem hbS haS)] using! hvpar b hxb
        · have hbS := hclosed x hxS b hxb
          simpa [f', Function.update_apply, (ne_of_mem_of_not_mem hxS haS),
            Function.update_apply, (ne_of_mem_of_not_mem hbS haS)] using! hadj x hxS b hxb
      · intro x hx z hz
        rcases mem_insert.mp hx with rfl | hxS
        · simpa [f'] using! hvanchor z hz
        · simpa [f', Function.update_apply, (ne_of_mem_of_not_mem hxS haS)] using!
            hanchor x hxS z hz
    have hnewP : insert a S ∈ P := by simp [P, hnew]
    have := hmax (insert a S) hnewP
    simp [card_insert_of_notMem haS] at this
  subst S
  exact ⟨f, fun _ _ h => hinj (mem_univ _) (mem_univ _) h,
    fun a => hmem a (mem_univ a), fun a b h => hadj a (mem_univ a) b h,
    fun a z h => hanchor a (mem_univ a) z h⟩

/-- Route-local cardinal form of the dynamic engine. The pool can already have
retired, atypical and rounded-away vertices deleted. Its cardinality only needs
to exceed the number of vertices previously used on the same route. Disjoint
route domains make vertices used on other routes irrelevant. -/
theorem dynamic_routed_anchored_embedding
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {α κ : Type*} [Fintype α] [DecidableEq α] [DecidableEq κ]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (route : α → κ)
    (domain : κ → Finset V)
    (hdisj : ∀ k l, k ≠ l → Disjoint (domain k) (domain l))
    (cand : α → Finset V) (hcand_domain : ∀ a, cand a ⊆ domain (route a))
    (anchors : α → Finset V)
    (pool : Finset α → (α → V) → α → Finset V)
    (hpool_cand : ∀ S f a, pool S f a ⊆ cand a)
    (hpool_parent : ∀ S f a v, v ∈ pool S f a →
      ∀ b, parent a = some b → G.Adj v (f b))
    (hpool_anchor : ∀ S f a v, v ∈ pool S f a →
      ∀ z ∈ anchors a, G.Adj z v)
    (hpool_large : ∀ (S : Finset α) (f : α → V),
      (∀ x ∈ S, f x ∈ cand x) → Set.InjOn f S →
      ∀ a ∉ S, (∀ b, parent a = some b → b ∈ S) →
        (S.filter (fun x => route x = route a)).card < (pool S f a).card) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ cand a) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) ∧
      (∀ a z, z ∈ anchors a → G.Adj z (f a)) := by
  apply dynamic_sequential_embedding G parent rank hrank cand anchors
  intro S f hclosed hinj hmem hadj hanchor a haS hready
  have hinter : (S.image f ∩ pool S f a).card ≤
      (S.filter (fun x => route x = route a)).card := by
    calc
      (S.image f ∩ pool S f a).card ≤
          ((S.filter (fun x => route x = route a)).image f).card := by
        apply card_le_card
        intro v hv
        obtain ⟨hvimg, hvpool⟩ := mem_inter.mp hv
        obtain ⟨x, hxS, rfl⟩ := mem_image.mp hvimg
        apply mem_image.mpr
        refine ⟨x, mem_filter.mpr ⟨hxS, ?_⟩, rfl⟩
        by_contra hrouteNe
        have hfx : f x ∈ domain (route x) := hcand_domain x (hmem x hxS)
        have hfpool : f x ∈ domain (route a) :=
          hcand_domain a (hpool_cand S f a hvpool)
        exact Finset.disjoint_left.mp (hdisj (route x) (route a) hrouteNe) hfx hfpool
      _ ≤ (S.filter (fun x => route x = route a)).card := card_image_le
  have hcard : (S.image f ∩ pool S f a).card < (pool S f a).card :=
    hinter.trans_lt (hpool_large S f hmem hinj a haS hready)
  obtain ⟨v, hvpool, hvfresh⟩ : ∃ v ∈ pool S f a, v ∉ S.image f := by
    by_contra h
    push_neg at h
    have hsub : pool S f a ⊆ S.image f := fun v hv => h v hv
    have : S.image f ∩ pool S f a = pool S f a := inter_eq_right.mpr hsub
    rw [this] at hcard
    exact (lt_irrefl _ hcard)
  exact ⟨v, hpool_cand S f a hvpool, hvfresh,
    hpool_parent S f a v hvpool, hpool_anchor S f a v hvpool⟩


/-! ## Explicit slicing and loss instantiation -/

/-- Vertices unavailable at a dynamic step. -/
def dynamicExcluded {α V : Type*} [DecidableEq V]
    (retired atypical rounding : Finset α → (α → V) → α → Finset V)
    (S : Finset α) (f : α → V) (a : α) : Finset V :=
  retired S f a ∪ atypical S f a ∪ rounding S f a

/-- Vertices satisfying the slice, current-parent, and endpoint-anchor
conditions before retirement and error deletions. -/
noncomputable def dynamicEligiblePool
    {α V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (parent : α → Option α)
    (slice : α → Finset V) (anchors : α → Finset V)
    (f : α → V) (a : α) : Finset V :=
  ((slice a).filter fun v => ∀ b, parent a = some b → G.Adj v (f b)).filter
    (fun v => ∀ z ∈ anchors a, G.Adj z v)

/-- The exact legal pool after slicing and all three losses. -/
noncomputable def dynamicLegalPool
    {α V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (parent : α → Option α)
    (slice : α → Finset V) (anchors : α → Finset V)
    (retired atypical rounding : Finset α → (α → V) → α → Finset V)
    (S : Finset α) (f : α → V) (a : α) : Finset V :=
  dynamicEligiblePool G parent slice anchors f a \
    dynamicExcluded retired atypical rounding S f a

lemma dynamicLegalPool_subset_slice
    {α V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (parent : α → Option α)
    (slice : α → Finset V) (anchors : α → Finset V)
    (retired atypical rounding : Finset α → (α → V) → α → Finset V)
    (S : Finset α) (f : α → V) (a : α) :
    dynamicLegalPool G parent slice anchors retired atypical rounding S f a ⊆ slice a := by
  exact fun _ h => (mem_sdiff.mp h).1 |> mem_filter.mp |>.1 |> mem_filter.mp |>.1

lemma dynamicLegalPool_parent
    {α V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (parent : α → Option α)
    (slice : α → Finset V) (anchors : α → Finset V)
    (retired atypical rounding : Finset α → (α → V) → α → Finset V)
    (S : Finset α) (f : α → V) (a : α) {v : V}
    (hv : v ∈ dynamicLegalPool G parent slice anchors retired atypical rounding S f a) :
    ∀ b, parent a = some b → G.Adj v (f b) := by
  exact (mem_filter.mp (mem_filter.mp (mem_sdiff.mp hv).1).1).2

lemma dynamicLegalPool_anchor
    {α V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (parent : α → Option α)
    (slice : α → Finset V) (anchors : α → Finset V)
    (retired atypical rounding : Finset α → (α → V) → α → Finset V)
    (S : Finset α) (f : α → V) (a : α) {v : V}
    (hv : v ∈ dynamicLegalPool G parent slice anchors retired atypical rounding S f a) :
    ∀ z ∈ anchors a, G.Adj z v := by
  exact (mem_filter.mp (mem_sdiff.mp hv).1).2

/-- The three named losses have at most the sum of their separate sizes. -/
lemma dynamicExcluded_card_le
    {α V : Type*} [DecidableEq V]
    (retired atypical rounding : Finset α → (α → V) → α → Finset V)
    (S : Finset α) (f : α → V) (a : α) :
    (dynamicExcluded retired atypical rounding S f a).card ≤
      (retired S f a).card + (atypical S f a).card + (rounding S f a).card := by
  unfold dynamicExcluded
  calc
    #(retired S f a ∪ atypical S f a ∪ rounding S f a) ≤
        #(retired S f a ∪ atypical S f a) + #(rounding S f a) := card_union_le _ _
    _ ≤ ((retired S f a).card + (atypical S f a).card) +
        (rounding S f a).card := Nat.add_le_add_right (card_union_le _ _) _
    _ = _ := by omega

/-- Separate retirement, atypicality, and rounding estimates imply a lower
bound for the exact legal pool. -/
lemma dynamicLegalPool_card_lower
    {α V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (parent : α → Option α)
    (slice : α → Finset V) (anchors : α → Finset V)
    (retired atypical rounding : Finset α → (α → V) → α → Finset V)
    (S : Finset α) (f : α → V) (a : α)
    (r t u : ℕ)
    (hr : (retired S f a).card ≤ r)
    (ht : (atypical S f a).card ≤ t)
    (hu : (rounding S f a).card ≤ u) :
    (dynamicEligiblePool G parent slice anchors f a).card ≤
      (dynamicLegalPool G parent slice anchors retired atypical rounding S f a).card + r + t + u := by
  have hsplit : (dynamicEligiblePool G parent slice anchors f a).card ≤
      (dynamicEligiblePool G parent slice anchors f a \
        dynamicExcluded retired atypical rounding S f a).card +
      (dynamicExcluded retired atypical rounding S f a).card :=
    Finset.card_le_card_sdiff_add_card
  have hex := dynamicExcluded_card_le retired atypical rounding S f a
  dsimp [dynamicLegalPool]
  omega

/-- **Dynamic near-capacity shrub engine.**  The source forest may contain
routed internal or two-ended shrubs: endpoint obligations are simply members of
`anchors a`.  Matching-cluster slices are `slice`; retirement, atypicality and
rounding are instantiated by the three deletion families.  The sole local room
hypothesis concerns the resulting exact pool and the *current* same-route load.
Thus a route can ultimately be filled near capacity as long as every sequential
step retains one legal vertex. -/
theorem dynamic_matching_shrub_embedding
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {α κ : Type*} [Fintype α] [DecidableEq α] [DecidableEq κ]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (route : α → κ)
    (domain : κ → Finset V)
    (hdisj : ∀ k l, k ≠ l → Disjoint (domain k) (domain l))
    (slice : α → Finset V) (hslice : ∀ a, slice a ⊆ domain (route a))
    (anchors : α → Finset V)
    (retired atypical rounding : Finset α → (α → V) → α → Finset V)
    (hroom : ∀ (S : Finset α) (f : α → V),
      (∀ x ∈ S, f x ∈ slice x) → Set.InjOn f S →
      ∀ a ∉ S, (∀ b, parent a = some b → b ∈ S) →
        (S.filter (fun x => route x = route a)).card <
          (dynamicLegalPool G parent slice anchors retired atypical rounding S f a).card) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ slice a) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) ∧
      (∀ a z, z ∈ anchors a → G.Adj z (f a)) := by
  apply dynamic_routed_anchored_embedding G parent rank hrank route domain hdisj
      slice hslice anchors
      (dynamicLegalPool G parent slice anchors retired atypical rounding)
  · exact dynamicLegalPool_subset_slice G parent slice anchors retired atypical rounding
  · intro S f a v hv
    exact dynamicLegalPool_parent G parent slice anchors retired atypical rounding S f a hv
  · intro S f a v hv
    exact dynamicLegalPool_anchor G parent slice anchors retired atypical rounding S f a hv
  · exact hroom



/-- Graph-containment packaging of the dynamic shrub engine.  Any source graph
whose edges are classified by the parent forest is embedded in the host. -/
theorem dynamic_matching_shrub_graph_embedding
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {α κ : Type*} [Fintype α] [DecidableEq α] [DecidableEq κ]
    (T : SimpleGraph α)
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hedge : ∀ a b, T.Adj a b → parent a = some b ∨ parent b = some a)
    (route : α → κ)
    (domain : κ → Finset V)
    (hdisj : ∀ k l, k ≠ l → Disjoint (domain k) (domain l))
    (slice : α → Finset V) (hslice : ∀ a, slice a ⊆ domain (route a))
    (anchors : α → Finset V)
    (retired atypical rounding : Finset α → (α → V) → α → Finset V)
    (hroom : ∀ (S : Finset α) (f : α → V),
      (∀ x ∈ S, f x ∈ slice x) → Set.InjOn f S →
      ∀ a ∉ S, (∀ b, parent a = some b → b ∈ S) →
        (S.filter (fun x => route x = route a)).card <
          (dynamicLegalPool G parent slice anchors retired atypical rounding S f a).card) :
    T ⊑ G := by
  obtain ⟨f, hinj, _, hparent, _⟩ :=
    dynamic_matching_shrub_embedding G parent rank hrank route domain hdisj
      slice hslice anchors retired atypical rounding hroom
  refine ⟨SimpleGraph.Copy.mk (RelHom.mk f ?_) hinj⟩
  intro a b hab
  rcases hedge a b hab with h | h
  · exact hparent a b h
  · exact (hparent b a h).symm

/-- A directly instantiable form of the dynamic engine.  The pre-deletion
eligible pool pays separately for retirement, atypicality, and rounding, plus
one fresh vertex beyond the current route load. -/
theorem dynamic_matching_shrub_embedding_of_loss_bounds
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {α κ : Type*} [Fintype α] [DecidableEq α] [DecidableEq κ]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (route : α → κ)
    (domain : κ → Finset V)
    (hdisj : ∀ k l, k ≠ l → Disjoint (domain k) (domain l))
    (slice : α → Finset V) (hslice : ∀ a, slice a ⊆ domain (route a))
    (anchors : α → Finset V)
    (retired atypical rounding : Finset α → (α → V) → α → Finset V)
    (retireCap atypicalCap roundingCap : ℕ)
    (hretired : ∀ S f a, (retired S f a).card ≤ retireCap)
    (hatypical : ∀ S f a, (atypical S f a).card ≤ atypicalCap)
    (hrounding : ∀ S f a, (rounding S f a).card ≤ roundingCap)
    (heligible : ∀ (S : Finset α) (f : α → V),
      (∀ x ∈ S, f x ∈ slice x) → Set.InjOn f S →
      ∀ a ∉ S, (∀ b, parent a = some b → b ∈ S) →
        (S.filter (fun x => route x = route a)).card +
            retireCap + atypicalCap + roundingCap + 1 ≤
          (dynamicEligiblePool G parent slice anchors f a).card) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ slice a) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) ∧
      (∀ a z, z ∈ anchors a → G.Adj z (f a)) := by
  apply dynamic_matching_shrub_embedding G parent rank hrank route domain hdisj
      slice hslice anchors retired atypical rounding
  intro S f hmem hinj a ha hready
  have hlower := dynamicLegalPool_card_lower G parent slice anchors
    retired atypical rounding S f a retireCap atypicalCap roundingCap
    (hretired S f a) (hatypical S f a) (hrounding S f a)
  have helig := heligible S f hmem hinj a ha hready
  omega

end Erdos550

import ErdosProblems.Erdos118.ConservativeRuns
import ErdosProblems.Erdos118.ConservativeAlphabet
import Mathlib.Data.Set.Finite.List

/-!
Finitely many actual decision states use a fixed finite coordinate support.
Finite-support fusion then dominates the actual conservative guards, with
an explicit bound on the command. This is not yet a realization of runs.
-/

namespace Erdos118.FiniteGuards

open LabelledExtensions LabelledFrames DecisionStates AdaptiveGame ConservativeRuns

private def listsOn (s : Finset ℕ) : Set (List ℕ) :=
  {l | l.Pairwise (· < ·) ∧ ∀ x ∈ l, x ∈ s}

private theorem listsOn_finite (s : Finset ℕ) : (listsOn s).Finite := by
  classical
  have hi : Set.InjOn List.toFinset (listsOn s) := by
    intro l hl m hm he
    exact hl.1.eq_of_mem_iff hm.1 (fun x ↦ by
      simpa only [List.mem_toFinset] using
        (show x ∈ l.toFinset ↔ x ∈ m.toFinset by rw [he]))
  apply Set.Finite.of_finite_image (f := List.toFinset) _ hi
  apply s.powerset.finite_toSet.subset
  rintro _ ⟨l, hl, rfl⟩
  exact Finset.mem_powerset.mpr (fun x hx ↦ hl.2 x (List.mem_toFinset.mp hx))

private theorem finite_bounded_lists {α : Type*} {A : Set α} (hA : A.Finite) (n : ℕ) :
    {l : List α | l.length ≤ n ∧ ∀ x ∈ l, x ∈ A}.Finite := by
  have := hA.to_subtype
  apply ((List.finite_length_le A n).image (List.map Subtype.val)).subset
  intro l hl
  let m : List A := l.pmap (fun x hx ↦ ⟨x, hx⟩) hl.2
  refine ⟨m, ?_, ?_⟩
  · simpa [m] using hl.1
  · simp only [m, List.map_pmap, List.pmap_eq_map, List.map_id_fun']
    rfl

private theorem finite_by_fields {α β : Type*} (f : α → β) (hf : Function.Injective f)
    {A : Set α} {D : Set β} (hD : D.Finite) (h : ∀ a ∈ A, f a ∈ D) : A.Finite :=
  (Set.Finite.preimage hf.injOn hD).subset h

private def bodiesOn (s : Finset ℕ) : Set Body :=
  {a | a.decorated.Pairwise (· < ·) ∧ ∀ x ∈ a.decorated, x ∈ s}

private theorem bodiesOn_finite (s : Finset ℕ) : (bodiesOn s).Finite := by
  apply finite_by_fields (fun a : Body ↦ (a.values, a.label))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq, Body.mk.injEq] using h)
    ((listsOn_finite s).prod (listsOn_finite s))
  intro a ha
  have hp := List.pairwise_append.mp ha.1
  have hv : a.values.Sublist a.decorated :=
    (List.sublist_cons_self _ _).trans (List.sublist_append_right _ _)
  have hl : a.label.Sublist a.decorated := List.sublist_append_left _ _
  exact ⟨⟨ha.1.sublist hv, fun x hx ↦ ha.2 x (hv.subset hx)⟩,
    ⟨hp.1, fun x hx ↦ ha.2 x (hl.subset hx)⟩⟩

private def stemsOn (s : Finset ℕ) : Set Stem := {S | ∀ x ∈ S.decorated, x ∈ s}

private theorem stemsOn_finite (s : Finset ℕ) : (stemsOn s).Finite := by
  let ds := {l : List Body | l.length ≤ s.sup id ∧ ∀ a ∈ l, a ∈ bodiesOn s}
  have hds : ds.Finite := finite_bounded_lists (bodiesOn_finite s) (s.sup id)
  apply finite_by_fields (fun S : Stem ↦ (S.root, S.rootLabel, S.done))
    (by intro S T h; cases S; cases T; simpa only [Prod.mk.injEq, Stem.mk.injEq] using h)
    (s.finite_toSet.prod ((listsOn_finite s).prod hds))
  intro S hS
  have hr : S.root ∈ s := hS _ (by simp [Stem.decorated])
  have hroot : S.root ≤ s.sup id := Finset.le_sup (f := id) hr
  refine ⟨hr, ⟨S.label_pairwise, fun x hx ↦ hS x (by simp [Stem.decorated, hx])⟩,
    S.count.trans hroot, ?_⟩
  intro a ha
  have hflat := (List.pairwise_cons.mp (List.pairwise_append.mp S.increasing).2.1).2
  refine ⟨(List.pairwise_flatMap.mp hflat).1 a ha, ?_⟩
  intro x hx
  exact hS x (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨a, ha, hx⟩))))

private def positionsOn (s : Finset ℕ) : Set Position :=
  {P | ∀ x ∈ P.decorated, x ∈ s}

private theorem positionsOn_finite (s : Finset ℕ) : (positionsOn s).Finite := by
  apply finite_by_fields (fun P : Position ↦ (P.stem, P.size, P.label, P.entries))
    (by intro P Q h; cases P; cases Q;
        simpa only [Prod.mk.injEq, Position.mk.injEq] using h)
    ((stemsOn_finite s).prod (s.finite_toSet.prod
      ((listsOn_finite s).prod (listsOn_finite s))))
  intro P hP
  have hstem : P.stem.decorated.Sublist P.decorated := List.sublist_append_left _ _
  have htail : (P.label ++ P.size :: P.entries).Sublist P.decorated :=
    List.sublist_append_right _ _
  have hlabel : P.label.Sublist P.decorated := (List.sublist_append_left _ _).trans htail
  have hentries : P.entries.Sublist P.decorated :=
    ((List.sublist_cons_self _ _).trans (List.sublist_append_right _ _)).trans htail
  exact ⟨(fun x hx ↦ hP x (hstem.subset hx)),
    hP _ (by simp [Position.decorated]),
    ⟨P.label_pairwise, fun x hx ↦ hP x (hlabel.subset hx)⟩,
    ⟨P.increasing.sublist hentries, fun x hx ↦ hP x (hentries.subset hx)⟩⟩

private theorem pendingOn_finite (s : Finset ℕ) :
    {P : Pending | ∀ x ∈ P.position.decorated, x ∈ s}.Finite := by
  apply finite_by_fields (fun P : Pending ↦ (P.position, P.roots, P.leaves))
    (by intro P Q h; cases P; cases Q;
        simpa only [Prod.mk.injEq, Pending.mk.injEq] using h)
    ((positionsOn_finite s).prod ((listsOn_finite s).prod (listsOn_finite s)))
  intro P hP
  refine ⟨hP, ⟨P.rootSlots.increasing, ?_⟩, ⟨P.leafSlots.increasing, ?_⟩⟩
  · intro x hx
    have hm := (P.rootSlots.bounded x hx).2.2
    exact hP x (by simp [Position.decorated, Stem.decorated, hm])
  · intro x hx
    have hm := (P.leafSlots.bounded x hx).2.2
    exact hP x (by simp [Position.decorated, hm])

private theorem bodyOn_finite (s : Finset ℕ) :
    {D : BodyDecision | ∀ x ∈ D.stem.decorated, x ∈ s}.Finite := by
  apply finite_by_fields (fun D : BodyDecision ↦ (D.stem, D.roots))
    (by intro D E h; cases D; cases E;
        simpa only [Prod.mk.injEq, BodyDecision.mk.injEq] using h)
    ((stemsOn_finite s).prod (listsOn_finite s))
  intro D hD
  refine ⟨hD, D.rootSlots.increasing, ?_⟩
  intro x hx
  have hm := (D.rootSlots.bounded x hx).2.2
  exact hD x (by simp [Stem.decorated, hm])

private theorem completedOn_finite (s : Finset ℕ) :
    {T : Completed | ∀ x ∈ T.stem.decorated, x ∈ s}.Finite := by
  exact finite_by_fields Completed.stem
    (by intro T U h; cases T; cases U; cases h; rfl) (stemsOn_finite s)
    (fun _ h ↦ h)

/-- This includes all legal unused-slot lists, not just exact or reachable states. -/
theorem statesOn_finite (s : Finset ℕ) :
    {S : State | ∀ x ∈ S.decorated, x ∈ s}.Finite := by
  have h := (((Set.finite_singleton State.initial).union
    ((bodyOn_finite s).image State.body)).union
    ((pendingOn_finite s).image State.leaf)).union
    ((completedOn_finite s).image State.complete)
  apply h.subset
  intro S hS
  cases S with
  | initial => exact Or.inl (Or.inl (Or.inl rfl))
  | body D => exact Or.inl (Or.inl (Or.inr ⟨D, hS, rfl⟩))
  | leaf P => exact Or.inl (Or.inr ⟨P, hS, rfl⟩)
  | complete T => exact Or.inr ⟨T, hS, rfl⟩

private noncomputable def requests (s : Finset ℕ) : Finset ((State × State) × ℕ) := by
  classical
  exact (((statesOn_finite s).toFinset).product
    ((statesOn_finite s).toFinset)).product (Finset.range (s.sup id + 1))

noncomputable def envelope (H : Set ℕ) (payoff : Completed → Completed → Bool)
    (s : Finset ℕ) : ℕ :=
  (requests s).sup fun a ↦ max (pairBound a.1)
    (max (leftGuard H payoff a.1 a.2) (rightGuard H payoff a.1 a.2))

theorem envelope_bounds (H : Set ℕ) (payoff : Completed → Completed → Bool)
    (s : Finset ℕ) (S : State × State) (n : ℕ)
    (hleft : ∀ x ∈ S.1.decorated, x ∈ s) (hright : ∀ x ∈ S.2.decorated, x ∈ s)
    (hn : n ≤ s.sup id) :
    pairBound S ≤ envelope H payoff s ∧ leftGuard H payoff S n ≤ envelope H payoff s ∧
      rightGuard H payoff S n ≤ envelope H payoff s := by
  classical
  have hm : (S, n) ∈ requests s := by
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨(statesOn_finite s).mem_toFinset.mpr hleft,
        (statesOn_finite s).mem_toFinset.mpr hright⟩,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hn)⟩
  have hmax : max (pairBound S) (max (leftGuard H payoff S n) (rightGuard H payoff S n)) ≤
      envelope H payoff s := Finset.le_sup (f := fun a : (State × State) × ℕ ↦
        max (pairBound a.1) (max (leftGuard H payoff a.1 a.2)
          (rightGuard H payoff a.1 a.2))) hm
  exact ⟨(le_max_left _ _).trans hmax,
    ((le_max_left _ _).trans (le_max_right _ _)).trans hmax,
    ((le_max_right _ _).trans (le_max_right _ _)).trans hmax⟩

/-- The alphabet used to define the guards stays H throughout the thinning. -/
theorem exists_alphabet (H : Set ℕ) (payoff : Completed → Completed → Bool)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ K ⊆ N, K.Infinite ∧ ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ K →
      ∀ S : State × State, (∀ x ∈ S.1.decorated, x ∈ s) →
      (∀ x ∈ S.2.decorated, x ∈ s) → ∀ n : ℕ, n ≤ s.sup id →
      ∀ x ∈ K, (∀ y ∈ s, y < x) → pairBound S < x ∧
        leftGuard H payoff S n < x ∧ rightGuard H payoff S n < x := by
  obtain ⟨K, hKN, hK, hb⟩ := ConservativeAlphabet.exists_alphabet (envelope H payoff) hN
  refine ⟨K, hKN, hK, ?_⟩
  intro s hs S hleft hright n hn x hx hlt
  have h := hb s hs x hx hlt
  have he := envelope_bounds H payoff s S n hleft hright hn
  exact ⟨he.1.trans_lt h, he.2.1.trans_lt h, he.2.2.trans_lt h⟩

def Sparse (H K : Set ℕ) (payoff : Completed → Completed → Bool) : Prop :=
    ∀ S : State × State,
      (∀ x ∈ S.1.decorated, x ∈ K) → (∀ x ∈ S.2.decorated, x ∈ K) →
      ∀ n q : ℕ, q ∈ K → n ≤ q → ∀ x ∈ K, q < x →
      (∀ y ∈ S.1.decorated, y < x) → (∀ y ∈ S.2.decorated, y < x) →
      pairBound S < x ∧ leftGuard H payoff S n < x ∧ rightGuard H payoff S n < x

/-- A previously chosen coordinate can bound the command without becoming
part of either word. The response must lie after this anchor as well. -/
theorem exists_anchored_alphabet (H : Set ℕ) (payoff : Completed → Completed → Bool)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ K ⊆ N, K.Infinite ∧ Sparse H K payoff := by
  classical
  obtain ⟨K, hKN, hK, hb⟩ := exists_alphabet H payoff hN
  refine ⟨K, hKN, hK, ?_⟩
  intro S hleft hright n q hq hn x hx hqx hxl hxr
  let s : Finset ℕ := insert q (S.1.decorated.toFinset ∪ S.2.decorated.toFinset)
  have hqmem : q ∈ s := Finset.mem_insert_self _ _
  have hlmem : ∀ y ∈ S.1.decorated, y ∈ s := by
    intro y hy
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (List.mem_toFinset.mpr hy))
  have hrmem : ∀ y ∈ S.2.decorated, y ∈ s := by
    intro y hy
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (List.mem_toFinset.mpr hy))
  apply hb s (by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hq
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact hleft y (List.mem_toFinset.mp hy)
      · exact hright y (List.mem_toFinset.mp hy)) S hlmem hrmem n
      (hn.trans (Finset.le_sup (f := id) hqmem)) x hx
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact hqx
  · rcases Finset.mem_union.mp hy with hy | hy
    · exact hxl y (List.mem_toFinset.mp hy)
    · exact hxr y (List.mem_toFinset.mp hy)

theorem Sparse.mono {H K L : Set ℕ} {payoff : Completed → Completed → Bool}
    (h : Sparse H K payoff) (hLK : L ⊆ K) : Sparse H L payoff := by
  intro S hl hr n q hq hn x hx hqx hxl hxr
  exact h S (fun z hz ↦ hLK (hl z hz)) (fun z hz ↦ hLK (hr z hz))
    n q (hLK hq) hn x (hLK hx) hqx hxl hxr

theorem exists_graph_alphabet {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph Negative.Exact.G) :
    ∃ K ⊆ H, K.Infinite ∧ Sparse H K (GraphPayoff.payoff B .inside) ∧
      Sparse H K (GraphPayoff.payoff B .outside) := by
  obtain ⟨K, hKH, hK, hin⟩ := exists_anchored_alphabet H (GraphPayoff.payoff B .inside) hH
  obtain ⟨L, hLK, hL, hout⟩ := exists_anchored_alphabet H (GraphPayoff.payoff B .outside) hK
  exact ⟨L, hLK.trans hKH, hL, hin.mono hLK, hout⟩

end Erdos118.FiniteGuards

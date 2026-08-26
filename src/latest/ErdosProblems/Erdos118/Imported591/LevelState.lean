import ErdosProblems.Erdos118.Imported591.PartialSequence

open Set Ordinal

namespace Erdos118.Negative.Exact.Levels

/-! The state of one side of the alternating pair: an extracted level,
a fixed body length, and a maximal prefix inside that body family. -/

structure State (W : Set G) (m r k : ℕ) where
  outer : List (List ℕ)
  size : ℕ
  body : List ℕ
  maximal : BodyPrefix.Maximal
    (InnerLevels.RawFiber (Level W outer) size) body k
  root : ∀ x ∈ W, x.1.length = m
  retained : ∀ a ∈ Level W outer, continuationBound r ≤ typeLT (Child W outer a)

def State.fragment {W : Set G} {m r k : ℕ} (s : State W m r k) : List TaggedCoord :=
  partialSequence m s.outer s.size s.body

theorem State.fragment_ne_nil {W : Set G} {m r k : ℕ} (s : State W m r k) :
    s.fragment ≠ [] := partialSequence_ne_nil _ _ _ _

theorem State.fragment_hasBox {W : Set G} {m r k : ℕ} (s : State W m r k) :
    HasBox s.fragment := partialSequence_hasBox _ _ _ _

theorem State.fragment_pairwise {W : Set G} {m r k : ℕ}
    (s : State W m r k) (hk : 0 < k) :
    s.fragment.Pairwise (fun a b ↦ a.value < b.value) := by
  obtain ⟨a, ha⟩ := s.maximal.nonempty
  have haLevel : (a.1 : InnerLevels.OrderedSL) ∈ Level W s.outer := ha.1
  rcases haLevel with ⟨x, hx⟩
  exact partialSequence_pairwise_of_body_prefix x m s.outer s.size a.1 s.body
    (s.root x hx.1) hx.2 a.2 ha.2 (s.maximal.length_lt hk)

theorem State.root_le_value {W : Set G} {m r k : ℕ}
    (s : State W m r k) (hk : 0 < k) :
    ∀ a ∈ s.fragment, m ≤ a.value := by
  have hp := s.fragment_pairwise hk
  change (⟨m, true⟩ ::
    (s.outer.flatMap taggedLevel ++ (⟨s.size, true⟩ :: plainBody s.body))).Pairwise
      (fun a b ↦ a.value < b.value) at hp
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact le_rfl
  · exact ((List.pairwise_cons.mp hp).1 a ha).le

def State.reprefix {W : Set G} {m r k j : ℕ} (s : State W m r k)
    (v : List ℕ)
    (hv : BodyPrefix.Maximal (InnerLevels.RawFiber (Level W s.outer) s.size) v j) :
    State W m r j where
  outer := s.outer
  size := s.size
  body := v
  maximal := hv
  root := s.root
  retained := s.retained

/-- Advance within the current level, adding a nonempty nonbox segment
above the prescribed numerical bound. -/
theorem State.advance {W : Set G} {m r k j : ℕ}
    (s : State W m r k) (hjk : j < k) (bound : ℕ) :
    ∃ (s' : State W m r j) (t : List TaggedCoord),
      t ≠ [] ∧ NoBox t ∧ (∀ z ∈ t, bound < z.value) ∧
      s'.fragment = s.fragment ++ t := by
  obtain ⟨v, hvne, habove, hv⟩ :=
    s.maximal.extend_above (rawLevel_pairwise W s.outer s.size) hjk bound
  let s' := s.reprefix (s.body ++ v) hv
  refine ⟨s', plainBody v, plainBody_ne_nil hvne, noBox_plainBody v,
    above_plainBody habove, ?_⟩
  exact partialSequence_append m s.outer s.size s.body v

/-- Finish one side above the prescribed bound.  The terminal segment
contains the final box coordinate and the point still lies in `W`. -/
theorem State.finish {W : Set G} {m r k : ℕ}
    (s : State W m r k) (hk : 0 < k) (bound : ℕ) :
    ∃ x ∈ W, ∃ t : List TaggedCoord,
      t ≠ [] ∧ HasBox t ∧ (∀ z ∈ t, bound < z.value) ∧
      sequence x = s.fragment ++ t := by
  obtain ⟨a, ha, v, hvne, habove, hv⟩ :=
    s.maximal.complete_above (rawLevel_pairwise W s.outer s.size) hk bound
  have haLevel : (a.1 : InnerLevels.OrderedSL) ∈ Level W s.outer := ha
  rcases haLevel with ⟨x, hx⟩
  obtain ⟨t, htne, htbox, hseq, htabove⟩ :=
    sequence_finish_above x m s.outer s.size a.1 s.body v
      (s.root x hx.1) hx.2 a.2 hv hvne bound habove
  exact ⟨x, hx.1, t, htne, htbox, htabove, hseq⟩

/-- Initialize an active level from a sufficiently large fixed-root set. -/
theorem exists_state_from_large_set
    (W : Set G) {m : ℕ} (hroot : ∀ x ∈ W, x.1.length = m)
    (r k : ℕ) (hW : continuationBound (r + 2) ≤ typeLT W) :
    ∃ U : Set G, U ⊆ W ∧ Nonempty (State U m r k) := by
  obtain ⟨U, p, hUW, _, hlevel, hchildren⟩ :=
    exists_large_level_with_slack W hroot r (k + 1) hW
  obtain ⟨n, u, hun, htype, hmax⟩ := exists_level_maximal_prefix hlevel
  exact ⟨U, hUW, ⟨
    { outer := p
      size := n
      body := u
      maximal := ⟨hun, htype, hmax⟩
      root := fun x hx ↦ hroot x (hUW hx)
      retained := hchildren }⟩⟩

end Erdos118.Negative.Exact.Levels

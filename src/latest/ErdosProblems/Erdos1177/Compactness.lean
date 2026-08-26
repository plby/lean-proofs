-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# de Bruijn–Erdős compactness for graph colourings

If every finite subset of the vertex set of a simple graph admits a proper
`k`-colouring, then the whole graph is `k`-colourable.  This is the compactness
theorem used in the proof of closure of obligatory triple systems under
one-point amalgamation (`lem:obligatory-closure`).
-/

open SimpleGraph

namespace Erdos1177

/-- **de Bruijn–Erdős compactness.**  If for every finite set `s` of vertices
there is a total colouring `V → Fin k` that is proper on `s`, then there is a
total colouring proper on all adjacent pairs. -/
theorem colorable_of_forall_finite {V : Type*} (G : SimpleGraph V) (k : ℕ) [NeZero k]
    (h : ∀ s : Finset V, ∃ c : V → Fin k, ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → c a ≠ c b) :
    ∃ c : V → Fin k, ∀ a b, G.Adj a b → c a ≠ c b := by
  classical
  by_contra h_contra
  push_neg at h_contra
  set T : V × V → Set (V → Fin k) := fun p => {c | G.Adj p.1 p.2 → c p.1 ≠ c p.2} with hT_def
  have hT_closed : ∀ p : V × V, IsClosed (T p) := by
    intro p
    by_cases h_adj : G.Adj p.1 p.2
    · simp_all +decide
      exact isClosed_compl_iff.mpr (isOpen_discrete {x : Fin k × Fin k | x.1 = x.2}
        |> IsOpen.preimage (show Continuous fun c : V → Fin k => (c p.1, c p.2) from
          Continuous.prodMk (continuous_apply _) (continuous_apply _)))
    · aesop
  have h_empty : (Set.univ : Set (V → Fin k)) ∩ ⋂ p : V × V, T p = ∅ := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_iInter, Set.mem_empty_iff_false,
      iff_false, not_forall]
    obtain ⟨a, b, hab, hcab⟩ := h_contra c
    exact ⟨(a, b), by simp only [hT_def, Set.mem_setOf_eq, not_forall]; exact ⟨hab, not_not.mpr hcab⟩⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subfamily_closed T hT_closed h_empty
  -- The finite set of vertices appearing in the pairs of `s`.
  set s' : Finset V := s.image Prod.fst ∪ s.image Prod.snd with hs'_def
  have hs' : ∀ p ∈ s, p.1 ∈ s' ∧ p.2 ∈ s' := by
    intro p hp
    exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  obtain ⟨c, hc⟩ := h s'
  apply Set.not_nonempty_empty
  rw [← hs]
  exact ⟨c, Set.mem_univ _, Set.mem_iInter₂.2 fun p hp hadj =>
    hc _ (hs' p hp).1 _ (hs' p hp).2 hadj⟩

end Erdos1177

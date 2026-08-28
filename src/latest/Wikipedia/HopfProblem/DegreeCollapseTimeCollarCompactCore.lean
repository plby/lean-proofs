import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior
import Mathlib.Topology.Sets.Compacts

/-!
# Actual compact cores exhaust the positive interior

Inside a compact ambient space, the sets t >= c for positive c are compact
subsets of the actual positive interior. Every compact subset of that
interior lies in one such core with c strictly inside the given collar.
-/

noncomputable section

open Set Function TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

def interiorCore (c : ℝ) : Set C.positiveInterior := {p | c ≤ t p.val}

theorem isCompact_interiorCore [CompactSpace M] (c : ℝ) (hc : 0 < c) :
    IsCompact (C.interiorCore c) := by
  let D := {p : M // c ≤ t p}
  let : CompactSpace D := isCompact_iff_compactSpace.mp
    (isClosed_le continuous_const C.continuous_time).isCompact
  let f : C(D, C.positiveInterior) :=
    ⟨fun p ↦ ⟨p.val, hc.trans_le p.property⟩, continuous_subtype_val.subtype_mk _⟩
  have he : f '' univ = C.interiorCore c := by
    ext p
    constructor
    · rintro ⟨q, _, rfl⟩
      exact q.property
    · intro hp
      exact ⟨⟨p.val, hp⟩, mem_univ _, Subtype.ext rfl⟩
  rw [← he]
  exact isCompact_univ.image f.continuous

def interiorCoreCompact [CompactSpace M] (c : ℝ) (hc : 0 < c) : Compacts C.positiveInterior :=
  ⟨C.interiorCore c, C.isCompact_interiorCore c hc⟩

theorem exists_interiorCore_containing (K : Compacts C.positiveInterior) :
    ∃ c : ℝ, 0 < c ∧ c < C.width ∧ (K : Set C.positiveInterior) ⊆ C.interiorCore c := by
  by_cases hK : (K : Set C.positiveInterior).Nonempty
  · obtain ⟨p, hp, hmin⟩ := K.isCompact.exists_isMinOn hK
      (C.continuous_time.comp continuous_subtype_val).continuousOn
    let c := min (C.width / 2) (t p.val / 2)
    have hc : 0 < c := lt_min (half_pos C.width_pos) (half_pos p.property)
    refine ⟨c, hc, (min_le_left _ _).trans_lt (half_lt_self C.width_pos), ?_⟩
    intro q hq
    change c ≤ t q.val
    have hq' : t p.val ≤ t q.val := hmin hq
    exact (min_le_right _ _).trans ((half_lt_self p.property).le.trans hq')
  · refine ⟨C.width / 2, half_pos C.width_pos, half_lt_self C.width_pos, ?_⟩
    intro p hp
    exact (hK ⟨p, hp⟩).elim

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

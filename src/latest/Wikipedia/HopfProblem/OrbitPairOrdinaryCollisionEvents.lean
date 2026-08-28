import Wikipedia.HopfProblem.OrbitPairCollisionEvents
import Wikipedia.HopfProblem.OrbitPairTriplePoints

/-!
# Triple-free events contain exactly one unordered collision

At a double point of a triple-free family, its entire spatial fiber consists
of the two displayed source points. Consequently equal collision events
give equal unordered pairs, and separation of event times separates all
unordered collision times.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints

variable {M N : Type*}

theorem collisionFiber_eq_pair_of_no_triples {F : ℝ × M → N}
    (hno : triplePoints F = ∅) {t : ℝ} {x y : M} (hp : (t, (x, y)) ∈ doublePoints F) :
    collisionFiber F (t, x) = {x, y} := by
  ext z
  change F (t, z) = F (t, x) ↔ z ∈ ({x, y} : Set M)
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · intro hz
    by_cases hx : z = x
    · exact Or.inl hx
    by_cases hy : z = y
    · exact Or.inr hy
    have htr : (t, (x, (y, z))) ∈ triplePoints F :=
      ⟨hp.1, Ne.symm hx, Ne.symm hy, hp.2, hz.symm⟩
    rw [hno] at htr
    exact False.elim htr
  · rintro (rfl | rfl)
    · rfl
    · exact hp.2.symm

theorem unorderedProjection_eq_of_eventProjection_eq {F : ℝ × M → N}
    (hno : triplePoints F = ∅) {p q : ℝ × (M × M)}
    (hp : p ∈ doublePoints F) (hq : q ∈ doublePoints F)
    (he : eventProjection F p = eventProjection F q) :
    unorderedProjection p = unorderedProjection q := by
  rcases p with ⟨s, x, y⟩
  rcases q with ⟨t, u, v⟩
  have hst : s = t := congrArg (fun r : ℝ × N => r.1) he
  subst t
  have hvalue : F (s, x) = F (s, u) := congrArg (fun r : ℝ × N => r.2) he
  have hu : u ∈ collisionFiber F (s, x) := hvalue.symm
  have hv : v ∈ collisionFiber F (s, x) := hq.2.symm.trans hvalue.symm
  rw [collisionFiber_eq_pair_of_no_triples hno hp] at hu hv
  simp only [mem_insert_iff, mem_singleton_iff] at hu hv
  change (s, s(x, y)) = (s, s(u, v))
  refine congrArg (fun w : Sym2 M => (s, w)) ?_
  apply Sym2.eq_iff.mpr
  have huv := hq.1
  aesop

theorem unordered_times_injective_of_event_times
    {F : ℝ × M → N} (hno : triplePoints F = ∅)
    (hsep : InjOn Prod.fst (collisionEvents F)) : InjOn Prod.fst (unorderedDoublePoints F) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ ht
  apply unorderedProjection_eq_of_eventProjection_eq hno hp hq
  exact hsep (eventProjection_mem hp) (eventProjection_mem hq) ht

end Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints

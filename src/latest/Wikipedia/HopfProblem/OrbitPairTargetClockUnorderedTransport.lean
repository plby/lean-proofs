import Wikipedia.HopfProblem.OrbitPairTargetClockCollisionTransport
import Wikipedia.HopfProblem.OrbitPairUnorderedCollisions

/-!
# Unordered collisions and separated spatial sources under target clocks

Choose one representative of each unordered source pair to define a global
time equivalence on unordered pairs. At an actual collision either choice
has exactly the same clock value. The ordered transport therefore descends
to an explicit equivalence of unordered collisions and retains their pairing.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.TargetClock

open FamilyDoublePoints SynchronizedPairs

variable {M N : Type*}

def unorderedEquiv (e : M → ℝ ≃ ℝ) : (ℝ × Sym2 M) ≃ (ℝ × Sym2 M) :=
  sourceEquiv (fun z : Sym2 M => e z.out.1)

theorem unorderedProjection_pairEquiv {F : ℝ × M → N} {e : M → ℝ ≃ ℝ} {β : N → ℝ}
    (hclock : ∀ t x, e x t = t + β (F (t, x)))
    {p : ℝ × (M × M)} (hp : p ∈ doublePoints F) :
    unorderedProjection (pairEquiv e p) = unorderedEquiv e (unorderedProjection p) := by
  apply Prod.ext
  · change e p.2.1 p.1 = e (s(p.2.1, p.2.2) : Sym2 M).out.1 p.1
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem (s(p.2.1, p.2.2) : Sym2 M)) with h | h
    · rw [h]
    · rw [h, hclock, hclock, hp.2]
  · rfl

theorem unorderedDoublePoints_eq_image {F : ℝ × M → N} {e : M → ℝ ≃ ℝ} {β : N → ℝ}
    (hclock : ∀ t x, e x t = t + β (F (t, x))) :
    unorderedDoublePoints (family F e) = unorderedEquiv e '' unorderedDoublePoints F := by
  apply subset_antisymm
  · rintro q ⟨p, hp, rfl⟩
    rw [doublePoints_eq_image hclock] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    exact ⟨unorderedProjection r, ⟨r, hr, rfl⟩,
      (unorderedProjection_pairEquiv hclock hr).symm⟩
  · rintro q ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    have hp' : pairEquiv e p ∈ doublePoints (family F e) := by
      rw [doublePoints_eq_image hclock]
      exact ⟨p, hp, rfl⟩
    exact ⟨pairEquiv e p, hp', unorderedProjection_pairEquiv hclock hp⟩

theorem mem_unordered_iff {F : ℝ × M → N} {e : M → ℝ ≃ ℝ} {β : N → ℝ}
    (hclock : ∀ t x, e x t = t + β (F (t, x))) (p : ℝ × Sym2 M) :
    p ∈ unorderedDoublePoints (family F e) ↔
      (unorderedEquiv e).symm p ∈ unorderedDoublePoints F := by
  rw [unorderedDoublePoints_eq_image hclock]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [Equiv.symm_apply_apply] using hq
  · intro hp
    exact ⟨(unorderedEquiv e).symm p, hp, (unorderedEquiv e).apply_symm_apply p⟩

def unorderedCollisionEquiv {F : ℝ × M → N} {e : M → ℝ ≃ ℝ} {β : N → ℝ}
    (hclock : ∀ t x, e x t = t + β (F (t, x))) :
    unorderedDoublePoints (family F e) ≃ unorderedDoublePoints F :=
  (unorderedEquiv e).symm.subtypeEquiv (mem_unordered_iff hclock)

theorem unordered_pairing {F : ℝ × M → N} {e : M → ℝ ≃ ℝ} {β : N → ℝ}
    (hclock : ∀ t x, e x t = t + β (F (t, x)))
    (hpair : ∃ k : ℕ, Nonempty ((Fin k × Fin 2) ≃ unorderedDoublePoints F)) :
    ∃ k : ℕ, Nonempty ((Fin k × Fin 2) ≃ unorderedDoublePoints (family F e)) := by
  obtain ⟨k, ⟨P⟩⟩ := hpair
  exact ⟨k, ⟨P.trans (unorderedCollisionEquiv hclock).symm⟩⟩

theorem spatial_sources_injective {F : ℝ × M → N} {e : M → ℝ ≃ ℝ} {β : N → ℝ}
    (hclock : ∀ t x, e x t = t + β (F (t, x)))
    (hspace : InjOn Prod.snd (collisionSources F)) :
    InjOn Prod.snd (collisionSources (family F e)) := by
  rw [collisionSources_eq_image hclock]
  rintro q ⟨u, hu, rfl⟩ z ⟨v, hv, rfl⟩ heq
  have huv : u = v := hspace hu hv heq
  exact congrArg (sourceEquiv e) huv

end Wikipedia.HopfProblem.OrbitPair.TargetClock

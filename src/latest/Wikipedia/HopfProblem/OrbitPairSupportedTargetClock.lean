import Wikipedia.HopfProblem.OrbitPairNativeTargetClock
import Wikipedia.HopfProblem.OrbitPairTargetClockUnorderedTransport
import Wikipedia.HopfProblem.OrbitPairGlobalProjectedNeighborhood
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# A supported target clock selecting one collision value

The globally exact fiber at the selected collision gives a target
neighborhood whose whole source preimage lies in the permitted time and
spatial region. A native target bump is one at this collision value and
zero at every other collision value. Its small multiples yield actual
native retimings, with exact event relocation and unchanged other events.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.TargetClock

open FamilyDoublePoints SynchronizedPairs NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem exists_supported_target_clock_at_collision
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (hreg : RegularOn (I := I) (J := J) F {p | p.2.1 ≠ p.2.2})
    (hfinite : (doublePoints F).Finite)
    {a b : ℝ} (hab : a ≤ b)
    (hlo : ∀ t x, t ≤ a → F (t, x) = F (a, x))
    (hhi : ∀ t x, b ≤ t → F (t, x) = F (b, x))
    {p : ℝ × (M × M)} (hglobal : HasGlobalProjectedCollisionFiber F p)
    (hptime : p.1 ∈ Ioo a b) {U : Set M} (hU : IsOpen U)
    (hxU : p.2.1 ∈ U) (hyU : p.2.2 ∈ U) :
    ∃ β : N → ℝ, ContMDiff J 𝓘(ℝ, ℝ) ∞ β ∧ HasCompactSupport β ∧
      β (F (first p)) = 1 ∧
      (∀ q ∉ Ioo a b ×ˢ U, β (F q) = 0) ∧
      (∀ q ∈ doublePoints F,
        F (first q) ≠ F (first p) → β (F (first q)) = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, ‖δ‖ < ε →
        HasNativeRetiming (I := I) (J := J) F (fun z => δ * β z) a b := by
  classical
  let Z : Set N := F '' collisionSources F
  have hZ : Z.Finite := (finite_collisionSources hfinite).image F
  let O₀ : Set N := (Z \ {F (first p)})ᶜ
  have hO₀ : IsOpen O₀ := (hZ.sdiff (t := {F (first p)})).isClosed.isOpen_compl
  have hpO₀ : F (first p) ∈ O₀ := fun h => h.2 (mem_singleton _)
  have hVtime : Ioo a b ×ˢ U ⊆ Ioo a b ×ˢ (univ : Set M) :=
    fun _ h => ⟨h.1, mem_univ _⟩
  obtain ⟨O, hO, hOO₀, hpO, hpre⟩ := exists_open_projected_neighborhood_of_global_fiber
    hF.continuous hab hlo hhi hglobal (isOpen_Ioo.prod hU) hVtime
      ⟨hptime, hxU⟩ ⟨hptime, hyU⟩ hO₀ hpO₀
  obtain ⟨β, -, hβO⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := J) (F (first p))).mem_iff.mp (hO.mem_nhds hpO)
  have hone : β (F (first p)) = 1 := β.eventuallyEq_one.eq_of_nhds
  have hfixed : ∀ q ∉ Ioo a b ×ˢ U, β (F q) = 0 := by
    intro q hq
    by_contra hn
    exact hq (hpre (hβO (subset_tsupport β hn)))
  have hvalues : ∀ q ∈ doublePoints F,
      F (first q) ≠ F (first p) → β (F (first q)) = 0 := by
    intro q hq heq
    by_contra hn
    have hmem := hOO₀ (hβO (subset_tsupport β hn))
    exact hmem ⟨⟨first q, first_mem_collisionSources hq, rfl⟩, heq⟩
  refine ⟨β, β.contMDiff, β.hasCompactSupport, hone, hfixed, hvalues, ?_⟩
  exact exists_radius_native_target_clock hF hi hreg hfinite β.contMDiff
    (fun t x ht => hfixed (t, x) (fun h => ht h.1))

def relocateCollision (F : ℝ × M → N) (p : ℝ × (M × M)) (δ : ℝ)
    (q : ℝ × (M × M)) : ℝ × (M × M) := by
  classical
  exact (if F (first q) = F (first p) then q.1 + δ else q.1, q.2)

/-- An actual small event relocation, including exact transport of all
collision data and pointwise agreement outside the permitted region. -/
def HasSupportedCollisionRelocation (F : ℝ × M → N) (a b : ℝ)
    (p : ℝ × (M × M)) (U : Set M) : Prop :=
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, ‖δ‖ < ε → ∃ F' : ℝ × M → N,
      ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F' ∧
      (∀ t x, Injective (mfderiv I J (fun y => F' (t, y)) x)) ∧
      RegularOn (I := I) (J := J) F' {p | p.2.1 ≠ p.2.2} ∧
      (doublePoints F').Finite ∧ triplePoints F' = ∅ ∧
      (∀ q ∈ collisionSources F', Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F' q)) ∧
      (∀ q ∈ doublePoints F', HasGlobalProjectedCollisionFiber F' q) ∧
      InjOn Prod.snd (collisionSources F') ∧
      Nonempty (unorderedDoublePoints F' ≃ unorderedDoublePoints F) ∧
      (∀ q ∉ Ioo a b ×ˢ U, F' q = F q) ∧
      doublePoints F' = relocateCollision F p δ '' doublePoints F ∧
      (p.1 + δ, p.2) ∈ doublePoints F'

theorem exists_supported_target_clock_relocation
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (hreg : RegularOn (I := I) (J := J) F {p | p.2.1 ≠ p.2.2})
    (hfinite : (doublePoints F).Finite) (hno : triplePoints F = ∅)
    (hfull : ∀ q ∈ collisionSources F, Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F q))
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p)
    (hspace : InjOn Prod.snd (collisionSources F))
    {a b : ℝ} (hab : a ≤ b)
    (hlo : ∀ t x, t ≤ a → F (t, x) = F (a, x))
    (hhi : ∀ t x, b ≤ t → F (t, x) = F (b, x))
    {p : ℝ × (M × M)} (hp : p ∈ doublePoints F) (hptime : p.1 ∈ Ioo a b)
    {U : Set M} (hU : IsOpen U) (hxU : p.2.1 ∈ U) (hyU : p.2.2 ∈ U) :
    HasSupportedCollisionRelocation (I := I) (J := J) F a b p U := by
  classical
  obtain ⟨β, hβ, -, hone, hfixed, hvalues, ε, hε, hretime⟩ :=
    exists_supported_target_clock_at_collision hF hi hreg hfinite hab hlo hhi
      (hglobal p hp) hptime hU hxU hyU
  refine ⟨ε, hε, ?_⟩
  intro δ hδ
  obtain ⟨e, Ψ, hclock, -, -, hnew, hi', hr', hfin', hD, hzero, -, hno', hfull', hglobal'⟩ :=
    hretime δ hδ
  have hmap : ∀ q ∈ doublePoints F, pairEquiv e q = relocateCollision F p δ q := by
    intro q hq
    apply Prod.ext
    · change e q.2.1 q.1 = if F (first q) = F (first p) then q.1 + δ else q.1
      rw [hclock]
      change q.1 + δ * β (F (first q)) =
        if F (first q) = F (first p) then q.1 + δ else q.1
      by_cases heq : F (first q) = F (first p)
      · rw [if_pos heq, heq, hone, mul_one]
      · rw [if_neg heq, hvalues q hq heq, mul_zero, add_zero]
    · rfl
  have hD' : doublePoints (family F e) = relocateCollision F p δ '' doublePoints F := by
    rw [hD]
    exact image_congr hmap
  refine ⟨family F e, hnew, hi', hr', hfin', hno' hno, hfull' hfull, hglobal' hglobal,
    spatial_sources_injective (β := fun z => δ * β z) hclock hspace,
    ⟨unorderedCollisionEquiv (β := fun z => δ * β z) hclock⟩,
    (fun q hq => hzero q (by change δ * β (F q) = 0; rw [hfixed q hq, mul_zero])),
    hD', ?_⟩
  rw [hD']
  refine ⟨p, hp, ?_⟩
  simp [relocateCollision]

end Wikipedia.HopfProblem.OrbitPair.TargetClock

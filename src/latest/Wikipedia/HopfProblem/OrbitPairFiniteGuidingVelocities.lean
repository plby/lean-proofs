import Wikipedia.HopfProblem.OrbitPairCollisionGuidingVelocity

/-!
# Simultaneous transverse guiding directions at all collisions

Globally exact collision fibers imply that the first-source map on ordered
collisions is injective. The supported spatial construction therefore
prepares the finitely many ordered collisions one at a time, preserving
every earlier guiding direction and all globally exact collision fibers.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open FamilyDoublePoints SynchronizedPairs

theorem first_injOn_of_global_collision_fibers {M N : Type*} {F : ℝ × M → N}
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p) :
    InjOn first (doublePoints F) := by
  intro p hp q hq hfirst
  have hvalue : F (second q) = F (first p) := hq.2.symm.trans (congrArg F hfirst.symm)
  rcases (hglobal p hp (second q)).mp hvalue with h | h
  · exact False.elim (hq.1 (congrArg Prod.snd (hfirst.symm.trans h.symm)))
  · have ht : p.1 = q.1 := congrArg (fun z : ℝ × M => z.1) hfirst
    have hx : p.2.1 = q.2.1 := congrArg (fun z : ℝ × M => z.2) hfirst
    have hy : p.2.2 = q.2.2 := congrArg (fun z : ℝ × M => z.2) h.symm
    exact Prod.ext ht (Prod.ext hx hy)

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace K N]

structure GuidingVelocityState (F F' : ℝ × M → N) (T : Set ℝ) : Prop where
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F'
  spatial : ∀ t x, Injective (mfderiv I J (fun y => F' (t, y)) x)
  regular : RegularOn (I := I) (J := J) F' {q | q.2.1 ≠ q.2.2}
  collisions : doublePoints F' = doublePoints F
  full : ∀ q ∈ collisionSources F', Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F' q)
  globalFibers : ∀ p ∈ doublePoints F', HasGlobalProjectedCollisionFiber F' p
  fixed : ∀ t x, t ∉ T → F' (t, x) = F (t, x)
  fixedCollisions : ∀ q ∈ collisionSources F, F' q = F q

theorem exists_all_transverse_guiding_velocities
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (hreg : RegularOn (I := I) (J := J) F {q | q.2.1 ≠ q.2.2})
    (hfinite : (doublePoints F).Finite)
    (hfull : ∀ q ∈ collisionSources F,
      Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F q))
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p)
    (hspace : InjOn Prod.snd (collisionSources F))
    (hdim : Module.finrank ℝ (ℝ × E) < Module.finrank ℝ G)
    {T : Set ℝ} (hT : IsOpen T) (htimes : ∀ p ∈ doublePoints F, p.1 ∈ T) :
    ∃ F' : ℝ × M → N, GuidingVelocityState (I := I) (J := J) F F' T ∧
      ∀ p ∈ doublePoints F', HasTransverseGuidingVelocity (I := I) (J := J) F' p := by
  classical
  letI := hfinite.fintype
  have main : ∀ s : Finset (doublePoints F), ∃ F' : ℝ × M → N,
      GuidingVelocityState (I := I) (J := J) F F' T ∧
      ∀ p ∈ s, HasTransverseGuidingVelocity (I := I) (J := J) F' p.val := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨F, ⟨hF, hi, hreg, rfl, hfull, hglobal,
        (fun _ _ _ => rfl), (fun _ _ => rfl)⟩, by simp⟩
    | @insert i s his ih =>
      obtain ⟨F₁, h₁, hprevious⟩ := ih
      have hfinite₁ : (doublePoints F₁).Finite := h₁.collisions.symm ▸ hfinite
      have hsourceEq := collisionSources_eq_of_doublePoints_eq h₁.collisions
      have hspace₁ : InjOn Prod.snd (collisionSources F₁) := hsourceEq.symm ▸ hspace
      have hi₁ : i.val ∈ doublePoints F₁ := h₁.collisions.symm ▸ i.property
      obtain ⟨F₂, hF₂, hi₂, hr₂, hD₂, hfull₂, hglobal₂, hfixed₂, hfixedC₂,
        hnew, hkeep⟩ := SpatialReparametrization.exists_transverse_guiding_velocity
          h₁.smooth h₁.spatial h₁.regular hfinite₁ h₁.full h₁.globalFibers hspace₁ hdim
          hi₁ hT (htimes i.val i.property) isOpen_univ (mem_univ _)
      refine ⟨F₂, ⟨hF₂, hi₂, hr₂, hD₂.trans h₁.collisions, hfull₂, hglobal₂,
        ?_, ?_⟩, ?_⟩
      · intro t x ht
        exact (hfixed₂ t x (Or.inl ht)).trans (h₁.fixed t x ht)
      · intro q hq
        exact (hfixedC₂ q (hsourceEq.symm ▸ hq)).trans (h₁.fixedCollisions q hq)
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hnew
        · have hj₁ : j.val ∈ doublePoints F₁ := h₁.collisions.symm ▸ j.property
          have hfirst : first j.val ≠ first i.val := by
            intro heq
            have hji : j = i := Subtype.ext
              (first_injOn_of_global_collision_fibers h₁.globalFibers hj₁ hi₁ heq)
            exact his (hji ▸ hj)
          exact hkeep j.val hj₁ hfirst (hprevious j hj)
  obtain ⟨F', hstate, hall⟩ := main Finset.univ
  refine ⟨F', hstate, ?_⟩
  intro p hp
  exact hall ⟨p, hstate.collisions ▸ hp⟩ (Finset.mem_univ _)

end Wikipedia.HopfProblem.OrbitPair.NativeFamily

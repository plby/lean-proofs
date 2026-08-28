import Wikipedia.HopfProblem.OrbitPairGlobalProjectedCollisionFiber

/-!
# Simultaneously exact global projected fibers at every ordinary collision

Prepare the finitely many collision values in succession. Every ambient
clock step creates no new projected coincidences with any collision source,
so an already exact global fiber remains exact. The synchronized collision
set is unchanged throughout, as are all exterior time slices.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

def HasGlobalProjectedCollisionFiber {M N : Type*} (F : ℝ × M → N)
    (p : ℝ × (M × M)) : Prop :=
  ∀ z : ℝ × M, F z = F (SynchronizedPairs.first p) ↔
    z = SynchronizedPairs.first p ∨ z = SynchronizedPairs.second p

theorem HasGlobalProjectedCollisionFiber.avoids_image {M N : Type*} {F : ℝ × M → N}
    {p : ℝ × (M × M)} (hp : HasGlobalProjectedCollisionFiber F p) {C : Set (ℝ × M)}
    (hfirst : SynchronizedPairs.first p ∉ C) (hsecond : SynchronizedPairs.second p ∉ C) :
    F (SynchronizedPairs.first p) ∉ F '' C := by
  rintro ⟨q, hq, heq⟩
  rcases (hp q).mp heq with rfl | rfl
  · exact hfirst hq
  · exact hsecond hq

theorem preimage_image_collisionSources_eq {M N : Type*} {F : ℝ × M → N}
    (hfibers : ∀ p ∈ FamilyDoublePoints.doublePoints F, HasGlobalProjectedCollisionFiber F p) :
    F ⁻¹' (F '' FamilyDoublePoints.collisionSources F) = FamilyDoublePoints.collisionSources F := by
  have hsource (q : ℝ × M) (p : ℝ × (M × M)) (hp : p ∈ FamilyDoublePoints.doublePoints F)
      (hq : F q = F (SynchronizedPairs.first p)) : q ∈ FamilyDoublePoints.collisionSources F := by
    rcases (hfibers p hp q).mp hq with rfl | rfl
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩
  ext q
  constructor
  · rintro ⟨z, hz, heq⟩
    rcases hz with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact hsource q p hp heq.symm
    · exact hsource q p hp (heq.symm.trans hp.2.symm)
  · intro hq
    exact ⟨q, hq, rfl⟩

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

structure ProjectedFiberState (F F' : ℝ × M → N) (U : Set ℝ) : Prop where
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F'
  collisions : FamilyDoublePoints.doublePoints F' = FamilyDoublePoints.doublePoints F
  spatial : ∀ t x, Injective (mfderiv I J (fun y => F' (t, y)) x)
  regular : SynchronizedPairs.RegularOn (I := I) (J := J) F' {q | q.2.1 ≠ q.2.2}
  finite : (FamilyDoublePoints.doublePoints F').Finite
  noTriples : FamilyDoublePoints.triplePoints F' = ∅
  full : ∀ q ∈ FamilyDoublePoints.collisionSources F',
    Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F' q)
  fixed : ∀ t x, t ∉ U → F' (t, x) = F (t, x)
  noNew : ∀ q ∈ FamilyDoublePoints.collisionSources F, ∀ z, F' q = F' z → F q = F z

theorem exists_all_global_projected_collision_fibers
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hiF : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (hrF : SynchronizedPairs.RegularOn (I := I) (J := J) F {q | q.2.1 ≠ q.2.2})
    (hfinite : (FamilyDoublePoints.doublePoints F).Finite)
    (hno : FamilyDoublePoints.triplePoints F = ∅)
    (hfull : ∀ q ∈ FamilyDoublePoints.collisionSources F,
      Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F q))
    (hdim : Module.finrank ℝ (ℝ × E) < Module.finrank ℝ G)
    {U : Set ℝ} (hU : IsOpen U)
    (hUtimes : ∀ p ∈ FamilyDoublePoints.doublePoints F, p.1 ∈ U) :
    ∃ F' : ℝ × M → N, ProjectedFiberState (I := I) (J := J) F F' U ∧
      ∀ p ∈ FamilyDoublePoints.doublePoints F', HasGlobalProjectedCollisionFiber F' p := by
  classical
  letI := hfinite.fintype
  have main : ∀ s : Finset (FamilyDoublePoints.doublePoints F), ∃ F' : ℝ × M → N,
      ProjectedFiberState (I := I) (J := J) F F' U ∧
        ∀ i ∈ s, HasGlobalProjectedCollisionFiber F' i.val := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨F, ⟨hF, rfl, hiF, hrF, hfinite, hno, hfull,
        (fun _ _ _ => rfl), (fun _ _ _ h => h)⟩, ?_⟩
      simp
    | @insert i s his ih =>
      obtain ⟨F₁, h₁, hprevious⟩ := ih
      have hi₁ : i.val ∈ FamilyDoublePoints.doublePoints F₁ := h₁.collisions.symm ▸ i.property
      obtain ⟨F₂, hF₂, hD₂, hi₂, hr₂, hfin₂, hno₂, hfull₂, hfix₂, hnew₂, hfiber₂⟩ :=
        exists_global_projected_fiber_at_collision h₁.smooth h₁.spatial h₁.regular h₁.finite
          h₁.noTriples h₁.full hdim hi₁ hU (hUtimes i.val i.property)
      have hsourceEq := FamilyDoublePoints.collisionSources_eq_of_doublePoints_eq h₁.collisions
      have hstate : ProjectedFiberState (I := I) (J := J) F F₂ U := by
        refine ⟨hF₂, hD₂.trans h₁.collisions, hi₂, hr₂, hfin₂, hno₂, hfull₂, ?_, ?_⟩
        · intro t x ht
          exact (hfix₂ t x ht).trans (h₁.fixed t x ht)
        · intro q hq z hqz
          have hq₁ : q ∈ FamilyDoublePoints.collisionSources F₁ := hsourceEq.symm ▸ hq
          exact h₁.noNew q hq z (hnew₂ q hq₁ z hqz)
      refine ⟨F₂, hstate, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hfiber₂
      · intro z
        constructor
        · intro hz
          have hj₁ : j.val ∈ FamilyDoublePoints.doublePoints F₁ :=
            h₁.collisions.symm ▸ j.property
          have hq₁ : SynchronizedPairs.first j.val ∈ FamilyDoublePoints.collisionSources F₁ :=
            Or.inl ⟨j.val, hj₁, rfl⟩
          have hold := hnew₂ (SynchronizedPairs.first j.val) hq₁ z hz.symm
          exact (hprevious j hj z).mp hold.symm
        · rintro (rfl | rfl)
          · rfl
          · have hj₂ : j.val ∈ FamilyDoublePoints.doublePoints F₂ :=
              hstate.collisions.symm ▸ j.property
            exact hj₂.2.symm
  obtain ⟨F', hstate, hfibers⟩ := main Finset.univ
  refine ⟨F', hstate, ?_⟩
  intro p hp
  have hp₀ : p ∈ FamilyDoublePoints.doublePoints F := hstate.collisions ▸ hp
  exact hfibers ⟨p, hp₀⟩ (Finset.mem_univ _)

end Wikipedia.HopfProblem.OrbitPair.NativeFamily

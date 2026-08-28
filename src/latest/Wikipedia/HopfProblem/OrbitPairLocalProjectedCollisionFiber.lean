import Wikipedia.HopfProblem.OrbitPairCleanCrossingNeighborhood
import Wikipedia.HopfProblem.OrbitPairNativeLocalInjectivity
import Wikipedia.HopfProblem.OrbitPairOrdinaryCollisionEvents

/-!
# Locally exact projected fibers at ordinary immersive collisions

Full projected immersion makes each of the two source branches locally
injective. Compactness of the spatial source excludes all other branches
from a short time neighborhood. Consequently the projected collision
value has exactly its two intended source preimages throughout that time
neighborhood, even when the comparison point has a different time.

This is local in time; repetitions of the value at remote times are not
excluded by this theorem.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem exists_local_projected_collision_fiber
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    {t : ℝ} {x y : M} (hxy : F (t, x) = F (t, y))
    (hfiber : ∀ z, F (t, z) = F (t, x) → z = x ∨ z = y)
    (hxfull : Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F (t, x)))
    (hyfull : Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F (t, y)))
    {a b : ℝ} (ha : a < t) (hb : t < b) :
    ∃ l r : ℝ, t ∈ Ioo l r ∧ Ioo l r ⊆ Ioo a b ∧
      ∀ p : ℝ × M, p.1 ∈ Ioo l r →
        (F p = F (t, x) ↔ p = (t, x) ∨ p = (t, y)) := by
  obtain ⟨V₁, hV₁, hxV, -, hi₁⟩ := NativeImmersion.exists_open_injOn_on isOpen_univ
    hF.contMDiffOn (mem_univ (t, x)) hxfull
  obtain ⟨V₂, hV₂, hyV, -, hi₂⟩ := NativeImmersion.exists_open_injOn_on isOpen_univ
    hF.contMDiffOn (mem_univ (t, y)) hyfull
  have hfiberV : ∀ z, F (t, z) = F (t, x) → (t, z) ∈ V₁ ∪ V₂ := by
    intro z hz
    rcases hfiber z hz with rfl | rfl
    · exact Or.inl hxV
    · exact Or.inr hyV
  obtain ⟨W, hW, hqW, hWtime, hpre⟩ := exists_open_track_neighborhood_of_fiber_subset
    hF.continuous (t, x) (hV₁.union hV₂) hfiberV ha hb
  have htimeOpen : IsOpen ((fun s : ℝ => (s, F (t, x))) ⁻¹' W) :=
    hW.preimage (continuous_id.prodMk continuous_const)
  have hcenter : t ∈ (fun s : ℝ => (s, F (t, x))) ⁻¹' W := hqW
  obtain ⟨l, r, htlr, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (htimeOpen.mem_nhds hcenter)
  refine ⟨l, r, htlr, (fun s hs => (hWtime (hsub hs)).1), ?_⟩
  intro p hp
  constructor
  · intro hvalue
    have htrack : track F p ∈ W := by
      change (p.1, F p) ∈ W
      rw [hvalue]
      exact hsub hp
    rcases hpre htrack with hp₁ | hp₂
    · exact Or.inl (hi₁ hp₁ hxV hvalue)
    · exact Or.inr (hi₂ hp₂ hyV (hvalue.trans hxy))
  · rintro (rfl | rfl)
    · rfl
    · exact hxy.symm

theorem exists_local_projected_fiber_of_ordinary_collision
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hno : FamilyDoublePoints.triplePoints F = ∅)
    (hfull : ∀ q ∈ FamilyDoublePoints.collisionSources F,
      Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F q))
    {p : ℝ × (M × M)} (hp : p ∈ FamilyDoublePoints.doublePoints F)
    {a b : ℝ} (ha : a < p.1) (hb : p.1 < b) :
    ∃ l r : ℝ, p.1 ∈ Ioo l r ∧ Ioo l r ⊆ Ioo a b ∧
      ∀ q : ℝ × M, q.1 ∈ Ioo l r →
        (F q = F (SynchronizedPairs.first p) ↔
          q = SynchronizedPairs.first p ∨ q = SynchronizedPairs.second p) := by
  have hfiber : ∀ z, F (p.1, z) = F (p.1, p.2.1) → z = p.2.1 ∨ z = p.2.2 := by
    intro z hz
    have hmem : z ∈ FamilyDoublePoints.collisionFiber F (p.1, p.2.1) := hz
    rw [FamilyDoublePoints.collisionFiber_eq_pair_of_no_triples hno hp] at hmem
    simpa only [mem_insert_iff, mem_singleton_iff] using hmem
  exact exists_local_projected_collision_fiber hF hp.2 hfiber
    (hfull (SynchronizedPairs.first p) (Or.inl ⟨p, hp, rfl⟩))
    (hfull (SynchronizedPairs.second p) (Or.inr ⟨p, hp, rfl⟩)) ha hb

end Wikipedia.HopfProblem.OrbitPair.NativeFamily

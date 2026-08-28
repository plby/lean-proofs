import Wikipedia.HopfProblem.OrbitPairGuidingVelocity
import Wikipedia.HopfProblem.OrbitPairSpatialDerivativeTransport
import Wikipedia.HopfProblem.OrbitPairSpatialGlobalFibers
import Wikipedia.HopfProblem.OrbitPairGuidingCurveDerivative

/-!
# Preparing one collision's guiding velocity by a source motion

The selected branch receives a small spatial time velocity. All collision
source points are fixed, and every other collision-source vertical curve
is fixed for all times. Projected tangent images at the collision sources
are unchanged. These exact identities retain all previously prepared
guiding velocities whose first source differs from the selected source.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization

open FamilyDoublePoints SynchronizedPairs NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace K N]

theorem exists_transverse_guiding_velocity
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (hreg : RegularOn (I := I) (J := J) F {q | q.2.1 ≠ q.2.2})
    (hfinite : (doublePoints F).Finite)
    (hfull : ∀ q ∈ collisionSources F,
      Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F q))
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p)
    (hspace : InjOn Prod.snd (collisionSources F))
    (hdim : Module.finrank ℝ (ℝ × E) < Module.finrank ℝ G)
    {p : ℝ × (M × M)} (hp : p ∈ doublePoints F)
    {T : Set ℝ} (hT : IsOpen T) (ht : p.1 ∈ T)
    {U : Set M} (hU : IsOpen U) (hxU : p.2.1 ∈ U) :
    ∃ F' : ℝ × M → N, ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F' ∧
      (∀ t x, Injective (mfderiv I J (fun y => F' (t, y)) x)) ∧
      RegularOn (I := I) (J := J) F' {q | q.2.1 ≠ q.2.2} ∧
      doublePoints F' = doublePoints F ∧
      (∀ q ∈ collisionSources F',
        Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F' q)) ∧
      (∀ q ∈ doublePoints F', HasGlobalProjectedCollisionFiber F' q) ∧
      (∀ s y, s ∉ T ∨ y ∉ U → F' (s, y) = F (s, y)) ∧
      (∀ q ∈ collisionSources F, F' q = F q) ∧
      HasTransverseGuidingVelocity (I := I) (J := J) F' p ∧
      (∀ q ∈ doublePoints F, first q ≠ first p →
        HasTransverseGuidingVelocity (I := I) (J := J) F q →
        HasTransverseGuidingVelocity (I := I) (J := J) F' q) := by
  let Z : Set M := Prod.snd '' collisionSources F
  have hZ : Z.Finite := (finite_collisionSources hfinite).image Prod.snd
  let U' : Set M := U ∩ (Z \ {p.2.1})ᶜ
  have hU' : IsOpen U' := hU.inter (hZ.sdiff (t := {p.2.1})).isClosed.isOpen_compl
  have hxU' : p.2.1 ∈ U' := ⟨hxU, fun h => h.2 (mem_singleton _)⟩
  obtain ⟨ε, hε, hmotion⟩ := exists_radius_supported_spatial_velocity (I := I) hT ht hU' hxU'
  let A : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (first p)
  let B : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (second p)
  have hr : Surjective (B.comp secondLinear - A.comp firstLinear) := by
    let D₁ : ℝ × (E × E) →L[ℝ] G :=
      mfderiv (𝓘(ℝ, ℝ).prod (I.prod I)) J (F ∘ first) p
    let D₂ : ℝ × (E × E) →L[ℝ] G :=
      mfderiv (𝓘(ℝ, ℝ).prod (I.prod I)) J (F ∘ second) p
    have h₁ : D₁ = A.comp firstLinear := by
      have hh := mfderiv_comp p (hF.mdifferentiableAt (by simp))
        (first_hasMFDerivAt (I := I) p).mdifferentiableAt
      rw [(first_hasMFDerivAt (I := I) p).mfderiv] at hh
      exact hh
    have h₂ : D₂ = B.comp secondLinear := by
      have hh := mfderiv_comp p (hF.mdifferentiableAt (by simp))
        (second_hasMFDerivAt (I := I) p).mdifferentiableAt
      rw [(second_hasMFDerivAt (I := I) p).mfderiv] at hh
      exact hh
    have hh : Surjective (D₂ - D₁) := hreg p hp.1 hp.2
    rwa [h₁, h₂] at hh
  obtain ⟨a, ha, havoid⟩ := GuidingVelocity.exists_small_velocity_transverse A B hr hdim hε
  obtain ⟨D, hD, hfixedSlice, hfixed, hvelocity⟩ := hmotion a ha
  let e := fun t => (D t).toEquiv
  let F' : ℝ × M → N := changedFamily F e
  have hfixC : ∀ q ∈ collisionSources F, sourceEquiv e q = q := by
    intro q hq
    by_cases hqx : q.2 = p.2.1
    · have hqp : q = first p := hspace hq (first_mem_collisionSources hp) hqx
      subst q
      exact Prod.ext rfl (hfixedSlice p.2.1)
    · have hout : q.2 ∉ U' := fun h => h.2 ⟨⟨q, hq, rfl⟩, hqx⟩
      exact Prod.ext rfl (hfixed q.1 q.2 (Or.inr hout))
  have hF' := changedFamily_smooth D hD hF
  have hDexact := doublePoints_eq_of_fixed_collisionSources e hfixC
  have hrange (q : ℝ × M) (hq : q ∈ collisionSources F) :
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ).prod I) J F' q).toLinearMap =
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ).prod I) J F q).toLinearMap := by
    have hh := changedFamily_derivative_range D hD hF q
    rw [hfixC q hq] at hh
    exact hh
  refine ⟨F', hF', changedFamily_spatial D hD hF hi,
    changedFamily_regular D hD hF hreg, hDexact,
    changedFamily_full_at_collisionSources D hD hF hfull,
    global_projected_collision_fibers e hglobal, ?_, ?_, ?_, ?_⟩
  · intro s y hsy
    have hd : D s y = y := hfixed s y (hsy.imp id (fun h h' => h h'.1))
    change F (s, D s y) = F (s, y)
    rw [hd]
  · intro q hq
    change F (sourceEquiv e q) = F q
    rw [hfixC q hq]
  · have htder := changedFamily_time_derivative D hD hF (hfixedSlice p.2.1) hvelocity
    let A' : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F' (first p)
    let B' : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F' (second p)
    have htder' : A' (1, 0) = A (1, a) := htder
    have hrange' : LinearMap.range B'.toLinearMap = LinearMap.range B.toLinearMap :=
      hrange (second p) (second_mem_collisionSources hp)
    change A' (1, 0) ∉ LinearMap.range B'.toLinearMap
    rw [hrange', htder']
    exact havoid
  · intro q hq hqp hgood
    have hqx : q.2.1 ≠ p.2.1 := fun h => hqp
      (hspace (first_mem_collisionSources hq) (first_mem_collisionSources hp) h)
    have hout : q.2.1 ∉ U' := fun h =>
      h.2 ⟨⟨first q, first_mem_collisionSources hq, rfl⟩, hqx⟩
    have hcurve : (fun s => F' (s, q.2.1)) = (fun s => F (s, q.2.1)) := by
      funext s
      change F (s, D s q.2.1) = F (s, q.2.1)
      rw [hfixed s q.2.1 (Or.inr hout)]
    let A' : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F' (first q)
    let A₀ : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (first q)
    let B' : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F' (second q)
    let B₀ : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (second q)
    let C' : ℝ →L[ℝ] G := mfderiv 𝓘(ℝ, ℝ) J (fun s => F' (s, q.2.1)) q.1
    let C₀ : ℝ →L[ℝ] G := mfderiv 𝓘(ℝ, ℝ) J (fun s => F (s, q.2.1)) q.1
    have hC : C' = C₀ := by dsimp only [C', C₀]; rw [hcurve]
    have ht' : C' 1 = A' (1, 0) := guiding_curve_derivative hF' q.1 q.2.1
    have ht₀ : C₀ 1 = A₀ (1, 0) := guiding_curve_derivative hF q.1 q.2.1
    have htime : A' (1, 0) = A₀ (1, 0) :=
      ht'.symm.trans ((congrArg (fun C : ℝ →L[ℝ] G => C 1) hC).trans ht₀)
    have hrange' : LinearMap.range B'.toLinearMap = LinearMap.range B₀.toLinearMap :=
      hrange (second q) (second_mem_collisionSources hq)
    change A' (1, 0) ∉ LinearMap.range B'.toLinearMap
    rw [hrange', htime]
    exact hgood

end Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization

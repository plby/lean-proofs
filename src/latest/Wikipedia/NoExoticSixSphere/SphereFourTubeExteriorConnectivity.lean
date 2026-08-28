import Wikipedia.NoExoticSixSphere.SphereFourTubeHalfRetract

/-!
# Two-connectivity of the actual collared tube exterior

The positive core complement is two-connected by native image avoidance.
Its actual homotopy right inverse onto the new half transfers paths and
sphere contractions. This proves simple connectivity, native `π₂ = 0`,
and integral `H₂ = 0` for the literal new half, without a torsion or
homology-equivalence assumption about its inclusion in the old half.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem SingularMayerVietoris

variable {M B B' : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] [TopologicalSpace B] [TopologicalSpace B']
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (t τ : C(M, ℝ)) (C : TimeCollar t B) (D : TimeCollar τ B')
  (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)
  (hhalf : ∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1)

include Φ hΦ C D hpos hout hhalf in
theorem simplyConnected_modifiedHalf [SimplyConnectedSpace (NonnegativeHalf t)] :
    SimplyConnectedSpace (NonnegativeHalf τ) := by
  let : SimplyConnectedSpace (positiveCoreComplement Φ hΦ t C hpos) :=
    simplyConnected_positiveCoreComplement Φ hΦ t C hpos
  let r := positiveRetraction Φ hΦ t τ C hpos hhalf
  let s := (interiorToCoreComplement Φ hΦ t τ C D hpos hout hhalf).comp D.halfToInterior
  have h : (r.comp s).Homotopic (ContinuousMap.id (NonnegativeHalf τ)) :=
    half_retraction_right_homotopy Φ hΦ t τ C D hpos hout hhalf
  let : PathConnectedSpace (NonnegativeHalf τ) := HomotopyRetractConnectivity.pathConnected r s h
  exact OrbitPair.simplyConnected_of_roundCircle_nullhomotopies
    (HomotopyRetractConnectivity.nullhomotopies r s h
      ImmersedSource.circle_nullhomotopic_of_simplyConnected)

include Φ hΦ C D hpos hout hhalf in
theorem pi_two_modifiedHalf [SimplyConnectedSpace (NonnegativeHalf t)]
    [Subsingleton (SingularHomology (NonnegativeHalf t) 2)] (x : NonnegativeHalf τ) :
    Subsingleton (π_ 2 (NonnegativeHalf τ) x) := by
  let r := positiveRetraction Φ hΦ t τ C hpos hhalf
  let s := (interiorToCoreComplement Φ hΦ t τ C D hpos hout hhalf).comp D.halfToInterior
  have h : (r.comp s).Homotopic (ContinuousMap.id (NonnegativeHalf τ)) :=
    half_retraction_right_homotopy Φ hΦ t τ C D hpos hout hhalf
  exact OrbitPair.SphereNullhomotopy.pi_subsingleton_of_sphere_nullhomotopies (by decide)
    (HomotopyRetractConnectivity.nullhomotopies r s h
      (positiveCoreComplement_two_sphere_nullhomotopies Φ hΦ t C hpos)) x

include Φ hΦ C D hpos hout hhalf in
theorem h2_modifiedHalf [SimplyConnectedSpace (NonnegativeHalf t)]
    [Subsingleton (SingularHomology (NonnegativeHalf t) 2)] :
    Subsingleton (SingularHomology (NonnegativeHalf τ) 2) := by
  let : SimplyConnectedSpace (NonnegativeHalf τ) :=
    simplyConnected_modifiedHalf Φ hΦ t τ C D hpos hout hhalf
  let x : NonnegativeHalf τ := Classical.arbitrary _
  let : Subsingleton (π_ 2 (NonnegativeHalf τ) x) :=
    pi_two_modifiedHalf Φ hΦ t τ C D hpos hout hhalf x
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).symm.injective.subsingleton

include hΦ hpos in
theorem exists_two_connected_collared_exterior [CompactSpace M]
    [SimplyConnectedSpace (NonnegativeHalf t)]
    [Subsingleton (SingularHomology (NonnegativeHalf t) 2)]
    (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t x)) :
    ∃ (τ : C(M, ℝ)) (D : TimeCollar τ (B ⊕ (Sphere 3 × Sphere 3))),
      ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ ∧
      (∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x)) ∧
      (∀ x ∉ closedRegion Φ 2, τ x = t x) ∧
      (∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1) ∧
      (∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1) ∧
      SimplyConnectedSpace (NonnegativeHalf τ) ∧
      Subsingleton (SingularHomology (NonnegativeHalf τ) 2) ∧
      D.width ≤ C.width ∧
      (∀ b : B, (D.zeroPoint (Sum.inl b)).val = (C.zeroPoint b).val) ∧
      ∀ s v : Sphere 3, (D.zeroPoint (Sum.inr (s, v))).val = Φ (s, v.val) := by
  obtain ⟨τ, D, hτ, hτreg, hout, hinner, hhalf, hw, hold, hnew⟩ :=
    exists_collared_regular_time_modification Φ hΦ t C ht hreg hpos
  exact ⟨τ, D, hτ, hτreg, hout, hinner, hhalf,
    simplyConnected_modifiedHalf Φ hΦ t τ C D hpos hout hhalf,
    h2_modifiedHalf Φ hΦ t τ C D hpos hout hhalf, hw, hold, hnew⟩

end NoExoticSixSphere.SphereFourTube

import Wikipedia.NoExoticSixSphere.OrthogonalLocalizedCriticalCrossing

/-!
# Arbitrarily small localized crossings

In addition to the energy and support conditions, every point of the homotopy
can be kept within an arbitrary positive distance of its original polygon.
The initial neighborhood and the lower crossing thresholds are constructed
after the spatial allowance is fixed.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m : ℕ}

include I

theorem exists_small_localized_critical_crossing (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v)
    (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) (hd : finrank ℝ B + 2 < n) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∧
      ∃ l k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
          ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
            ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
              ∃ q : C(M, Space n m), (∀ x ∈ K, energy a b τ (q x) < k) ∧
                ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                  ∀ t x, G (t, x) ∈ admissible a b m ∧
                    energy a b τ (G (t, x)) ≤
                      max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                    dist (G (t, x)) (p x) < ρ := by
  obtain ⟨V, hV, hvV, hVsub, l, k, hlk, hk, hcross⟩ :=
    exists_localized_critical_crossing_in (I := I) (M := M) a b τ hτ hzero hone v hv
      hcrit hanti habove (Metric.ball v (ρ / 2)) Metric.isOpen_ball
      (Metric.mem_ball_self (by linarith)) ε hε hd
  refine ⟨V, hV, hvV, hVsub.trans inter_subset_left, l, k, hlk, hk, ?_⟩
  intro p hp K hK hKV S hS hLow
  obtain ⟨q, hq, G, hG⟩ := hcross p hp K hK hKV S hS hLow
  refine ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1, ?_⟩⟩
  by_cases hx : x ∈ p ⁻¹' V
  · have hpBall : dist (p x) v < ρ / 2 := (hVsub hx).2
    rcases (hG t x).2.2 with he | hBall
    · rw [he, dist_self]
      exact hρ
    · have hdist : dist (G (t, x)) v < ρ / 2 := hBall
      have htriangle := dist_triangle (G (t, x)) v (p x)
      rw [dist_comm v (p x)] at htriangle
      linarith
  · rw [G.eq_fst t (Or.inr hx), dist_self]
    exact hρ

end NoExoticSixSphere.OrthogonalPolygon

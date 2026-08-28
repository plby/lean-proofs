import Wikipedia.NoExoticSixSphere.PartialGradientHighEnergyControl
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Quantitative crossing control in the target metric

The initial chart neighborhood and energy thresholds are fixed first. Uniform
continuity of the inverse chart on the fixed closed coordinate ball transports
every later spatial tolerance without shrinking that neighborhood.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {B H M D E Y : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [PseudoMetricSpace Y]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

include I

theorem exists_quantitative_crossing_in_chart (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (e : OpenPartialHomeomorph Y E) (hinv : Continuous e.symm)
    (hzero : (0 : E) ∈ e.target) (energy : Y → ℝ)
    (henergy : ∀ z, f z = energy (e.symm z))
    (admissible : Set Y) (hadm : C.chart.source ⊆ e.symm ⁻¹' admissible)
    (N : Set Y) (hN : IsOpen N) (hcenter : e.symm 0 ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < finrank ℝ D) :
    ∃ W : Set Y, IsOpen W ∧ e.symm 0 ∈ W ∧ W ⊆ admissible ∩ N ∧
      ∃ l k : ℝ, l < k ∧ k < energy (e.symm 0) ∧
        ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
          ∀ (p : C(M, Y)), (∀ x, p x ∈ W) →
            ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
              ∃ q : C(M, Y), (∀ x, energy (q x) < k) ∧
                ∃ G : ContinuousMap.HomotopyRel p q S,
                  ∀ t x, G (t, x) ∈ admissible ∧
                    energy (G (t, x)) < energy (e.symm 0) + ε ∧ G (t, x) ∈ N ∧
                    energy (G (t, x)) < energy (p x) + ξ ∧
                    (energy (p x) - energy (G (t, x)) ≤ 2 * ζ → dist (G (t, x)) (p x) < ρ) := by
  obtain ⟨r, hr, W₀, hW₀, hW₀zero, hW₀sub, hW₀norm, l, k, hlk, hk, hcross⟩ :=
    C.exists_quantitative_crossing_neighborhood (I := I) (M := M) hU hf
      (e.target ∩ e.symm ⁻¹' N) (e.open_target.inter (hN.preimage hinv))
      ⟨hzero, hcenter⟩ ε hε hd
  let W := e.source ∩ e ⁻¹' W₀
  have hW : IsOpen W := e.isOpen_inter_preimage hW₀
  have hWcenter : e.symm 0 ∈ W := ⟨e.map_target hzero, by
    change e (e.symm 0) ∈ W₀
    rwa [e.right_inv hzero]⟩
  have hWsub : W ⊆ admissible ∩ N := by
    intro y hy
    have hh := hW₀sub hy.2
    have ha := hadm hh.1
    change e.symm (e y) ∈ admissible at ha
    have hn := hh.2.2
    change e.symm (e y) ∈ N at hn
    rw [e.left_inv hy.1] at ha hn
    exact ⟨ha, hn⟩
  refine ⟨W, hW, hWcenter, hWsub, l, k, hlk, (henergy 0) ▸ hk, ?_⟩
  intro ρ hρ
  have huc := (isCompact_closedBall (0 : E) (2 * r)).uniformContinuousOn_of_continuous
    hinv.continuousOn
  obtain ⟨σ, hσ, hmetric⟩ := Metric.uniformContinuousOn_iff.mp huc ρ hρ
  obtain ⟨ζ, hζ, hcrossζ⟩ := hcross σ hσ
  refine ⟨ζ, hζ, ?_⟩
  intro ξ hξ hξζ p hp S hS hLow
  let p' : C(M, E) := ⟨fun x ↦ e (p x),
    e.continuousOn.comp_continuous p.continuous (fun x ↦ (hp x).1)⟩
  have hp' : ∀ x, p' x ∈ W₀ := fun x ↦ (hp x).2
  have hpEnergy (x) : f (p' x) = energy (p x) := by
    rw [henergy]
    exact congrArg energy (e.left_inv (hp x).1)
  obtain ⟨q', hq', G', hG'⟩ := hcrossζ ξ hξ hξζ p' hp' S hS
    (fun x hx ↦ by rw [hpEnergy]; exact hLow x hx)
  let inverse : C(E, Y) := ⟨e.symm, hinv⟩
  have hround : inverse.comp p' = p :=
    ContinuousMap.ext (fun x ↦ e.left_inv (hp x).1)
  let G : ContinuousMap.HomotopyRel p (inverse.comp q') S :=
    (G'.compContinuousMap inverse).cast hround rfl
  refine ⟨inverse.comp q', ?_, G, fun t x ↦ ?_⟩
  · intro x
    change energy (e.symm (q' x)) < k
    rw [← henergy]
    exact hq' x
  have hh := hG' t x
  refine ⟨hadm hh.1, ?_, hh.2.2.2.1.2, ?_, ?_⟩
  · change energy (e.symm (G' (t, x))) < energy (e.symm 0) + ε
    rw [← henergy, ← henergy]
    exact hh.2.1
  · change energy (e.symm (G' (t, x))) < energy (p x) + ξ
    rw [← henergy, ← hpEnergy x]
    exact hh.2.2.2.2.1
  intro hLoss
  have hLoss' : f (p' x) - f (G' (t, x)) ≤ 2 * ζ := by
    rw [hpEnergy, henergy]
    exact hLoss
  have hdist := hh.2.2.2.2.2 hLoss'
  have hleft : G' (t, x) ∈ Metric.closedBall (0 : E) (2 * r) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hh.2.2.1.le
  have hright : p' x ∈ Metric.closedBall (0 : E) (2 * r) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hW₀norm _ (hp' x)).le
  have ht := hmetric (G' (t, x)) hleft (p' x) hright hdist
  change dist (e.symm (G' (t, x))) (e.symm (e (p x))) < ρ at ht
  rwa [e.left_inv (hp x).1] at ht

end NoExoticSixSphere.PartialGradientCoordinates.LocalData

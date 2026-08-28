import Wikipedia.HopfProblem.OrbitPairSpherePolygonDescent
import Wikipedia.NoExoticSixSphere.CompactParameter
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniform actual descent on compact noncritical sphere polygon sets

Compactness makes both the admissibility interval and the negative energy
derivative uniform over the starting polygon. The mean value theorem then
gives a quantitative decrease of the actual energy over a positive time
interval, not just an infinitesimal descent direction.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace

variable {n m : ℕ}

theorem isOpen_descent_condition (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (C : Set (Space n m)) (hC : C ⊆ admissible (costDomain n) a b m) (c : ℝ) :
    IsOpen {p : ℝ × C | descent a b τ (p.2.1, p.1) ∈ admissible (costDomain n) a b m ∧
      descentRate a b τ (p.2.1, p.1) < -c} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hmap : Continuous (fun q : ℝ × C => (q.2.1, q.1)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst
  have hd : ContinuousAt (fun q : ℝ × C => descent a b τ (q.2.1, q.1)) p :=
    (continuousAt_descent a b τ (hC p.2.2)).comp hmap.continuousAt
  have hr0 : ContinuousAt (descentRate a b τ) (p.2.1, p.1) :=
    continuousAt_descentRate a b τ (p := (p.2.1, p.1)) (hC p.2.2) hp.1
  have hr : ContinuousAt (fun q : ℝ × C => descentRate a b τ (q.2.1, q.1)) p :=
    ContinuousAt.comp (f := fun q : ℝ × C => (q.2.1, q.1))
      (g := descentRate a b τ) hr0 hmap.continuousAt
  filter_upwards [hd.eventually ((isOpen_admissible (costDomain n) a b m).mem_nhds hp.1),
    hr.eventually (isOpen_Iio.mem_nhds hp.2)] with q hq hqr
  exact ⟨hq, hqr⟩

theorem exists_uniform_descent_rate (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (C : Set (Space n m)) (hC : IsCompact C) (ha : C ⊆ admissible (costDomain n) a b m)
    (hn : ∀ v ∈ C, mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0) :
    ∃ c > 0, ∃ T > 0, ∀ v ∈ C, ∀ s ∈ Icc (0 : ℝ) T,
      descent a b τ (v, s) ∈ admissible (costDomain n) a b m ∧ descentRate a b τ (v, s) < -c := by
  have hj : ContinuousOn (balanceSquareNorm a b τ) C :=
    fun v hv => (continuousAt_balanceSquareNorm a b τ (ha hv)).continuousWithinAt
  obtain ⟨c, hc, hlower⟩ := hC.exists_forall_le' hj
    (fun v hv => balanceSquareNorm_pos_of_noncritical a b τ v (ha hv) (hn v hv))
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have ho : IsOpen {s : ℝ | ∀ v : C,
      descent a b τ (v.1, s) ∈ admissible (costDomain n) a b m ∧ descentRate a b τ (v.1, s) < -c} :=
    isOpen_forall_compact (isOpen_descent_condition a b τ C ha c)
  have hzero : (0 : ℝ) ∈ {s : ℝ | ∀ v : C,
      descent a b τ (v.1, s) ∈ admissible (costDomain n) a b m ∧ descentRate a b τ (v.1, s) < -c} := by
    intro v
    rw [descent_zero, descentRate_zero]
    refine ⟨ha v.2, ?_⟩
    have hv := hlower v.1 v.2
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hzero)
  refine ⟨c, hc, ε / 2, by linarith, ?_⟩
  intro v hv s hs
  have hsball : s ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    linarith [hs.2]
  exact hball hsball ⟨v, hv⟩

theorem energy_descent_le_of_rate (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (c s : ℝ) (hs : 0 ≤ s)
    (ha : ∀ t ∈ Icc (0 : ℝ) s, descent a b τ (v, t) ∈ admissible (costDomain n) a b m)
    (hr : ∀ t ∈ Icc (0 : ℝ) s, descentRate a b τ (v, t) ≤ -c) :
    energy a b τ (descent a b τ (v, s)) ≤ energy a b τ v - c * s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [descent_zero]
  let f : ℝ → ℝ := fun t => energy a b τ (descent a b τ (v, t))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) s) :
      HasDerivAt f (descentRate a b τ (v, t)) t :=
    hasDerivAt_descent_energy a b τ v t (ha t ht)
  have hcont : ContinuousOn f (Icc (0 : ℝ) s) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Ioo (0 : ℝ) s) :=
    fun t ht => (hd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope f hs hcont hdiff
  have hrate : deriv f t ≤ -c := by
    rw [(hd t ⟨ht.1.le, ht.2.le⟩).deriv]
    exact hr t ⟨ht.1.le, ht.2.le⟩
  rw [he, sub_zero, div_le_iff₀ hs] at hrate
  have hz : f 0 = energy a b τ v := by simp [f, descent_zero]
  change f s ≤ energy a b τ v - c * s
  rw [hz] at hrate
  linarith

theorem exists_uniform_descent (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (C : Set (Space n m)) (hC : IsCompact C) (ha : C ⊆ admissible (costDomain n) a b m)
    (hn : ∀ v ∈ C, mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0) :
    ∃ c > 0, ∃ T > 0, ∀ v ∈ C, ∀ s ∈ Icc (0 : ℝ) T,
      descent a b τ (v, s) ∈ admissible (costDomain n) a b m ∧
        energy a b τ (descent a b τ (v, s)) ≤ energy a b τ v - c * s := by
  obtain ⟨c, hc, T, hT, hstep⟩ := exists_uniform_descent_rate a b τ C hC ha hn
  refine ⟨c, hc, T, hT, ?_⟩
  intro v hv s hs
  refine ⟨(hstep v hv s hs).1, energy_descent_le_of_rate a b τ v c s hs.1 ?_ ?_⟩
  · intro t ht
    exact (hstep v hv t ⟨ht.1, ht.2.trans hs.2⟩).1
  · intro t ht
    exact (hstep v hv t ⟨ht.1, ht.2.trans hs.2⟩).2.le

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

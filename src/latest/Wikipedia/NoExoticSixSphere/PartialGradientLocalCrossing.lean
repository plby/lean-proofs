import Wikipedia.NoExoticSixSphere.PartialGradientAvoidance
import Wikipedia.NoExoticSixSphere.PartialGradientSmallAvoidance
import Wikipedia.NoExoticSixSphere.PartialGradientEnergyAvoidance
import Wikipedia.NoExoticSixSphere.PartialGradientRadialDisplacement
import Wikipedia.NoExoticSixSphere.PartialGradientFiberDistance
import Wikipedia.NoExoticSixSphere.PartialGradientCrossingDomain
import Wikipedia.NoExoticSixSphere.EnergyHomotopyCutoff

/-!
# A local relative crossing of a critical energy

First perturb a lower-dimensional family off the partial-critical slice,
fixing its lower-energy part. Then use the radial homotopy with an energy
time cutoff. The concatenation remains in the admissible chart, satisfies a
prescribed energy cap, fixes the prescribed lower-energy parameter set, and
ends below the crossing threshold.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {B H M D E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

include I

theorem exists_crossing_homotopy_with_cost (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    (c : ℝ) (hc : 0 < c)
    (hcost : ∀ z ∈ C.radialDomain r, ∀ s : Set.Icc (0 : ℝ) 1,
      c * dist (C.radial r (s, z)) z ^ 2 ≤ f z - f (C.radial r (s, z)))
    (η ξ : ℝ) (hη : 0 < η) (hξ : 0 < ξ)
    (δ l k e : ℝ) (hlk : l < k)
    (hgap : ∀ z ∈ C.radialDomain r, f (C.radial r (1, z)) ≤ f (C.center z) - δ)
    (p : C(M, E)) (hp : ∀ x, p x ∈ C.crossingDomain r l (k + δ) e)
    (S : Set M) (hS : IsCompact S) (hLow : ∀ x ∈ S, f (p x) ≤ l)
    (hd : finrank ℝ B < finrank ℝ D) :
    ∃ q : C(M, E), (∀ x, f (q x) < k) ∧
      ∃ G : ContinuousMap.HomotopyRel p q S,
        ∀ t x, G (t, x) ∈ C.chart.source ∧ f (G (t, x)) < e ∧ ‖G (t, x)‖ < 2 * r ∧
          C.center (G (t, x)) = C.center (p x) ∧
          ‖p x - C.center (p x)‖ - η < ‖G (t, x) - C.center (G (t, x))‖ ∧
          f (G (t, x)) < f (p x) + ξ ∧
          (c / 2) * dist (G (t, x)) (p x) ^ 2 ≤
            c * η ^ 2 + f (p x) + ξ - f (G (t, x)) := by
  obtain ⟨q, hq, G₁, hG₁⟩ := C.exists_energy_small_gradient_avoiding_homotopy (I := I)
    hU hf.continuousOn p
    (C.crossingDomain r l (k + δ) e)
    (C.isOpen_crossingDomain hU hf.continuousOn r l (k + δ) e)
    (C.crossingDomain_subset_source r l (k + δ) e) hp η ξ hη hξ S hS
    (fun x hx ↦ C.crossingDomain_gradient_ne_zero r l (k + δ) e (hp x) (hLow x hx)) hd
  have hqDomain (x) : q x ∈ C.crossingDomain r l (k + δ) e := by
    have hh := (hG₁ 1 x).1
    simpa only [G₁.apply_one] using hh
  have hqCenter (x) : C.center (q x) = C.center (p x) := by
    simpa only [G₁.apply_one] using (hG₁ 1 x).2.2.1
  have hqClose (x) : dist (q x) (p x) < η := by
    simpa only [G₁.apply_one] using (hG₁ 1 x).2.2.2.1
  have hqEnergy (x) : f (q x) < f (p x) + ξ := by
    simpa only [G₁.apply_one] using (hG₁ 1 x).2.2.2.2
  have hG₁Cost (t) (x) : (c / 2) * dist (G₁ (t, x)) (p x) ^ 2 ≤
      c * η ^ 2 + f (p x) + ξ - f (G₁ (t, x)) := by
    have hsquare := pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist (G₁ (t, x)) (p x))
      (hG₁ t x).2.2.2.1.le 2
    have hh := mul_le_mul_of_nonneg_left hsquare (by linarith : 0 ≤ c / 2)
    have he := (hG₁ t x).2.2.2.2
    nlinarith [mul_nonneg hc.le (sq_nonneg η)]
  let qR : C(M, C.radialDomain r) := ⟨fun x ↦
    ⟨q x, C.crossingDomain_mem_radialDomain r l (k + δ) e (hqDomain x) (hq x)⟩,
    q.continuous.subtype_mk _⟩
  let energy : C(C.radialDomain r, ℝ) := ⟨fun z ↦ f z.1,
    hf.continuousOn.comp_continuous continuous_subtype_val
      (fun z ↦ C.source_subset z.2.1.1)⟩
  let R₀ := (C.radialHomotopy r hr hball).toHomotopy
  have hEnergy (s : Set.Icc (0 : ℝ) 1) (z : C.radialDomain r) :
      energy (R₀ (s, z)) ≤ energy z :=
    C.radialHomotopy_energy_le hU hf r hr hball s z
  let R := EnergyHomotopyCutoff.homotopy R₀ energy l k hlk.le
  let q' : C(M, E) := ⟨fun x ↦ (R (1, qR x)).1,
    continuous_subtype_val.comp (R.continuous.comp (continuous_const.prodMk qR.continuous))⟩
  let G₂ : ContinuousMap.HomotopyRel q q' S :=
    { toFun := fun tx ↦ (R (tx.1, qR tx.2)).1
      continuous_toFun := continuous_subtype_val.comp
        (R.continuous.comp (continuous_fst.prodMk (qR.continuous.comp continuous_snd)))
      map_zero_left := fun x ↦ by
        change (R (0, qR x)).1 = q x
        rw [R.apply_zero]
        rfl
      map_one_left := fun _ ↦ rfl
      prop' := fun t x hx ↦ by
        change (R (t, qR x)).1 = q x
        have hlow : energy (qR x) ≤ l := by
          change f (q x) ≤ l
          rw [← G₁.fst_eq_snd hx]
          exact hLow x hx
        exact congrArg Subtype.val (R.eq_fst t hlow) }
  have hG₂ (t) (x) : G₂ (t, x) ∈ C.chart.source ∧ f (G₂ (t, x)) < e ∧
      ‖G₂ (t, x)‖ < 2 * r := by
    refine ⟨(R (t, qR x)).2.1.1, ?_, C.norm_lt_of_mem_radialDomain r (R (t, qR x)).2⟩
    have he := EnergyHomotopyCutoff.energy_le R₀ energy l k hEnergy t (qR x)
    exact he.trans_lt (hqDomain x).2.2.2.2.2
  have hG₂Center (t) (x) : C.center (G₂ (t, x)) = C.center (p x) := by
    change C.center (C.radial r (EnergyHomotopyCutoff.time energy l k (t, qR x), q x)) = _
    exact (C.center_radial r (qR x).2 _).trans (hqCenter x)
  have hG₂Fiber (t) (x) : ‖p x - C.center (p x)‖ - η <
      ‖G₂ (t, x) - C.center (G₂ (t, x))‖ := by
    change ‖p x - C.center (p x)‖ - η <
      ‖C.radial r (EnergyHomotopyCutoff.time energy l k (t, qR x), q x) -
        C.center (C.radial r (EnergyHomotopyCutoff.time energy l k (t, qR x), q x))‖
    exact C.radial_fiber_norm_gt_of_close r (qR x).2 (hqCenter x) (hqClose x) _
  have hG₂Energy (t) (x) : f (G₂ (t, x)) < f (p x) + ξ := by
    have hh : f (G₂ (t, x)) ≤ f (q x) :=
      EnergyHomotopyCutoff.energy_le R₀ energy l k hEnergy t (qR x)
    exact hh.trans_lt (hqEnergy x)
  have hG₂Cost (t) (x) : (c / 2) * dist (G₂ (t, x)) (p x) ^ 2 ≤
      c * η ^ 2 + f (p x) + ξ - f (G₂ (t, x)) := by
    have hrad : c * dist (G₂ (t, x)) (q x) ^ 2 ≤ f (q x) - f (G₂ (t, x)) :=
      hcost (q x) (qR x).2 (EnergyHomotopyCutoff.time energy l k (t, qR x))
    have htri : dist (G₂ (t, x)) (p x) ≤ dist (G₂ (t, x)) (q x) + η :=
      (dist_triangle (G₂ (t, x)) (q x) (p x)).trans (add_le_add le_rfl (hqClose x).le)
    have hsquare := pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist (G₂ (t, x)) (p x)) htri 2
    have htwo : dist (G₂ (t, x)) (p x) ^ 2 ≤ 2 * dist (G₂ (t, x)) (q x) ^ 2 + 2 * η ^ 2 := by
      nlinarith [sq_nonneg (dist (G₂ (t, x)) (q x) - η)]
    have hh := mul_le_mul_of_nonneg_left htwo (by linarith : 0 ≤ c / 2)
    have he := hqEnergy x
    nlinarith
  refine ⟨q', fun x ↦ ?_, G₁.trans G₂, fun t x ↦ ?_⟩
  · have hbelow : energy (C.radialEndpoint r hr hball (qR x)) < k := by
      change f (C.radial r (1, q x)) < k
      have hh := hgap (q x) (qR x).2
      have hb := (hqDomain x).2.2.2.2.1
      linarith
    exact EnergyHomotopyCutoff.endpoint_lt R₀ energy l k hlk hEnergy hbelow
  · rw [ContinuousMap.HomotopyRel.trans_apply]
    split_ifs
    · exact ⟨(hG₁ _ x).1.1.1, (hG₁ _ x).1.2.2.2.2.2,
        C.norm_lt_of_mem_crossingDomain r l (k + δ) e (hG₁ _ x).1,
        (hG₁ _ x).2.2.1,
        C.fiber_norm_gt_of_dist_lt (hG₁ _ x).2.2.1 (hG₁ _ x).2.2.2.1,
        (hG₁ _ x).2.2.2.2, hG₁Cost _ x⟩
    · exact ⟨(hG₂ _ x).1, (hG₂ _ x).2.1, (hG₂ _ x).2.2, hG₂Center _ x, hG₂Fiber _ x,
        hG₂Energy _ x, hG₂Cost _ x⟩

theorem exists_crossing_homotopy_with_fiber_control (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    (η : ℝ) (hη : 0 < η)
    (δ l k e : ℝ) (hlk : l < k)
    (hgap : ∀ z ∈ C.radialDomain r, f (C.radial r (1, z)) ≤ f (C.center z) - δ)
    (p : C(M, E)) (hp : ∀ x, p x ∈ C.crossingDomain r l (k + δ) e)
    (S : Set M) (hS : IsCompact S) (hLow : ∀ x ∈ S, f (p x) ≤ l)
    (hd : finrank ℝ B < finrank ℝ D) :
    ∃ q : C(M, E), (∀ x, f (q x) < k) ∧
      ∃ G : ContinuousMap.HomotopyRel p q S,
        ∀ t x, G (t, x) ∈ C.chart.source ∧ f (G (t, x)) < e ∧ ‖G (t, x)‖ < 2 * r ∧
          C.center (G (t, x)) = C.center (p x) ∧
          ‖p x - C.center (p x)‖ - η < ‖G (t, x) - C.center (G (t, x))‖ := by
  obtain ⟨c, hc, hcost⟩ := C.exists_radial_displacement_bound hU hf
  obtain ⟨q, hq, G, hG⟩ := C.exists_crossing_homotopy_with_cost (I := I) hU hf r hr hball
    c hc (hcost r hr hball) η 1 hη zero_lt_one δ l k e hlk hgap p hp S hS hLow hd
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1, (hG t x).2.2.1,
    (hG t x).2.2.2.1, (hG t x).2.2.2.2.1⟩⟩

theorem exists_crossing_homotopy_with_norm (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    (δ l k e : ℝ) (hlk : l < k)
    (hgap : ∀ z ∈ C.radialDomain r, f (C.radial r (1, z)) ≤ f (C.center z) - δ)
    (p : C(M, E)) (hp : ∀ x, p x ∈ C.crossingDomain r l (k + δ) e)
    (S : Set M) (hS : IsCompact S) (hLow : ∀ x ∈ S, f (p x) ≤ l)
    (hd : finrank ℝ B < finrank ℝ D) :
    ∃ q : C(M, E), (∀ x, f (q x) < k) ∧
      ∃ G : ContinuousMap.HomotopyRel p q S,
        ∀ t x, G (t, x) ∈ C.chart.source ∧ f (G (t, x)) < e ∧ ‖G (t, x)‖ < 2 * r := by
  obtain ⟨q, hq, G, hG⟩ := C.exists_crossing_homotopy_with_fiber_control (I := I)
    hU hf r hr hball 1 zero_lt_one δ l k e hlk hgap p hp S hS hLow hd
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1, (hG t x).2.2.1⟩⟩

theorem exists_crossing_homotopy (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    (δ l k e : ℝ) (hlk : l < k)
    (hgap : ∀ z ∈ C.radialDomain r, f (C.radial r (1, z)) ≤ f (C.center z) - δ)
    (p : C(M, E)) (hp : ∀ x, p x ∈ C.crossingDomain r l (k + δ) e)
    (S : Set M) (hS : IsCompact S) (hLow : ∀ x ∈ S, f (p x) ≤ l)
    (hd : finrank ℝ B < finrank ℝ D) :
    ∃ q : C(M, E), (∀ x, f (q x) < k) ∧
      ∃ G : ContinuousMap.HomotopyRel p q S,
        ∀ t x, G (t, x) ∈ C.chart.source ∧ f (G (t, x)) < e := by
  obtain ⟨q, hq, G, hG⟩ := C.exists_crossing_homotopy_with_norm (I := I) hU hf r hr hball
    δ l k e hlk hgap p hp S hS hLow hd
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1⟩⟩

theorem exists_local_crossing_neighborhood (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < finrank ℝ D) :
    ∃ V : Set E, IsOpen V ∧ (0 : E) ∈ V ∧ V ⊆ C.chart.source ∧
      ∃ l k : ℝ, l < k ∧ k < f 0 ∧
        ∀ (p : C(M, E)), (∀ x, p x ∈ V) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, f (p x) ≤ l) →
            ∃ q : C(M, E), (∀ x, f (q x) < k) ∧
              ∃ G : ContinuousMap.HomotopyRel p q S,
                ∀ t x, G (t, x) ∈ C.chart.source ∧ f (G (t, x)) < f 0 + ε := by
  obtain ⟨r, hr, hball⟩ := C.exists_radial_radius
  obtain ⟨δ, hδ, hgap⟩ := C.exists_radial_endpoint_gap hU hf r hr hball
  let l := f 0 - 3 * δ / 4
  let k := f 0 - δ / 2
  have hlk : l < k := by dsimp [l, k]; linarith
  let V := C.crossingDomain r l (k + δ) (f 0 + ε)
  refine ⟨V, C.isOpen_crossingDomain hU hf.continuousOn r l (k + δ) (f 0 + ε),
    C.zero_mem_crossingDomain r l (k + δ) (f 0 + ε) hr
      (by dsimp [l]; linarith) (by dsimp [k]; linarith) (by linarith),
    C.crossingDomain_subset_source r l (k + δ) (f 0 + ε), l, k, hlk,
    (by dsimp [k]; linarith), ?_⟩
  intro p hp S hS hLow
  exact C.exists_crossing_homotopy (I := I) hU hf r hr hball δ l k (f 0 + ε) hlk
    hgap p hp S hS hLow hd

end NoExoticSixSphere.PartialGradientCoordinates.LocalData

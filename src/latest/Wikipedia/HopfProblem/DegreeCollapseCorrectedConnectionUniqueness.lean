import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins
import Wikipedia.HopfProblem.DegreeCollapseNativeBlockHolonomy

/-!
# Complete connection uniqueness from the corrected native cylinder

The full corrected flow chart puts every internal connection through its
zero and one sections. The actual retained exterior half-orbits transfer
their endpoint limits to the original flow. Exact endpoint basin labels
then give the proved finite plane intersection. Exterior orbits are
unchanged and cannot create another connection outside the cylinder.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {A B Z E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem corrected_cylinder_unique_connection
    (Φ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (h0U : (0 : Z) ∈ U)
    (hΦsource : Φ.source = U ×ˢ univ) (hΩsource : Ω.source = U ×ˢ univ)
    (hΩtarget : Ω.target = Φ.target)
    (F G : Flow ℝ M)
    (hΦflow : ∀ z ∈ U, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0)))
    (hΩflow : ∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0)))
    (hΩsection : ∀ z ∈ U, ∃ w ∈ U, Ω (z, 1) = Φ (w, 1))
    (hleft : ∀ z ∈ U, ∀ t : ℝ, t ≤ 0 → G t (Φ (z, 0)) = F t (Φ (z, 0)))
    (hright : ∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → G t (Ω (z, 1)) = F t (Ω (z, 1)))
    (hout : ∀ x ∉ Φ.target, ∀ t, G t x = F t x)
    (Q P : (A × B) → Z) (hQ0 : Q 0 = 0) (S T : Set (A × B)) {p q : M}
    (hleftBasin : ∀ z ∈ U, Tendsto (fun t => F t (Φ (z, 0))) atBot (𝓝 q) ↔
      ∃ x : A, (x, (0 : B)) ∈ S ∧ Q (x, 0) = z)
    (hrightBasin : ∀ z ∈ U, Tendsto (fun t => F t (Φ (z, 1))) atTop (𝓝 p) ↔
      ∃ y ∈ T, y.1 = 0 ∧ P y = z)
    (hsection : ∀ x : A, (x, (0 : B)) ∈ S → ∀ y ∈ T, y.1 = 0 →
      Ω (Q (x, 0), 1) = Φ (P y, 1) → x = 0 ∧ y = 0)
    (hold : ∀ x, Tendsto (fun t => F t x) atBot (𝓝 q) →
      Tendsto (fun t => F t x) atTop (𝓝 p) → ∃ t, F t (Φ (0, 0)) = x) :
    ∀ x, Tendsto (fun t => G t x) atBot (𝓝 q) →
      Tendsto (fun t => G t x) atTop (𝓝 p) → ∃ t, G t (Φ (0, 0)) = x := by
  intro x hbot htop
  by_cases hx : x ∈ Φ.target
  · have hxΩ : x ∈ Ω.target := hΩtarget.symm ▸ hx
    let w := Ω.symm x
    have hw : w ∈ Ω.source := Ω.map_target' hxΩ
    have hwU : w.1 ∈ U := by rw [hΩsource] at hw; exact hw.1
    have hpoint : x = G w.2 (Φ (w.1, 0)) := by
      calc
        x = Ω w := (Ω.right_inv' hxΩ).symm
        _ = G w.2 (Φ (w.1, 0)) := hΩflow w.1 hwU w.2
    have hbot0 : Tendsto (fun t => G t (Φ (w.1, 0))) atBot (𝓝 q) := by
      apply (MorseCancellation.flow_time_atBot_limit_iff G w.2 (Φ (w.1, 0)) q).mp
      rwa [← hpoint]
    have htop0 : Tendsto (fun t => G t (Φ (w.1, 0))) atTop (𝓝 p) := by
      apply (MorseCancellation.flow_time_atTop_limit_iff G w.2 (Φ (w.1, 0)) p).mp
      rwa [← hpoint]
    have htop1 : Tendsto (fun t => G t (Ω (w.1, 1))) atTop (𝓝 p) := by
      rw [hΩflow w.1 hwU 1]
      exact (MorseCancellation.flow_time_atTop_limit_iff G 1 (Φ (w.1, 0)) p).mpr htop0
    have hbotF : Tendsto (fun t => F t (Φ (w.1, 0))) atBot (𝓝 q) := by
      apply hbot0.congr'
      filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
      exact hleft w.1 hwU t ht
    have htopF : Tendsto (fun t => F t (Ω (w.1, 1))) atTop (𝓝 p) := by
      apply htop1.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hright w.1 hwU t ht
    obtain ⟨a, ha, hQa⟩ := (hleftBasin w.1 hwU).mp hbotF
    obtain ⟨v, hv, hΩv⟩ := hΩsection w.1 hwU
    rw [hΩv] at htopF
    obtain ⟨y, hy, hy0, hPy⟩ := (hrightBasin v hv).mp htopF
    have hcross : Ω (Q (a, 0), 1) = Φ (P y, 1) := by rw [hQa, hPy]; exact hΩv
    have ha0 := (hsection a ha y hy hy0 hcross).1
    have hw0 : w.1 = 0 := by
      rw [← hQa, ha0]
      exact hQ0
    refine ⟨w.2, ?_⟩
    rw [hpoint, hw0]
  · have hbotF : Tendsto (fun t => F t x) atBot (𝓝 q) :=
      hbot.congr' (Eventually.of_forall (hout x hx))
    have htopF : Tendsto (fun t => F t x) atTop (𝓝 p) :=
      htop.congr' (Eventually.of_forall (hout x hx))
    obtain ⟨t, ht⟩ := hold x hbotF htopF
    have hsource : (0, t) ∈ Φ.source := by rw [hΦsource]; exact ⟨h0U, mem_univ _⟩
    have hxt : x ∈ Φ.target := by
      rw [← ht, ← hΦflow 0 h0U t]
      exact Φ.map_source' hsource
    exact (hx hxt).elim

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

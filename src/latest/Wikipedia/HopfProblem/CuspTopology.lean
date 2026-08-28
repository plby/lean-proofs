import Wikipedia.HopfProblem.CuspProper
import Mathlib.Analysis.Convex.PathConnected

/-!
# Connectedness and countability of the cusp quotient

Each affine tube is star-shaped. Their images all meet at a nonzero torus
point, so the tube and its quotient are connected. The quotient is second
countable because its covering projection is open.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricSpace

def affineTube (ε : ℝ) : Set (CoordinateSpace 3) :=
  {z | ‖Triangle.time z‖ < ε}

theorem affineTube_starConvex (ε : ℝ) : StarConvex ℝ 0 (affineTube ε) := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  simp only [smul_zero, zero_add]
  change ‖Triangle.time (b • z)‖ < ε
  have he : ‖Triangle.time (b • z)‖ = b ^ 3 * ‖Triangle.time z‖ := by
    simp only [Triangle.time, Pi.smul_apply, norm_mul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hb]
    ring
  rw [he]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hb hb1)).trans_lt hz

theorem affineTube_connected {ε : ℝ} (hε : 0 < ε) : IsConnected (affineTube ε) :=
  ((affineTube_starConvex ε).isPathConnected
    (by simpa [affineTube, Triangle.time] using hε)).isConnected

theorem tube_eq_union (ε : ℝ) :
    (tubeOpen (disc ε) : Set Space) = ⋃ s : Triangle, inclusion s '' affineTube ε := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
    refine mem_iUnion.mpr ⟨s, z, ?_, rfl⟩
    have he : time (inclusion s z) ∈ Metric.ball 0 ε := hx
    simpa only [affineTube, Set.mem_ofPred_eq, time_inclusion,
      Metric.mem_ball, dist_zero_right] using he
  · intro hx
    obtain ⟨s, z, hz, rfl⟩ := mem_iUnion.mp hx
    change time (inclusion s z) ∈ Metric.ball 0 ε
    simpa only [affineTube, Set.mem_ofPred_eq,
      time_inclusion, Metric.mem_ball, dist_zero_right] using hz

theorem tube_charts_common_point {ε : ℝ} (hε : 0 < ε) :
    (⋂ s : Triangle, inclusion s '' affineTube ε).Nonempty := by
  let x := inclusion referenceTriangle ![((ε / 2 : ℝ) : ℂ), 1, 1]
  have hxT : x ∈ openTorus := by
    apply inclusion_torus_subset referenceTriangle
    refine ⟨_, ?_, rfl⟩
    intro i
    fin_cases i
    · change ((ε / 2 : ℝ) : ℂ) ≠ 0
      exact_mod_cast (half_pos hε).ne'
    · exact one_ne_zero
    · exact one_ne_zero
  have hxt : ‖time x‖ < ε := by
    simpa [x, Triangle.time, abs_of_pos hε] using half_lt_self hε
  refine ⟨x, mem_iInter.mpr fun s => ?_⟩
  obtain ⟨z, _, he⟩ := exists_torus_chart s hxT
  refine ⟨z, ?_, he⟩
  change ‖Triangle.time z‖ < ε
  rw [← time_inclusion s z, he]
  exact hxt

theorem tube_connected {ε : ℝ} (hε : 0 < ε) : ConnectedSpace (Tube (disc ε)) := by
  apply isConnected_iff_connectedSpace.mp
  have hpre : IsPreconnected (⋃ s : Triangle, inclusion s '' affineTube ε) :=
    isPreconnected_iUnion (tube_charts_common_point hε)
      (fun s => (affineTube_connected hε).isPreconnected.image _
        (inclusion_openEmbedding s).continuous.continuousOn)
  rw [← tube_eq_union] at hpre
  refine ⟨⟨inclusion referenceTriangle 0, ?_⟩, hpre⟩
  change time (inclusion referenceTriangle 0) ∈ Metric.ball 0 ε
  simpa [Triangle.time] using hε

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

theorem quotient_connected (hε : 0 < ε) : ConnectedSpace (QuotientSpace C ε) := by
  let := tube_connected hε
  infer_instance

theorem quotient_secondCountable (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) : SecondCountableTopology (QuotientSpace C ε) := by
  let := tubeAction C (disc ε)
  have hq := quotientMap_covering C ε hε hε1 hC hR
  exact hq.toIsQuotientMap.secondCountableTopology hq.isCoveringMap.isOpenMap

end Wikipedia.HopfProblem.CuspQuotient

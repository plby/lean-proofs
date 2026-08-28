import Wikipedia.HopfProblem.ToricBounds
import Mathlib.Topology.Covering.Quotient

/-!
# Proper discontinuity of the cusp action

Position bounds give finiteness of the lattice translates meeting any two
fixed bounded chart neighbourhoods. Density of the torus extends the argument
to neighbourhoods of the central fibre; a finite subcover then handles all
compact subsets of the tube.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

def SmallDrift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) : Prop :=
  ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ε → entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4

def chartNeighbourhood (s : Triangle) (n : ℕ) (ε : ℝ) : Set Space :=
  inclusion s '' {z : CoordinateSpace 3 |
    (∀ j, ‖z j‖ < (n : ℝ) + 2) ∧ ‖Triangle.time z‖ < ε}

theorem chartNeighbourhood_open (s : Triangle) (n : ℕ) (ε : ℝ) :
    IsOpen (chartNeighbourhood s n ε) := by
  apply (inclusion_openEmbedding s).isOpenMap
  have hc : IsOpen {z : CoordinateSpace 3 | ∀ j, ‖z j‖ < (n : ℝ) + 2} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (continuous_apply j).norm continuous_const
  exact hc.inter (isOpen_lt Triangle.time_holomorphic.continuous.norm continuous_const)

theorem chartNeighbourhood_time {s : Triangle} {n : ℕ} {ε : ℝ} {x : Space}
    (hx : x ∈ chartNeighbourhood s n ε) : ‖time x‖ < ε := by
  obtain ⟨z, hz, rfl⟩ := hx
  simpa only [time_inclusion] using hz.2

theorem chartNeighbourhood_cover {ε : ℝ} {x : Space} (hx : ‖time x‖ < ε) :
    ∃ s n, x ∈ chartNeighbourhood s n ε := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  refine ⟨s, n, z, ⟨?_, by simpa using hx⟩, rfl⟩
  intro j
  have h := norm_le_pi_norm z j
  linarith

def chartTranslates (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s t : Triangle) (n m : ℕ) : Set (Fin 2 → ℤ) :=
  {v | (chartNeighbourhood s n ε ∩ twistedTranslate C v ⁻¹' chartNeighbourhood t m ε).Nonempty}

theorem chartTranslates_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (s t : Triangle) (n m : ℕ) :
    (chartTranslates C ε s t n m).Finite := by
  apply (lattice_bounded_finite
    (2 * (positionBound s ((n : ℝ) + 2) ε + positionBound t ((m : ℝ) + 2) ε))).subset
  intro v hv
  have hcont : ContinuousOn (twistedTranslate C v) (chartNeighbourhood s n ε) :=
    (twistedTranslate_holomorphic C v Metric.isOpen_ball hC).continuousOn.mono (by
      intro x hx
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using
        chartNeighbourhood_time hx)
  have hV := hcont.isOpen_inter_preimage (chartNeighbourhood_open s n ε)
    (chartNeighbourhood_open t m ε)
  obtain ⟨p, hpT, hpV⟩ := openTorus_dense.exists_mem_open hV hv
  obtain ⟨z, hz, rfl⟩ := hpV.1
  have hzT : z ∈ torus := by
    rw [← inclusion_preimage_openTorus s]
    exact hpT
  obtain ⟨w, hw, hew⟩ := hpV.2
  have hwT : w ∈ torus := by
    rw [← inclusion_preimage_openTorus t]
    change inclusion t w ∈ openTorus
    rw [hew, mem_openTorus_iff, time_twistedTranslate]
    exact (mem_openTorus_iff _).mp hpT
  have ht : 0 < ‖time (inclusion s z)‖ := norm_pos_iff.mpr ((mem_openTorus_iff _).mp hpT)
  have htime : ‖time (inclusion s z)‖ < ε := by simpa only [time_inclusion] using hz.2
  have hvbound := lattice_bound_of_small_drift C v hpT
    (Real.log_neg ht (htime.trans hε1)) (hR _ ht htime)
  have hpbound := position_norm_bound s hzT
    (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith : (1 : ℝ) ≤ n + 2)
    hε hε1 hz.2 (fun j => (hz.1 j).le)
  have hqbound := position_norm_bound t hwT
    (by have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m; linarith : (1 : ℝ) ≤ m + 2)
    hε hε1 hw.2 (fun j => (hw.1 j).le)
  rw [hew] at hqbound
  have hd := norm_sub_le (position (twistedTranslate C v (inclusion s z)))
    (position (inclusion s z))
  change ‖latticeReal v‖ ≤ _
  linarith

theorem compact_translates_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) {K : Set Space} (hK : IsCompact K)
    (hKt : ∀ x ∈ K, ‖time x‖ < ε) :
    {v : Fin 2 → ℤ | (twistedTranslate C v '' K ∩ K).Nonempty}.Finite := by
  let U : Triangle × ℕ → Set Space := fun i => chartNeighbourhood i.1 i.2 ε
  have hcover : K ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨s, n, hn⟩ := chartNeighbourhood_cover (hKt x hx)
    exact mem_iUnion.mpr ⟨(s, n), hn⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover U (fun i => chartNeighbourhood_open _ _ _) hcover
  have hfinite : (⋃ i ∈ I, ⋃ j ∈ I, chartTranslates C ε i.1 j.1 i.2 j.2).Finite :=
    I.finite_toSet.biUnion fun i _ => I.finite_toSet.biUnion fun j _ =>
      chartTranslates_finite C hε hε1 hC hR i.1 j.1 i.2 j.2
  apply hfinite.subset
  rintro v ⟨q, ⟨p, hp, hpq⟩, hq⟩
  obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp (hI hp)
  obtain ⟨j, hj, hqj⟩ := mem_iUnion₂.mp (hI hq)
  apply mem_iUnion₂.mpr ⟨i, hi, ?_⟩
  apply mem_iUnion₂.mpr ⟨j, hj, ?_⟩
  exact ⟨p, hpi, by simpa only [Set.mem_preimage, hpq] using hqj⟩

theorem SmallDrift.mono {C : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {ε δ : ℝ}
    (h : SmallDrift C ε) (hδε : δ ≤ ε) : SmallDrift C δ :=
  fun t ht hδ => h t ht (hδ.trans_le hδε)

/-- Continuity of the supplied matrix at the cusp actually supplies a
small-drift radius; the quantitative hypothesis is not postulated. -/
theorem exists_smallDrift_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (hC : ∀ i j, ContinuousAt (fun t => C t i j) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ SmallDrift C ε := by
  have hentries : ContinuousAt (fun t : ℂ => fun i : Fin 2 => fun j : Fin 2 =>
      driftMatrix C t i j) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact continuousAt_const.mul (Complex.continuous_im.continuousAt.comp (hC i j))
  have hnorm : ContinuousAt (fun t => entryNorm (driftMatrix C t)) 0 := hentries.norm
  let M := entryNorm (driftMatrix C 0) + 1
  have hM : entryNorm (driftMatrix C 0) < M := by dsimp [M]; linarith
  have hevent : ∀ᶠ t in 𝓝 (0 : ℂ), entryNorm (driftMatrix C t) < M :=
    hnorm (gt_mem_nhds hM)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hevent
  let ε := min δ (min (1 / 2) (Real.exp (-4 * M)))
  have hε : 0 < ε := lt_min hδ (lt_min (by norm_num) (Real.exp_pos _))
  refine ⟨ε, hε, lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num), ?_⟩
  intro t ht htε
  have htδ : dist t 0 < δ := by
    simpa only [dist_zero_right] using htε.trans_le (min_le_left _ _)
  have hbound := hδbound htδ
  have hlog : Real.log ‖t‖ ≤ -4 * M := by
    have hsmall : ‖t‖ ≤ Real.exp (-4 * M) :=
      htε.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [Real.log_exp] using Real.log_le_log ht hsmall
  linarith

end Wikipedia.HopfProblem.ToricSpace

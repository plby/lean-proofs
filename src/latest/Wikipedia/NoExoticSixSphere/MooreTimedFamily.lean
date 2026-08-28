import Wikipedia.NoExoticSixSphere.MooreLoopTopology

/-!
# Continuous loop families whose duration can vanish

Reparameterizing by a vanishing duration is continuous provided that the
corresponding unit-interval loop is constant. Compactness of the time
interval gives continuity at the apparent division singularity. This is
what allows the basepoint generator of a James word to have duration zero.
-/

noncomputable section

open Set Filter Topology
open scoped unitInterval

namespace NoExoticSixSphere.Moore

variable {X K Y : Type*} [TopologicalSpace X] [TopologicalSpace K] [TopologicalSpace Y]

theorem continuousAt_arbitrary_evaluation_of_const [CompactSpace K]
    (f : X → C(K, Y)) {x₀ : X} (hf : ContinuousAt f x₀)
    (y₀ : Y) (hconst : ∀ k, f x₀ k = y₀) (k : X → K) :
    ContinuousAt (fun x ↦ f x (k x)) x₀ := by
  apply continuousAt_def.mpr
  intro U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  have hmap : MapsTo (f x₀) univ V := by
    intro t _
    rw [hconst t, ← hconst (k x₀)]
    exact hxV
  have he := hf.eventually (ContinuousMap.eventually_mapsTo isCompact_univ hV hmap)
  filter_upwards [he] with x hx
  exact hVU (hx (mem_univ (k x)))

namespace Loop

variable {y₀ : Y}

def timed (c : X → Path y₀ y₀) (d : X → ℝ) (hn : ∀ x, 0 ≤ d x) (x : X) : Loop y₀ := by
  let f : C(ℝ, Y) := (c x).extend.comp ⟨fun t ↦ t / d x, continuous_id.div_const _⟩
  refine ⟨(d x, f), hn x, ?_, ?_⟩
  · intro t ht
    exact (c x).extend_of_le_zero (div_nonpos_of_nonpos_of_nonneg ht (hn x))
  · intro t ht
    change (c x).extend (t / d x) = y₀
    by_cases hx : d x = 0
    · rw [hx, div_zero, Path.extend_zero]
    · have hp : 0 < d x := lt_of_le_of_ne (hn x) (Ne.symm hx)
      apply (c x).extend_of_one_le
      exact (le_div_iff₀ hp).mpr (by simpa only [one_mul] using ht)

omit [TopologicalSpace X] in
theorem duration_timed (c : X → Path y₀ y₀) (d : X → ℝ) (hn : ∀ x, 0 ≤ d x) (x : X) :
    (timed c d hn x).duration = d x := rfl

omit [TopologicalSpace X] in
theorem curve_timed (c : X → Path y₀ y₀) (d : X → ℝ) (hn : ∀ x, 0 ≤ d x)
    (x : X) (t : ℝ) : (timed c d hn x).curve t = (c x).extend (t / d x) := rfl

omit [TopologicalSpace X] in
theorem timed_eq_one_of_zero (c : X → Path y₀ y₀) (d : X → ℝ) (hn : ∀ x, 0 ≤ d x)
    (x : X) (hx : d x = 0) : timed c d hn x = 1 := by
  apply ext
  · exact hx
  · intro t
    rw [curve_timed, hx, div_zero, Path.extend_zero, curve_one]

omit [TopologicalSpace X] in
theorem toPath_timed (c : X → Path y₀ y₀) (d : X → ℝ) (hn : ∀ x, 0 ≤ d x)
    (x : X) (hzero : d x = 0 → c x = Path.refl y₀) : toPath (timed c d hn x) = c x := by
  by_cases hx : d x = 0
  · rw [timed_eq_one_of_zero c d hn x hx, toPath_one, hzero hx]
  · apply Path.ext
    funext t
    change (c x).extend (d x * (t : ℝ) / d x) = c x t
    rw [mul_div_cancel_left₀ (t : ℝ) hx]
    exact (c x).extend_extends' t

theorem continuous_timed_evaluation (c : X → Path y₀ y₀) (hc : Continuous c)
    (d : X → ℝ) (hd : Continuous d) (hzero : ∀ x, d x = 0 → c x = Path.refl y₀) :
    Continuous (fun u : X × ℝ ↦ (c u.1).extend (u.2 / d u.1)) := by
  have hcm : Continuous (fun u : X × ℝ ↦ (c u.1).toContinuousMap) :=
    continuous_induced_dom.comp (hc.comp continuous_fst)
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hz : d u.1 = 0
  · apply continuousAt_arbitrary_evaluation_of_const
      (fun v : X × ℝ ↦ (c v.1).toContinuousMap) hcm.continuousAt y₀
      (fun t ↦ ?_) (fun v ↦ projIcc 0 1 zero_le_one (v.2 / d v.1))
    change c u.1 t = y₀
    rw [hzero u.1 hz]
    rfl
  · have ht : ContinuousAt (fun v : X × ℝ ↦ v.2 / d v.1) u :=
      continuous_snd.continuousAt.div (hd.comp continuous_fst).continuousAt hz
    have hk : ContinuousAt
        (fun v : X × ℝ ↦ projIcc (0 : ℝ) 1 zero_le_one (v.2 / d v.1)) u :=
      continuous_projIcc.continuousAt.comp ht
    exact continuous_eval.continuousAt.comp (hcm.continuousAt.prodMk hk)

theorem continuous_timed (c : X → Path y₀ y₀) (hc : Continuous c) (d : X → ℝ)
    (hd : Continuous d) (hn : ∀ x, 0 ≤ d x)
    (hzero : ∀ x, d x = 0 → c x = Path.refl y₀) : Continuous (timed c d hn) := by
  have hcurve : Continuous (fun x ↦ (timed c d hn x).curve) :=
    ContinuousMap.continuous_of_continuous_uncurry _
      (continuous_timed_evaluation c hc d hd hzero)
  exact (hd.prodMk hcurve).subtype_mk _

end Loop

end NoExoticSixSphere.Moore

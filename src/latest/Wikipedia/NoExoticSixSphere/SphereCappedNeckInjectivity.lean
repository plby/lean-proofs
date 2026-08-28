import Wikipedia.NoExoticSixSphere.SphereSumCappedNeckImmersion

/-!
# Global injectivity and exact axis loci of the capped neck

For positive opening, one radial component is positive at every parameter.
Its norm determines time by strict monotonicity, and its direction then
determines the sphere coordinate. Thus the whole capped neck is injective,
not only immersive. Positive scaling and restriction to the actual target
chart preserve this injectivity.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem norm_capProfile_smul (a : ℝ) (q : Parameter) :
    ‖capProfile a q.1 • q.2.val‖ = capProfile a q.1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (capProfile_nonneg a q.1),
    ClosedHemisphere.unit_norm, mul_one]

theorem capProfile_smul_injective {a : ℝ} (ha : 0 ≤ a) {q w : Parameter}
    (hq : -a < q.1) (he : capProfile a q.1 • q.2.val = capProfile a w.1 • w.2.val) : q = w := by
  have hr : capProfile a q.1 = capProfile a w.1 := by
    simpa only [norm_capProfile_smul] using congrArg norm he
  have hw : -a < w.1 := (capProfile_pos_iff ha w.1).mp (hr ▸ capProfile_pos hq)
  have ht : q.1 = w.1 := (capProfile_strictMonoOn a).injOn hq hw hr
  have hv := congrArg (fun v : Vector 3 ↦ (capProfile a q.1)⁻¹ • v) he
  rw [← ht, inv_smul_smul₀ (capProfile_pos hq).ne',
    inv_smul_smul₀ (capProfile_pos hq).ne'] at hv
  exact Prod.ext ht (Subtype.ext hv)

theorem capPair_injective {a : ℝ} (ha : 0 < a) : Injective (capPair a) := by
  intro q w he
  by_cases hq : -a < q.1
  · exact capProfile_smul_injective ha.le hq (congrArg Prod.fst he)
  · have hq' : -a < (reverse q).1 := by dsimp [reverse]; linarith
    exact reverse_involutive.injective
      (capProfile_smul_injective ha.le hq' (congrArg Prod.snd he))

theorem scaledCapPair_injective {ε a : ℝ} (hε : ε ≠ 0) (ha : 0 < a) :
    Injective (scaledCapPair ε a) := by
  intro q w he
  apply capPair_injective ha
  have h := congrArg (fun v : Vector 3 × Vector 3 ↦ ε⁻¹ • v) he
  simpa only [scaledCapPair, inv_smul_smul₀ hε] using h

theorem capPair_fst_eq_zero_iff {a : ℝ} (ha : 0 ≤ a) (q : Parameter) :
    (capPair a q).1 = 0 ↔ q.1 ≤ -a := by
  change capProfile a q.1 • q.2.val = 0 ↔ _
  rw [smul_eq_zero, or_iff_left (ne_zero_of_mem_unit_sphere q.2), capProfile_zero_iff ha]

theorem capPair_snd_eq_zero_iff {a : ℝ} (ha : 0 ≤ a) (q : Parameter) :
    (capPair a q).2 = 0 ↔ a ≤ q.1 := by
  change capProfile a (-q.1) • q.2.val = 0 ↔ _
  rw [smul_eq_zero, or_iff_left (ne_zero_of_mem_unit_sphere q.2), capProfile_zero_iff ha]
  constructor <;> intro h <;> linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

theorem chartCapNeck_injOn {ε a R : ℝ} (hε : 0 < ε) (ha : 0 < a) (hR : 1 ≤ R)
    (hprod : closedBall (0 : Vector 3) (ε * R) ×ˢ
      closedBall (0 : Vector 3) (ε * R) ⊆ Φ.source) :
    InjOn (fun q ↦ chartCapNeck Φ ε (a, q)) {q : Parameter | q.1 ∈ Icc (-R) R} := by
  intro q hq w hw he
  apply scaledCapPair_injective hε.ne' ha
  exact Φ.injOn (hprod (scaled_capPair_mem_product hε hR a q hq))
    (hprod (scaled_capPair_mem_product hε hR a w hw)) he

end NoExoticSixSphere.SphereSumNeck

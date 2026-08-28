import Wikipedia.NoExoticSixSphere.SphereSumNeck

/-!
# The actual neck inside an original manifold chart

Positive scaling places the entire neck in a prescribed product of balls.
Composition with an actual partial diffeomorphism preserves smoothness,
injectivity, and the injectivity of the native manifold derivative. The
end collars agree exactly with the original sheet parametrizations.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def scaledPair (ε : ℝ) (q : Parameter) : Vector 3 × Vector 3 := ε • pairMap q

theorem contMDiff_scaledPair (ε : ℝ) :
    ContMDiff Model 𝓘(ℝ, Vector 3 × Vector 3) ∞ (scaledPair ε) := by
  have hc : ContMDiff Model 𝓘(ℝ, ℝ) ∞ (fun _ : Parameter ↦ ε) := contMDiff_const
  exact hc.smul contMDiff_pairMap

theorem scaledPair_injective {ε : ℝ} (hε : ε ≠ 0) : Injective (scaledPair ε) := by
  intro q w h
  exact pairMap_injective (smul_right_injective (Vector 3 × Vector 3) hε h)

theorem injective_mfderiv_scaledPair {ε : ℝ} (hε : ε ≠ 0) (q : Parameter) :
    Injective (mfderiv Model 𝓘(ℝ, Vector 3 × Vector 3) (scaledPair ε) q) := by
  let π : Vector 3 × Vector 3 → Vector 3 × Vector 3 := fun z ↦ ε⁻¹ • z
  have hc : ContMDiff 𝓘(ℝ, Vector 3 × Vector 3) 𝓘(ℝ, ℝ) ∞
      (fun _ : Vector 3 × Vector 3 ↦ ε⁻¹) := contMDiff_const
  have hπ : ContMDiff 𝓘(ℝ, Vector 3 × Vector 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ π :=
    hc.smul contMDiff_id
  have he : pairMap = π ∘ scaledPair ε := by
    funext w
    exact (inv_smul_smul₀ hε (pairMap w)).symm
  have hi := injective_mfderiv_pairMap q
  rw [he, mfderiv_comp q (hπ.mdifferentiableAt (by simp))
    ((contMDiff_scaledPair ε).mdifferentiableAt (by simp))] at hi
  intro v w hvw
  apply hi
  exact congrArg (mfderiv 𝓘(ℝ, Vector 3 × Vector 3)
    𝓘(ℝ, Vector 3 × Vector 3) π (scaledPair ε q)) hvw

theorem scaledPair_mem_product {ε : ℝ} (hε : 0 < ε) (q : Parameter) :
    scaledPair ε q ∈ closedBall (0 : Vector 3) ε ×ˢ closedBall (0 : Vector 3) ε := by
  have hnorm (w : Parameter) : ‖ε • radialMap w‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, norm_radialMap]
    nlinarith [profile_lt_one w.1]
  exact ⟨by simpa [scaledPair, pairMap, mem_closedBall, dist_zero_right] using hnorm q,
    by simpa [scaledPair, pairMap, mem_closedBall, dist_zero_right] using hnorm (reverse q)⟩

theorem scaledPair_fst_eq_zero_iff {ε : ℝ} (hε : ε ≠ 0) (q : Parameter) :
    (scaledPair ε q).1 = 0 ↔ q.1 ≤ -1 := by
  change ε • (pairMap q).1 = 0 ↔ _
  rw [smul_eq_zero, or_iff_right hε, pairMap_fst_eq_zero_iff]

theorem scaledPair_snd_eq_zero_iff {ε : ℝ} (hε : ε ≠ 0) (q : Parameter) :
    (scaledPair ε q).2 = 0 ↔ 1 ≤ q.1 := by
  change ε • (pairMap q).2 = 0 ↔ _
  rw [smul_eq_zero, or_iff_right hε, pairMap_snd_eq_zero_iff]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

def chartNeck (ε : ℝ) (q : Parameter) : M := Φ (scaledPair ε q)

variable {ε : ℝ} (hε : 0 < ε)
  (hprod : closedBall (0 : Vector 3) ε ×ˢ closedBall (0 : Vector 3) ε ⊆ Φ.source)

include hε hprod

theorem scaledPair_mem_source (q : Parameter) : scaledPair ε q ∈ Φ.source :=
  hprod (scaledPair_mem_product hε q)

theorem contMDiff_chartNeck : ContMDiff Model (𝓡 6) ∞ (chartNeck Φ ε) := by
  intro q
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) ∞ Φ
      (scaledPair ε q) := ⟨Φ, scaledPair_mem_source Φ hε hprod q, fun _ _ ↦ rfl⟩
  exact hlocal.contMDiffAt.comp q (contMDiff_scaledPair ε q)

theorem chartNeck_injective : Injective (chartNeck Φ ε) := by
  intro q w he
  exact scaledPair_injective hε.ne' (Φ.injOn
    (scaledPair_mem_source Φ hε hprod q) (scaledPair_mem_source Φ hε hprod w) he)

theorem injective_mfderiv_chartNeck (q : Parameter) :
    Injective (mfderiv Model (𝓡 6) (chartNeck Φ ε) q) := by
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) ∞ Φ
      (scaledPair ε q) := ⟨Φ, scaledPair_mem_source Φ hε hprod q, fun _ _ ↦ rfl⟩
  have hinj := (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  change Injective (mfderiv 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) Φ (scaledPair ε q)) at hinj
  change Injective (mfderiv Model (𝓡 6) (Φ ∘ scaledPair ε) q)
  rw [mfderiv_comp q (hlocal.mdifferentiableAt (by simp))
    ((contMDiff_scaledPair ε).mdifferentiableAt (by simp))]
  exact hinj.comp (injective_mfderiv_scaledPair hε.ne' q)

theorem chartNeck_mem_target (q : Parameter) : chartNeck Φ ε q ∈ Φ.target :=
  Φ.map_source (scaledPair_mem_source Φ hε hprod q)

theorem chartNeck_closedCylinder_embedded [T2Space M] (u v : ℝ) :
    IsClosedEmbedding (fun q : Icc u v × Sphere 2 ↦ chartNeck Φ ε (q.1.val, q.2)) := by
  have hc : Continuous (fun q : Icc u v × Sphere 2 ↦ chartNeck Φ ε (q.1.val, q.2)) :=
    (contMDiff_chartNeck Φ hε hprod).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  apply hc.isClosedEmbedding
  intro q w he
  have h := chartNeck_injective Φ hε hprod he
  have hs := congrArg Prod.snd h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) hs

theorem chartNeck_right_collar {f : Vector 3 → M}
    (haxis : ∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x)
    (t : ℝ) (s : Sphere 2) (ht : 1 ≤ t) :
    chartNeck Φ ε (t, s) = f ((ε * profile t) • s.val) := by
  have he : scaledPair ε (t, s) = ((ε * profile t) • s.val, 0) := by
    rw [scaledPair, pairMap_right_collar t s ht]
    simp [smul_smul]
  have hsource := scaledPair_mem_source Φ hε hprod (t, s)
  rw [he] at hsource
  exact (congrArg Φ he).trans (haxis _ hsource)

theorem chartNeck_left_collar {g : Vector 3 → M}
    (haxis : ∀ x, (0, x) ∈ Φ.source → Φ (0, x) = g x)
    (t : ℝ) (s : Sphere 2) (ht : t ≤ -1) :
    chartNeck Φ ε (t, s) = g ((ε * profile (-t)) • s.val) := by
  have he : scaledPair ε (t, s) = (0, (ε * profile (-t)) • s.val) := by
    rw [scaledPair, pairMap_left_collar t s ht]
    simp [smul_smul]
  have hsource := scaledPair_mem_source Φ hε hprod (t, s)
  rw [he] at hsource
  exact (congrArg Φ he).trans (haxis _ hsource)

theorem chartNeck_mem_sheet_iff {f g : Vector 3 → M} {U V : Set (Vector 3)}
    (hclean : ∀ z ∈ Φ.source,
      (Φ z ∈ f '' U ↔ z.2 = 0) ∧ (Φ z ∈ g '' V ↔ z.1 = 0)) (q : Parameter) :
    (chartNeck Φ ε q ∈ f '' U ↔ 1 ≤ q.1) ∧
      (chartNeck Φ ε q ∈ g '' V ↔ q.1 ≤ -1) := by
  obtain ⟨hf, hg⟩ := hclean _ (scaledPair_mem_source Φ hε hprod q)
  exact ⟨hf.trans (scaledPair_snd_eq_zero_iff hε.ne' q),
    hg.trans (scaledPair_fst_eq_zero_iff hε.ne' q)⟩

end NoExoticSixSphere.SphereSumNeck

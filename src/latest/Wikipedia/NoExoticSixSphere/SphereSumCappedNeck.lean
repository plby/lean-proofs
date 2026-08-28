import Wikipedia.NoExoticSixSphere.SphereSumCapProfile
import Wikipedia.NoExoticSixSphere.SphereSumNeckOpening

/-!
# The neck with exact linear tails for sphere gluing

Both radial components are jointly smooth in opening, time, and direction.
For openings between zero and one the tails lie on the original axes and
are exactly linear beyond time two. On bounded cylinders a common scaling
keeps every opening in the same actual target chart.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def capPair (a : ℝ) (q : Parameter) : Vector 3 × Vector 3 :=
  (capProfile a q.1 • q.2.val, capProfile a (-q.1) • q.2.val)

theorem contMDiff_capPair :
    ContMDiff OpeningModel 𝓘(ℝ, Vector 3 × Vector 3) ∞
      (fun p : ℝ × Parameter ↦ capPair p.1 p.2) := by
  let : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have ht : ContMDiff OpeningModel 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × Parameter ↦ p.2.1) :=
    contMDiff_fst.comp contMDiff_snd
  have ha : ContMDiff OpeningModel 𝓘(ℝ, ℝ) ∞ (Prod.fst : ℝ × Parameter → ℝ) :=
    contMDiff_fst
  have hs : ContMDiff OpeningModel (𝓡 3) ∞ (fun p : ℝ × Parameter ↦ p.2.2.val) :=
    contMDiff_coe_sphere.comp (contMDiff_snd.comp contMDiff_snd)
  exact ((contDiff_capProfile.contMDiff.comp (ha.prodMk_space ht)).smul hs).prodMk_space
    ((contDiff_capProfile.contMDiff.comp (ha.prodMk_space ht.neg)).smul hs)

theorem contMDiff_capPair_slice (a : ℝ) :
    ContMDiff Model 𝓘(ℝ, Vector 3 × Vector 3) ∞ (capPair a) :=
  contMDiff_capPair.comp (contMDiff_const.prodMk contMDiff_id)

theorem capPair_middle (a : ℝ) (q : Parameter) (hq : q.1 ∈ Icc (-1 : ℝ) 1) :
    capPair a q = openingPair (a, q) := by
  change (capProfile a q.1 • q.2.val, capProfile a (-q.1) • q.2.val) = _
  rw [capProfile_eq_profile a q.1 hq.2,
    capProfile_eq_profile a (-q.1) (by linarith [hq.1])]
  rfl

theorem capPair_right (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (t : ℝ) (s : Sphere 2)
    (ht : 2 ≤ t) : capPair a (t, s) = (t • s.val, 0) := by
  have hz := (capProfile_zero_iff ha.1 (-t)).mpr (by linarith [ha.2])
  simp only [capPair, capProfile_eq_id a t ht, hz, zero_smul]

theorem capPair_left (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (t : ℝ) (s : Sphere 2)
    (ht : t ≤ -2) : capPair a (t, s) = (0, (-t) • s.val) := by
  have hz := (capProfile_zero_iff ha.1 t).mpr (by linarith [ha.2])
  simp only [capPair, hz, capProfile_eq_id a (-t) (by linarith), zero_smul]

theorem capPair_zero_middle (s : Sphere 2) : capPair 0 (0, s) = 0 := by
  rw [capPair_middle 0 (0, s) (by norm_num), openingPair_zero_middle]

theorem scaled_capPair_mem_product {ε R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R)
    (a : ℝ) (q : Parameter) (hq : q.1 ∈ Icc (-R) R) :
    ε • capPair a q ∈
      closedBall (0 : Vector 3) (ε * R) ×ˢ closedBall (0 : Vector 3) (ε * R) := by
  have hn (t : ℝ) (ht : t ≤ R) : ‖ε • (capProfile a t • q.2.val)‖ ≤ ε * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (capProfile_nonneg a t), ClosedHemisphere.unit_norm, mul_one]
    exact mul_le_mul_of_nonneg_left (capProfile_le a hR ht) hε.le
  exact ⟨by simpa [capPair, mem_closedBall, dist_zero_right] using hn q.1 hq.2,
    by simpa [capPair, mem_closedBall, dist_zero_right] using hn (-q.1) (by linarith [hq.1])⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

def chartCapNeck (ε : ℝ) (p : ℝ × Parameter) : M := Φ (ε • capPair p.1 p.2)

theorem contMDiffAt_chartCapNeck {ε R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R)
    (hprod : closedBall (0 : Vector 3) (ε * R) ×ˢ closedBall (0 : Vector 3) (ε * R) ⊆ Φ.source)
    (p : ℝ × Parameter) (hp : p.2.1 ∈ Icc (-R) R) :
    ContMDiffAt OpeningModel (𝓡 6) ∞ (chartCapNeck Φ ε) p := by
  have hc : ContMDiff OpeningModel 𝓘(ℝ, ℝ) ∞ (fun _ : ℝ × Parameter ↦ ε) :=
    contMDiff_const
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) ∞ Φ
      (ε • capPair p.1 p.2) :=
    ⟨Φ, hprod (scaled_capPair_mem_product hε hR p.1 p.2 hp), fun _ _ ↦ rfl⟩
  exact hlocal.contMDiffAt.comp p ((hc.smul contMDiff_capPair) p)

end NoExoticSixSphere.SphereSumNeck

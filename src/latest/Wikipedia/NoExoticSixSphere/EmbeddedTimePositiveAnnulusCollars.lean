import Wikipedia.NoExoticSixSphere.EmbeddedTimeAnnulusCollarGerms
import Wikipedia.NoExoticSixSphere.EmbeddedTimeSphereCollarAnnulus

/-!
# Uniform positive collars at both ends of the actual annulus

The original gradient collars give quantitative collar widths after unit
inversion or half scaling. The two chosen cut radii are separated. Both
collars are smooth and have positive time in the annulus interior, with
globally smooth ambient extensions agreeing on their entire closed collars.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))

theorem exists_positive_innerAnnulusCollar (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f → Injective f →
      (∀ s, Injective (mfderiv (𝓡 p) (𝓡 n) f s)) →
      ∃ R : ℝ, 1 < R ∧ R < 4 / 3 ∧
        (∀ x, 1 ≤ ‖x‖ → ‖x‖ ≤ R →
          ContMDiffAt (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ (innerAnnulusCollar e r t b f) x) ∧
        (∀ x, 1 < ‖x‖ → ‖x‖ ≤ R → 0 < t (innerAnnulusCollar e r t b f x)) ∧
        ∃ H : C(Vector (p + 1), Vector e.ambientDimension), ContDiff ℝ ∞ H ∧
          ∀ x, 1 ≤ ‖x‖ → ‖x‖ ≤ R → H x = e.toFun (innerAnnulusCollar e r t b f x) := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  obtain ⟨ρ, hρ, hρ1, hgs, -, -, hgp, H, hH, hHeq⟩ :=
    exists_positive_embedded_sphereCollar_annulus e r t ht hreg b f hf hi hd
  have hinv : 1 < 1 / ρ := (lt_div_iff₀ hρ).mpr (by simpa using hρ1)
  let R := (1 + min (1 / ρ) (4 / 3)) / 2
  have hmin : 1 < min (1 / ρ) (4 / 3) := lt_min hinv (by norm_num)
  have hR : 1 < R := by dsimp only [R]; linarith
  have hRmin : R < min (1 / ρ) (4 / 3) := by dsimp only [R]; linarith
  have hRinv : R < 1 / ρ := hRmin.trans_le (min_le_left _ _)
  have hRsmall : R < 4 / 3 := hRmin.trans_le (min_le_right _ _)
  have hRρ : R * ρ < 1 := (lt_div_iff₀ hρ).mp hRinv
  have hmap (x : Vector (p + 1)) (hx : 1 ≤ ‖x‖) (hxR : ‖x‖ ≤ R) :
      SphereCollarInversion.map x ∈ closedBall 0 1 ∩ {y | ρ ≤ ‖y‖} := by
    have hxpos : 0 < ‖x‖ := zero_lt_one.trans_le hx
    have hmul := mul_le_mul_of_nonneg_left hxR hρ.le
    constructor
    · rw [mem_closedBall_zero_iff, SphereCollarInversion.norm_map]
      exact (div_le_iff₀ hxpos).mpr (by simpa using hx)
    · change ρ ≤ ‖SphereCollarInversion.map x‖
      rw [SphereCollarInversion.norm_map]
      apply (le_div_iff₀ hxpos).mpr
      nlinarith
  obtain ⟨J, hJ, hJeq⟩ := SphereCollarInversion.exists_smooth_ambient_extension H hH
  refine ⟨R, hR, hRsmall, ?_, ?_, J, hJ, ?_⟩
  · intro x hx hxR
    have hmx := hmap x hx hxR
    have hxne : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hx))
    exact (hgs _ hmx.1 hmx.2).comp x
      (SphereCollarInversion.contDiffAt_map hxne).contMDiffAt
  · intro x hx hxR
    have hmx := hmap x hx.le hxR
    apply hgp _ _ hmx.2
    rw [mem_ball_zero_iff, SphereCollarInversion.norm_map]
    exact (div_lt_iff₀ (zero_lt_one.trans hx)).mpr (by simpa using hx)
  · intro x hx hxR
    rw [hJeq x ⟨hx, hxR.trans (by linarith)⟩]
    exact hHeq (hmap x hx hxR)

theorem exists_positive_outerAnnulusCollar (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f → Injective f →
      (∀ s, Injective (mfderiv (𝓡 p) (𝓡 n) f s)) →
      ∃ R : ℝ, 7 / 4 < R ∧ R < 2 ∧
        (∀ x, R ≤ ‖x‖ → ‖x‖ ≤ 2 →
          ContMDiffAt (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ (outerAnnulusCollar e r t b f) x) ∧
        (∀ x, R ≤ ‖x‖ → ‖x‖ < 2 → 0 < t (outerAnnulusCollar e r t b f x)) ∧
        ∃ H : C(Vector (p + 1), Vector e.ambientDimension), ContDiff ℝ ∞ H ∧
          ∀ x, R ≤ ‖x‖ → ‖x‖ ≤ 2 → H x = e.toFun (outerAnnulusCollar e r t b f x) := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  obtain ⟨ρ, hρ, hρ1, hgs, -, -, hgp, H, hH, hHeq⟩ :=
    exists_positive_embedded_sphereCollar_annulus e r t ht hreg b f hf hi hd
  let R := (max (2 * ρ) (7 / 4) + 2) / 2
  have hmax : max (2 * ρ) (7 / 4) < 2 := max_lt (by linarith) (by norm_num)
  have hR : R < 2 := by dsimp only [R]; linarith
  have hmaxR : max (2 * ρ) (7 / 4) < R := by dsimp only [R]; linarith
  have hRlarge : 7 / 4 < R := (le_max_right _ _).trans_lt hmaxR
  have hρR : 2 * ρ < R := (le_max_left _ _).trans_lt hmaxR
  have hmap (x : Vector (p + 1)) (hxR : R ≤ ‖x‖) (hx : ‖x‖ ≤ 2) :
      SphereAnnulus.halfCoordinates p x ∈ closedBall 0 1 ∩ {y | ρ ≤ ‖y‖} := by
    constructor
    · rw [mem_closedBall_zero_iff, SphereAnnulus.norm_halfCoordinates]
      linarith
    · change ρ ≤ ‖SphereAnnulus.halfCoordinates p x‖
      rw [SphereAnnulus.norm_halfCoordinates]
      linarith
  let J : C(Vector (p + 1), Vector e.ambientDimension) :=
    ⟨H ∘ SphereAnnulus.halfCoordinates p,
      H.continuous.comp (SphereAnnulus.halfCoordinates p).continuous⟩
  have hJ : ContDiff ℝ ∞ J := hH.comp (SphereAnnulus.halfCoordinates p).contDiff
  refine ⟨R, hRlarge, hR, ?_, ?_, J, hJ, ?_⟩
  · intro x hxR hx
    have hmx := hmap x hxR hx
    exact (hgs _ hmx.1 hmx.2).comp x
      (SphereAnnulus.halfCoordinates p).contDiff.contMDiff.contMDiffAt
  · intro x hxR hx
    have hmx := hmap x hxR hx.le
    apply hgp _ _ hmx.2
    rw [mem_ball_zero_iff, SphereAnnulus.norm_halfCoordinates]
    linarith
  · intro x hxR hx
    exact hHeq (hmap x hxR hx)

end NoExoticSixSphere.EmbeddedTime

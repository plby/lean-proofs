import Wikipedia.NoExoticSixSphere.ImmersedInternalSphereTube
import Wikipedia.NoExoticSixSphere.SphereInternalNormalFrame
import Wikipedia.NoExoticSixSphere.ImmersedSphereDoublePoints
import Wikipedia.NoExoticSixSphere.TransverseSphereIntersections
import Mathlib.Topology.Separation.Regular

/-!
# A smooth immersed push-off family with a compact off-diagonal container

A bounded nonzero scalar multiple of the internal normal frame gives a
globally smooth family whose zero slice is the original immersion. Uniform
local injectivity excludes near-diagonal coincidences at every nonzero
time. A smaller diagonal neighborhood has closure in that exclusion region.
Its compact complement contains the double-point set and all nonzero-time
coincidence sets in its interior, with an exact zero-time comparison.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ImmersedPushOff

def amount (ε t : ℝ) : ℝ := ε * t / (1 + t ^ 2)

theorem denominator_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

theorem contDiff_amount (ε : ℝ) : ContDiff ℝ ∞ (amount ε) :=
  (contDiff_const.mul contDiff_id).div (contDiff_const.add (contDiff_id.pow 2))
    (fun t ↦ (denominator_pos t).ne')

theorem amount_zero (ε : ℝ) : amount ε 0 = 0 := by simp [amount]

theorem abs_amount_le {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : |amount ε t| ≤ ε := by
  have ht : |t| ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  rw [amount, abs_div, abs_mul, abs_of_nonneg hε, abs_of_pos (denominator_pos t)]
  exact (div_le_iff₀ (denominator_pos t)).mpr (mul_le_mul_of_nonneg_left ht hε)

theorem amount_ne_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≠ 0) : amount ε t ≠ 0 :=
  div_ne_zero (mul_ne_zero hε.ne' ht) (denominator_pos t).ne'

end NoExoticSixSphere.ImmersedPushOff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization ImmersedPushOff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

include e a r in
theorem exists_immersed_pushOff_family (f : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    ∃ G : ℝ → Sphere 3 → M,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry G) ∧ (∀ s, G 0 s = f s) ∧
      ∃ K : Set (Sphere 3 × Sphere 3), IsCompact K ∧
        K ∩ MapIntersections.pairs f f = SphereSelfIntersections.pairs f ∧
        SphereSelfIntersections.pairs f ⊆ interior K ∧
        ∀ t, t ≠ 0 → MapIntersections.pairs f (G t) ⊆ interior K := by
  obtain ⟨C, hC, hCn, hCr⟩ := e.exists_smooth_internalNormalFrame f a hf hd
  have hiC (s : Sphere 3) : Injective (C s) := Stiefel.injective ⟨C s, hCn s⟩
  obtain ⟨ε₀, hε₀, hmem⟩ := e.exists_immersed_internalSphereTube_radius f C r hf hC hd hiC hCr
  obtain ⟨ε₁, hε₁, V, hV, hdiag, hVi, hsep⟩ :=
    e.exists_internalSphereTube_diagonal_separation f C r hf hC hd hiC hCr
  let ε := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  let w : Vector 3 := (spherePole 2).val
  have hwn : ‖w‖ = 1 := ClosedHemisphere.unit_norm _
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (hwn.trans_ne one_ne_zero)
  let v : ℝ → Vector 3 := fun t ↦ amount ε t • w
  have hv (t : ℝ) : ‖v t‖ ≤ ε := by
    simpa only [v, norm_smul, Real.norm_eq_abs, hwn, mul_one] using abs_amount_le hε.le t
  have hvne (t : ℝ) (ht : t ≠ 0) : v t ≠ 0 :=
    smul_ne_zero (amount_ne_zero hε ht) hwne
  have hvs : ContDiff ℝ ∞ v := (contDiff_amount ε).smul contDiff_const
  let G : ℝ → Sphere 3 → M := fun t s ↦ e.internalSphereTube f C r (s, v t)
  have hparam : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun q : ℝ × Sphere 3 ↦ (q.2, v q.1)) :=
    contMDiff_snd.prodMk (hvs.contMDiff.comp contMDiff_fst)
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry G) :=
    (e.contMDiffOn_internalSphereTube f C r hf hC).comp_contMDiff hparam
      (fun q ↦ (hmem q.2 (v q.1) ((hv q.1).trans (min_le_left _ _))).1)
  have hG₀ (s : Sphere 3) : G 0 s = f s := by
    change e.internalSphereTube f C r (s, amount ε 0 • w) = f s
    rw [amount_zero, zero_smul, e.internalSphereTube_core]
  let D : Set (Sphere 3 × Sphere 3) := range (fun s : Sphere 3 ↦ (s, s))
  have hD : IsCompact D := isCompact_range (continuous_id.prodMk continuous_id)
  have hDV : D ⊆ V := by rintro _ ⟨s, rfl⟩; exact hdiag s
  obtain ⟨U, hU, hDU, hUV⟩ := hD.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hDV)
  let K := Uᶜ
  have hInt : interior K = (closure U)ᶜ := interior_compl
  have hself : SphereSelfIntersections.pairs f ⊆ interior K := by
    intro p hp
    rw [hInt]
    intro hcl
    exact hp.1 (hVi p.1 p.2 (hUV hcl) hp.2)
  refine ⟨G, hG, hG₀, K, hU.isClosed_compl.isCompact, ?_, hself, ?_⟩
  · ext p
    constructor
    · rintro ⟨hpK, he⟩
      refine ⟨?_, he⟩
      intro hp
      apply hpK
      have heq : p = (p.1, p.1) := Prod.ext rfl hp.symm
      rw [heq]
      exact hDU ⟨p.1, rfl⟩
    · intro hp
      exact ⟨interior_subset (hself hp), hp.2⟩
  · intro t ht p hp
    rw [hInt]
    intro hcl
    exact hsep p.1 p.2 (hUV hcl) (v t) ((hv t).trans (min_le_right _ _)) (hvne t ht) hp

end NoExoticSixSphere.EuclideanEmbedding

import Wikipedia.NoExoticSixSphere.SphereFourTubeCutoff

/-!
# A genuine smooth time modification cutting out the inner tube

Inside the smaller tube, the new time is exactly squared normal radius
minus one. Outside the larger compact tube it is exactly the old time.
The transition is a convex combination of two positive values, so no
new zero occurs on the outer side of the unit normal sphere.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [CompactSpace M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

theorem exists_time_modification (hΦ : Φ.source = univ) (t : C(M, ℝ))
    (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t) (hpos : ∀ x ∈ Φ.target, 0 < t x) :
    ∃ τ : C(M, ℝ), ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ ∧
      (∀ x ∉ closedRegion Φ 2, τ x = t x) ∧
      (∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1) ∧
      ∀ p : Sphere 3 × Vector 4, 1 < ‖p.2‖ → 0 < τ (Φ p) := by
  obtain ⟨Q, χ, hQ, hχ1, hχ0, hχrange⟩ := exists_radial_cutoff_extension Φ hΦ
  have hs : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞
      (fun x ↦ χ x * (Q x - 1) + (1 - χ x) * t x) :=
    (χ.contMDiff.mul (Q.contMDiff.sub contMDiff_const)).add
      ((contMDiff_const.sub χ.contMDiff).mul ht)
  let τ : C(M, ℝ) := ⟨fun x ↦ χ x * (Q x - 1) + (1 - χ x) * t x, hs.continuous⟩
  have hout (x : M) (hx : x ∉ closedRegion Φ 2) : τ x = t x := by
    have hx' : x ∉ openRegion Φ 2 := fun h ↦ hx
      ((image_mono (prod_mono Subset.rfl ball_subset_closedBall)) h)
    change χ x * (Q x - 1) + (1 - χ x) * t x = t x
    rw [hχ0 x hx']
    ring
  have hnormQ (p : Sphere 3 × Vector 4) (hp : ‖p.2‖ ≤ 2) : Q (Φ p) = ‖p.2‖ ^ 2 :=
    (hQ (Φ p) ⟨p, ⟨mem_univ _, mem_closedBall_zero_iff.mpr hp⟩, rfl⟩).trans
      (radiusSquared_apply Φ hΦ p)
  have hinner (p : Sphere 3 × Vector 4) (hp : ‖p.2‖ ≤ 3 / 2) :
      τ (Φ p) = ‖p.2‖ ^ 2 - 1 := by
    have hχp : χ (Φ p) = 1 :=
      hχ1 (Φ p) ⟨p, ⟨mem_univ _, mem_closedBall_zero_iff.mpr hp⟩, rfl⟩
    change χ (Φ p) * (Q (Φ p) - 1) + (1 - χ (Φ p)) * t (Φ p) = _
    rw [hχp, hnormQ p (by linarith)]
    ring
  refine ⟨τ, hs, hout, hinner, ?_⟩
  intro p hp
  have hpSource : p ∈ Φ.source := hΦ.symm ▸ mem_univ p
  have htp : 0 < t (Φ p) := hpos _ (Φ.toPartialEquiv.map_source hpSource)
  have hrad : 0 < ‖p.2‖ ^ 2 - 1 := by nlinarith
  by_cases hp₂ : ‖p.2‖ ≤ 2
  · change 0 < χ (Φ p) * (Q (Φ p) - 1) + (1 - χ (Φ p)) * t (Φ p)
    rw [hnormQ p hp₂]
    by_cases hχp : χ (Φ p) = 1
    · rw [hχp]
      simpa only [one_mul, sub_self, zero_mul, add_zero] using hrad
    · have hχlt : χ (Φ p) < 1 := lt_of_le_of_ne (hχrange (Φ p)).2 hχp
      exact add_pos_of_nonneg_of_pos (mul_nonneg (hχrange (Φ p)).1 hrad.le)
        (mul_pos (sub_pos.mpr hχlt) htp)
  · have houtp : Φ p ∉ closedRegion Φ 2 := by
      intro hmem
      have hn := ((mem_closedRegion_iff Φ hΦ 2 (Φ p)).mp hmem).2
      have he := congrArg (fun q : Sphere 3 × Vector 4 ↦ ‖q.2‖)
        (Φ.toPartialEquiv.left_inv hpSource)
      exact hp₂ (he.symm.trans_le hn)
    rw [hout _ houtp]
    exact htp

end NoExoticSixSphere.SphereFourTube

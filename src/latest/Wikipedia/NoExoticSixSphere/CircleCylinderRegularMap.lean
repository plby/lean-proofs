import Wikipedia.NoExoticSixSphere.CircleCylinderClock
import Wikipedia.NoExoticSixSphere.RegularCollaredCylinder

/-!
# A smooth regular circle double retaining both original cylinder ends

Evaluate the original regular cylinder on the genuine circle clock.
At its two critical clock points, the retained endpoint germs give
regularity from the original endpoint maps. Elsewhere the clock is
a submersion. No endpoint fiber is assumed empty.
-/

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

def parameter (m : ℕ) : C(Sphere 1 × Sphere m, ℝ × Sphere m) :=
  clockMap.prodMap (ContinuousMap.id _)

theorem contMDiff_parameter (m : ℕ) :
    ContMDiff ((𝓡 1).prod (𝓡 m)) ((𝓘(ℝ, ℝ)).prod (𝓡 m)) ∞ (parameter m) :=
  contMDiff_clock.prodMap contMDiff_id

theorem surjective_mfderiv_parameter (m : ℕ) (p : Sphere 1 × Sphere m)
    (hp : p.1 ∈ SphereCylinder.band 0) :
    Surjective (mfderiv ((𝓡 1).prod (𝓡 m)) ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (parameter m) p) := by
  change Surjective (mfderiv ((𝓡 1).prod (𝓡 m)) ((𝓘(ℝ, ℝ)).prod (𝓡 m))
    (Prod.map clock id) p)
  rw [mfderiv_prodMap (contMDiff_clock.mdifferentiableAt (by simp)) mdifferentiableAt_id,
    mfderiv_id]
  intro v
  obtain ⟨u, hu⟩ := surjective_mfderiv_clock p.1 hp v.1
  exact ⟨(u, v.2), Prod.ext hu rfl⟩

theorem surjective_mfderiv_endpoint {m n : ℕ} (f : C(Sphere m, Sphere n))
    (hs : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (p : Sphere 1 × Sphere m)
    (hr : Surjective (mfderiv (𝓡 m) (𝓡 n) f p.2)) :
    Surjective (mfderiv ((𝓡 1).prod (𝓡 m)) (𝓡 n)
      (fun q : Sphere 1 × Sphere m ↦ f q.2) p) := by
  change Surjective (mfderiv ((𝓡 1).prod (𝓡 m)) (𝓡 n) (f ∘ Prod.snd) p)
  rw [mfderiv_comp p (hs.mdifferentiableAt (by simp)) mdifferentiableAt_snd, mfderiv_snd]
  intro v
  obtain ⟨w, hw⟩ := hr v
  exact ⟨(0, w), hw⟩

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def map : C(Sphere 1 × Sphere m, Sphere n) := d.map.comp (parameter m)

theorem contMDiff_map : ContMDiff ((𝓡 1).prod (𝓡 m)) (𝓡 n) ∞ (map d) :=
  d.smooth_map.comp (contMDiff_parameter m)

theorem left_germ (p : Sphere 1 × Sphere m) (hp : clock p.1 = 0) :
    (map d : Sphere 1 × Sphere m → Sphere n) =ᶠ[𝓝 p] fun q ↦ d.leftMap q.2 := by
  have hmem : clock p.1 ∈ d.leftTimes := hp.symm ▸ d.left_mem
  filter_upwards [(d.leftTimes.isOpen.preimage
    (contMDiff_clock.continuous.comp continuous_fst)).mem_nhds hmem] with q hq
  exact d.left_eq _ hq _

theorem right_germ (p : Sphere 1 × Sphere m) (hp : clock p.1 = 1) :
    (map d : Sphere 1 × Sphere m → Sphere n) =ᶠ[𝓝 p] fun q ↦ d.rightMap q.2 := by
  have hmem : clock p.1 ∈ d.rightTimes := hp.symm ▸ d.right_mem
  filter_upwards [(d.rightTimes.isOpen.preimage
    (contMDiff_clock.continuous.comp continuous_fst)).mem_nhds hmem] with q hq
  exact d.right_eq _ hq _

theorem map_left (x : Sphere m) : map d (SphereCylinder.endPole 0 true, x) = d.leftMap x :=
  (left_germ d _ clock_left).self_of_nhds

theorem map_right (x : Sphere m) : map d (SphereCylinder.endPole 0 false, x) = d.rightMap x :=
  (right_germ d _ clock_right).self_of_nhds

theorem regular_map (p : Sphere 1 × Sphere m) (hp : map d p = b) :
    Surjective (mfderiv ((𝓡 1).prod (𝓡 m)) (𝓡 n) (map d) p) := by
  by_cases hc : p.1 ∈ SphereCylinder.band 0
  · change Surjective (mfderiv ((𝓡 1).prod (𝓡 m)) (𝓡 n) (d.map ∘ parameter m) p)
    rw [mfderiv_comp p (d.smooth_map.mdifferentiableAt (by simp))
      ((contMDiff_parameter m).mdifferentiableAt (by simp))]
    exact (d.regular_map _ hp).comp (surjective_mfderiv_parameter m p hc)
  · rcases (SphereCylinder.not_mem_band_iff 0 p.1).mp hc with hr | hl
    · have he := right_germ d p (hr ▸ clock_right)
      rw [he.mfderiv_eq]
      exact surjective_mfderiv_endpoint d.rightMap d.smooth_right p
        (d.regular_right p.2 (he.self_of_nhds.symm.trans hp))
    · have he := left_germ d p (hl ▸ clock_left)
      rw [he.mfderiv_eq]
      exact surjective_mfderiv_endpoint d.leftMap d.smooth_left p
        (d.regular_left p.2 (he.self_of_nhds.symm.trans hp))

end NoExoticSixSphere.CircleCylinder

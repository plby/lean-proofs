import Wikipedia.NoExoticSixSphere.SmoothSpherePinch
import Wikipedia.NoExoticSixSphere.SphereFoldHemisphereInverse

/-!
# Native transversality of the hemisphere pinch

At every intersection the source lies in an open hemisphere. The native
derivative is the derivative of the corresponding input composed with the
invertible derivative of the explicit fold. Thus transversality of both
input pairs implies transversality of the pinched pair. Local constancy at
the collapsed pole is not needed for this local assertion.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFold

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

theorem mfderiv_pinch_north (v : Sphere 3) (f g : C(Sphere 3, M))
    (hbase : f (antipode v) = g (antipode v))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (x : Sphere 3) (hx : 0 < height v x) :
    (mfderiv (𝓡 3) (𝓡 6) (pinch v f g hbase) x : Vector 3 →L[ℝ] Vector 6) =
      (mfderiv (𝓡 3) (𝓡 6) f (fold v x) : Vector 3 →L[ℝ] Vector 6).comp
        (mfderiv (𝓡 3) (𝓡 3) (fold v) x : Vector 3 →L[ℝ] Vector 3) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp [GLOrthonormalization.Vector]⟩
  rw [(pinch_eventuallyEq_north v f g hbase x hx).mfderiv_eq]
  exact mfderiv_comp x (hf.mdifferentiableAt (by simp))
    ((contMDiff_fold (n := 3) v).mdifferentiableAt (by simp))

theorem mfderiv_pinch_south (v : Sphere 3) (f g : C(Sphere 3, M))
    (hbase : f (antipode v) = g (antipode v))
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) (x : Sphere 3) (hx : height v x < 0) :
    (mfderiv (𝓡 3) (𝓡 6) (pinch v f g hbase) x : Vector 3 →L[ℝ] Vector 6) =
      (mfderiv (𝓡 3) (𝓡 6) g (fold v x) : Vector 3 →L[ℝ] Vector 6).comp
        (mfderiv (𝓡 3) (𝓡 3) (fold v) x : Vector 3 →L[ℝ] Vector 3) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp [GLOrthonormalization.Vector]⟩
  rw [(pinch_eventuallyEq_south v f g hbase x hx).mfderiv_eq]
  exact mfderiv_comp x (hg.mdifferentiableAt (by simp))
    ((contMDiff_fold (n := 3) v).mdifferentiableAt (by simp))

theorem surjective_coprod_comp_left (A B : Vector 3 →L[ℝ] Vector 6)
    (S : Vector 3 →L[ℝ] Vector 3) (hS : Surjective S) (h : Surjective (A.coprod B)) :
    Surjective ((A.comp S).coprod B) := by
  intro w
  obtain ⟨z, hz⟩ := h w
  obtain ⟨a, ha⟩ := hS z.1
  refine ⟨(a, z.2), ?_⟩
  change A (S a) + B z.2 = w
  rw [ha]
  exact hz

theorem transverse_pinch (v : Sphere 3) (f g k : C(Sphere 3, M))
    (hbase : f (antipode v) = g (antipode v))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hm : f (antipode v) ∉ range k)
    (hfk : ∀ x y, f x = k y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) k y)))
    (hgk : ∀ x y, g x = k y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) k y))) :
    ∀ x y, pinch v f g hbase x = k y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (pinch v f g hbase) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) k y)) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp [GLOrthonormalization.Vector]⟩
  intro x y hxy
  have hn := pinch_intersection_off_equator v f g hbase k hm x y hxy
  have hD := (bijective_mfderiv_fold (n := 3) v x hn).2
  change Surjective
    ((mfderiv (𝓡 3) (𝓡 6) (pinch v f g hbase) x : Vector 3 →L[ℝ] Vector 6).coprod
      (mfderiv (𝓡 3) (𝓡 6) k y : Vector 3 →L[ℝ] Vector 6))
  rcases lt_or_gt_of_ne hn with hs | hn
  · have hgxy : g (fold v x) = k y :=
      (pinch_south v f g hbase x hs.le).symm.trans hxy
    rw [mfderiv_pinch_south v f g hbase hg x hs]
    exact surjective_coprod_comp_left _ _ _ hD (hgk (fold v x) y hgxy)
  · have hfxy : f (fold v x) = k y :=
      (pinch_north v f g hbase x hn.le).symm.trans hxy
    rw [mfderiv_pinch_north v f g hbase hf x hn]
    exact surjective_coprod_comp_left _ _ _ hD (hfk (fold v x) y hfxy)

end NoExoticSixSphere.SphereFold

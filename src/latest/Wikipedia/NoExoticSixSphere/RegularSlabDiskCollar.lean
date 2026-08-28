import Wikipedia.NoExoticSixSphere.RegularSlabCollaredDisk
import Wikipedia.NoExoticSixSphere.SignedSphereCollar

/-!
# Smooth immersive collars for the original regular-slab disk construction

The disk's actual time and sphere coordinates agree on the outer half-annulus
with a globally smooth Euclidean collar. Its signed radial derivative and
boundary immersion follow from the original spatial sphere map. Both ends
are treated with their actual, opposite signs.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularSlabDiskCollar

open GLOrthonormalization CylinderFiberSlab
open Wikipedia.HopfProblem.DegreeCollapse
open DiskCylinder

variable {m n p : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}

def spatial (f : C(NoExoticSixSphere.Sphere p, slab d.map z s t)) :
    C(NoExoticSixSphere.Sphere p, Vector (m + 1)) :=
  ⟨fun q ↦ (f q).val.val.2.val, continuous_subtype_val.comp
    (continuous_snd.comp ((continuous_subtype_val.comp continuous_subtype_val).comp f.continuous))⟩

variable {f : C(NoExoticSixSphere.Sphere p, slab d.map z s t)}
  (D : d.CollaredDiskExtension p f)

def ambient : C(Disk (E := Vector (p + 1)), ℝ × Vector (m + 1)) where
  toFun x := ((D.map x).val.val.1, (D.map x).val.val.2.val)
  continuous_toFun := by
    have h := (continuous_subtype_val.comp continuous_subtype_val).comp D.map.continuous
    exact h.fst.prodMk (continuous_subtype_val.comp h.snd)

def leftCollar (b : NoExoticSixSphere.Sphere p) : Vector (p + 1) → ℝ × Vector (m + 1) :=
  SignedSphereCollar.map b (spatial f) s (s - D.leftCut)

def rightCollar (b : NoExoticSixSphere.Sphere p) : Vector (p + 1) → ℝ × Vector (m + 1) :=
  SignedSphereCollar.map b (spatial f) t (t - D.rightCut)

theorem ambient_eq_leftCollar (b : NoExoticSixSphere.Sphere p)
    (hf : ∀ q, (f q).val.val.1 = s) (x : Disk (E := Vector (p + 1)))
    (hx : 1 / 2 ≤ ‖x.val‖) : ambient D x = leftCollar D b x.val := by
  obtain ⟨⟨u, q⟩, rfl⟩ := DiskCone.radial_surjective b x
  rw [DiskCone.radial_norm] at hx
  have he := congrArg (fun v : ℝ × NoExoticSixSphere.Sphere m ↦ (v.1, v.2.val))
    (D.left_collar u hx q (hf q))
  change ambient D (DiskCone.radial (u, q)) =
    SignedSphereCollar.map b (spatial f) s (s - D.leftCut) ((u : ℝ) • q.val)
  rw [SignedSphereCollar.map_radial b (spatial f) s (s - D.leftCut) u hx q]
  change ambient D (DiskCone.radial (u, q)) =
    (s + (1 - (u : ℝ) ^ 2) * (D.leftCut - s), spatial f q) at he
  rw [he]
  congr 1
  ring

theorem ambient_eq_rightCollar (b : NoExoticSixSphere.Sphere p)
    (hf : ∀ q, (f q).val.val.1 = t) (x : Disk (E := Vector (p + 1)))
    (hx : 1 / 2 ≤ ‖x.val‖) : ambient D x = rightCollar D b x.val := by
  obtain ⟨⟨u, q⟩, rfl⟩ := DiskCone.radial_surjective b x
  rw [DiskCone.radial_norm] at hx
  have he := congrArg (fun v : ℝ × NoExoticSixSphere.Sphere m ↦ (v.1, v.2.val))
    (D.right_collar u hx q (hf q))
  change ambient D (DiskCone.radial (u, q)) =
    SignedSphereCollar.map b (spatial f) t (t - D.rightCut) ((u : ℝ) • q.val)
  rw [SignedSphereCollar.map_radial b (spatial f) t (t - D.rightCut) u hx q]
  change ambient D (DiskCone.radial (u, q)) =
    (t + (1 - (u : ℝ) ^ 2) * (D.rightCut - t), spatial f q) at he
  rw [he]
  congr 1
  ring

variable (b : NoExoticSixSphere.Sphere p)
  (hf : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f))

include hf

theorem contDiff_leftCollar : ContDiff ℝ ∞ (leftCollar D b) :=
  SignedSphereCollar.contDiff_map b (spatial f) s (s - D.leftCut) hf

theorem contDiff_rightCollar : ContDiff ℝ ∞ (rightCollar D b) :=
  SignedSphereCollar.contDiff_map b (spatial f) t (t - D.rightCut) hf

theorem injective_leftCollar_sphere
    (hi : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 (m + 1)) (spatial f) q))
    (q : NoExoticSixSphere.Sphere p) : Injective (fderiv ℝ (leftCollar D b) q.val) :=
  SignedSphereCollar.injective_fderiv_map_sphere b (spatial f) s (s - D.leftCut) hf
    (sub_ne_zero.mpr D.left_lt.ne) hi q

theorem injective_rightCollar_sphere
    (hi : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 (m + 1)) (spatial f) q))
    (q : NoExoticSixSphere.Sphere p) : Injective (fderiv ℝ (rightCollar D b) q.val) :=
  SignedSphereCollar.injective_fderiv_map_sphere b (spatial f) t (t - D.rightCut) hf
    (sub_ne_zero.mpr D.right_lt.ne') hi q

theorem fderiv_leftCollar_radial (q : NoExoticSixSphere.Sphere p) :
    fderiv ℝ (leftCollar D b) q.val q.val = (2 * (s - D.leftCut), 0) :=
  SignedSphereCollar.fderiv_map_radial b (spatial f) s (s - D.leftCut) hf q

theorem fderiv_rightCollar_radial (q : NoExoticSixSphere.Sphere p) :
    fderiv ℝ (rightCollar D b) q.val q.val = (2 * (t - D.rightCut), 0) :=
  SignedSphereCollar.fderiv_map_radial b (spatial f) t (t - D.rightCut) hf q

end NoExoticSixSphere.RegularSlabDiskCollar

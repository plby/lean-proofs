import Wikipedia.NoExoticSixSphere.RegularCylinderFiberEmbedding
import Wikipedia.NoExoticSixSphere.RegularSlabDiskCollar
import Wikipedia.NoExoticSixSphere.DiskCollarSmoothing

/-!
# Smooth disks in the original regular fiber, retaining the actual slab collar

The constructed compact-image retraction is applied to the original closed
Euclidean embedding of the full regular fiber. The new map is smooth at
every point of the closed source disk, agrees with the original disk on
the outer quarter-annulus, and sends its interior into the original slab
interior. Its ambient boundary derivative is exactly the collar derivative.
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
  {f : C(NoExoticSixSphere.Sphere p, slab d.map z s t)}
  (D : d.CollaredDiskExtension p f)

def fiberMap : C(Disk (E := Vector (p + 1)),
    {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z}) :=
  ⟨fun x ↦ (D.map x).val, continuous_subtype_val.comp D.map.continuous⟩

theorem exists_smooth_of_collar (k : ℕ) (hd : m = n + k)
    (H : Vector (p + 1) → ℝ × Vector (m + 1)) (hH : ContDiff ℝ ∞ H)
    (hHG : ∀ x : Disk (E := Vector (p + 1)), 1 / 2 ≤ ‖x.val‖ → H x.val = ambient D x) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
      (CylinderFiberNormalFrame.dimension_eq hd)
    let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd
    ∃ g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z},
      (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 (p + 1)) (𝓡 (k + 1)) ∞ g x) ∧
      (∀ x : Disk (E := Vector (p + 1)), 3 / 4 ≤ ‖x.val‖ → g x.val = (D.map x).val) ∧
      (∀ x ∈ ball 0 1, (g x).val.1 ∈ Ioo s t) ∧
      ∀ q : NoExoticSixSphere.Sphere p, fderiv ℝ (e.toFun ∘ g) q.val =
        (EuclideanProduct.coordinates (m + 1)).toContinuousLinearMap.comp (fderiv ℝ H q.val) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)
  let := regularFiber_isManifold d.map d.smooth_map z d.regular_map (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)
  let : Nonempty {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} :=
    ⟨(D.map ⟨0, by simp⟩).val⟩
  let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd
  let L := EuclideanProduct.coordinates (m + 1)
  let H' : C(Vector (p + 1), Vector e.ambientDimension) :=
    ⟨L ∘ H, L.continuous.comp hH.continuous⟩
  have hH' : ContDiff ℝ ∞ H' := L.contDiff.comp hH
  have hmatch (x : Disk (E := Vector (p + 1))) (hx : 1 / 2 ≤ ‖x.val‖) :
      H' x.val = e.toFun (fiberMap D x) := by
    change L (H x.val) = L (ambient D x)
    rw [hHG x hx]
  let V : Set {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} :=
    {v | v.val.1 ∈ Ioo s t}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_fst.comp continuous_subtype_val)
  obtain ⟨g, hgs, hgeq, hgV⟩ := e.exists_smooth_disk_with_collar
    (fiberMap D) H' hH' hmatch V hV (fun x hx ↦ D.interior x hx)
  refine ⟨g, hgs, hgeq, hgV, ?_⟩
  intro q
  rw [e.fderiv_eq_disk_collar (fiberMap D) H' hH' hmatch g hgs hgeq q]
  exact (L.hasFDerivAt.comp q.val (hH.differentiable (by simp) q.val).hasFDerivAt).fderiv

theorem exists_smooth_with_immersive_boundary (k : ℕ) (hd : m = n + k)
    (b : NoExoticSixSphere.Sphere p)
    (hf : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f))
    (hi : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 (m + 1)) (spatial f) q))
    (hend : (∀ q, (f q).val.val.1 = s) ∨ ∀ q, (f q).val.val.1 = t) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
      (CylinderFiberNormalFrame.dimension_eq hd)
    let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd
    ∃ g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z},
      (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 (p + 1)) (𝓡 (k + 1)) ∞ g x) ∧
      (∀ q, g q.val = (f q).val) ∧
      (∀ x : Disk (E := Vector (p + 1)), 3 / 4 ≤ ‖x.val‖ → g x.val = (D.map x).val) ∧
      (∀ x ∈ ball 0 1, (g x).val.1 ∈ Ioo s t) ∧
      ∀ q : NoExoticSixSphere.Sphere p, Injective (fderiv ℝ (e.toFun ∘ g) q.val) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)
  let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd
  have hcollar : ∃ H : Vector (p + 1) → ℝ × Vector (m + 1), ContDiff ℝ ∞ H ∧
      (∀ x : Disk (E := Vector (p + 1)), 1 / 2 ≤ ‖x.val‖ → H x.val = ambient D x) ∧
      ∀ q : NoExoticSixSphere.Sphere p, Injective (fderiv ℝ H q.val) := by
    rcases hend with hl | hr
    · exact ⟨leftCollar D b, contDiff_leftCollar D b hf,
        fun x hx ↦ (ambient_eq_leftCollar D b hl x hx).symm,
        injective_leftCollar_sphere D b hf hi⟩
    · exact ⟨rightCollar D b, contDiff_rightCollar D b hf,
        fun x hx ↦ (ambient_eq_rightCollar D b hr x hx).symm,
        injective_rightCollar_sphere D b hf hi⟩
  obtain ⟨H, hH, hHG, hHi⟩ := hcollar
  obtain ⟨g, hgs, hgeq, hgV, hgD⟩ := exists_smooth_of_collar D k hd H hH hHG
  refine ⟨g, hgs, ?_, hgeq, hgV, ?_⟩
  · intro q
    have he := hgeq (boundaryToDisk q) (by
      change (3 / 4 : ℝ) ≤ ‖q.val‖
      rw [ClosedHemisphere.unit_norm]
      norm_num)
    exact he.trans (congrArg Subtype.val (D.boundary q))
  · intro q
    rw [hgD q]
    exact (EuclideanProduct.coordinates (m + 1)).injective.comp (hHi q)

end NoExoticSixSphere.RegularSlabDiskCollar

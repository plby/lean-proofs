import Wikipedia.NoExoticSixSphere.RegularSlabAnnulusCollars
import Wikipedia.NoExoticSixSphere.AnnulusCollarSmoothing
import Wikipedia.NoExoticSixSphere.RegularCylinderFiberEmbedding

/-!
# Smooth original slab cylinders with both prescribed end collars

The original closed regular-fiber embedding and its constructed compact-image
retraction smooth the actual annulus map. Both endpoint maps and both
protected collars remain exact, and every interior point stays in the
original strict-time slab. No compactness of the full regular fiber,
interior immersion, genericity, or framing-extension hypothesis is used.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSlabCylinderCollar

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar
open Wikipedia.HopfProblem.DegreeCollapse

variable {m n p : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  {f₀ f₁ : C(NoExoticSixSphere.Sphere p, slab d.map z s t)}
  (D : d.CollaredCylinderExtension p f₀ f₁) (b : NoExoticSixSphere.Sphere p)

theorem exists_smooth_with_original_collars (k : ℕ) (hd : m = n + k)
    (hf₀ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₀))
    (hf₁ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₁))
    (h₀ : ∀ q, (f₀ q).val.val.1 = s) (h₁ : ∀ q, (f₁ q).val.val.1 = t) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
      (CylinderFiberNormalFrame.dimension_eq hd)
    ∃ g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z},
      (∀ x ∈ SphereAnnulus.domain p, ContMDiffAt (𝓡 (p + 1)) (𝓡 (k + 1)) ∞ g x) ∧
      (∀ q : NoExoticSixSphere.Sphere p, g q.val = (f₀ q).val) ∧
      (∀ q : NoExoticSixSphere.Sphere p, g ((2 : ℝ) • q.val) = (f₁ q).val) ∧
      (∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x.val‖ →
        g x.val = (D.map (SphereAnnulus.toCylinder b x)).val) ∧
      ∀ x : Vector (p + 1), 1 < ‖x‖ → ‖x‖ < 2 → (g x).val.1 ∈ Ioo s t := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)
  let := regularFiber_isManifold d.map d.smooth_map z d.regular_map (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)
  let : Nonempty {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} :=
    ⟨(D.map (0, b)).val⟩
  let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd
  let L := EuclideanProduct.coordinates (m + 1)
  let H₀ : C(Vector (p + 1), Vector e.ambientDimension) :=
    ⟨L ∘ leftCollar D b, L.continuous.comp (contDiff_leftCollar D b hf₀).continuous⟩
  let H₁ : C(Vector (p + 1), Vector e.ambientDimension) :=
    ⟨L ∘ rightCollar D b, L.continuous.comp (contDiff_rightCollar D b hf₁).continuous⟩
  have hH₀ : ContDiff ℝ ∞ H₀ := L.contDiff.comp (contDiff_leftCollar D b hf₀)
  have hH₁ : ContDiff ℝ ∞ H₁ := L.contDiff.comp (contDiff_rightCollar D b hf₁)
  have hmatch₀ (x : SphereAnnulus.domain p) (hx : ‖x.val‖ ≤ 4 / 3) :
      H₀ x.val = e.toFun (annulusMap D b x) := by
    change L (leftCollar D b x.val) = L (ambient D b x)
    rw [ambient_eq_leftCollar D b h₀ x hx]
  have hmatch₁ (x : SphereAnnulus.domain p) (hx : 7 / 4 ≤ ‖x.val‖) :
      H₁ x.val = e.toFun (annulusMap D b x) := by
    change L (rightCollar D b x.val) = L (ambient D b x)
    rw [ambient_eq_rightCollar D b h₁ x hx]
  let V : Set {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} :=
    {v | v.val.1 ∈ Ioo s t}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_fst.comp continuous_subtype_val)
  obtain ⟨g, hgs, hgeq, hgV⟩ := e.exists_smooth_annulus_with_collars
    (annulusMap D b) H₀ H₁ hH₀ hH₁ hmatch₀ hmatch₁ V hV (annulusMap_interior D b)
  refine ⟨g, hgs, ?_, ?_, hgeq, hgV⟩
  · intro q
    have he := hgeq (SphereAnnulus.fromCylinder p (0, q)) (Or.inl (by
      rw [SphereAnnulus.fromCylinder_zero_val, ClosedHemisphere.unit_norm]
      norm_num))
    rw [SphereAnnulus.fromCylinder_zero_val] at he
    exact he.trans ((annulusMap_fromCylinder D b 0 q).trans
      (congrArg Subtype.val (D.map.apply_zero q)))
  · intro q
    have he := hgeq (SphereAnnulus.fromCylinder p (1, q)) (Or.inr (by
      rw [SphereAnnulus.fromCylinder_one_val, norm_smul, ClosedHemisphere.unit_norm]
      norm_num))
    rw [SphereAnnulus.fromCylinder_one_val] at he
    exact he.trans ((annulusMap_fromCylinder D b 1 q).trans
      (congrArg Subtype.val (D.map.apply_one q)))

end NoExoticSixSphere.RegularSlabCylinderCollar

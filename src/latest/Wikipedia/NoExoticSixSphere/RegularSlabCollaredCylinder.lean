import Wikipedia.NoExoticSixSphere.CollaredSlabCylinderExtension
import Wikipedia.NoExoticSixSphere.RegularSlabInteriorEquivalence
import Wikipedia.NoExoticSixSphere.IntegralKernelDiskExtension

/-!
# Actual collared cylinders for equal integral images in the original slab

Equality of original integral sphere classes in an actually two-connected
slab gives a genuine homotopy. The original regular cylinder supplies the
collars, producing a cylinder with the prescribed endpoint maps and with
all interior parameters in the strict-time interior. This applies when
two nonzero endpoint images agree; neither image is assumed to vanish.

The construction is continuous. Relative smoothing, genericity, and the
comparison of the original endpoint framing obstructions are not asserted.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab
open Wikipedia.HopfProblem.SingularMayerVietoris

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)

structure CollaredCylinderExtension (n : ℕ)
    (f₀ f₁ : C(NoExoticSixSphere.Sphere n, slab d.map z s t)) where
  leftCut : ℝ
  rightCut : ℝ
  left_lt : s < leftCut
  cuts_le : leftCut ≤ rightCut
  right_lt : rightCut < t
  left_subset : Icc s leftCut ⊆ d.leftTimes
  right_subset : Icc rightCut t ⊆ d.rightTimes
  map : f₀.Homotopy f₁
  interior : ∀ (u : unitInterval), 0 < (u : ℝ) → (u : ℝ) < 1 →
    ∀ q, map (u, q) ∈ interiorDomain d.map z s t
  left_collar : ∀ (u : unitInterval), (u : ℝ) ≤ 1 / 3 →
    ∀ q, (f₀ q).val.val.1 = s → (map (u, q)).val.val =
      (s + (4 * (u : ℝ) * (1 - (u : ℝ))) * (leftCut - s), (f₀ q).val.val.2)
  right_collar : ∀ (u : unitInterval), 2 / 3 ≤ (u : ℝ) →
    ∀ q, (f₁ q).val.val.1 = t → (map (u, q)).val.val =
      (t + (4 * (u : ℝ) * (1 - (u : ℝ))) * (rightCut - t), (f₁ q).val.val.2)

def collaredCylinderOfHomotopy (n : ℕ)
    (f₀ f₁ : C(NoExoticSixSphere.Sphere n, slab d.map z s t)) (G : f₀.Homotopy f₁) :
    d.CollaredCylinderExtension n f₀ f₁ := by
  let a := d.exists_inner_times.choose
  let b := d.exists_inner_times.choose_spec.choose
  have h := d.exists_inner_times.choose_spec.choose_spec
  have hL : ∀ r ∈ Icc s a, ∀ x, d.map (r, x) = d.map (s, x) :=
    fun r hr x ↦ (d.left_eq r (h.2.2.2.1 hr) x).trans (d.left_eq s d.left_mem x).symm
  have hR : ∀ r ∈ Icc b t, ∀ x, d.map (r, x) = d.map (t, x) :=
    fun r hr x ↦ (d.right_eq r (h.2.2.2.2 hr) x).trans (d.right_eq t d.right_mem x).symm
  exact {
    leftCut := a
    rightCut := b
    left_lt := h.1
    cuts_le := h.2.1
    right_lt := h.2.2.1
    left_subset := h.2.2.2.1
    right_subset := h.2.2.2.2
    map := InteriorPush.collaredCylinder d.map z s t a b h.1 h.2.1 h.2.2.1 hL hR G
    interior := fun u hu₀ hu₁ q ↦ InteriorPush.collaredCylinder_interior
      d.map z s t a b h.1 h.2.1 h.2.2.1 hL hR G u ⟨hu₀, hu₁⟩ q
    left_collar := InteriorPush.collaredCylinder_left
      d.map z s t a b h.1 h.2.1 h.2.2.1 hL hR G
    right_collar := InteriorPush.collaredCylinder_right
      d.map z s t a b h.1 h.2.1 h.2.2.1 hL hR G }

theorem CollaredCylinderExtension.boundary_iff {n : ℕ}
    {f₀ f₁ : C(NoExoticSixSphere.Sphere n, slab d.map z s t)}
    (D : d.CollaredCylinderExtension n f₀ f₁)
    (h₀ : ∀ q, f₀ q ∈ BoundaryPush.ends d.map z s t)
    (h₁ : ∀ q, f₁ q ∈ BoundaryPush.ends d.map z s t)
    (u : unitInterval) (q : NoExoticSixSphere.Sphere n) :
    D.map (u, q) ∈ BoundaryPush.ends d.map z s t ↔ u = 0 ∨ u = 1 := by
  constructor
  · intro hb
    by_contra hn
    push Not at hn
    have hu₀ : (u : ℝ) ≠ 0 := fun h ↦ hn.1 (Subtype.ext h)
    have hu₁ : (u : ℝ) ≠ 1 := fun h ↦ hn.2 (Subtype.ext h)
    have hi := D.interior u (lt_of_le_of_ne u.property.1 hu₀.symm)
      (lt_of_le_of_ne u.property.2 hu₁) q
    exact hb.elim (ne_of_gt hi.1) (ne_of_lt hi.2)
  · rintro (rfl | rfl)
    · rw [D.map.apply_zero]
      exact h₀ q
    · rw [D.map.apply_one]
      exact h₁ q

variable [SimplyConnectedSpace (slab d.map z s t)] (w : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w)]

include w hW₂ in
theorem collaredCylinderExtension_nonempty_iff
    (f₀ f₁ : C(NoExoticSixSphere.Sphere 3, slab d.map z s t)) :
    Nonempty (d.CollaredCylinderExtension 3 f₀ f₁) ↔
      SmoothCube.integralSphereClass f₀ = SmoothCube.integralSphereClass f₁ := by
  constructor
  · rintro ⟨D⟩
    exact SmoothCube.integralSphereClass_homotopic ⟨D.map⟩
  · intro he
    obtain ⟨G⟩ := (SmoothCube.integralSphereClass_eq_iff_homotopic w f₀ f₁).mp he
    exact ⟨d.collaredCylinderOfHomotopy 3 f₀ f₁ G⟩

include w hW₂ in
theorem nonempty_collaredCylinderExtension_of_integral_images
    {L R : Type} [TopologicalSpace L] [TopologicalSpace R]
    (jL : C(L, slab d.map z s t)) (jR : C(R, slab d.map z s t))
    (f : C(NoExoticSixSphere.Sphere 3, L)) (g : C(NoExoticSixSphere.Sphere 3, R))
    (he : singularHomologyMap jL 3 (SmoothCube.integralSphereClass f) =
      singularHomologyMap jR 3 (SmoothCube.integralSphereClass g)) :
    Nonempty (d.CollaredCylinderExtension 3 (jL.comp f) (jR.comp g)) := by
  apply (d.collaredCylinderExtension_nonempty_iff w _ _).mpr
  rw [SmoothCube.integralSphereClass_comp, SmoothCube.integralSphereClass_comp, he]

end NoExoticSixSphere.RegularCollaredCylinder

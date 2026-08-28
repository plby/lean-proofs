import Wikipedia.NoExoticSixSphere.RegularSlabCollaredCylinder

/-!
# Injectivity of both retained original cylinder collars

The inward clock is injective on each protected collar. The two collar
images are separated by the original inner-time cuts. Thus injective
original endpoint spheres give an injective map on the union of both
collars. No assertion about injectivity in the middle of the cylinder
is made or used.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularCollaredCylinder.CollaredCylinderExtension

open CylinderFiberSlab

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  {z : N} {s t : ℝ} {d : RegularCollaredCylinder (M := M) I J z s t}
  {n : ℕ} {f₀ f₁ : C(NoExoticSixSphere.Sphere n, slab d.map z s t)}
  (D : d.CollaredCylinderExtension n f₀ f₁)
  (h₀ : ∀ q, (f₀ q).val.val.1 = s) (h₁ : ∀ q, (f₁ q).val.val.1 = t)

include h₀ in
theorem left_time_lt_cut (u : unitInterval) (hu : (u : ℝ) ≤ 1 / 3)
    (q : NoExoticSixSphere.Sphere n) : (D.map (u, q)).val.val.1 < D.leftCut := by
  have hval := congrArg Prod.fst (D.left_collar u hu q (h₀ q))
  change (D.map (u, q)).val.val.1 =
    s + (CylinderTime.interiorClock u : ℝ) * (D.leftCut - s) at hval
  rw [hval]
  calc
    _ < s + 1 * (D.leftCut - s) := by
      have h := mul_lt_mul_of_pos_right (CylinderTime.interiorClock_lt_one_left u hu)
        (sub_pos.mpr D.left_lt)
      linarith
    _ = D.leftCut := by ring

include h₁ in
theorem right_cut_lt_time (u : unitInterval) (hu : 2 / 3 ≤ (u : ℝ))
    (q : NoExoticSixSphere.Sphere n) : D.rightCut < (D.map (u, q)).val.val.1 := by
  have hval := congrArg Prod.fst (D.right_collar u hu q (h₁ q))
  change (D.map (u, q)).val.val.1 =
    t + (CylinderTime.interiorClock u : ℝ) * (D.rightCut - t) at hval
  rw [hval]
  calc
    D.rightCut = t + 1 * (D.rightCut - t) := by ring
    _ < _ := by
      have h := mul_lt_mul_of_neg_right (CylinderTime.interiorClock_lt_one_right u hu)
        (sub_neg.mpr D.right_lt)
      linarith

include h₀ in
theorem left_eq_iff (hf₀ : Injective f₀)
    (u v : unitInterval) (hu : (u : ℝ) ≤ 1 / 3) (hv : (v : ℝ) ≤ 1 / 3)
    (x y : NoExoticSixSphere.Sphere n) :
    D.map (u, x) = D.map (v, y) ↔ u = v ∧ x = y := by
  constructor
  · intro he
    have hvv := congrArg (fun p : slab d.map z s t ↦ p.val.val) he
    rw [D.left_collar u hu x (h₀ x), D.left_collar v hv y (h₀ y)] at hvv
    have ht := congrArg Prod.fst hvv
    change s + (CylinderTime.interiorClock u : ℝ) * (D.leftCut - s) =
      s + (CylinderTime.interiorClock v : ℝ) * (D.leftCut - s) at ht
    have hc : CylinderTime.interiorClock u = CylinderTime.interiorClock v :=
      Subtype.ext (mul_right_cancel₀ (ne_of_gt (sub_pos.mpr D.left_lt)) (add_left_cancel ht))
    have hsp := congrArg Prod.snd hvv
    refine ⟨CylinderTime.interiorClock_injectiveOn_left hu hv hc, hf₀ ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ((h₀ x).trans (h₀ y).symm) hsp
  · rintro ⟨rfl, rfl⟩
    rfl

include h₁ in
theorem right_eq_iff (hf₁ : Injective f₁)
    (u v : unitInterval) (hu : 2 / 3 ≤ (u : ℝ)) (hv : 2 / 3 ≤ (v : ℝ))
    (x y : NoExoticSixSphere.Sphere n) :
    D.map (u, x) = D.map (v, y) ↔ u = v ∧ x = y := by
  constructor
  · intro he
    have hvv := congrArg (fun p : slab d.map z s t ↦ p.val.val) he
    rw [D.right_collar u hu x (h₁ x), D.right_collar v hv y (h₁ y)] at hvv
    have ht := congrArg Prod.fst hvv
    change t + (CylinderTime.interiorClock u : ℝ) * (D.rightCut - t) =
      t + (CylinderTime.interiorClock v : ℝ) * (D.rightCut - t) at ht
    have hc : CylinderTime.interiorClock u = CylinderTime.interiorClock v :=
      Subtype.ext (mul_right_cancel₀ (ne_of_lt (sub_neg.mpr D.right_lt)) (add_left_cancel ht))
    have hsp := congrArg Prod.snd hvv
    refine ⟨CylinderTime.interiorClock_injectiveOn_right hu hv hc, hf₁ ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ((h₁ x).trans (h₁ y).symm) hsp
  · rintro ⟨rfl, rfl⟩
    rfl

include h₀ h₁ in
theorem left_ne_right (u v : unitInterval)
    (hu : (u : ℝ) ≤ 1 / 3) (hv : 2 / 3 ≤ (v : ℝ))
    (x y : NoExoticSixSphere.Sphere n) : D.map (u, x) ≠ D.map (v, y) := by
  intro he
  have ht := congrArg (fun p : slab d.map z s t ↦ p.val.val.1) he
  have hl := D.left_time_lt_cut h₀ u hu x
  have hr := D.right_cut_lt_time h₁ v hv y
  have hc := D.cuts_le
  linarith

include h₀ h₁ in
theorem injOn_end_collars (hf₀ : Injective f₀) (hf₁ : Injective f₁) :
    Set.InjOn D.map {p : unitInterval × NoExoticSixSphere.Sphere n |
      (p.1 : ℝ) ≤ 1 / 3 ∨ 2 / 3 ≤ (p.1 : ℝ)} := by
  rintro ⟨u, x⟩ hu ⟨v, y⟩ hv he
  rcases hu with hu | hu
  · rcases hv with hv | hv
    · exact Prod.ext_iff.mpr ((D.left_eq_iff h₀ hf₀ u v hu hv x y).mp he)
    · exact (D.left_ne_right h₀ h₁ u v hu hv x y he).elim
  · rcases hv with hv | hv
    · exact (D.left_ne_right h₀ h₁ v u hv hu y x he.symm).elim
    · exact Prod.ext_iff.mpr ((D.right_eq_iff h₁ hf₁ u v hu hv x y).mp he)

end NoExoticSixSphere.RegularCollaredCylinder.CollaredCylinderExtension

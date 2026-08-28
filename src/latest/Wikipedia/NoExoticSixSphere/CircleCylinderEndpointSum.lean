import Wikipedia.NoExoticSixSphere.CircleCylinderEndpointImmersion

/-!
# The original endpoint sum parametrizes the entire circle seam

The two literal endpoint inclusions assemble to a smooth injective
immersion of their disjoint union. Its image is exactly the actual
zero set of seam time. Both original endpoint regular-fiber atlases
are retained in the sum atlas.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

abbrev Endpoints := {x : Sphere m // d.leftMap x = b} ⊕ {x : Sphere m // d.rightMap x = b}

def endpointsMap : C(Endpoints d, Fiber d) :=
  ⟨Sum.elim (leftInclusion d) (rightInclusion d),
    (leftInclusion d).continuous.sumElim (rightInclusion d).continuous⟩

theorem endpointsMap_inl (x : {x : Sphere m // d.leftMap x = b}) :
    endpointsMap d (Sum.inl x) = leftInclusion d x := rfl

theorem endpointsMap_inr (x : {x : Sphere m // d.rightMap x = b}) :
    endpointsMap d (Sum.inr x) = rightInclusion d x := rfl

theorem endpointsMap_injective : Injective (endpointsMap d) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (leftInclusion_injective d h)
    | inr y => exact (leftInclusion_ne_rightInclusion d x y h).elim
  | inr x =>
    cases y with
    | inl y => exact (leftInclusion_ne_rightInclusion d y x h.symm).elim
    | inr y => exact congrArg Sum.inr (rightInclusion_injective d h)

theorem time_eq_zero_iff_endpoints (p : Fiber d) :
    time d p = 0 ↔ ∃ x, endpointsMap d x = p := by
  rw [time_eq_zero_iff]
  constructor
  · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr y, hy⟩
  · rintro ⟨x | y, h⟩
    · exact Or.inl ⟨x, h⟩
    · exact Or.inr ⟨y, h⟩

theorem contMDiff_endpointsMap (k : ℕ) (hd : m = n + k) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    letI := fiberAtlas d k hd;
    ContMDiff (𝓡 k) (𝓡 (k + 1)) ∞ (endpointsMap d) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := fiberAtlas d k hd
  exact (contMDiff_leftInclusion d k hd).sumElim (contMDiff_rightInclusion d k hd)

theorem mfderiv_endpointsMap_injective (k : ℕ) (hd : m = n + k) (p : Endpoints d) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    letI := fiberAtlas d k hd;
    Injective (mfderiv (𝓡 k) (𝓡 (k + 1)) (endpointsMap d) p) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := fiberAtlas d k hd
  cases p with
  | inl x =>
    have hc := mfderiv_comp x
      ((contMDiff_endpointsMap d k hd).mdifferentiableAt (by simp))
      ((ContMDiff.inl (I := 𝓡 k) (n := ∞)).mdifferentiableAt (by simp))
    change mfderiv (𝓡 k) (𝓡 (k + 1)) (leftInclusion d) x = _ at hc
    rw [mfderiv_sumInl (p := (Sum.inl x : Endpoints d))] at hc
    change mfderiv (𝓡 k) (𝓡 (k + 1)) (leftInclusion d) x =
      mfderiv (𝓡 k) (𝓡 (k + 1)) (endpointsMap d) (Sum.inl x) at hc
    exact hc ▸ mfderiv_leftInclusion_injective d k hd x
  | inr x =>
    have hc := mfderiv_comp x
      ((contMDiff_endpointsMap d k hd).mdifferentiableAt (by simp))
      ((ContMDiff.inr (I := 𝓡 k) (n := ∞)).mdifferentiableAt (by simp))
    change mfderiv (𝓡 k) (𝓡 (k + 1)) (rightInclusion d) x = _ at hc
    rw [mfderiv_sumInr] at hc
    change mfderiv (𝓡 k) (𝓡 (k + 1)) (rightInclusion d) x =
      mfderiv (𝓡 k) (𝓡 (k + 1)) (endpointsMap d) (Sum.inr x) at hc
    exact hc ▸ mfderiv_rightInclusion_injective d k hd x

end NoExoticSixSphere.CircleCylinder

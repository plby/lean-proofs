import Wikipedia.SmoothSixDPoincare.SublevelDisk

/-!
# Gluing complementary sublevel disks along their common level

The boundary identifications are constructed from the two actual disk
parametrizations. They give a genuine two-disk decomposition and hence a
homeomorphism to the standard sphere.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare

variable {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ} {f : M → ℝ} {a : ℝ}

/-- The level set of the negative function is the same native topological subspace. -/
def negLevelHomeomorph (f : M → ℝ) (a : ℝ) :
    {x : M // -f x = -a} ≃ₜ {x : M // f x = a} where
  toFun x := ⟨x.1, neg_inj.mp x.2⟩
  invFun x := ⟨x.1, congrArg Neg.neg x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The exact level-boundary correspondences construct the whole two-disk decomposition. -/
def twoDiskDecompositionOfSublevels (L : SublevelDisk n f a)
    (R : SublevelDisk n (fun x => -f x) (-a)) : TwoDiskDecomposition n M := by
  let B := L.boundaryHomeomorph
  let C := R.boundaryHomeomorph.trans (negLevelHomeomorph f a)
  let e := B.trans C.symm
  refine
    { boundaryEquiv := e
      left := L.map
      right := R.map
      left_injective := L.map_injective
      right_injective := R.map_injective
      covers := ?_
      overlap := ?_ }
  · intro y
    by_cases hy : f y ≤ a
    · left
      exact ⟨L.homeomorph.symm ⟨y, hy⟩,
        congrArg Subtype.val (L.homeomorph.apply_symm_apply ⟨y, hy⟩)⟩
    · right
      have hy' : -f y ≤ -a := neg_le_neg (le_of_not_ge hy)
      exact ⟨R.homeomorph.symm ⟨y, hy'⟩,
        congrArg Subtype.val (R.homeomorph.apply_symm_apply ⟨y, hy'⟩)⟩
  · intro x y
    constructor
    · intro h
      have hL : f (L.map x) ≤ a := (L.homeomorph x).2
      have hR : -f (R.map y) ≤ -a := (R.homeomorph y).2
      have hxlevel : f (L.map x) = a := by rw [← h] at hR; linarith
      have hylevel : -f (R.map y) = -a := by rw [← h, hxlevel]
      have hxnorm := (L.boundary_iff x).mp hxlevel
      have hynorm := (R.boundary_iff y).mp hylevel
      let z : DiskDouble.Boundary (Hemisphere.Ambient n) :=
        ⟨x.1, mem_sphere_zero_iff_norm.mpr hxnorm⟩
      let w : DiskDouble.Boundary (Hemisphere.Ambient n) :=
        ⟨y.1, mem_sphere_zero_iff_norm.mpr hynorm⟩
      have hbc : B z = C w := Subtype.ext h
      have hew : e z = w := by
        apply C.injective
        change C (C.symm (B z)) = C w
        rw [C.apply_symm_apply]
        exact hbc
      refine ⟨z, rfl, ?_⟩
      rw [hew]
      rfl
    · rintro ⟨z, rfl, rfl⟩
      have heq := congrArg Subtype.val (C.apply_symm_apply (B z))
      exact heq.symm

/-- Complementary genuine sublevel disks form the standard sphere. -/
def homeomorphSphereOfSublevelDisks (L : SublevelDisk n f a)
    (R : SublevelDisk n (fun x => -f x) (-a)) : M ≃ₜ Hemisphere.Sphere n :=
  (twoDiskDecompositionOfSublevels L R).homeomorphSphere

end Wikipedia.SmoothSixDPoincare

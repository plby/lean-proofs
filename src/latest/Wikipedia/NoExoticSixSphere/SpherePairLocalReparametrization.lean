import Wikipedia.NoExoticSixSphere.SphereSumGluingImmersion

/-! # Native pair transversality through two actual local source diffeomorphisms -/

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem surjective_coprod_swap (A B : Vector 3 →L[ℝ] Vector 6)
    (h : Surjective (A.coprod B)) : Surjective (B.coprod A) := by
  intro w
  obtain ⟨p, hp⟩ := h w
  refine ⟨(p.2, p.1), ?_⟩
  change B p.2 + A p.1 = w
  rw [add_comm]
  exact hp

theorem surjective_coprod_comp_both (A B : Vector 3 →L[ℝ] Vector 6)
    (S T : Vector 3 →L[ℝ] Vector 3) (hS : Surjective S) (hT : Surjective T)
    (h : Surjective (A.coprod B)) : Surjective ((A.comp S).coprod (B.comp T)) := by
  intro w
  obtain ⟨⟨u, v⟩, huv⟩ := h w
  obtain ⟨x, hx⟩ := hS u
  obtain ⟨y, hy⟩ := hT v
  refine ⟨(x, y), ?_⟩
  change A (S x) + B (T y) = w
  rw [hx, hy]
  exact huv

theorem transverse_of_local_reparametrizations
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
    (K F G : Sphere 3 → M) (u v : Sphere 3 → Sphere 3) (x y : Sphere 3)
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x)
    (hv : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ v y)
    (hx : K =ᶠ[𝓝 x] F ∘ u) (hy : K =ᶠ[𝓝 y] G ∘ v)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) F (u x)).coprod
      (mfderiv (𝓡 3) (𝓡 6) G (v y)))) :
    Surjective ((mfderiv (𝓡 3) (𝓡 6) K x).coprod (mfderiv (𝓡 3) (𝓡 6) K y)) := by
  rw [hx.mfderiv_eq, hy.mfderiv_eq,
    mfderiv_comp (f := u) (g := F) x (hF.mdifferentiableAt (by simp))
      (hu.mdifferentiableAt (by simp)),
    mfderiv_comp (f := v) (g := G) y (hG.mdifferentiableAt (by simp))
      (hv.mdifferentiableAt (by simp))]
  intro z
  obtain ⟨⟨a, b⟩, hab⟩ := ht z
  let U := hu.mfderivToContinuousLinearEquiv (by simp)
  let V := hv.mfderivToContinuousLinearEquiv (by simp)
  refine ⟨(U.symm a, V.symm b), ?_⟩
  change ((mfderiv (𝓡 3) (𝓡 6) F (u x)).coprod
    (mfderiv (𝓡 3) (𝓡 6) G (v y))) (U (U.symm a), V (V.symm b)) = z
  exact (congrArg ((mfderiv (𝓡 3) (𝓡 6) F (u x)).coprod
    (mfderiv (𝓡 3) (𝓡 6) G (v y)))
      (Prod.ext (U.apply_symm_apply a) (V.apply_symm_apply b))).trans hab

end NoExoticSixSphere.SphereSumNeck

import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack
import Wikipedia.HopfProblem.OrbitPairAmbientFamily
import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse

/-!
# A native source diffeomorphism from a smooth family of slice diffeomorphisms

The source map retains time and applies the given spatial slice map. Its
derivative is injective by the track lemma, hence invertible in equal finite
dimensions. Slice bijectivity gives global bijectivity, and the native
inverse-function theorem supplies a jointly smooth inverse.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open Wikipedia.SmoothSixDPoincare

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_spatial_source_diffeomorph {A : ℝ × M → M}
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A)
    (hD : ∀ t, ∃ D : Diffeomorph I I M M ∞, ∀ x, D x = A (t, x)) :
    ∃ Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞,
      ∀ p, Ψ p = (p.1, A p) := by
  have hbij : ∀ t, Bijective (fun x => A (t, x)) := by
    intro t
    obtain ⟨D, hd⟩ := hD t
    have heq : (fun x => A (t, x)) = D := funext (fun x => (hd x).symm)
    rw [heq]
    exact D.bijective
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ (track A) :=
    contMDiff_fst.prodMk hA
  have hinv (q : ℝ × M) :
      (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (track A) q).IsInvertible := by
    let T : ℝ × E →L[ℝ] ℝ × E :=
      mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (track A) q
    have hi : Injective T := injective_mfderiv_track q (hA.mdifferentiableAt (by simp))
      (ambient_slice_bijective_mfderiv hD q.1 q.2).injective
    have hs : Surjective T :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi
    let L := (LinearEquiv.ofBijective T.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv
    change T.IsInvertible
    exact ⟨L, rfl⟩
  have hl : IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ (track A) :=
    fun p => isLocalDiffeomorphAt_boundaryless isOpen_univ (mem_univ p)
      hsmooth.contMDiffOn (hinv p)
  have hglobal : Bijective (track A) := by
    constructor
    · rintro ⟨t, x⟩ ⟨s, y⟩ heq
      have ht : t = s := congrArg (fun p : ℝ × M => p.1) heq
      subst s
      exact Prod.ext rfl ((hbij t).injective (congrArg (fun p : ℝ × M => p.2) heq))
    · rintro ⟨t, x⟩
      obtain ⟨y, hy⟩ := (hbij t).surjective x
      exact ⟨(t, y), Prod.ext rfl hy⟩
  exact ⟨hl.diffeomorphOfBijective hglobal, fun _ => rfl⟩

end Wikipedia.HopfProblem.OrbitPair.NativeFamily

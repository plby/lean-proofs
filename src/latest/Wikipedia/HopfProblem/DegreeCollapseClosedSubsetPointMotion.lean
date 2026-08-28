import Wikipedia.HopfProblem.DegreeCollapseNativeImageDensity

/-!
# Supported point transport avoiding a closed subset of a smooth image

The protected subset need not itself be a manifold or a full smooth image.
Small supported motions first move both endpoints off the containing smooth
image. Relative path avoidance connects the moved endpoints; composition
then gives the original endpoint formula while fixing the protected subset.
-/

noncomputable section

open Set Function ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def supported_isotopy_fixing_set_disjoint_from_support
    {d : Diffeomorph J J M M ∞} {K S T : Set M}
    (A : SupportedRelativeIsotopy d K S) (hTK : ∀ z ∈ T, z ∉ K) :
    SupportedRelativeIsotopy d K T where
  family := A.family
  smooth := A.smooth
  zero := A.zero
  one := A.one
  slices := A.slices
  fixedOutside := A.fixedOutside
  fixedOn t z hz := A.fixedOutside t z (hTK z hz)

variable {V H' Y : Type*}
  [FiniteDimensional ℝ E] [J.Boundaryless] [IsManifold J ∞ M] [T2Space M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ V H'}
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]

theorem exists_supported_point_motion_avoiding_closed_subset
    (b : C(Y, M)) (hb : ContMDiff I J ∞ b) (hclosed : IsClosed (range b))
    (hdim : 1 + Module.finrank ℝ V < Module.finrank ℝ E)
    {C : Set M} (hC : IsClosed C) (hCb : C ⊆ range b)
    {x y : M} (γ : Path x y) (hx : x ∉ C) (hy : y ∉ C) :
    ∃ (d : Diffeomorph J J M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ Cᶜ ∧ Nonempty (SupportedRelativeIsotopy d K C) ∧ d x = y := by
  have hdense := dense_compl_native_smooth_image hb
    (show Module.finrank ℝ V < Module.finrank ℝ E by omega)
  have hpush (z : M) (hz : z ∉ C) :
      ∃ (d : Diffeomorph J J M M ∞) (K : Set M),
        IsCompact K ∧ K ⊆ Cᶜ ∧ Nonempty (SupportedRelativeIsotopy d K ∅) ∧
        d z ∉ range b := by
    obtain ⟨U, hU, hzU, -, hmove⟩ :=
      exists_open_compactly_supported_point_motion (J := J) hC.isOpen_compl hz
    obtain ⟨w, hwavoid, hwU⟩ := hdense.exists_mem_open hU ⟨z, hzU⟩
    obtain ⟨d, K, hK, hKC, hIso, hdz⟩ := hmove w hwU
    exact ⟨d, K, hK, hKC, hIso, hdz.symm ▸ hwavoid⟩
  obtain ⟨d, K, hK, hKC, ⟨A⟩, hdx⟩ := hpush x hx
  obtain ⟨e, L, hL, hLC, ⟨B⟩, hey⟩ := hpush y hy
  let η : Path (d x) (e y) :=
    (((isotopicToIdentity_joined A.isotopicToIdentity x).somePath.symm).trans γ).trans
      (isotopicToIdentity_joined B.isotopicToIdentity y).somePath
  obtain ⟨ξ, -, hξ⟩ := exists_smooth_path_avoiding_closed_image η b hb hclosed hdim hdx hey
  obtain ⟨p, N, hN, hNb, ⟨P⟩, hp⟩ :=
    exists_compactly_supported_point_motion_of_path (J := J) hclosed.isOpen_compl ξ hξ
  have hNC : N ⊆ Cᶜ := fun z hz hzc => hNb hz (hCb hzc)
  have htotal : (K ∪ N) ∪ L ⊆ Cᶜ := union_subset (union_subset hKC hNC) hLC
  let A' := SupportedGerms.compose_supported_relative_isotopies
    (SupportedGerms.compose_supported_relative_isotopies A P)
    (SupportedGerms.inverse_supported_relative_isotopy B)
  refine ⟨(d.trans p).trans e.symm, (K ∪ N) ∪ L,
    (hK.union hN).union hL, htotal,
    ⟨supported_isotopy_fixing_set_disjoint_from_support A'
      (fun z hz hzk => htotal hzk hz)⟩, ?_⟩
  change e.symm (p (d x)) = y
  rw [hp, e.symm_apply_apply]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

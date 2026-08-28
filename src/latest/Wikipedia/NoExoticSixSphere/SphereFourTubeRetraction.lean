import Wikipedia.NoExoticSixSphere.SphereFourTubeCore

/-!
# An actual retraction from the core complement to the tube exterior

Clamp a nonzero normal radius upward to one and fix the complement of
the open unit tube. Compactness of the closed unit tube proves continuity
across the edge of the coordinate target. No inverse-coordinate function
is asserted continuous outside its actual domain.
-/

noncomputable section

open Function Set Metric Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization

def normalClamp (v : Vector 4) : Vector 4 := (max 1 ‖v‖ / ‖v‖) • v

theorem norm_normalClamp {v : Vector 4} (hv : v ≠ 0) :
    ‖normalClamp v‖ = max 1 ‖v‖ := by
  rw [normalClamp, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (le_max_of_le_left zero_le_one) (norm_nonneg v)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)]

theorem normalClamp_eq_self {v : Vector 4} (hv : 1 ≤ ‖v‖) : normalClamp v = v := by
  have hn : ‖v‖ ≠ 0 := ne_of_gt (zero_lt_one.trans_le hv)
  rw [normalClamp, max_eq_right hv, div_self hn, one_smul]

theorem continuousAt_normalClamp {v : Vector 4} (hv : v ≠ 0) :
    ContinuousAt normalClamp v :=
  ((continuous_const.max continuous_norm).continuousAt.div continuous_norm.continuousAt
    (norm_ne_zero_iff.mpr hv)).smul continuousAt_id

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

def rawRetraction (x : CoreComplement Φ) : M := by
  classical
  exact if x.val ∈ Φ.target then
    Φ ((Φ.symm x.val).1, normalClamp (Φ.symm x.val).2) else x.val

theorem rawRetraction_eq_of_exterior (hΦ : Φ.source = univ) (x : CoreComplement Φ)
    (hx : x.val ∉ openRegion Φ 1) : rawRetraction Φ x = x.val := by
  classical
  by_cases hxT : x.val ∈ Φ.target
  · have hn : 1 ≤ ‖(Φ.symm x.val).2‖ := not_lt.mp
      (fun h ↦ hx ((mem_openRegion_iff Φ hΦ 1 x.val).mpr ⟨hxT, h⟩))
    rw [rawRetraction, if_pos hxT, normalClamp_eq_self hn]
    exact Φ.toPartialEquiv.right_inv hxT
  · simp only [rawRetraction, if_neg hxT]

theorem rawRetraction_mem_exterior (hΦ : Φ.source = univ) (x : CoreComplement Φ) :
    rawRetraction Φ x ∉ openRegion Φ 1 := by
  classical
  by_cases hxT : x.val ∈ Φ.target
  · rw [rawRetraction, if_pos hxT]
    intro hmem
    have hn := ((mem_openRegion_iff Φ hΦ 1 _).mp hmem).2
    have hi : Φ.symm (Φ ((Φ.symm x.val).1, normalClamp (Φ.symm x.val).2)) =
        ((Φ.symm x.val).1, normalClamp (Φ.symm x.val).2) :=
      Φ.toPartialEquiv.left_inv (hΦ.symm ▸ mem_univ _)
    rw [hi] at hn
    change ‖normalClamp (Φ.symm x.val).2‖ < 1 at hn
    rw [norm_normalClamp (inverse_normal_ne_zero Φ hΦ x hxT)] at hn
    exact not_lt_of_ge (le_max_left _ _) hn
  · rw [rawRetraction, if_neg hxT]
    exact fun h ↦ hxT ((mem_openRegion_iff Φ hΦ 1 x.val).mp h).1

theorem continuous_rawRetraction [T2Space M] (hΦ : Φ.source = univ) :
    Continuous (rawRetraction Φ) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hxT : x.val ∈ Φ.target
  · have hi : ContinuousAt (fun y : CoreComplement Φ ↦ Φ.symm y.val) x :=
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hxT)).continuousAt.comp
        (f := fun y : CoreComplement Φ ↦ y.val) continuous_subtype_val.continuousAt
    have hc : ContinuousAt
        (fun y : CoreComplement Φ ↦ normalClamp (Φ.symm y.val).2) x :=
      (continuousAt_normalClamp (inverse_normal_ne_zero Φ hΦ x hxT)).comp
        (f := fun y : CoreComplement Φ ↦ (Φ.symm y.val).2) hi.snd
    have hraw : ContinuousAt (fun y : CoreComplement Φ ↦
        Φ ((Φ.symm y.val).1, normalClamp (Φ.symm y.val).2)) x :=
      (contMDiff Φ hΦ).continuous.continuousAt.comp
        (f := fun y : CoreComplement Φ ↦ ((Φ.symm y.val).1, normalClamp (Φ.symm y.val).2))
        (hi.fst.prodMk hc)
    apply hraw.congr_of_eventuallyEq
    filter_upwards [(Φ.open_target.preimage continuous_subtype_val).mem_nhds hxT] with y hy
    change y.val ∈ Φ.target at hy
    simp only [rawRetraction, if_pos hy]
  · have hxK : x.val ∉ closedRegion Φ 1 :=
      fun h ↦ hxT (closedRegion_subset_target Φ hΦ 1 h)
    apply (continuous_subtype_val.continuousAt :
      ContinuousAt (fun y : CoreComplement Φ ↦ y.val) x).congr_of_eventuallyEq
    filter_upwards [((isCompact_closedRegion Φ hΦ 1).isClosed.isOpen_compl.preimage
      continuous_subtype_val).mem_nhds hxK] with y hy
    exact rawRetraction_eq_of_exterior Φ hΦ y
      (fun h ↦ hy (openRegion_one_subset_closedRegion_one Φ h))

def exteriorInclusion : C(Exterior Φ, CoreComplement Φ) :=
  ⟨fun x ↦ ⟨x.val, fun hx ↦ x.property (core_subset_openRegion_one Φ hx)⟩,
    continuous_subtype_val.subtype_mk _⟩

def retraction [T2Space M] (hΦ : Φ.source = univ) : C(CoreComplement Φ, Exterior Φ) :=
  ⟨fun x ↦ ⟨rawRetraction Φ x, rawRetraction_mem_exterior Φ hΦ x⟩,
    (continuous_rawRetraction Φ hΦ).subtype_mk _⟩

theorem retraction_exterior [T2Space M] (hΦ : Φ.source = univ) (x : Exterior Φ) :
    retraction Φ hΦ (exteriorInclusion Φ x) = x :=
  Subtype.ext (rawRetraction_eq_of_exterior Φ hΦ _ x.property)

end NoExoticSixSphere.SphereFourTube

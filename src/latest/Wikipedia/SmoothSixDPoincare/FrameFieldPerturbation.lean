import Wikipedia.SmoothSixDPoincare.PlaneSingularParameters
import Wikipedia.SmoothSixDPoincare.ManifoldImageDimension

/-!
# Small full-rank perturbations of arbitrary smooth two-column fields

The field need not be the differential of a map. Two normalized kernel
directions parametrize every singular perturbation; their bad parameter
images have dimension at most `dim F + 3`. Thus in normal dimension four
or higher a single arbitrarily small two-column perturbation is injective
throughout any open smooth field domain.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold ENNReal

namespace Wikipedia.SmoothSixDPoincare.FrameField

open PlaneImmersion (Plane linearMap)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def badFirst (L : Plane → (Plane →L[ℝ] F)) (q : Plane × (ℝ × F)) : F × F :=
  (-L q.1 (1, q.2.1) - q.2.1 • q.2.2, q.2.2)

def badSecond (L : Plane → (Plane →L[ℝ] F)) (q : Plane × (ℝ × F)) : F × F :=
  (q.2.2, -L q.1 (q.2.1, 1) - q.2.1 • q.2.2)

theorem contDiffOn_badFirst {L : Plane → (Plane →L[ℝ] F)} {U : Set Plane}
    (hL : ContDiffOn ℝ ∞ L U) :
    ContDiffOn ℝ ∞ (badFirst L) (U ×ˢ (univ : Set (ℝ × F))) := by
  have he : ContDiffOn ℝ ∞ (fun q : Plane × (ℝ × F) => L q.1 (1, q.2.1))
      (U ×ˢ (univ : Set (ℝ × F))) :=
    (hL.comp contDiffOn_fst (fun _ hp => hp.1)).clm_apply
      (contDiff_const.prodMk (contDiff_fst.comp contDiff_snd)).contDiffOn
  exact (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul
    (contDiff_snd.comp contDiff_snd)).contDiffOn).prodMk
      (contDiff_snd.comp contDiff_snd).contDiffOn

theorem contDiffOn_badSecond {L : Plane → (Plane →L[ℝ] F)} {U : Set Plane}
    (hL : ContDiffOn ℝ ∞ L U) :
    ContDiffOn ℝ ∞ (badSecond L) (U ×ˢ (univ : Set (ℝ × F))) := by
  have he : ContDiffOn ℝ ∞ (fun q : Plane × (ℝ × F) => L q.1 (q.2.1, 1))
      (U ×ˢ (univ : Set (ℝ × F))) :=
    (hL.comp contDiffOn_fst (fun _ hp => hp.1)).clm_apply
      ((contDiff_fst.comp contDiff_snd).prodMk contDiff_const).contDiffOn
  exact (contDiff_snd.comp contDiff_snd).contDiffOn.prodMk
    (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul
      (contDiff_snd.comp contDiff_snd)).contDiffOn)

/-- Every nontrivial kernel gives a parameter in one of the two explicit bad images. -/
theorem mem_bad_of_nonzero_kernel (L : Plane → (Plane →L[ℝ] F)) (A : F × F)
    {U : Set Plane} {x v : Plane} (hx : x ∈ U) (hv : v ≠ 0)
    (hker : (L x + linearMap A) v = 0) :
    A ∈ badFirst L '' (U ×ˢ (univ : Set (ℝ × F))) ∪
      badSecond L '' (U ×ˢ (univ : Set (ℝ × F))) := by
  have hker' : (fderiv ℝ (L x) 0 + linearMap A) v = 0 := by
    rw [(L x).hasFDerivAt.fderiv]
    exact hker
  rcases PlaneImmersion.mem_bad_of_nonzero_kernel (L x) A 0 v hv hker' with hfirst | hsecond
  · obtain ⟨q, hq⟩ := hfirst
    refine Or.inl ⟨(x, q.2), ⟨hx, mem_univ _⟩, ?_⟩
    unfold PlaneImmersion.badFirst at hq
    rw [(L x).hasFDerivAt.fderiv] at hq
    exact hq
  · obtain ⟨q, hq⟩ := hsecond
    refine Or.inr ⟨(x, q.2), ⟨hx, mem_univ _⟩, ?_⟩
    unfold PlaneImmersion.badSecond at hq
    rw [(L x).hasFDerivAt.fderiv] at hq
    exact hq

theorem injective_of_not_bad (L : Plane → (Plane →L[ℝ] F)) {A : F × F} {U : Set Plane}
    (hA : A ∉ badFirst L '' (U ×ˢ (univ : Set (ℝ × F))) ∪
      badSecond L '' (U ×ˢ (univ : Set (ℝ × F)))) {x : Plane} (hx : x ∈ U) :
    Injective (L x + linearMap A) := by
  intro v w hvw
  have hz : (L x + linearMap A) (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have heq : v - w = 0 := by
    by_contra hne
    exact hA (mem_bad_of_nonzero_kernel L A hx hne hz)
  exact sub_eq_zero.mp heq

variable [FiniteDimensional ℝ F]

theorem dense_good_parameters {L : Plane → (Plane →L[ℝ] F)} {U : Set Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hdim : 4 ≤ Module.finrank ℝ F) :
    Dense (badFirst L '' (U ×ˢ (univ : Set (ℝ × F))) ∪
      badSecond L '' (U ×ˢ (univ : Set (ℝ × F))))ᶜ := by
  have hfirst := GeneralPosition.dimH_image_manifold_le (hU.prod isOpen_univ)
    (contDiffOn_badFirst hL).contMDiffOn
  have hsecond := GeneralPosition.dimH_image_manifold_le (hU.prod isOpen_univ)
    (contDiffOn_badSecond hL).contMDiffOn
  have hbad : dimH (badFirst L '' (U ×ˢ (univ : Set (ℝ × F))) ∪
      badSecond L '' (U ×ˢ (univ : Set (ℝ × F)))) ≤
      (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
    rw [dimH_union]
    exact max_le hfirst hsecond
  have hd : Module.finrank ℝ (Plane × (ℝ × F)) < Module.finrank ℝ (F × F) := by
    change Module.finrank ℝ ((ℝ × ℝ) × (ℝ × F)) < Module.finrank ℝ (F × F)
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  exact dense_compl_of_dimH_lt_finrank (hbad.trans_lt (Nat.cast_lt.mpr hd))

/-- Arbitrarily small constant columns make the arbitrary smooth field full-rank on its domain. -/
theorem exists_small_fullRank_perturbation {L : Plane → (Plane →L[ℝ] F)} {U : Set Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hdim : 4 ≤ Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : F × F, ‖A‖ < ε ∧ ∀ x ∈ U, Injective (L x + linearMap A) := by
  obtain ⟨A, hA, hnorm⟩ := (dense_good_parameters hU hL hdim).exists_dist_lt 0 hε
  exact ⟨A, by simpa only [dist_zero_left] using hnorm, fun _ hx => injective_of_not_bad L hA hx⟩

end Wikipedia.SmoothSixDPoincare.FrameField

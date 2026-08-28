import Wikipedia.HopfProblem.DegreeCollapseNativeLevelSuspensionGerms

/-!
# Compact native realization of an actual level isotopy

The smooth native suspension generator has time speed one, no zeros, and
agrees with the old vertical field outside the compact product slab.
Its complete flow realizes the original level diffeomorphism exactly,
while all prescribed fixed lines retain their entire old trajectories.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z N : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
  [IsManifold 𝓘(ℝ, Z) ∞ N]

theorem nativeSuspensionFlow_fixed_line
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) {x : N}
    (hfix : ∀ s : ℝ, Ψ (x, s) = (x, s)) (s t : ℝ) :
    nativeSuspensionFlow Ψ t (x, s) = (x, s + t) := by
  have hi : Ψ.symm (x, s) = (x, s) := by
    have hh := congrArg Ψ.symm (hfix s)
    rw [Ψ.symm_apply_apply] at hh
    exact hh.symm
  change Ψ ((Ψ.symm (x, s)).1, (Ψ.symm (x, s)).2 + t) = _
  rw [hi]
  exact hfix (s + t)

variable [T2Space N]

theorem exists_compact_native_level_suspension
    (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞) {K S : Set N}
    (hK : IsCompact K) (I : SupportedRelativeIsotopy D K S) :
    ∃ Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
        (N × ℝ) (N × ℝ) ∞,
      IsCompact (K ×ˢ Icc (1 / 3 : ℝ) (2 / 3)) ∧
      (∀ p, (Ψ p).2 = p.2) ∧
      (∀ p, p.2 ≤ 1 / 3 → Ψ p = p) ∧
      (∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2)) ∧
      ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)).tangent ∞
        (fun p : N × ℝ => (⟨p, nativeSuspensionField Ψ p⟩ :
          TangentBundle (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ))) ∧
      (∀ p, IsMIntegralCurve (fun t : ℝ => nativeSuspensionFlow Ψ t p)
        (nativeSuspensionField Ψ)) ∧
      (∀ p, (nativeSuspensionField Ψ p).2 = 1) ∧
      (∀ p, nativeSuspensionField Ψ p ≠ 0) ∧
      (∀ p ∉ K ×ˢ Icc (1 / 3 : ℝ) (2 / 3),
        nativeSuspensionField Ψ p = nativeVerticalField p) ∧
      (∀ p ∉ K ×ˢ Icc (1 / 3 : ℝ) (2 / 3),
        ∀ᶠ q in 𝓝 p, nativeSuspensionField Ψ q = nativeVerticalField q) ∧
      (∀ x, nativeSuspensionFlow Ψ 1 (x, 0) = (D x, 1)) ∧
      (∀ t p, (nativeSuspensionFlow Ψ t p).2 = p.2 + t) ∧
      (∀ x ∉ K, ∀ s t : ℝ, nativeSuspensionFlow Ψ t (x, s) = (x, s + t)) ∧
      ∀ x ∈ S, ∀ s t : ℝ, nativeSuspensionFlow Ψ t (x, s) = (x, s + t) := by
  obtain ⟨Ψ, hheight, hleft, hright, hout, hfixed⟩ := exists_native_base_suspension D I
  have hC : IsCompact (K ×ˢ Icc (1 / 3 : ℝ) (2 / 3)) := hK.prod isCompact_Icc
  have hfield (p : N × ℝ) (hp : p ∉ K ×ˢ Icc (1 / 3 : ℝ) (2 / 3)) :
      nativeSuspensionField Ψ p = nativeVerticalField p := by
    by_cases hx : p.1 ∈ K
    · have ht : p.2 ∉ Icc (1 / 3 : ℝ) (2 / 3) := fun ht => hp ⟨hx, ht⟩
      by_cases hlo : p.2 < 1 / 3
      · exact nativeSuspensionField_eq_vertical_below Ψ hleft p hlo
      · have hhi : 2 / 3 < p.2 := lt_of_not_ge (fun hh => ht ⟨le_of_not_gt hlo, hh⟩)
        exact nativeSuspensionField_eq_vertical_above Ψ D hheight hright p hhi
    · exact nativeSuspensionField_eq_vertical_off_base Ψ hout p hx
  have hgerm (p : N × ℝ) (hp : p ∉ K ×ˢ Icc (1 / 3 : ℝ) (2 / 3)) :
      ∀ᶠ q in 𝓝 p, nativeSuspensionField Ψ q = nativeVerticalField q := by
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hfield q hq
  refine ⟨Ψ, hC, hheight, hleft, hright, contMDiff_nativeSuspensionField Ψ,
    nativeSuspensionFlow_integralCurve Ψ, nativeSuspensionField_height Ψ hheight,
    nativeSuspensionField_ne_zero Ψ hheight, hfield, hgerm, ?_,
    nativeSuspensionFlow_height Ψ hheight, ?_, ?_⟩
  · intro x
    have hzero : Ψ (x, (0 : ℝ)) = (x, 0) := hleft (x, 0) (by norm_num)
    rw [← hzero, nativeSuspensionFlow_chart, zero_add]
    exact hright (x, 1) (by norm_num)
  · intro x hx s t
    exact nativeSuspensionFlow_fixed_line Ψ (fun u => hout (x, u) hx) s t
  · intro x hx s t
    exact nativeSuspensionFlow_fixed_line Ψ (fun u => hfixed (x, u) hx) s t

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

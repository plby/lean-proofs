import Wikipedia.HopfProblem.DegreeCollapseNativeLevelSuspensionHeight

/-!
# Stationary exterior germs of a native level suspension

Equality of the actual flow germs identifies their native generator
vectors. The fixed base region and the two stationary time collars then
give equality with the original vertical field outside the suspension
slab, without coordinates on the level manifold.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z N : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
  [IsManifold 𝓘(ℝ, Z) ∞ N]

theorem nativeSuspensionField_eq_vertical_of_flow_germ
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) (p : N × ℝ)
    (heq : (fun t : ℝ => nativeSuspensionFlow Ψ t p) =ᶠ[𝓝 0]
      (fun t : ℝ => (p.1, p.2 + t))) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
  have hw := nativeSuspensionFlow_integralCurve Ψ p 0
  have hv := nativeVerticalField_integralCurve (Z := Z) p 0
  have hh := hw.mfderiv.symm.trans (heq.mfderiv_eq.trans hv.mfderiv)
  have hval := congrArg (fun L : ℝ →L[ℝ] (Z × ℝ) => L 1) hh
  change (1 : ℝ) • nativeSuspensionField Ψ (nativeSuspensionFlow Ψ 0 p) =
    (1 : ℝ) • nativeVerticalField (p.1, p.2 + 0) at hval
  have h0 : nativeSuspensionFlow Ψ (0 : ℝ) p = p := by
    change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + 0) = p
    rw [add_zero, Prod.mk.eta, Ψ.apply_symm_apply]
  rw [one_smul, one_smul, h0] at hval
  convert! hval using 1

theorem nativeSuspensionField_eq_vertical_off_base
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) {K : Set N}
    (hfix : ∀ p, p.1 ∉ K → Ψ p = p) (p : N × ℝ) (hp : p.1 ∉ K) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
  have hi : Ψ.symm p = p := by
    have hh := congrArg Ψ.symm (hfix p hp)
    rw [Ψ.symm_apply_apply] at hh
    exact hh.symm
  apply nativeSuspensionField_eq_vertical_of_flow_germ Ψ p
  apply Eventually.of_forall
  intro t
  change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t) = (p.1, p.2 + t)
  rw [hi]
  exact hfix (p.1, p.2 + t) hp

theorem nativeSuspensionField_eq_vertical_below
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) {a : ℝ}
    (hleft : ∀ p, p.2 ≤ a → Ψ p = p) (p : N × ℝ) (hp : p.2 < a) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
  have hi : Ψ.symm p = p := by
    have hh := congrArg Ψ.symm (hleft p hp.le)
    rw [Ψ.symm_apply_apply] at hh
    exact hh.symm
  apply nativeSuspensionField_eq_vertical_of_flow_germ Ψ p
  filter_upwards [eventually_lt_nhds (sub_pos.mpr hp)] with t ht
  change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t) = (p.1, p.2 + t)
  rw [hi]
  exact hleft (p.1, p.2 + t) (by dsimp; linarith)

theorem nativeSuspensionField_eq_vertical_above
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) (D : N → N) {b : ℝ}
    (hheight : ∀ p, (Ψ p).2 = p.2)
    (hright : ∀ p, b ≤ p.2 → Ψ p = (D p.1, p.2)) (p : N × ℝ) (hp : b < p.2) :
    nativeSuspensionField Ψ p = nativeVerticalField p := by
  let q := Ψ.symm p
  have hq : Ψ q = p := Ψ.apply_symm_apply p
  have htime : q.2 = p.2 := (hheight q).symm.trans (congrArg Prod.snd hq)
  have hbase : D q.1 = p.1 := by
    have hh := hright q (by rw [htime]; exact hp.le)
    rw [hq] at hh
    exact (congrArg Prod.fst hh).symm
  apply nativeSuspensionField_eq_vertical_of_flow_germ Ψ p
  filter_upwards [eventually_gt_nhds (show b - p.2 < (0 : ℝ) by linarith)] with t ht
  change Ψ (q.1, q.2 + t) = (p.1, p.2 + t)
  rw [hright (q.1, q.2 + t) (by dsimp; rw [htime]; linarith), hbase, htime]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

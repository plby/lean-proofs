import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse
import Wikipedia.SmoothSixDPoincare.CompactLocalDiffeomorph

/-!
# The coordinate change that straightens height on a compact collar

Keep the original level point and replace the transverse parameter by the
actual height. Unit transverse derivative and constant zero-section height
make this coordinate change locally invertible along the whole zero section.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.CollarHeight

variable {D H X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [TopologicalSpace H] {I : ModelWithCorners ℝ D H}
  [TopologicalSpace X] [ChartedSpace H X]

def heightChange (h : X × ℝ → ℝ) (z : X × ℝ) : X × ℝ := (z.1, h z)

omit [TopologicalSpace X] in
theorem heightChange_zero {h : X × ℝ → ℝ} (hzero : ∀ x, h (x, 0) = 0) (x : X) :
    heightChange h (x, 0) = (x, 0) := Prod.ext rfl (hzero x)

theorem contMDiffOn_heightChange {h : X × ℝ → ℝ} {U : Set (X × ℝ)}
    (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ (heightChange h) U :=
  contMDiff_fst.contMDiffOn.prodMk hh

/-- The full derivative of the replacement height is the original transverse coordinate. -/
theorem mfderiv_height_zero {h : X × ℝ → ℝ} {U : Set (X × ℝ)}
    (hU : IsOpen U) (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U)
    (hzero : ∀ x, h (x, 0) = 0) (x : X) (hx : (x, 0) ∈ U)
    (htime : HasDerivAt (fun t : ℝ => h (x, t)) 1 0) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) h (x, 0) = ContinuousLinearMap.snd ℝ D ℝ := by
  have hbase : (fun y : X => h (y, 0)) = fun _ => 0 := funext hzero
  have ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => h (x, t)) 0 =
      ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv, htime.hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext
    intro t
    simp only [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, mul_one]
  apply ContinuousLinearMap.ext
  intro v
  rw [mfderiv_prod_eq_add_apply ((hh.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)),
    hbase, mfderiv_const, ht]
  change (0 : ℝ) + v.2 = v.2
  exact zero_add _

/-- The height-coordinate change has identity differential along the actual zero section. -/
theorem mfderiv_heightChange_zero {h : X × ℝ → ℝ} {U : Set (X × ℝ)}
    (hU : IsOpen U) (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U)
    (hzero : ∀ x, h (x, 0) = 0) (x : X) (hx : (x, 0) ∈ U)
    (htime : HasDerivAt (fun t : ℝ => h (x, t)) 1 0) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (heightChange h) (x, 0) =
      ContinuousLinearMap.id ℝ (D × ℝ) := by
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (fun z => (z.1, h z)) (x, 0) = _
  rw [mfderiv_prodMk mdifferentiableAt_fst
    ((hh.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)),
    mfderiv_fst, mfderiv_height_zero hU hh hzero x hx htime]
  rfl

variable [CompleteSpace D] [I.Boundaryless] [IsManifold I ∞ X]
  [T2Space X] [CompactSpace X] [Nonempty X]

/-- Compactness gives a single actual inverse neighborhood for the height-coordinate change. -/
theorem exists_heightChangeChart {h : X × ℝ → ℝ} {U : Set (X × ℝ)}
    (hU : IsOpen U) (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U)
    (hzero : ∀ x, h (x, 0) = 0) (hsource : ∀ x, (x, 0) ∈ U)
    (htime : ∀ x, HasDerivAt (fun t : ℝ => h (x, t)) 1 0) :
    ∃ χ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (X × ℝ) (X × ℝ) ∞,
      (univ : Set X) ×ˢ {(0 : ℝ)} ⊆ χ.source ∧ χ.source ⊆ U ∧
      (χ : X × ℝ → X × ℝ) = heightChange h := by
  let K : Set (X × ℝ) := univ ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hinj : InjOn (heightChange h) K := by
    rintro ⟨x, s⟩ ⟨-, hs⟩ ⟨y, t⟩ ⟨-, ht⟩ hxy
    have hs0 : s = 0 := hs
    have ht0 : t = 0 := ht
    subst s
    subst t
    rw [heightChange_zero hzero x, heightChange_zero hzero y] at hxy
    exact hxy
  have hloc : ∀ z ∈ K, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (heightChange h) z := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    apply isLocalDiffeomorphAt_boundaryless hU (hsource x) (contMDiffOn_heightChange hh)
    rw [mfderiv_heightChange_zero hU hh hzero x (hsource x) (htime x)]
    exact ⟨ContinuousLinearEquiv.refl ℝ (D × ℝ), rfl⟩
  exact exists_partialDiffeomorph_near_compact hK hinj hloc hU
    (fun ⟨x, t⟩ hx => by
      have ht : t = 0 := hx.2
      simpa only [ht] using hsource x)

end Wikipedia.SmoothSixDPoincare.CollarHeight

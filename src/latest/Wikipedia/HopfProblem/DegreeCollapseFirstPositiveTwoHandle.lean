import Wikipedia.HopfProblem.DegreeCollapseCappedBeltMeridian
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenFirstPositiveHandle
import Wikipedia.HopfProblem.DegreeCollapseBoundedPrescribedFlowWindows
import Wikipedia.SmoothSixDPoincare.RegularBandDiffeomorph

/-!
# The actual first positive two-handle and its capped meridian sphere

The original boundary identifies the native zero level topologically.
Before the first positive critical value the entire positive band is
regular. Its native level diffeomorphism transfers simple connectivity to
the actual lower surgery level, supplying the cap required by the sphere
construction. No simple-connectivity hypothesis on that level is supplied.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_first_positive_of_index_lower_bound {k : ℕ}
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hlower : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      k ≤ nativeMorseIndex (Vector 7) P.function p)
    (q₀ : criticalPoints (Vector 7) P.function) (hq₀ : 0 < P.function q₀)
    (hi₀ : nativeMorseIndex (Vector 7) P.function q₀ = k) :
    ∃ q : criticalPoints (Vector 7) P.function,
      0 < P.function q ∧ nativeMorseIndex (Vector 7) P.function q = k ∧
      ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
        P.function q ≤ P.function p := by
  classical
  let _ := P.finite_criticalPoints.fintype
  let K := Finset.univ.filter (fun p : criticalPoints (Vector 7) P.function => 0 < P.function p)
  have hq₀K : q₀ ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₀⟩
  obtain ⟨q, hqK, hmin⟩ := K.exists_min_image
    (fun p : criticalPoints (Vector 7) P.function => P.function p) ⟨q₀, hq₀K⟩
  have hq : 0 < P.function q := (Finset.mem_filter.mp hqK).2
  have hfirst (p : criticalPoints (Vector 7) P.function) (hp : 0 < P.function p) :
      P.function q ≤ P.function p := hmin p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
  have hindex : nativeMorseIndex (Vector 7) P.function q ≤ k := by
    rcases (hfirst q₀ hq₀).eq_or_lt with heq | hlt
    · have he : q = q₀ := Subtype.ext (P.distinct q.property q₀.property heq)
      rw [he, hi₀]
    · exact (horder q q₀ hq hlt).trans hi₀.le
  exact ⟨q, hq, le_antisymm hindex (hlower q hq), hfirst⟩

variable [SimplyConnectedSpace B]

theorem zeroLevel_simplyConnected :
    SimplyConnectedSpace {y : S.Space // P.function y = 0} := by
  let e₀ : {y : S.Space // P.function y = 0} ≃ₜ {y : S.Space // S.time y = 0} :=
    Homeomorph.setCongr (Set.ext (fun y => P.zero_iff y))
  exact (e₀.trans S.collar.zeroHomeomorph).toHomotopyEquiv.simplyConnectedSpace

theorem level_before_first_positive_simplyConnected
    (q : criticalPoints (Vector 7) P.function)
    (hfirst : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      P.function q ≤ P.function p)
    {a : ℝ} (ha : 0 ≤ a) (haq : a < P.function q) :
    SimplyConnectedSpace {y : S.Space // P.function y = a} := by
  let _ := P.zeroLevel_simplyConnected
  have hband : ∀ y, P.function y ∈ Icc 0 a → y ∉ criticalPoints (Vector 7) P.function := by
    intro y hy hcrit
    have hne : P.function y ≠ 0 := fun hz =>
      RegularTimeMorse.regular_zero_not_critical P.regular y hz hcrit
    have hpos : 0 < P.function y := lt_of_le_of_ne hy.1 (Ne.symm hne)
    exact (haq.not_ge ((hfirst ⟨y, hcrit⟩ hpos).trans hy.2)).elim
  let hz : ∀ y, P.function y = 0 → y ∉ criticalPoints (Vector 7) P.function :=
    fun y hy => hband y (by rw [hy]; exact ⟨le_rfl, ha⟩)
  let hr : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function :=
    fun y hy => hband y (by rw [hy]; exact ⟨ha, le_rfl⟩)
  let _ := RegularLevel.chartedSpace P.smooth hz
  let _ := RegularLevel.chartedSpace P.smooth hr
  obtain ⟨D⟩ := RegularLevel.nonempty_regularLevelDiffeomorph P.smooth ha hband
  exact D.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

theorem exists_capped_two_sphere_at_first_positive_handle
    (A : AdaptedSurgeryWindows (Vector 7) P.function)
    (q : criticalPoints (Vector 7) P.function)
    (hi : nativeMorseIndex (Vector 7) P.function q = 2)
    (hfirst : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      P.function q ≤ P.function p)
    (hlower : 0 ≤ A.toSurgeryWindows.lower q)
    (v : sphere (0 : (A.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ)) :
    let _ := RegularLevel.chartedSpace P.smooth (A.data q).upper_regular
    ∃ (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] (A.data q).chart.NegativeCoordinates)
      (γ : C(Hemisphere.Sphere 2, (A.data q).UpperLevel)),
      (∀ x : Hemisphere.Sphere 2, x.val 0 ≤ 0 →
        γ x = nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x))) ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ
        BeltMeridianSphere.negativeHemisphere ∧
      ∀ x (w : sphere (0 : (A.data q).chart.PositiveCoordinates) 1),
        γ x = (A.data q).surgery.beltSphere w ↔ x = BeltMeridianSphere.pole ∧ v = w := by
  let _ := RegularLevel.chartedSpace P.smooth (A.data q).upper_regular
  have hn : Module.finrank ℝ (A.data q).chart.NegativeCoordinates = 2 :=
    (nativeMorseIndex_eq_chart (A.data q).chart).symm.trans hi
  let _ : Fact (Module.finrank ℝ (A.data q).chart.NegativeCoordinates = 1 + 1) := ⟨hn⟩
  let _ : SimplyConnectedSpace (A.data q).LowerLevel :=
    P.level_before_first_positive_simplyConnected q hfirst hlower
      (A.toSurgeryWindows.lower_lt_value q)
  let L := StandardDiskCoordinates.coordinates hn
  obtain ⟨γ, hformula, hsmooth, hcount⟩ :=
    BeltMeridianSphere.exists_capped_meridian_sphere A P.smooth q (by simp) L v s hs hs0
  exact ⟨L, γ, hformula, hsmooth, hcount⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

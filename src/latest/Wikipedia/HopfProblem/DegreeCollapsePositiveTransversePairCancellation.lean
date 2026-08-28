import Wikipedia.HopfProblem.DegreeCollapsePositiveConnectionDescent
import Wikipedia.HopfProblem.DegreeCollapseFlowPreservingTransverseCancellation
import Wikipedia.HopfProblem.DegreeCollapseBoundedPrescribedFlowWindows

/-!
# Cancel an actual positive transverse pair with arbitrary negative endpoints

The positive connection-exclusion theorem first makes the pair consecutive
without changing the complete flow or the nonpositive germ. The same actual
native basin sheets therefore remain transverse. Native unique-connection
cancellation in a zero-avoiding band gives an excellent presentation of the
SAME state, deletes exactly the selected pair, and preserves every surviving
index and the entire original nonpositive germ.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B₀ : Type} [TopologicalSpace B₀] {S : CollaredSevenState B₀}
  (P : S.ExcellentMorsePresentation)
  {A B HA HB X Y : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace HA] [TopologicalSpace HB]
  {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB}
  [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]

theorem cancel_transverse_pair_of_no_other_positive_connection
    {V : (x : S.Space) → TangentSpace (𝓡 7) x}
    (hV : ContMDiff (𝓡 7) (𝓡 7).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡 7) S.Space)))
    (F : Flow ℝ S.Space) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints (Vector 7) P.function, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints (Vector 7) P.function →
      mvfderiv (𝓡 7) P.function x (V x) < 0)
    (hmodels : ∀ x ∈ criticalPoints (Vector 7) P.function,
      ∃ c : SignedMorseChart (E := Vector 7) P.function x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p q : criticalPoints (Vector 7) P.function)
    (hpositive : 0 < P.function p) (hpq : P.function p < P.function q)
    (hindex : nativeMorseIndex (Vector 7) P.function q =
      nativeMorseIndex (Vector 7) P.function p + 1)
    (hnoconnection : ∀ j : criticalPoints (Vector 7) P.function,
      0 < P.function j → j ≠ q → j ≠ p → ∀ x,
        ¬(Tendsto (fun t => F t x) atBot (𝓝 q.val) ∧
          Tendsto (fun t => F t x) atTop (𝓝 j.val)))
    {z : S.Space} (hzp : Tendsto (fun t => F t z) atTop (𝓝 p.val))
    (hzq : Tendsto (fun t => F t z) atBot (𝓝 q.val))
    (hunique : ∀ x, Tendsto (fun t => F t x) atBot (𝓝 q.val) →
      Tendsto (fun t => F t x) atTop (𝓝 p.val) → ∃ t, F t z = x)
    {α : X → S.Space} {β : Y → S.Space} {x : X} {y : Y}
    (hα : MDifferentiableAt I (𝓡 7) α x) (hβ : MDifferentiableAt I' (𝓡 7) β y)
    (hα0 : α x = z) (hβ0 : β y = z)
    (hαbasin : ∀ᶠ u in 𝓝 x, Tendsto (fun t => F t (α u)) atBot (𝓝 q.val))
    (hβbasin : ∀ᶠ u in 𝓝 y, Tendsto (fun t => F t (β u)) atTop (𝓝 p.val))
    (htrans : NativeTransversality.At I I' (𝓡 7) α β x y) :
    ∃ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) Q.function).ncard + 2 =
        (criticalPoints (Vector 7) P.function).ncard ∧
      (∀ w, w ∈ criticalPoints (Vector 7) Q.function ↔
        w ∈ criticalPoints (Vector 7) P.function ∧ w ≠ p.val ∧ w ≠ q.val) ∧
      (∀ w ∈ criticalPoints (Vector 7) Q.function,
        nativeMorseIndex (Vector 7) Q.function w = nativeMorseIndex (Vector 7) P.function w) ∧
      ∀ w, S.time w ≤ 0 → Q.function =ᶠ[𝓝 w] P.function := by
  obtain ⟨R, hcrit, hRp, hRpq, hconsecutive, hdescR, hmodelsR, hindices, hnegative⟩ :=
    P.exists_consecutive_pair_of_no_other_positive_connection hV F hF hzero hdesc hmodels
      p q hpositive hpq hnoconnection
  have hpcrit : p.val ∈ criticalPoints (Vector 7) R.function := hcrit.symm ▸ p.property
  have hqcrit : q.val ∈ criticalPoints (Vector 7) R.function := hcrit.symm ▸ q.property
  obtain ⟨cp, hcp⟩ := hmodelsR p.val hpcrit
  obtain ⟨cq, hcq⟩ := hmodelsR q.val hqcrit
  have hidx : Module.finrank ℝ cq.NegativeCoordinates =
      Module.finrank ℝ cp.NegativeCoordinates + 1 := by
    rw [← nativeMorseIndex_eq_chart cq, ← nativeMorseIndex_eq_chart cp,
      hindices q.val q.property, hindices p.val p.property]
    exact hindex
  have hcard : Fintype.card {i // cq.weights i = -1} =
      Fintype.card {i // cp.weights i = -1} + 1 := by
    simpa only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace,
      finrank_euclideanSpace] using hidx
  obtain ⟨W₀⟩ := nonempty_adaptedSurgeryWindows R.smooth R.morse R.distinct
  obtain ⟨W, _, _, _, _, hcut⟩ := W₀.exists_same_flow_windows_avoiding_level R.smooth R.morse
    (RegularTimeMorse.regular_zero_not_critical R.regular)
  let pR : criticalPoints (Vector 7) R.function := ⟨p.val, hpcrit⟩
  let qR : criticalPoints (Vector 7) R.function := ⟨q.val, hqcrit⟩
  have hpR : 0 < R.function pR := by change 0 < R.function p; rw [hRp]; exact hpositive
  have hconsecutiveR : ∀ s : criticalPoints (Vector 7) R.function,
      ¬(R.function pR < R.function s ∧ R.function s < R.function qR) := by
    intro s hs
    exact hconsecutive ⟨s.val, hcrit ▸ s.property⟩ hs
  have hpair := surgery_pair_band_isolation W.toSurgeryWindows pR qR hconsecutiveR
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior⟩ :=
    cancel_unique_connection_of_transverse_basin_sheets cp cq R.smooth R.morse
      (m := 6) (by simp [GLOrthonormalization.Vector]) hcard V hV
      (fun w hw => hzero w (hcrit ▸ hw)) hdescR F hF R.distinct hpcrit hqcrit hRpq
      (W.toSurgeryWindows.lower_lt_value pR) (W.toSurgeryWindows.value_lt_upper qR) hpair
      hzp hzq hunique hcp hcq hα hβ hα0 hβ0 hαbasin hβbasin htrans
  have hkeep := surviving_critical_germs_of_pair_band hpair hcritg hexterior
  have hregular (w : S.Space)
      (hw : R.function w ∈ Icc (W.toSurgeryWindows.lower pR) (W.toSurgeryWindows.upper qR)) :
      w ∉ criticalPoints (Vector 7) g := by
    intro h
    obtain ⟨hwR, hwp, hwq⟩ := (hcritg w).mp h
    exact (hpair w hwR hw).elim hwp hwq
  let Q := R.replacePositiveBand ⟨g, hg.continuous⟩ hg hmg (hcut pR hpR).le hexterior hregular
  rw [hcrit] at hcount
  refine ⟨Q, hcount, ?_, ?_, ?_⟩
  · intro w
    change w ∈ criticalPoints (Vector 7) g ↔ _
    rw [hcritg w, hcrit]
  · intro w hw
    exact (nativeMorseIndex_congr_germ (hkeep w hw)).trans
      (hindices w (hcrit ▸ ((hcritg w).mp hw).1))
  · intro w hw
    apply Filter.EventuallyEq.trans (hexterior w ?_) (hnegative w hw)
    intro hband
    have hpw : 0 < R.function w := (hcut pR hpR).trans hband.1
    exact (not_lt_of_ge hw) ((R.positive_iff w).mp hpw)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

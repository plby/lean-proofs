import Wikipedia.HopfProblem.DegreeCollapsePositiveMinimumBranches
import Wikipedia.HopfProblem.DegreeCollapsePositiveFlowPointDescent
import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchUniqueness
import Wikipedia.HopfProblem.DegreeCollapseZeroOneUniqueOrbitCancellation

/-!
# Actual relative zero/one cancellation eliminates positive births

The selected positive merging handle has two distinct minimum endpoints,
and the higher endpoint is positive. Preserve its actual flow while
making that pair consecutive, choose windows above zero, and apply native
unique-orbit cancellation. The resulting excellent presentation belongs
to the same original state and keeps the full nonpositive-half germ.
Minimal critical count therefore excludes every positive index-zero
critical point, without assuming a supplied cancellation sequence.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open MorseCancellation

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

namespace ExcellentMorsePresentation

variable (P : S.ExcellentMorsePresentation)

theorem cancel_realized_positive_higher_minimum
    (A : SurgeryWindows (Vector 7) P.function)
    {V : (x : S.Space) → TangentSpace (𝓡 7) x}
    (hV : ContMDiff (𝓡 7) (𝓡 7).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡 7) S.Space)))
    (G : Flow ℝ S.Space) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (hzero : ∀ x ∈ criticalPoints (Vector 7) P.function, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints (Vector 7) P.function →
      mvfderiv (𝓡 7) P.function x (V x) < 0)
    (hmodels : ∀ x ∈ criticalPoints (Vector 7) P.function,
      ∃ c : SignedMorseChart (E := Vector 7) P.function x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : criticalPoints (Vector 7) P.function)
    (hpzero : nativeMorseIndex (Vector 7) P.function p = 0)
    (hqone : nativeMorseIndex (Vector 7) P.function q = 1)
    (hpositive : 0 < P.function p) (hrp : P.function r < P.function p)
    (hp : P.function p < A.lower q)
    (u v : sphere (0 : (A.data q).chart.NegativeCoordinates) 1)
    (hback : ∀ x : (A.data q).LowerLevel,
      Tendsto (fun t => G t x) atBot (𝓝 q.val) ↔ x ∈ range (A.data q).surgery.attachingSphere)
    (hu : Tendsto (fun t => G t ((A.data q).surgery.attachingSphere u).val) atTop (𝓝 p.val))
    (hv : Tendsto (fun t => G t ((A.data q).surgery.attachingSphere v).val) atTop (𝓝 r.val))
    (hnoconnection : ∀ j : criticalPoints (Vector 7) P.function,
      j ≠ q → j ≠ p → j ≠ r → ∀ x,
        ¬(Tendsto (fun t => G t x) atBot (𝓝 q.val) ∧
          Tendsto (fun t => G t x) atTop (𝓝 j.val))) :
    ∃ R : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) R.function).ncard + 2 =
        (criticalPoints (Vector 7) P.function).ncard ∧
      (∀ x, x ∈ criticalPoints (Vector 7) R.function ↔
        x ∈ criticalPoints (Vector 7) P.function ∧ x ≠ p.val ∧ x ≠ q.val) ∧
      ∀ x, S.time x ≤ 0 → R.function =ᶠ[𝓝 x] P.function := by
  have hpr : p ≠ r := fun h => (ne_of_lt hrp) (congrArg (fun x => P.function x.val) h).symm
  obtain ⟨hzback, hunique⟩ := unique_connection_of_distinct_minimum_branches A
    P.smooth.continuous G p r q hqone hpr hp u v hback hu hv
  obtain ⟨Q, hcrit, hQp, _hQr, hQpq, hconsecutive, hdescQ, hmodelsQ, hindices, hnegative⟩ :=
    P.exists_positive_flow_preserving_consecutive_pair hV G hG hzero hdesc hmodels
      p r q hpositive hrp (hp.trans (A.lower_lt_value q)) hnoconnection
  let pQ : criticalPoints (Vector 7) Q.function := ⟨p.val, hcrit.symm ▸ p.property⟩
  let qQ : criticalPoints (Vector 7) Q.function := ⟨q.val, hcrit.symm ▸ q.property⟩
  have hconsecutiveQ : ∀ z : criticalPoints (Vector 7) Q.function,
      ¬(Q.function pQ < Q.function z ∧ Q.function z < Q.function qQ) := by
    intro z hz
    exact hconsecutive ⟨z.val, hcrit ▸ z.property⟩ hz
  have hpQpositive : 0 < Q.function pQ := by change 0 < Q.function p; rw [hQp]; exact hpositive
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows Q.smooth Q.morse Q.distinct
  obtain ⟨T, _, _, _, _, hcut⟩ := T₀.exists_same_flow_windows_avoiding_level Q.smooth Q.morse
    (RegularTimeMorse.regular_zero_not_critical Q.regular)
  obtain ⟨cp, hcp⟩ := hmodelsQ pQ pQ.property
  obtain ⟨cq, hcq⟩ := hmodelsQ qQ qQ.property
  obtain ⟨g, hg, hmg, hcount, hcritg, hkeep⟩ := cancel_unique_zero_one_connection cp cq
    Q.smooth Q.morse ((hindices p p.property).trans hpzero)
      ((hindices q q.property).trans hqone) hV G hG
      (fun x hx => hzero x (hcrit ▸ hx)) hdescQ Q.distinct pQ.property qQ.property hQpq
      (T.toSurgeryWindows.lower_lt_value pQ) (T.toSurgeryWindows.value_lt_upper qQ)
      (surgery_pair_band_isolation T.toSurgeryWindows pQ qQ hconsecutiveQ)
      hu hzback hunique hcp hcq
  have hreg (x : S.Space)
      (hx : Q.function x ∈ Icc (T.toSurgeryWindows.lower pQ) (T.toSurgeryWindows.upper qQ)) :
      x ∉ criticalPoints (Vector 7) g := by
    intro h
    obtain ⟨hxc, hxp, hxq⟩ := (hcritg x).mp h
    exact (surgery_pair_band_isolation T.toSurgeryWindows pQ qQ hconsecutiveQ x hxc hx).elim
      hxp hxq
  let R := Q.replacePositiveBand ⟨g, hg.continuous⟩ hg hmg (hcut pQ hpQpositive).le hkeep hreg
  refine ⟨R, hcount.trans (congrArg Set.ncard hcrit), ?_, ?_⟩
  · intro x
    change x ∈ criticalPoints (Vector 7) g ↔
      x ∈ criticalPoints (Vector 7) P.function ∧ x ≠ p.val ∧ x ≠ q.val
    simpa only [hcrit] using hcritg x
  · intro x hx
    apply Filter.EventuallyEq.trans (hkeep x ?_) (hnegative x hx)
    intro hband
    exact (not_lt_of_ge hx) ((Q.positive_iff x).mp ((hcut pQ hpQpositive).trans hband.1))

theorem exists_reduction_of_positive_minimum (eBoundary : B ≃ₜ Sphere 6)
    (p₀ : criticalPoints (Vector 7) P.function) (hp₀ : 0 < P.function p₀)
    (hzero₀ : nativeMorseIndex (Vector 7) P.function p₀ = 0) :
    ∃ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) Q.function).ncard + 2 =
        (criticalPoints (Vector 7) P.function).ncard ∧
      ∀ x, S.time x ≤ 0 → Q.function =ᶠ[𝓝 x] P.function := by
  obtain ⟨A, q, _hlower, hqone, u, v, V, G, p, r, _hnot, hV, hG, hzero, hdesc, hgerms,
    hpzero, hrzero, hpr, hpositive, hp, hr, hback, hu, hv, hnoconnection⟩ :=
    P.exists_positive_minimum_branches eBoundary p₀ hp₀ hzero₀
  have hmodels (x : S.Space) (hx : x ∈ criticalPoints (Vector 7) P.function) :
      ∃ c : SignedMorseChart (E := Vector 7) P.function x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    refine ⟨(A.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, A.critical_model_germ ⟨x, hx⟩] with y h₁ h₂
    exact h₁.trans h₂
  have hne : P.function p ≠ P.function r :=
    fun h => hpr (Subtype.ext (P.distinct p.property r.property h))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hrpositive : 0 < P.function r := hpositive.elim (fun h => h.trans hlt) id
    obtain ⟨Q, hcount, _, hkeep⟩ := P.cancel_realized_positive_higher_minimum
      A.toSurgeryWindows hV G hG hzero hdesc hmodels r p q hrzero hqone hrpositive hlt hr
      v u hback hv hu (fun j hjq hjr hjp => hnoconnection j hjq hjp hjr)
    exact ⟨Q, hcount, hkeep⟩
  · have hppositive : 0 < P.function p := hpositive.elim id (fun h => h.trans hgt)
    obtain ⟨Q, hcount, _, hkeep⟩ := P.cancel_realized_positive_higher_minimum
      A.toSurgeryWindows hV G hG hzero hdesc hmodels p r q hpzero hqone hppositive hgt hp
      u v hback hu hv hnoconnection
    exact ⟨Q, hcount, hkeep⟩

theorem no_positive_index_zero_of_minimal (eBoundary : B ≃ₜ Sphere 6)
    (hminimal : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) P.function).ncard ≤ (criticalPoints (Vector 7) Q.function).ncard)
    (p : criticalPoints (Vector 7) P.function) (hp : 0 < P.function p) :
    nativeMorseIndex (Vector 7) P.function p ≠ 0 := by
  intro hzero
  obtain ⟨Q, hcount, _⟩ := P.exists_reduction_of_positive_minimum eBoundary p hp hzero
  have h := hminimal Q
  omega

end ExcellentMorsePresentation

theorem exists_minimal_ordered_presentation_without_positive_births
    (S : CollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6) :
    ∃ P : S.ExcellentMorsePresentation,
      (∀ p q : criticalPoints (Vector 7) P.function,
        0 < P.function p → P.function p < P.function q →
          nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q) ∧
      (∀ Q : S.ExcellentMorsePresentation,
        (criticalPoints (Vector 7) P.function).ncard ≤
          (criticalPoints (Vector 7) Q.function).ncard) ∧
      ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
        nativeMorseIndex (Vector 7) P.function p ≠ 0 := by
  obtain ⟨P, horder, hminimal⟩ := S.exists_minimal_positive_index_ordered_presentation
  exact ⟨P, horder, hminimal, P.no_positive_index_zero_of_minimal eBoundary hminimal⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

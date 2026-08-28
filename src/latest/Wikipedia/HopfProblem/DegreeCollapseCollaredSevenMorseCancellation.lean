import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenExcellentMorse
import Wikipedia.HopfProblem.DegreeCollapseNativeBoundaryCancellation

/-!
# Cancel an actual positive Morse pair without changing the original filling

A critical-free replacement in a nonnegative band preserves the zero
set, both signs, and the full boundary germ. Every surviving critical
point keeps its old germ and value, so excellence is retained. Applying
the constructed unique-pair cancellation gives a new excellent Morse
presentation of the same seven-dimensional state with two fewer critical
points. The original ambient manifold, literal halves, and native zero
boundary are not replaced.

The more general positive-band replacement also allows surviving
critical values inside the band, with proved excellence supplied. The
critical-free cancellation uses this general construction as a special
case and retains its original public interface.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph
open MorseCancellation

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

def replacePositiveBandWithCriticalValues (g : C(S.Space, ℝ))
    (hg : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ g) (hm : IsMorse (Vector 7) g)
    (hinj : InjOn g (criticalPoints (Vector 7) g))
    {a b : ℝ} (ha : 0 ≤ a)
    (hkeep : ∀ x, P.function x ∉ Ioo a b → g =ᶠ[𝓝 x] P.function)
    (hvalues : ∀ x, P.function x ∈ Icc a b → x ∈ criticalPoints (Vector 7) g →
      g x ∈ Ioo a b) :
    S.ExcellentMorsePresentation := by
  have hsign (x : S.Space) : (g x = 0 ↔ P.function x = 0) ∧
      (0 ≤ g x ↔ 0 ≤ P.function x) ∧ (0 < g x ↔ 0 < P.function x) := by
    by_cases hx : P.function x ∈ Ioo a b
    · have hp : 0 < P.function x := ha.trans_lt hx.1
      have hgp : 0 < g x := ha.trans_lt
        (RegularBandReplacement.mem_open_band_of_critical_values P.smooth hg
          (fun y hy => (hkeep y hy).self_of_nhds) hvalues hx).1
      exact ⟨iff_of_false (ne_of_gt hgp) (ne_of_gt hp),
        iff_of_true hgp.le hp.le, iff_of_true hgp hp⟩
    · rw [(hkeep x hx).self_of_nhds]
      exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
  have hzeroOutside (x : S.Space) (hx : P.function x = 0) : P.function x ∉ Ioo a b := by
    intro h
    rw [hx] at h
    exact (not_lt_of_ge ha) h.1
  refine {
    function := g
    smooth := hg
    morse := hm
    regular := ?_
    zero_iff := fun x => (hsign x).1.trans (P.zero_iff x)
    nonnegative_iff := fun x => (hsign x).2.1.trans (P.nonnegative_iff x)
    positive_iff := fun x => (hsign x).2.2.trans (P.positive_iff x)
    boundary_germ := ?_
    distinct := hinj }
  · intro x hx
    have hpx := (hsign x).1.mp hx
    rw [(hkeep x (hzeroOutside x hpx)).mfderiv_eq]
    exact P.regular x hpx
  · intro x hx
    exact (hkeep x (hzeroOutside x ((P.zero_iff x).mpr hx))).trans (P.boundary_germ x hx)

def replacePositiveBand (g : C(S.Space, ℝ))
    (hg : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ g) (hm : IsMorse (Vector 7) g)
    {a b : ℝ} (ha : 0 ≤ a)
    (hkeep : ∀ x, P.function x ∉ Ioo a b → g =ᶠ[𝓝 x] P.function)
    (hreg : ∀ x, P.function x ∈ Icc a b → x ∉ criticalPoints (Vector 7) g) :
    S.ExcellentMorsePresentation := by
  have hsurvivor (x : S.Space) (hx : x ∈ criticalPoints (Vector 7) g) :
      g =ᶠ[𝓝 x] P.function :=
    hkeep x (fun h => hreg x ⟨h.1.le, h.2.le⟩ hx)
  have hinj : InjOn g (criticalPoints (Vector 7) g) := by
    intro x hx y hy hxy
    have hxf : x ∈ criticalPoints (Vector 7) P.function := by
      change mfderiv (𝓡 7) 𝓘(ℝ, ℝ) P.function x = 0
      rw [← (hsurvivor x hx).mfderiv_eq]
      exact hx
    have hyf : y ∈ criticalPoints (Vector 7) P.function := by
      change mfderiv (𝓡 7) 𝓘(ℝ, ℝ) P.function y = 0
      rw [← (hsurvivor y hy).mfderiv_eq]
      exact hy
    exact P.distinct hxf hyf ((hsurvivor x hx).self_of_nhds.symm.trans
      (hxy.trans (hsurvivor y hy).self_of_nhds))
  exact P.replacePositiveBandWithCriticalValues g hg hm hinj ha hkeep
    (fun x hx hcrit => (hreg x hx hcrit).elim)

theorem exists_positive_pair_cancellation
    (A : AdaptedSurgeryWindows (Vector 7) P.function)
    (p q : criticalPoints (Vector 7) P.function) (hpq : P.function p < P.function q)
    (hconsecutive : ∀ r : criticalPoints (Vector 7) P.function,
      ¬(P.function p < P.function r ∧ P.function r < P.function q))
    (hpositive : 0 ≤ A.toSurgeryWindows.lower p)
    (k l : ℕ) (hpk : Module.finrank ℝ (A.data p).chart.NegativeCoordinates = k)
    (hqk : Module.finrank ℝ (A.data q).chart.NegativeCoordinates = k + 1)
    (hpl : Module.finrank ℝ (A.data p).chart.PositiveCoordinates = l + 1) :
    letI := RegularLevel.chartedSpace P.smooth (A.data p).upper_regular
    letI := RegularLevel.chartedSpace P.smooth (A.data q).lower_regular
    letI : Fact (Module.finrank ℝ (A.data q).chart.NegativeCoordinates = k + 1) := ⟨hqk⟩
    letI : Fact (Module.finrank ℝ (A.data p).chart.PositiveCoordinates = l + 1) := ⟨hpl⟩
    ∀ b : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7))
        𝓘(ℝ, RegularLevel.Model (Vector 7)) (A.data p).UpperLevel (A.data q).LowerLevel ∞,
      (∀ x : (A.data p).UpperLevel, ∃ t, A.flow t x = (b x : S.Space)) →
      ∀ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7))
          𝓘(ℝ, RegularLevel.Model (Vector 7)) (A.data p).UpperLevel (A.data p).UpperLevel ∞,
        IsotopicToIdentity e →
        (∀ x y, NativeTransversality.At (𝓡 k) (𝓡 l) 𝓘(ℝ, RegularLevel.Model (Vector 7))
          (e ∘ (A.data p).transportedAttachingSphere (A.data q) k b.toHomeomorph)
          (A.data p).surgery.beltSphere x y) →
        (range (e ∘ (A.data p).transportedAttachingSphere (A.data q) k b.toHomeomorph) ∩
          range (A.data p).surgery.beltSphere).ncard = 1 →
        ∃ Q : S.ExcellentMorsePresentation,
          (criticalPoints (Vector 7) Q.function).ncard + 2 =
            (criticalPoints (Vector 7) P.function).ncard ∧
          (∀ z, z ∈ criticalPoints (Vector 7) Q.function ↔
            z ∈ criticalPoints (Vector 7) P.function ∧ z ≠ p.val ∧ z ≠ q.val) ∧
          ∀ z, P.function z ∉ Ioo (A.toSurgeryWindows.lower p) (A.toSurgeryWindows.upper q) →
            Q.function =ᶠ[𝓝 z] P.function := by
  let _ := RegularLevel.chartedSpace P.smooth (A.data p).upper_regular
  let _ := RegularLevel.chartedSpace P.smooth (A.data q).lower_regular
  let _ : Fact (Module.finrank ℝ (A.data q).chart.NegativeCoordinates = k + 1) := ⟨hqk⟩
  let _ : Fact (Module.finrank ℝ (A.data p).chart.PositiveCoordinates = l + 1) := ⟨hpl⟩
  intro b horbit e he ht hsingle
  obtain ⟨g, hg, hmg, hcount, hcrit, hkeep⟩ :=
    A.cancel_adjacent_transverse_spheres P.smooth P.morse p q hpq hconsecutive
      k l hpk hqk hpl b horbit e he ht hsingle
  have hreg (x : S.Space)
      (hx : P.function x ∈ Icc (A.toSurgeryWindows.lower p) (A.toSurgeryWindows.upper q)) :
      x ∉ criticalPoints (Vector 7) g := by
    intro h
    obtain ⟨hxf, hxp, hxq⟩ := (hcrit x).mp h
    exact (surgery_pair_band_isolation A.toSurgeryWindows p q hconsecutive x hxf hx).elim
      hxp hxq
  exact ⟨P.replacePositiveBand ⟨g, hg.continuous⟩ hg hmg hpositive hkeep hreg,
    hcount, hcrit, hkeep⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

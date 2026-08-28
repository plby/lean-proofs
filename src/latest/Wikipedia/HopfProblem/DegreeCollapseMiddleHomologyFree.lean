import Wikipedia.HopfProblem.DegreeCollapseOrderedMiddleBasis
import Wikipedia.HopfProblem.DegreeCollapseH2ZeroMiddleElimination
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Actual integral H3 is free on the constructed middle handles

The last index-six handle preserves H3 by the actual Morse exact sequence.
Compose its retained map with the original terminal-sublevel homeomorphism
and the actual last band to extend the coherent middle basis to the original
manifold. The constructed middle-only Morse system supplies all hypotheses
for a compact simply connected H2-zero six-manifold. No homology freeness,
integral duality, or sphere recognition is assumed.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleBasis

open SingularMayerVietoris PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}

theorem cap_middle_bijective (d : MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 6) :
    Bijective (d.lowerRealizationHomologyMap 3) := by
  let : Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 3) :=
    d.attachingHomology_subsingleton_of_index 3 (by norm_num) (by omega) (by omega)
  let : Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 2) :=
    d.attachingHomology_subsingleton_of_index 2 (by norm_num) (by omega) (by omega)
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [← d.morse_exact_at_lower hf 3 (by norm_num)]
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro a
    change d.coreBoundaryHomologyMap 3 a = 0
    rw [Subsingleton.elim a 0, map_zero]
  · intro a
    have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 2) := Subsingleton.elim _ _
    rw [← d.morse_exact_at_upper hf 2] at ha
    exact ha

def capMiddleEquiv (d : MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 6) :
    SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 3 ≃ₗ[ℤ]
      SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 3 :=
  LinearEquiv.ofBijective (d.lowerRealizationHomologyMap 3) (cap_middle_bijective d hf hindex)

theorem capMiddleEquiv_apply (d : MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 6)
    (x : SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 3) :
    capMiddleEquiv d hf hindex x = d.lowerRealizationHomologyMap 3 x := rfl

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  (S : SurgeryWindows E f)

def lastLowerToManifold (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hpos : 0 < S.count) :
    SingularHomology {y : M // f y ≤ S.lower (S.last hpos)} 3 ≃ₗ[ℤ]
      SingularHomology M 3 :=
  (capMiddleEquiv (S.data (S.last hpos)) hf.continuous
    ((S.last_index_dimension hf hpos).trans hdim)).trans
      (homeomorphHomologyEquiv (S.lastUpperHomeomorph hf hpos) 3)

def wholeBasis (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (n : ℕ) (hn : n < S.count)
    (hpre : S.HasIndexThreeBlock 0 n) (hcount : n + 2 = S.count) :
    (Fin n → ℤ) ≃ₗ[ℤ] SingularHomology M 3 :=
  let hpos : 0 < S.count := by omega
  let B := S.consecutiveBandData hf ⟨n, hn⟩
    ⟨S.count - 1, Nat.sub_lt hpos zero_lt_one⟩ (by change n + 1 = S.count - 1; omega)
  ((middleBasis S hf n hn hpre).trans (B.homologyEquiv 3)).trans
    (lastLowerToManifold S hf hdim hpos)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleBasis

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.SimplyConnected

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]

variable (E M) in
theorem exists_middleHomology_basis (hdim : Module.finrank ℝ E = 6) :
    ∃ n : ℕ, Nonempty ((Fin n → ℤ) ≃ₗ[ℤ] SingularHomology M 3) := by
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, htwo, hfour, hfive, -, -⟩ :=
    exists_minimal_ordered_morse_with_only_middle_handles E M hdim
  obtain ⟨r, n, hprefix, hn, hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr, -⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r n hprefix hn hthree hafter
  have hr0 : r = 0 := hr.symm.trans htwo
  clear hr
  subst r
  have hcount := middle_blocks_complete_of_no_four_five S.toSurgeryWindows hf hdim
    0 n hprefix hn hthree hafter hsix hfour hfive
  exact ⟨n, ⟨MiddleBasis.wholeBasis S.toSurgeryWindows hf hdim n (by omega) hthree
    (by omega)⟩⟩

variable (E M) in
theorem middleHomology_free (hdim : Module.finrank ℝ E = 6) :
    Module.Free ℤ (SingularHomology M 3) := by
  obtain ⟨n, ⟨B⟩⟩ := exists_middleHomology_basis E M hdim
  exact Module.Free.of_equiv B

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.SimplyConnected

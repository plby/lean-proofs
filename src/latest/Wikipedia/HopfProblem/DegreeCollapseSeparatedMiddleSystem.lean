import Wikipedia.HopfProblem.DegreeCollapseMiddleFlowExtrema

/-!
# A constructed middle system with both actual extremal caps

The bundled data keeps the original function, native chart model, windows,
and one complete separated flow. Every middle attaching sphere reaches the
actual minimum-disk boundary, and every belt sphere reaches the actual
maximum-disk boundary. Both cap disks are constructed, not supplied.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M]

structure SeparatedSystem where
  dimension : Module.finrank ℝ E = 6
  function : M → ℝ
  smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ function
  morse : IsMorse E function
  windows : AdaptedSurgeryWindows E function
  ordered : ∀ p q : criticalPoints E function, function p < function q →
    nativeMorseIndex E function p ≤ nativeMorseIndex E function q
  minimum_count : nativeMorseCount E function 0 = 1
  maximum_count : nativeMorseCount E function 6 = 1
  indices : ∀ p : criticalPoints E function,
    nativeMorseIndex E function p = 0 ∨ nativeMorseIndex E function p = 3 ∨
      nativeMorseIndex E function p = 6
  separated : NoMiddleConnections windows

open SingularMayerVietoris in
theorem nonempty_separatedSystem [SimplyConnectedSpace M]
    [Subsingleton (SingularHomology M 2)] (hdim : Module.finrank ℝ E = 6) :
    Nonempty (SeparatedSystem E M) := by
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, htwo, hfour, hfive, hindices, -⟩ :=
    SimplyConnected.exists_minimal_ordered_morse_with_only_middle_handles E M hdim
  obtain ⟨T, -, -, -, hsep, -⟩ :=
    exists_separated_middle_flow S hf hm hdim horder hzero hsix hone htwo hfour hfive
  exact ⟨⟨hdim, f, hf, hm, T, horder, hzero, hsix, hindices, hsep⟩⟩

namespace SeparatedSystem

variable {E M} (D : SeparatedSystem E M)

def minimum : criticalPoints E D.function :=
  D.windows.toSurgeryWindows.first (D.windows.toSurgeryWindows.count_pos D.smooth)

def maximum : criticalPoints E D.function :=
  D.windows.toSurgeryWindows.last (D.windows.toSurgeryWindows.count_pos D.smooth)

def lowerCut : ℝ := D.windows.toSurgeryWindows.upper D.minimum
def upperCut : ℝ := D.windows.toSurgeryWindows.lower D.maximum

theorem lowerCut_regular : ∀ x, D.function x = D.lowerCut → x ∉ criticalPoints E D.function :=
  (D.windows.data D.minimum).upper_regular

theorem upperCut_regular : ∀ x, D.function x = D.upperCut → x ∉ criticalPoints E D.function :=
  (D.windows.data D.maximum).lower_regular

theorem minimum_index : nativeMorseIndex E D.function D.minimum = 0 :=
  first_native_index D.windows D.smooth

theorem maximum_index : nativeMorseIndex E D.function D.maximum = 6 :=
  last_native_index D.windows D.smooth D.dimension

theorem middle_between_caps (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) :
    D.lowerCut < D.windows.toSurgeryWindows.lower p ∧
      D.windows.toSurgeryWindows.upper p < D.upperCut := by
  have hmin : D.function D.minimum < D.function p := by
    by_contra h
    have he := D.windows.toSurgeryWindows.unique_first D.smooth
      (D.windows.toSurgeryWindows.count_pos D.smooth) p.val (le_of_not_gt h)
    have hep : p = D.minimum := Subtype.ext he
    rw [hep, D.minimum_index] at hp
    omega
  have hmax : D.function p < D.function D.maximum := by
    by_contra h
    have he := D.windows.toSurgeryWindows.unique_last D.smooth
      (D.windows.toSurgeryWindows.count_pos D.smooth) p.val (le_of_not_gt h)
    have hep : p = D.maximum := Subtype.ext he
    rw [hep, D.maximum_index] at hp
    omega
  exact ⟨D.windows.toSurgeryWindows.separated D.minimum p hmin,
    D.windows.toSurgeryWindows.separated p D.maximum hmax⟩

theorem attaching_reaches_lower_cap (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3)
    (u : sphere (0 : (D.windows.data p).chart.NegativeCoordinates) 1) :
    ((D.windows.data p).surgery.attachingSphere u).val ∈
      FlowCancellation.levelBasin D.windows.flow D.function D.lowerCut := by
  have hforward := attaching_forward_minimum D.windows D.smooth D.dimension
    D.minimum_count D.separated D.indices p hp u
  have hback := (D.windows.attaching_basin_iff D.smooth p _).mpr ⟨u, rfl⟩
  exact FlowCancellation.exists_level_crossing_of_endpoint_limits D.windows.flow D.smooth.continuous
    hback hforward ((D.middle_between_caps p hp).1.trans
      (D.windows.toSurgeryWindows.lower_lt_value p))
    (D.windows.toSurgeryWindows.value_lt_upper D.minimum)

theorem belt_reaches_upper_cap (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3)
    (u : sphere (0 : (D.windows.data p).chart.PositiveCoordinates) 1) :
    ((D.windows.data p).surgery.beltSphere u).val ∈
      FlowCancellation.levelBasin D.windows.flow D.function D.upperCut := by
  have hback := belt_backward_maximum D.windows D.smooth D.dimension
    D.maximum_count D.separated D.indices p hp u
  have hforward := (D.windows.belt_basin_iff D.smooth p _).mpr ⟨u, rfl⟩
  exact FlowCancellation.exists_level_crossing_of_endpoint_limits D.windows.flow D.smooth.continuous
    hback hforward (D.windows.toSurgeryWindows.lower_lt_value D.maximum)
    ((D.windows.toSurgeryWindows.value_lt_upper p).trans (D.middle_between_caps p hp).2)

def lowerDisk : SublevelDisk 6 D.function D.lowerCut := by
  have h : Nonempty (SublevelDisk 6 D.function D.lowerCut) := by
    simpa only [lowerCut, minimum, D.dimension] using D.windows.toSurgeryWindows.nonempty_firstSublevelDisk
      D.smooth (D.windows.toSurgeryWindows.count_pos D.smooth)
  exact Classical.choice h

def upperDisk : SublevelDisk 6 (fun x => -D.function x) (-D.upperCut) := by
  have h : Nonempty (SublevelDisk 6 (fun x => -D.function x) (-D.upperCut)) := by
    simpa only [upperCut, maximum, D.dimension] using D.windows.toSurgeryWindows.nonempty_lastSuperlevelDisk
      D.smooth (D.windows.toSurgeryWindows.count_pos D.smooth)
  exact Classical.choice h

end SeparatedSystem
end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

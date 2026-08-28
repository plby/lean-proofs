import Wikipedia.HopfProblem.CuspDoubleCurves
import Wikipedia.HopfProblem.ToricAxisCharts

/-!
# The vertical edge-direction locus in the actual toric charts

The lattice edge direction `(0,1)` leaves the middle coordinate axis in
every lower or upper triangular chart.  The intrinsic edge-direction locus
is exactly the union of these actual chart-axis images and lies over time
zero.
-/

noncomputable section

open Set
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedToric

open ToricCharts

/-- Index one is the literal vertical lattice direction. -/
@[simp] theorem edgeDirection_one :
    ToricFan.edgeDirection (1 : Fin 3) = (![0, 1] : Fin 2 → ℤ) := rfl

/-- The middle coordinate is unchanged by either triangle orientation. -/
@[simp] theorem axisIndex_one (a : ToricFan.Triangle) : a.axisIndex 1 = 1 := by
  cases ha : a.upper <;> simp [ToricFan.Triangle.axisIndex, ha]

/-- The axis parametrization is the same literal vector in every chart. -/
@[simp] theorem axisPoint_one (a : ToricFan.Triangle) (t : ℂ) :
    ToricFan.Triangle.axisPoint a 1 t = ![0, t, 0] := by
  ext j
  fin_cases j <;> simp [ToricFan.Triangle.axisPoint, axisIndex_one]

/-- The intrinsic vertical edge-direction locus has these exact equations
in each of the actual toric charts. -/
theorem inclusion_mem_edgeDirectionLocus_one_iff
    (a : ToricFan.Triangle) (z : CoordinateSpace 3) :
    ToricSpace.inclusion a z ∈ ToricSpace.edgeDirectionLocus 1 ↔ z 0 = 0 ∧ z 2 = 0 := by
  change z ∈ ToricSpace.inclusion a ⁻¹' ToricSpace.edgeDirectionLocus 1 ↔ _
  rw [ToricSpace.edgeDirectionLocus_preimage]
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, axisIndex_one]
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 2 (by decide)⟩
  · rintro ⟨h0, h2⟩ j hj
    fin_cases j
    · exact h0
    · exact (hj rfl).elim
    · exact h2

/-- The actual locus is the union of the middle-axis images in the
jointly surjective toric charts. -/
theorem edgeDirectionLocus_one_eq_iUnion_axis :
    ToricSpace.edgeDirectionLocus 1 =
      ⋃ a : ToricFan.Triangle, Set.range (fun t : ℂ =>
        ToricSpace.inclusion a (ToricFan.Triangle.axisPoint a 1 t)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
    have hz := (inclusion_mem_edgeDirectionLocus_one_iff a z).mp hx
    refine Set.mem_iUnion.mpr ⟨a, Set.mem_range.mpr ⟨z 1, ?_⟩⟩
    apply congrArg (ToricSpace.inclusion a)
    rw [axisPoint_one]
    ext j
    fin_cases j
    · exact hz.1.symm
    · rfl
    · exact hz.2.symm
  · intro hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, rfl⟩ := ha
    apply (inclusion_mem_edgeDirectionLocus_one_iff a _).mpr
    rw [axisPoint_one]
    exact ⟨rfl, rfl⟩

/-- Every point of the vertical edge-direction locus has actual time zero. -/
theorem time_eq_zero_of_mem_edgeDirectionLocus_one {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.edgeDirectionLocus 1) : ToricSpace.time x = 0 := by
  rw [edgeDirectionLocus_one_eq_iUnion_axis] at hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  obtain ⟨t, rfl⟩ := ha
  exact (ToricSpace.time_inclusion a _).trans (ToricFan.Triangle.time_axisPoint a 1 t)

theorem edgeDirectionLocus_one_subset_central :
    ToricSpace.edgeDirectionLocus 1 ⊆ ToricSpace.time ⁻¹' ({0} : Set ℂ) :=
  fun _ hx => time_eq_zero_of_mem_edgeDirectionLocus_one hx

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedToric

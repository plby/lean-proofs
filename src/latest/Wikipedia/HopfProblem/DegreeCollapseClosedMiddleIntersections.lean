import Wikipedia.HopfProblem.DegreeCollapseCappedMiddleSpheres

/-!
# Exact intersections of the constructed closed middle sphere maps

The source is the literal standard S3. Only its negative pole maps to the
critical point. Opposite closed sphere maps agree only at those poles and
only for the same middle label. No generic-position hypothesis is supplied.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

def middlePole : Hemisphere.Sphere 3 :=
  Hemisphere.point false ⟨0, mem_closedBall_self zero_le_one⟩

namespace SeparatedSystem

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] (D : SeparatedSystem E M)

theorem descendingSphere_pole (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) : D.descendingSphere p hp middlePole = p.val := by
  rw [middlePole, D.descendingSphere_false]
  change CoreDisks.negativeFun (D.windows.data p) (D.negativeLinear p hp 0) = p.val
  rw [map_zero, CoreDisks.negative_zero]

theorem ascendingSphere_pole (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) : D.ascendingSphere p hp middlePole = p.val := by
  rw [middlePole, D.ascendingSphere_false]
  change CoreDisks.positiveFun (D.windows.data p) (D.positiveLinear p hp 0) = p.val
  rw [map_zero, CoreDisks.positive_zero]

theorem descendingSphere_eq_critical_iff (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (x : Hemisphere.Sphere 3) :
    D.descendingSphere p hp x = p.val ↔ x = middlePole := by
  constructor
  · intro hx
    obtain ⟨b, u, rfl⟩ := Hemisphere.point_jointly_surjective x
    cases b
    · rw [D.descendingSphere_false] at hx
      let zeroDisk : Hemisphere.Ball 3 := ⟨0, mem_closedBall_self zero_le_one⟩
      have he : CoreDisks.negativeDisk (D.windows.data p)
          (StandardDiskCoordinates.disk (D.negativeLinear p hp) u) =
        CoreDisks.negativeDisk (D.windows.data p)
          (StandardDiskCoordinates.disk (D.negativeLinear p hp) zeroDisk) := by
        change CoreDisks.negativeFun (D.windows.data p) (D.negativeLinear p hp u.val) =
          CoreDisks.negativeFun (D.windows.data p) (D.negativeLinear p hp 0)
        rw [map_zero, CoreDisks.negative_zero]
        exact hx
      have hu := (StandardDiskCoordinates.disk (D.negativeLinear p hp)).injective
        (CoreDisks.negative_injective (D.windows.data p) he)
      exact congrArg (Hemisphere.point false) hu
    · rw [D.descendingSphere_true] at hx
      have hc := D.ascendingSphere_mem p hp middlePole
      rw [D.ascendingSphere_pole] at hc
      have hd := D.attaching_cap_disjoint p p hp hp (D.attachingCap p hp)
        (D.attachingCap_image p hp)
      exact (Set.disjoint_left.mp hd ⟨_, hx⟩ hc).elim
  · rintro rfl
    exact D.descendingSphere_pole p hp

theorem ascendingSphere_eq_critical_iff (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (x : Hemisphere.Sphere 3) :
    D.ascendingSphere p hp x = p.val ↔ x = middlePole := by
  constructor
  · intro hx
    obtain ⟨b, u, rfl⟩ := Hemisphere.point_jointly_surjective x
    cases b
    · rw [D.ascendingSphere_false] at hx
      let zeroDisk : Hemisphere.Ball 3 := ⟨0, mem_closedBall_self zero_le_one⟩
      have he : CoreDisks.positiveDisk (D.windows.data p)
          (StandardDiskCoordinates.disk (D.positiveLinear p hp) u) =
        CoreDisks.positiveDisk (D.windows.data p)
          (StandardDiskCoordinates.disk (D.positiveLinear p hp) zeroDisk) := by
        change CoreDisks.positiveFun (D.windows.data p) (D.positiveLinear p hp u.val) =
          CoreDisks.positiveFun (D.windows.data p) (D.positiveLinear p hp 0)
        rw [map_zero, CoreDisks.positive_zero]
        exact hx
      have hu := (StandardDiskCoordinates.disk (D.positiveLinear p hp)).injective
        (CoreDisks.positive_injective (D.windows.data p) he)
      exact congrArg (Hemisphere.point false) hu
    · rw [D.ascendingSphere_true] at hx
      have hc := D.descendingSphere_mem p hp middlePole
      rw [D.descendingSphere_pole] at hc
      have hd := D.belt_cap_disjoint p p hp hp (D.beltCap p hp) (D.beltCap_image p hp)
      exact (Set.disjoint_left.mp hd hc ⟨_, hx⟩).elim
  · rintro rfl
    exact D.ascendingSphere_pole p hp

theorem closed_middle_pair_iff (p q : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (hq : nativeMorseIndex E D.function q = 3)
    (x y : Hemisphere.Sphere 3) :
    D.descendingSphere p hp x = D.ascendingSphere q hq y ↔
      x = middlePole ∧ y = middlePole ∧ p = q := by
  constructor
  · intro hxy
    have hy : D.descendingSphere p hp x ∈ D.ascendingCarrier q := by
      rw [hxy]
      exact D.ascendingSphere_mem q hq y
    obtain ⟨hxcrit, hpq⟩ := (D.carriers_pair_iff p q hp hq _).mp
      ⟨D.descendingSphere_mem p hp x, hy⟩
    refine ⟨(D.descendingSphere_eq_critical_iff p hp x).mp hxcrit, ?_, hpq⟩
    apply (D.ascendingSphere_eq_critical_iff q hq y).mp
    exact hxy.symm.trans (hxcrit.trans (congrArg Subtype.val hpq))
  · rintro ⟨rfl, rfl, rfl⟩
    rw [D.descendingSphere_pole, D.ascendingSphere_pole]

theorem closed_middle_images_iff (p q : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (hq : nativeMorseIndex E D.function q = 3)
    (z : M) : z ∈ range (D.descendingSphere p hp) ∩ range (D.ascendingSphere q hq) ↔
      z = p.val ∧ p = q := by
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    obtain ⟨rfl, rfl, hpq⟩ := (D.closed_middle_pair_iff p q hp hq x y).mp hy.symm
    exact ⟨D.descendingSphere_pole p hp, hpq⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨middlePole, D.descendingSphere_pole p hp⟩,
      ⟨middlePole, D.ascendingSphere_pole p hq⟩⟩

end SeparatedSystem
end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

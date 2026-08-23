/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Pointwise Topology

noncomputable section

namespace Erdos988

open scoped Classical in
abbrev E3 := EuclideanSpace ℝ (Fin 3)

open scoped Classical in
abbrev S2 := Metric.sphere (0 : E3) 1

open scoped Classical in
def northPole : S2 :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by
    simp [Metric.mem_sphere, dist_zero_right]⟩

open scoped Classical in
instance : Nonempty S2 := ⟨northPole⟩

open scoped Classical in
def sphericalCap (u : S2) (t : ℝ) : Set S2 :=
  {x | t ≤ inner ℝ (x : E3) (u : E3)}

open scoped Classical in
def surfaceFiniteMeasure : FiniteMeasure S2 :=
  ⟨(volume : Measure E3).toSphere, inferInstance⟩

open scoped Classical in
def surfaceProbability : ProbabilityMeasure S2 :=
  surfaceFiniteMeasure.normalize

open scoped Classical in
def normalizedArea (A : Set S2) : ℝ := (surfaceProbability A : ℝ)

end Erdos988

namespace Check991Fekete

variable {α : Type*} [MetricSpace α]

open scoped Classical in
def pairDist : Sym2 α → ℝ :=
  Sym2.lift ⟨dist, dist_comm⟩

open scoped Classical in
def unorderedDistanceProduct (A : Finset α) : ℝ := by
  classical
  exact ∏ p ∈ A.sym2 with ¬p.IsDiag, pairDist p

end Check991Fekete

namespace Erdos991

open scoped Classical in
abbrev E3 := EuclideanSpace ℝ (Fin 3)

end Erdos991

namespace Erdos991

open scoped Classical in
abbrev S2 := Metric.sphere (0 : E3) 1

end Erdos991

namespace Erdos991

open scoped Classical in
def distanceProduct (P : Finset S2) : ℝ :=
  Check991Fekete.unorderedDistanceProduct P

end Erdos991

namespace Erdos991

open scoped Classical in
def IsDistanceProductMaximizer (P : Finset S2) : Prop :=
  ∀ Q : Finset S2, Q.card = P.card → distanceProduct Q ≤ distanceProduct P

end Erdos991

namespace Erdos991

open Erdos988

open scoped Classical in
noncomputable def actualCapError (P : Finset S2) (u : S2) (t : ℝ) : ℝ := by
  classical
  exact |((P.filter fun x ↦ x ∈ sphericalCap u t).card : ℝ) -
    normalizedArea (sphericalCap u t) * P.card|

end Erdos991

namespace Erdos991

open scoped Classical in
noncomputable def actualCapErrorSet (P : Finset S2) : Set ℝ :=
  {r | ∃ u : S2, ∃ t : ℝ,
    t ∈ Icc (-1 : ℝ) 1 ∧ r = actualCapError P u t}

end Erdos991

namespace Erdos991

open scoped Classical in
noncomputable def actualSphericalCapDiscrepancy (P : Finset S2) : ℝ :=
  sSup (actualCapErrorSet P)

end Erdos991

namespace Erdos991

open scoped Classical in
theorem erdos_991
    (A : ℕ → Finset S2)
    (hcard : ∀ n : ℕ, (A n).card = n)
    (hmax : ∀ n : ℕ, IsDistanceProductMaximizer (A n)) :
    (fun n : ℕ ↦ actualSphericalCapDiscrepancy (A n)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  sorry

end Erdos991

end

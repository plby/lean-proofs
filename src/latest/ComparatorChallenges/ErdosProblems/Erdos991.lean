/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory Set

namespace Erdos988

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev S2 := Metric.sphere (0 : E3) 1

noncomputable def northPole : S2 :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by
    simp [Metric.mem_sphere, dist_zero_right]⟩

instance : Nonempty S2 := ⟨northPole⟩

def sphericalCap (u : S2) (t : ℝ) : Set S2 :=
  {x | t ≤ inner ℝ (x : E3) (u : E3)}

noncomputable def surfaceFiniteMeasure : FiniteMeasure S2 :=
  ⟨(volume : Measure E3).toSphere, inferInstance⟩

noncomputable def surfaceProbability : ProbabilityMeasure S2 :=
  surfaceFiniteMeasure.normalize

noncomputable def normalizedArea (A : Set S2) : ℝ := (surfaceProbability A : ℝ)

end Erdos988

namespace Check991Fekete

variable {α : Type*} [MetricSpace α]

def pairDist : Sym2 α → ℝ :=
  Sym2.lift ⟨dist, dist_comm⟩

noncomputable def unorderedDistanceProduct (A : Finset α) : ℝ := by
  classical
  exact ∏ p ∈ A.sym2 with ¬p.IsDiag, pairDist p

end Check991Fekete

namespace Erdos991

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev S2 := Metric.sphere (0 : E3) 1

noncomputable def distanceProduct (P : Finset S2) : ℝ :=
  Check991Fekete.unorderedDistanceProduct P

def IsDistanceProductMaximizer (P : Finset S2) : Prop :=
  ∀ Q : Finset S2, Q.card = P.card → distanceProduct Q ≤ distanceProduct P

noncomputable def actualCapError (P : Finset S2) (u : S2) (t : ℝ) : ℝ := by
  classical
  exact |((P.filter fun x ↦ x ∈ Erdos988.sphericalCap u t).card : ℝ) -
    Erdos988.normalizedArea (Erdos988.sphericalCap u t) * P.card|

noncomputable def actualCapErrorSet (P : Finset S2) : Set ℝ :=
  {r | ∃ u : S2, ∃ t : ℝ,
    t ∈ Icc (-1 : ℝ) 1 ∧ r = actualCapError P u t}

noncomputable def actualSphericalCapDiscrepancy (P : Finset S2) : ℝ :=
  sSup (actualCapErrorSet P)

theorem erdos_991
    (A : ℕ → Finset S2)
    (hcard : ∀ n : ℕ, (A n).card = n)
    (hmax : ∀ n : ℕ, IsDistanceProductMaximizer (A n)) :
    (fun n : ℕ ↦ actualSphericalCapDiscrepancy (A n)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  sorry

end Erdos991

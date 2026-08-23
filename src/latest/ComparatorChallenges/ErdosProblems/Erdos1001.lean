/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Set MeasureTheory
open scoped ENNReal Pointwise Topology

noncomputable section

namespace Erdos1001

open scoped Classical in
def HasApproximation (N : ℕ) (A c α : ℝ) : Prop :=
  α ∈ Ioo (0 : ℝ) 1 ∧
    ∃ x : ℤ, ∃ y : ℕ,
      0 < y ∧
      N ≤ y ∧
      (y : ℝ) ≤ c * (N : ℝ) ∧
      x.natAbs.Coprime y ∧
      |α - (x : ℝ) / (y : ℝ)| < A / (y : ℝ) ^ 2

end Erdos1001

namespace Erdos1001

open scoped Classical in
def approximableSet (N : ℕ) (A c : ℝ) : Set ℝ :=
  {α | HasApproximation N A c α}

end Erdos1001

namespace Erdos1001

open scoped Classical in
def S (N : ℕ) (A c : ℝ) : ℝ :=
  volume.real (approximableSet N A c)

end Erdos1001

namespace Erdos1001

open scoped Classical in
def IsLimitValue (A c f : ℝ) : Prop :=
  Tendsto (fun N : ℕ ↦ S N A c) atTop (𝓝 f)

end Erdos1001

namespace Erdos1001

open scoped Classical in
def fareyTriangle : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1 ∧ 1 < p.1 + p.2}

end Erdos1001

namespace Erdos1001

open scoped Classical in
def bczIndex (p : ℝ × ℝ) : ℤ :=
  ⌊(1 + p.1) / p.2⌋

end Erdos1001

namespace Erdos1001

open scoped Classical in
def bczMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2, (bczIndex p : ℝ) * p.2 - p.1)

end Erdos1001

namespace Erdos1001

open scoped Classical in
def normalizedDenominator (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  (bczMap^[j] p).1

end Erdos1001

namespace Erdos1001

open scoped Classical in
def normalizedGap (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.range j,
    1 / (normalizedDenominator ℓ p * normalizedDenominator (ℓ + 1) p)

end Erdos1001

namespace Erdos1001

open scoped Classical in
def normalizedUpperEndpoint (A : ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  normalizedGap j p + A / normalizedDenominator j p ^ 2

end Erdos1001

namespace Erdos1001

open scoped Classical in
def normalizedLowerEndpoint (A : ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  normalizedGap j p - A / normalizedDenominator j p ^ 2

end Erdos1001

namespace Erdos1001

open scoped Classical in
def finiteOverlapLength (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (p : ℝ × ℝ) : ℝ :=
  max 0
    ((J.image (fun j ↦ normalizedUpperEndpoint A j p)).min' (hJ.image _) -
      (J.image (fun j ↦ normalizedLowerEndpoint A j p)).max' (hJ.image _))

end Erdos1001

namespace Erdos1001

open scoped Classical in
def cutoffOverlapIntegrand (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (p : ℝ × ℝ) : ℝ :=
  if ∀ j ∈ J, 1 / c ≤ normalizedDenominator j p then
    finiteOverlapLength A J hJ p
  else 0

end Erdos1001

namespace Erdos1001

open scoped Classical in
def explicitLimitAtCutoff (A c : ℝ) (K : ℕ) : ℝ :=
  (6 / Real.pi ^ 2) *
    ∑ J ∈ (Finset.Icc 1 K).powerset,
      (-1 : ℝ) ^ J.card *
        ∫ p in fareyTriangle,
          cutoffOverlapIntegrand A c (insert 0 J) (Finset.insert_nonempty 0 J) p

end Erdos1001

namespace Erdos1001

open scoped Classical in
def overlapCutoff (A c : ℝ) : ℕ :=
  ⌈2 * A * c ^ 2⌉₊

end Erdos1001

namespace Erdos1001

open scoped Classical in
def erdosSzuszTuranLimit (A c : ℝ) : ℝ :=
  explicitLimitAtCutoff A c (overlapCutoff A c)

end Erdos1001

namespace Erdos1001

open scoped Classical in
theorem erdos_1001 (A c : ℝ) (hA : 0 < A) (hc : 1 ≤ c) :
    IsLimitValue A c (erdosSzuszTuranLimit A c) := by
  sorry

end Erdos1001

end

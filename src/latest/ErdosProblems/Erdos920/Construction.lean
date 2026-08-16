import ErdosProblems.Erdos920.ConcreteWitness
import ErdosProblems.Erdos920.DensitySide
import ErdosProblems.Erdos920.ForwardBound
import ErdosProblems.Erdos920.RamseyPackaging
import ErdosProblems.Erdos920.SamplingAdapter

/-!
# Assembly of the projective `D*` construction

This file is the narrow interface between the concrete finite-geometric
construction and the numerical packaging in `RamseyPackaging`.  The fields
whose proofs do not involve the container argument are supplied by
`ConcreteWitness.ofForwardBound`.  Consequently the only construction input
recorded below is the forward-independent-tuple estimate, together with the
finite ordering/sampling conclusion obtained from that estimate.

Keeping the interface in this form is useful for two reasons.  First, the
prime-field instance is reconstructed locally from the primality proof, so
users of the API do not have to manage `Fact q.Prime` arguments.  Second, the
eventual prime selection is not repeated here: it is exactly
`DStarConstruction.toFamily`.
-/

namespace Erdos920.Construction

open Erdos920.ProjectiveDStar
open Erdos920.RamseyPackaging

noncomputable section

/-- The concrete conclusion needed at one pair `(m,q)`.

The existentially quantified proof `hforward` is used to build the actual
projective `D*` witness.  The remaining conjunction is precisely the output
of the finite random-ordering and sampling/deletion argument for that
witness. -/
def HasConcreteBuild (u m q : ℕ) (C : ℝ) (hq : q.Prime) : Prop :=
  letI : Fact q.Prime := ⟨hq⟩
  ∃ hforward :
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q (u + 1))
          (ProjectiveDStar.vertexFintype q (u + 1))
          (ProjectiveDStar.digraph q (u + 1)) m : ℕ) : ℝ) ≤
        (C * (q : ℝ) ^ (u + 1)) ^ m,
    let W := ConcreteWitness.ofForwardBound q (u + 1) m C (by omega) hforward
    W.SamplingSideConditions ∧ W.HasAveragingSamplingConclusion

/-- The single theorem which the marked-tree/container and finite averaging
development must establish.  All quantifiers and side conditions agree
literally with `RamseyPackaging.DStarConstruction.build`.

This is a structure containing proved data, not a postulate: constructing a
value requires a proof of the concrete projective tuple bound and of the
ordering/sampling conclusion for every admissible prime. -/
structure ProjectiveBuildTheorem (u : ℕ) where
  C : ℝ
  C_pos : 0 < C
  qThreshold : ℕ
  build : ∀ (m q : ℕ), (hq : q.Prime) → qThreshold ≤ q →
    2 ≤ q → q ≤ m →
    (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) →
    C * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) →
      HasConcreteBuild u m q C hq

/-- Assemble the complete concrete build theorem from the one genuinely
geometric input: a thresholded forward-independent-tuple estimate.

The density threshold is supplied by `DensitySide`; the factorial ordering
and sampling/deletion conclusion is supplied by `SamplingAdapter`.  Thus a
caller proving the projective container bound does not need to repeat either
analytic argument. -/
def projectiveBuildTheoremOfForwardBound (u : ℕ) (hu : 1 ≤ u)
    (C : ℝ) (hC : 0 < C) (Qforward : ℕ)
    (hforward : ∀ (q m : ℕ), (hq : q.Prime) → Qforward ≤ q →
      C * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) →
      letI : Fact q.Prime := ⟨hq⟩
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q (u + 1))
          (ProjectiveDStar.vertexFintype q (u + 1))
          (ProjectiveDStar.digraph q (u + 1)) m : ℕ) : ℝ) ≤
        (C * (q : ℝ) ^ (u + 1)) ^ m) :
    ProjectiveBuildTheorem u := by
  let Qdensity := Classical.choose
    (DensitySide.exists_threshold_sampling_density C hC u hu)
  have hdensity := Classical.choose_spec
    (DensitySide.exists_threshold_sampling_density C hC u hu)
  refine
    { C := C
      C_pos := hC
      qThreshold := max Qforward Qdensity
      build := ?_ }
  intro m q hq hqThreshold hq2 hqm hscale hbudget
  letI : Fact q.Prime := ⟨hq⟩
  have hqForward : Qforward ≤ q :=
    (Nat.le_max_left Qforward Qdensity).trans hqThreshold
  have hqDensity : Qdensity ≤ q :=
    (Nat.le_max_right Qforward Qdensity).trans hqThreshold
  have htuple := hforward q m hq hqForward hbudget
  refine ⟨htuple, ?_⟩
  let W := ConcreteWitness.ofForwardBound q (u + 1) m C (by omega) htuple
  have hside : W.SamplingSideConditions := by
    exact hdensity m q hqDensity hqm hscale
  refine ⟨hside, ?_⟩
  exact W.hasAveragingSamplingConclusion_of_sideConditions
    (by omega) (by omega) hC hside

/-- The unconditional projective build theorem obtained from Bradač's
marked-tree estimate. -/
def projectiveBuildTheorem (u : ℕ) (hu : 1 ≤ u) :
    ProjectiveBuildTheorem u := by
  let E := ForwardBound.exists_forwardConstant (u + 1) (by omega)
  let C := Classical.choose E
  have hC_and := Classical.choose_spec E
  let Q := Classical.choose hC_and.2
  have hforward := Classical.choose_spec hC_and.2
  exact projectiveBuildTheoremOfForwardBound u hu C hC_and.1 Q hforward

/-- Turn the concrete projective build theorem into the abstract construction
interface consumed by the Ramsey packaging. -/
def projectiveDStarConstruction (u : ℕ) (_hu : 1 ≤ u)
    (B : ProjectiveBuildTheorem u) : DStarConstruction u where
  C := B.C
  C_pos := B.C_pos
  qThreshold := B.qThreshold
  build := by
    intro m q hq hqThreshold hq2 hqm hscale hbudget
    let _ : Fact q.Prime := ⟨hq⟩
    rcases B.build m q hq hqThreshold hq2 hqm hscale hbudget with
      ⟨hforward, hside, haverage⟩
    exact ⟨ConcreteWitness.ofForwardBound q (u + 1) m B.C (by omega) hforward,
      hside, haverage⟩

/-- The eventual `D*` family supplied by a proved concrete construction.

The `hu` hypothesis records the range in which Bradač's projective
container argument is used.  The conversion itself is numerical and is
exactly `DStarConstruction.toFamily`. -/
def dStarFamilyOfBuild (u : ℕ) (hu : 1 ≤ u) (B : ProjectiveBuildTheorem u) :
    DStarFamily u :=
  (projectiveDStarConstruction u hu B).toFamily

/-- The unconditional family of projective `D*` constructions used in the
resolution of Erdős Problem 920. -/
def dStarFamily (u : ℕ) (hu : 1 ≤ u) : DStarFamily u :=
  dStarFamilyOfBuild u hu (projectiveBuildTheorem u hu)

@[simp] theorem dStarFamilyOfBuild_C (u : ℕ) (hu : 1 ≤ u)
    (B : ProjectiveBuildTheorem u) :
    (dStarFamilyOfBuild u hu B).C = B.C := rfl

@[simp] theorem dStarFamilyOfBuild_κ (u : ℕ) (hu : 1 ≤ u)
    (B : ProjectiveBuildTheorem u) :
    (dStarFamilyOfBuild u hu B).κ = 1 / (8 * B.C) := rfl

/-- Direct Ramsey consequence of a proved projective build theorem. -/
theorem bradacRamseyLowerBoundOfBuild (u : ℕ) (hu : 1 ≤ u)
    (B : ProjectiveBuildTheorem u) :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        A * (m : ℝ) ^ (u + 1) / Real.log (m : ℝ) ^ (2 * u) ≤
          (Ramsey.ramseyNumber (u + 2) m : ℝ) :=
  bradac_ramsey_lower_bound_eventually_of_dStarFamily u
    (dStarFamilyOfBuild u hu B)

end

end Erdos920.Construction

#print axioms Erdos920.Construction.bradacRamseyLowerBoundOfBuild
#print axioms Erdos920.Construction.dStarFamily

import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsNative

/-!
# Actual local comparison of sections with the same divisor

The data consist of an open neighborhood in two genuine bundle charts,
a holomorphic nowhere-zero scalar there, and its exact equality between
the native coefficients of two given sections.  They produce holomorphic
comparison units in every other valid chart pair.  No divisor equality
is inferred merely from a name or an order label.
-/

noncomputable section

open Set Topology Bundle TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
  (A : TransitionData M ι) (B : TransitionData M κ)
  (sA : ∀ x, A.core.Fiber x) (sB : ∀ x, B.core.Fiber x)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- A genuine local unit relating the actual native section coefficients. -/
structure LocalSectionComparison where
  sourceChart : ι
  targetChart : κ
  domain : Opens M
  domain_subset : (domain : Set M) ⊆ A.baseSet sourceChart ∩ B.baseSet targetChart
  coefficient : M → ℂ
  holomorphicOn : ContMDiffOn I I₁ ω coefficient domain
  ne_zero : ∀ x ∈ domain, coefficient x ≠ 0
  equation : ∀ x ∈ domain,
    coefficient x * A.localCoefficient sA sourceChart x =
      B.localCoefficient sB targetChart x

namespace LocalSectionComparison

variable {I A B sA sB} (D : LocalSectionComparison I A B sA sB)

/-- Extend the actual local coefficient to unit-valued data by using
one outside its domain; no regularity outside that domain is asserted. -/
def coefficientUnit (x : M) : ℂˣ := by
  classical
  exact if hx : x ∈ D.domain then Units.mk0 (D.coefficient x) (D.ne_zero x hx) else 1

theorem coefficientUnit_val {x : M} (hx : x ∈ D.domain) :
    (D.coefficientUnit x : ℂ) = D.coefficient x := by
  simp only [coefficientUnit, dif_pos hx, Units.val_mk0]

theorem coefficientUnit_holomorphicOn :
    ContMDiffOn I I₁ ω (fun x => (D.coefficientUnit x : ℂ)) D.domain :=
  D.holomorphicOn.congr (fun _ hx => D.coefficientUnit_val hx)

/-- The exact local comparison unit in any other valid native chart pair. -/
def localValue (i : ι × κ) (x : M) : ℂˣ :=
  B.transition D.targetChart i.2 x * D.coefficientUnit x * A.transition i.1 D.sourceChart x

/-- Changing the two native charts preserves the literal section equation. -/
theorem localValue_equation (i : ι × κ) {x : M}
    (hi : x ∈ A.baseSet i.1 ∩ B.baseSet i.2) (hx : x ∈ D.domain) :
    (D.localValue i x : ℂ) * A.localCoefficient sA i.1 x =
      B.localCoefficient sB i.2 x := by
  have hA := A.localCoefficient_compatible sA i.1 D.sourceChart x
    ⟨hi.1, (D.domain_subset hx).1⟩
  have hB := B.localCoefficient_compatible sB D.targetChart i.2 x
    ⟨(D.domain_subset hx).2, hi.2⟩
  change ((B.transition D.targetChart i.2 x : ℂ) * (D.coefficientUnit x : ℂ) *
    (A.transition i.1 D.sourceChart x : ℂ)) * A.localCoefficient sA i.1 x = _
  rw [D.coefficientUnit_val hx]
  calc
    _ = (B.transition D.targetChart i.2 x : ℂ) *
        (D.coefficient x * ((A.transition i.1 D.sourceChart x : ℂ) *
          A.localCoefficient sA i.1 x)) := by ac_rfl
    _ = (B.transition D.targetChart i.2 x : ℂ) *
        (D.coefficient x * A.localCoefficient sA D.sourceChart x) := by rw [hA]
    _ = (B.transition D.targetChart i.2 x : ℂ) *
        B.localCoefficient sB D.targetChart x := by rw [D.equation x hx]
    _ = _ := hB

/-- Compatibility is derived from the original native transition cocycles. -/
theorem localValue_compatible (i j : ι × κ) {x : M}
    (hij : x ∈ (A.baseSet i.1 ∩ B.baseSet i.2) ∩
      (A.baseSet j.1 ∩ B.baseSet j.2)) (hx : x ∈ D.domain) :
    B.transition i.2 j.2 x * D.localValue i x =
      D.localValue j x * A.transition i.1 j.1 x := by
  have hB := B.transition_comp D.targetChart i.2 j.2 x
    ⟨⟨(D.domain_subset hx).2, hij.1.2⟩, hij.2.2⟩
  have hA := A.transition_comp i.1 j.1 D.sourceChart x
    ⟨⟨hij.1.1, hij.2.1⟩, (D.domain_subset hx).1⟩
  change B.transition i.2 j.2 x *
      (B.transition D.targetChart i.2 x * D.coefficientUnit x *
        A.transition i.1 D.sourceChart x) =
    (B.transition D.targetChart j.2 x * D.coefficientUnit x *
      A.transition j.1 D.sourceChart x) * A.transition i.1 j.1 x
  calc
    _ = (B.transition i.2 j.2 x * B.transition D.targetChart i.2 x) *
        D.coefficientUnit x * A.transition i.1 D.sourceChart x := by ac_rfl
    _ = B.transition D.targetChart j.2 x * D.coefficientUnit x *
        (A.transition j.1 D.sourceChart x * A.transition i.1 j.1 x) := by rw [hB, hA]
    _ = _ := by ac_rfl

variable [A.IsHolomorphic I] [B.IsHolomorphic I]

theorem localValue_holomorphicOn (i : ι × κ) :
    ContMDiffOn I I₁ ω (fun x => (D.localValue i x : ℂ))
      ((A.baseSet i.1 ∩ B.baseSet i.2) ∩ D.domain) := by
  change ContMDiffOn I I₁ ω
    (fun x => (B.transition D.targetChart i.2 x : ℂ) * (D.coefficientUnit x : ℂ) *
      (A.transition i.1 D.sourceChart x : ℂ)) _
  exact (((B.transition_holomorphic I D.targetChart i.2).mono
    (fun _ hx => ⟨(D.domain_subset hx.2).2, hx.1.2⟩)).mul
      (D.coefficientUnit_holomorphicOn.mono (fun _ hx => hx.2))).mul
        ((A.transition_holomorphic I i.1 D.sourceChart).mono
          (fun _ hx => ⟨hx.1.1, (D.domain_subset hx.2).1⟩))

end LocalSectionComparison

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle

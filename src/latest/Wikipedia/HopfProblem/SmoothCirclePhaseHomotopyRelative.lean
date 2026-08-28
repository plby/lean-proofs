import Wikipedia.HopfProblem.SmoothCirclePhaseHomotopyBasic

/-!
# Relative and invariant laws for the original unit-phase homotopy

The explicit normalized segment is stationary wherever the original two
functions agree, and is invariant under every family of self-maps under
which both functions are invariant. These properties are retained in native
relative homotopy and homotopy-with-properties objects.

The relative set need not be closed, and the invariance law needs no extra
continuity or algebraic assumptions on the action. The source is only a
topological space; no smoothness of the homotopy is asserted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SmoothCirclePhaseHomotopy

variable {M : Type*}

/-- Wherever the two functions agree, normalization fixes the original unit phase. -/
theorem phase_eqOn (f g : M → ℂ) (hunit : ∀ x, ‖f x‖ = 1)
    (S : Set M) (heq : Set.EqOn g f S) (t : unitInterval) :
    Set.EqOn (phase f g t) f S := by
  intro x hx
  rw [phase, segment_of_eq f g t x (heq hx)]
  exact SmoothCircleApproximation.normalize_eq_self (hunit x)

/-- Pointwise invariance of both inputs is retained by the literal phase formula. -/
theorem phase_invariant {A : Type*} (f g : M → ℂ) (act : A → M → M)
    (hfi : ∀ a x, f (act a x) = f x) (hgi : ∀ a x, g (act a x) = g x)
    (t : unitInterval) (a : A) (x : M) :
    phase f g t (act a x) = phase f g t x := by
  simp only [phase, segment, hfi a x, hgi a x]

variable [TopologicalSpace M]
variable (f g : M → ℂ) (hf : Continuous f) (hg : Continuous g)
  (hunit : ∀ x, ‖f x‖ = 1) (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ))

theorem ambientHomotopy_fixed (S : Set M) (heq : Set.EqOn g f S)
    (t : unitInterval) (x : M) (hx : x ∈ S) :
    ambientHomotopy f g hf hg hunit hclose (t, x) = f x :=
  phase_eqOn f g hunit S heq t hx

theorem circleHomotopy_fixed (S : Set M) (heq : Set.EqOn g f S)
    (t : unitInterval) (x : M) (hx : x ∈ S) :
    circleHomotopy f g hf hg hunit hclose (t, x) = unitCircleMap f hf hunit x :=
  _root_.Circle.ext (phase_eqOn f g hunit S heq t hx)

theorem ambientHomotopy_invariant {A : Type*} (act : A → M → M)
    (hfi : ∀ a x, f (act a x) = f x) (hgi : ∀ a x, g (act a x) = g x)
    (t : unitInterval) (a : A) (x : M) :
    ambientHomotopy f g hf hg hunit hclose (t, act a x) =
      ambientHomotopy f g hf hg hunit hclose (t, x) :=
  phase_invariant f g act hfi hgi t a x

theorem circleHomotopy_invariant {A : Type*} (act : A → M → M)
    (hfi : ∀ a x, f (act a x) = f x) (hgi : ∀ a x, g (act a x) = g x)
    (t : unitInterval) (a : A) (x : M) :
    circleHomotopy f g hf hg hunit hclose (t, act a x) =
      circleHomotopy f g hf hg hunit hclose (t, x) :=
  _root_.Circle.ext (phase_invariant f g act hfi hgi t a x)

/-- The actual ambient homotopy, fixed on the entire specified relative set. -/
def ambientHomotopyRel (S : Set M) (heq : Set.EqOn g f S) :
    ContinuousMap.HomotopyRel ⟨f, hf⟩
      (normalizedMap g hg (close_right_ne_zero f g hunit hclose)) S where
  toHomotopy := ambientHomotopy f g hf hg hunit hclose
  prop' t x hx := ambientHomotopy_fixed f g hf hg hunit hclose S heq t x hx

/-- The genuine unit-circle homotopy is relative to the unchanged original phase. -/
def circleHomotopyRel (S : Set M) (heq : Set.EqOn g f S) :
    ContinuousMap.HomotopyRel (unitCircleMap f hf hunit)
      (normalizedCircleMap g hg (close_right_ne_zero f g hunit hclose)) S where
  toHomotopy := circleHomotopy f g hf hg hunit hclose
  prop' t x hx := circleHomotopy_fixed f g hf hg hunit hclose S heq t x hx

/-- One native homotopy object retains both exact relative values and pointwise invariance. -/
def relativeInvariantCircleHomotopy {A : Type*} (S : Set M) (heq : Set.EqOn g f S)
    (act : A → M → M) (hfi : ∀ a x, f (act a x) = f x)
    (hgi : ∀ a x, g (act a x) = g x) :
    ContinuousMap.HomotopyWith (unitCircleMap f hf hunit)
      (normalizedCircleMap g hg (close_right_ne_zero f g hunit hclose))
      (fun k => Set.EqOn k (unitCircleMap f hf hunit) S ∧
        ∀ a x, k (act a x) = k x) where
  toHomotopy := circleHomotopy f g hf hg hunit hclose
  prop' t := by
    constructor
    · intro x hx
      exact circleHomotopy_fixed f g hf hg hunit hclose S heq t x hx
    · intro a x
      exact circleHomotopy_invariant f g hf hg hunit hclose act hfi hgi t a x

/-- The extra properties do not replace the original constructed homotopy. -/
@[simp] theorem relativeInvariantCircleHomotopy_toHomotopy {A : Type*}
    (S : Set M) (heq : Set.EqOn g f S) (act : A → M → M)
    (hfi : ∀ a x, f (act a x) = f x) (hgi : ∀ a x, g (act a x) = g x) :
    (relativeInvariantCircleHomotopy f g hf hg hunit hclose S heq act hfi hgi).toHomotopy =
      circleHomotopy f g hf hg hunit hclose := rfl

@[simp] theorem relativeInvariantCircleHomotopy_coe {A : Type*}
    (S : Set M) (heq : Set.EqOn g f S) (act : A → M → M)
    (hfi : ∀ a x, f (act a x) = f x) (hgi : ∀ a x, g (act a x) = g x)
    (t : unitInterval) (x : M) :
    (relativeInvariantCircleHomotopy f g hf hg hunit hclose S heq act hfi hgi (t, x) : ℂ) =
      SmoothCircleApproximation.normalize ((1 - (t : ℝ)) • f x + (t : ℝ) • g x) := rfl

end Wikipedia.HopfProblem.SmoothCirclePhaseHomotopy

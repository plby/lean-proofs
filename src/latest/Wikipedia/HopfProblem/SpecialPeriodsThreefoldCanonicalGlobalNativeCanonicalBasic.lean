import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorNative

/-!
# The native canonical bundle and its unit-valued transition presentation

The source below is the canonical bundle built from the actual tangent
atlas.  The target is independently built by `TransitionData.core` from
its unit-valued reverse Jacobians.  The two constructions use the same
preferred charts, so the fibre comparison is the identity in preferred
scalar coordinates.  On every valid chart its coefficients agree in the
two original local trivializations.  No equality of the two cores, or of
their transitions away from chart overlaps, is asserted.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.NativeCanonical

local notation "I" => modelWithCornersSelf ℂ Model

variable (M : Type*) [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]

/-- The identity in the common preferred scalar coordinates is a genuine
continuous complex-linear equivalence of the independently built fibres. -/
def fiberEquiv (x : M) :
    (Atlas.core M).Fiber x ≃L[ℂ] (NativeTransitions.data M).core.Fiber x :=
  ContinuousLinearEquiv.refl ℂ ℂ

@[simp] theorem fiberEquiv_apply (x : M) (v : (Atlas.core M).Fiber x) :
    fiberEquiv M x v = id (α := ℂ) v := rfl

@[simp] theorem fiberEquiv_symm_apply (x : M)
    (v : (NativeTransitions.data M).core.Fiber x) :
    (fiberEquiv M x).symm v = id (α := ℂ) v := rfl

/-- The actual total-space map, preserving the literal base point. -/
def forward (p : (Atlas.core M).TotalSpace) : (NativeTransitions.data M).core.TotalSpace :=
  ⟨p.proj, fiberEquiv M p.proj p.2⟩

/-- The inverse map into the original native canonical total space. -/
def backward (p : (NativeTransitions.data M).core.TotalSpace) : (Atlas.core M).TotalSpace :=
  ⟨p.proj, (fiberEquiv M p.proj).symm p.2⟩

@[simp] theorem forward_proj (p : (Atlas.core M).TotalSpace) :
    (forward M p).proj = p.proj := rfl

@[simp] theorem backward_proj (p : (NativeTransitions.data M).core.TotalSpace) :
    (backward M p).proj = p.proj := rfl

@[simp] theorem forward_mk (x : M) (v : (Atlas.core M).Fiber x) :
    forward M ⟨x, v⟩ = ⟨x, fiberEquiv M x v⟩ := rfl

@[simp] theorem backward_mk (x : M) (v : (NativeTransitions.data M).core.Fiber x) :
    backward M ⟨x, v⟩ = ⟨x, (fiberEquiv M x).symm v⟩ := rfl

@[simp] theorem backward_forward (p : (Atlas.core M).TotalSpace) :
    backward M (forward M p) = p := by
  cases p
  rfl

@[simp] theorem forward_backward (p : (NativeTransitions.data M).core.TotalSpace) :
    forward M (backward M p) = p := by
  cases p
  rfl

/-- The actual local coefficients agree in every valid native chart. -/
theorem forward_localTriv (i : atlas Model M) (p : (Atlas.core M).TotalSpace)
    (hp : p.proj ∈ i.val.source) :
    ((NativeTransitions.data M).core.localTriv i (forward M p)).2 =
      ((Atlas.core M).localTriv i p).2 := by
  change (NativeTransitions.transition M (achart Model p.proj) i p.proj : ℂ) *
    id (α := ℂ) p.2 = Atlas.jacobian M i (achart Model p.proj) p.proj * id (α := ℂ) p.2
  rw [NativeTransitions.transition_val_eq M (achart Model p.proj) i
    ⟨mem_chart_source Model p.proj, hp⟩]

/-- The inverse preserves the same original trivialization coefficients. -/
theorem backward_localTriv (i : atlas Model M)
    (p : (NativeTransitions.data M).core.TotalSpace) (hp : p.proj ∈ i.val.source) :
    ((Atlas.core M).localTriv i (backward M p)).2 =
      ((NativeTransitions.data M).core.localTriv i p).2 := by
  have h := forward_localTriv M i (backward M p) hp
  rw [forward_backward] at h
  exact h.symm

/-- The full top covector read from the transition presentation's actual
local trivialization, rather than from a formal line character. -/
def inCoordinates (i : atlas Model M) (x : M)
    (v : (NativeTransitions.data M).core.Fiber x) : TopCovector :=
  coefficientEquiv ((NativeTransitions.data M).core.localTriv i ⟨x, v⟩).2

/-- The target fibre's preferred-coordinate identification with genuine
continuous alternating three-covectors on the actual tangent space. -/
def intrinsicEquiv (x : M) :
    (NativeTransitions.data M).core.Fiber x ≃L[ℂ] Atlas.IntrinsicTopCovector M x :=
  coefficientEquiv

theorem inCoordinates_fiberEquiv (i : atlas Model M) {x : M}
    (hx : x ∈ i.val.source) (v : (Atlas.core M).Fiber x) :
    inCoordinates M i x (fiberEquiv M x v) = Atlas.inCoordinates M i x v :=
  congrArg coefficientEquiv (forward_localTriv M i ⟨x, v⟩ hx)

theorem inCoordinates_fiberEquiv_symm (i : atlas Model M) {x : M}
    (hx : x ∈ i.val.source) (v : (NativeTransitions.data M).core.Fiber x) :
    Atlas.inCoordinates M i x ((fiberEquiv M x).symm v) = inCoordinates M i x v :=
  congrArg coefficientEquiv (backward_localTriv M i ⟨x, v⟩ hx)

@[simp] theorem intrinsicEquiv_fiberEquiv (x : M) (v : (Atlas.core M).Fiber x) :
    intrinsicEquiv M x (fiberEquiv M x v) = Atlas.intrinsicEquiv M x v := rfl

@[simp] theorem intrinsicEquiv_fiberEquiv_symm (x : M)
    (v : (NativeTransitions.data M).core.Fiber x) :
    Atlas.intrinsicEquiv M x ((fiberEquiv M x).symm v) = intrinsicEquiv M x v := rfl

/-- The target's actual chart coefficient represents the same intrinsic
covector pulled back by the actual tangent coordinate change. -/
theorem inCoordinates_eq_intrinsic_pullback (i : atlas Model M) {x : M}
    (hx : x ∈ i.val.source) (v : (NativeTransitions.data M).core.Fiber x) :
    inCoordinates M i x v = (intrinsicEquiv M x v).compContinuousLinearMap
      ((Atlas.tangentCore M).coordChange i (achart Model x) x) := by
  rw [← inCoordinates_fiberEquiv_symm M i hx v,
    Atlas.inCoordinates_eq_intrinsic_pullback, intrinsicEquiv_fiberEquiv_symm]

theorem inCoordinates_preferred (x : M) (v : (NativeTransitions.data M).core.Fiber x) :
    inCoordinates M (achart Model x) x v = intrinsicEquiv M x v := by
  rw [← inCoordinates_fiberEquiv_symm M (achart Model x) (mem_chart_source Model x) v,
    Atlas.inCoordinates_preferred, intrinsicEquiv_fiberEquiv_symm]

/-- Transitions of the actual target covectors are genuine derivative
pullback on overlaps, inherited through the proved coefficient comparison. -/
theorem inCoordinates_change (i j : atlas Model M) {x : M}
    (hi : x ∈ i.val.source) (hj : x ∈ j.val.source)
    (v : (NativeTransitions.data M).core.Fiber x) :
    inCoordinates M j x v = (inCoordinates M i x v).compContinuousLinearMap
      (fderiv ℂ (i.val ∘ j.val.symm) (j.val x)) := by
  rw [← inCoordinates_fiberEquiv_symm M j hj v,
    Atlas.inCoordinates_change M i j hi hj,
    inCoordinates_fiberEquiv_symm M i hi v]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.NativeCanonical

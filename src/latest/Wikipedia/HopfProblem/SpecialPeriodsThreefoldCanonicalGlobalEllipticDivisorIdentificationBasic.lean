import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorOrders

/-!
# Actual divisor-to-canonical comparison over the elliptic patch

The source is the natural total-space restriction of the independently
clutched divisor bundle; the target is the natural restriction of the
original global canonical bundle.  The fibre map sends the divisor's
coefficient in its native `some (achart x)` chart to the preferred native
canonical coefficient.  The actual cocycle proves identity of the two
coefficients in every matched chart.  Both maps and their inverse laws
retain the original bundle topologies and atlases.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor

open TrianglePeriodFamily.Canonical

local notation "I" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace

local instance identificationBasicManifold : IsManifold I ω Threefold.Space :=
  Threefold.space_isManifold

/-- The actual change to the divisor chart matching the preferred
native canonical chart at the same literal base point. -/
def patchWeight (x : Threefold.Space) : ℂˣ :=
  transition (indexAt x) (some (achart Model x)) x

/-- A continuous complex-linear equivalence between the two actual
fibres, in their independently constructed preferred coordinates. -/
def patchFiberEquiv (x : Threefold.Space) :
    divisorBundle.Fiber x ≃L[ℂ] Threefold.Canonical.bundle.Fiber x where
  toFun v := (patchWeight x : ℂ) * id (α := ℂ) v
  invFun w := (patchWeight x : ℂ)⁻¹ * id (α := ℂ) w
  left_inv v := inv_mul_cancel_left₀ (patchWeight x).ne_zero v
  right_inv w := mul_inv_cancel_left₀ (patchWeight x).ne_zero w
  map_add' v w := by
    change (patchWeight x : ℂ) * (id (α := ℂ) v + id (α := ℂ) w) =
      (patchWeight x : ℂ) * id (α := ℂ) v + (patchWeight x : ℂ) * id (α := ℂ) w
    exact mul_add _ _ _
  map_smul' c v := by
    change (patchWeight x : ℂ) * (c * id (α := ℂ) v) =
      c * ((patchWeight x : ℂ) * id (α := ℂ) v)
    exact mul_left_comm _ _ _
  continuous_toFun := by
    change Continuous (fun v : ℂ => (patchWeight x : ℂ) * v)
    exact continuous_const.mul continuous_id
  continuous_invFun := by
    change Continuous (fun v : ℂ => (patchWeight x : ℂ)⁻¹ * v)
    exact continuous_const.mul continuous_id

@[simp] theorem patchFiberEquiv_apply (x : Threefold.Space) (v : divisorBundle.Fiber x) :
    patchFiberEquiv x v = (patchWeight x : ℂ) * id (α := ℂ) v := rfl

@[simp] theorem patchFiberEquiv_symm_apply (x : Threefold.Space)
    (v : Threefold.Canonical.bundle.Fiber x) :
    (patchFiberEquiv x).symm v = (patchWeight x : ℂ)⁻¹ * id (α := ℂ) v := rfl

/-- This is an actual local-trivialization coefficient of the divisor
bundle, not an arbitrarily chosen scalar identification. -/
theorem patchFiberEquiv_eq_localTriv (x : Threefold.Space) (v : divisorBundle.Fiber x) :
    id (α := ℂ) (patchFiberEquiv x v) =
      (divisorBundle.localTriv (some (achart Model x)) ⟨x, v⟩).2 := rfl

/-- The natural open total-space restriction of the divisor bundle. -/
def patchTotal : TopologicalSpace.Opens divisorBundle.TotalSpace :=
  ⟨Bundle.TotalSpace.proj ⁻¹' (patch : Set Threefold.Space),
    patch.isOpen.preimage divisorBundle.continuous_proj⟩

/-- The already constructed natural restriction of the original global
canonical bundle to the full order-four elliptic patch. -/
abbrev nativePatchTotal : TopologicalSpace.Opens Threefold.Canonical.bundle.TotalSpace :=
  Threefold.Canonical.bundlePatch (some (some Wikipedia.HopfProblem.Elliptic.Kind.four))

def patchTotalProjection (p : patchTotal) : patch := ⟨p.val.proj, p.property⟩

def nativePatchTotalProjection (p : nativePatchTotal) : patch := ⟨p.val.proj, p.property⟩

/-- The actual fibre-linear map over the identity of the entire elliptic patch. -/
def patchForward (p : patchTotal) : nativePatchTotal :=
  ⟨⟨p.val.proj, patchFiberEquiv p.val.proj p.val.2⟩, p.property⟩

/-- Its literal fibrewise inverse, in the original divisor-bundle fibres. -/
def patchBackward (p : nativePatchTotal) : patchTotal :=
  ⟨⟨p.val.proj, (patchFiberEquiv p.val.proj).symm p.val.2⟩, p.property⟩

@[simp] theorem patchForward_proj (p : patchTotal) :
    (patchForward p).val.proj = p.val.proj := rfl

@[simp] theorem patchBackward_proj (p : nativePatchTotal) :
    (patchBackward p).val.proj = p.val.proj := rfl

@[simp] theorem patchBackward_patchForward (p : patchTotal) :
    patchBackward (patchForward p) = p := by
  rcases p with ⟨⟨x, v⟩, hx⟩
  apply Subtype.ext
  change (⟨x, (patchFiberEquiv x).symm (patchFiberEquiv x v)⟩ : divisorBundle.TotalSpace) =
    ⟨x, v⟩
  rw [(patchFiberEquiv x).symm_apply_apply]

@[simp] theorem patchForward_patchBackward (p : nativePatchTotal) :
    patchForward (patchBackward p) = p := by
  rcases p with ⟨⟨x, v⟩, hx⟩
  apply Subtype.ext
  change (⟨x, patchFiberEquiv x ((patchFiberEquiv x).symm v)⟩ :
    Threefold.Canonical.bundle.TotalSpace) = ⟨x, v⟩
  rw [(patchFiberEquiv x).apply_symm_apply]

/-- The cocycle computes the actual preferred multiplier in every
matched native chart throughout the full elliptic patch. -/
theorem patchWeight_change (i : atlas Model Threefold.Space) {x : Threefold.Space}
    (hw : x ∈ patch) (hi : x ∈ i.val.source) :
    (NativeTransitions.transition Threefold.Space (achart Model x) i x : ℂ) *
      (patchWeight x : ℂ) = (transition (indexAt x) (some i) x : ℂ) := by
  have h := transition_comp (indexAt x) (some (achart Model x)) (some i) x
    ⟨⟨mem_baseSet_at x, ⟨hw, mem_chart_source Model x⟩⟩, ⟨hw, hi⟩⟩
  exact congrArg (fun u : ℂˣ => (u : ℂ)) h

/-- The forward map is the identity in the two original local
trivializations, at every point where that native chart is valid. -/
theorem patchForward_localTriv (i : atlas Model Threefold.Space) (p : patchTotal)
    (hp : p.val.proj ∈ i.val.source) :
    (Threefold.Canonical.bundle.localTriv i (patchForward p).val).2 =
      (divisorBundle.localTriv (some i) p.val).2 := by
  change Atlas.jacobian Threefold.Space i (achart Model p.val.proj) p.val.proj *
    ((patchWeight p.val.proj : ℂ) * id (α := ℂ) p.val.2) =
      (transition (indexAt p.val.proj) (some i) p.val.proj : ℂ) * id (α := ℂ) p.val.2
  rw [← NativeTransitions.transition_val_eq Threefold.Space (achart Model p.val.proj) i
    ⟨mem_chart_source Model p.val.proj, hp⟩, ← mul_assoc,
    patchWeight_change i p.property hp]

/-- The inverse has the same identity coordinate expression in the
same two original bundle atlases. -/
theorem patchBackward_localTriv (i : atlas Model Threefold.Space) (p : nativePatchTotal)
    (hp : p.val.proj ∈ i.val.source) :
    (divisorBundle.localTriv (some i) (patchBackward p).val).2 =
      (Threefold.Canonical.bundle.localTriv i p.val).2 := by
  have h := patchForward_localTriv i (patchBackward p) hp
  rw [patchForward_patchBackward] at h
  exact h.symm

/-- The actual divisor section is sent to the original order-four
canonical section on the full global elliptic patch. -/
theorem patchFiberEquiv_canonicalSection (x : patch) :
    patchFiberEquiv x.val (canonicalSection x.val) = Sections.patchSection .four x := by
  change id (α := ℂ) (patchFiberEquiv x.val (canonicalSection x.val)) =
    id (α := ℂ) (Sections.patchSection .four x)
  calc
    _ = (divisorBundle.localTriv (some (achart Model x.val))
        ⟨x.val, canonicalSection x.val⟩).2 := patchFiberEquiv_eq_localTriv _ _
    _ = patchCoefficient (achart Model x.val) x.val :=
      canonicalSection_localCoefficient (some (achart Model x.val))
        ⟨x.property, mem_chart_source Model x.val⟩
    _ = id (α := ℂ) (Sections.patchSection .four x) := by
      rw [patchCoefficient, extendedSection_of_mem x.property]
      change Atlas.jacobian Threefold.Space (achart Model x.val) (achart Model x.val) x.val *
        id (α := ℂ) (Sections.patchSection .four ⟨x.val, x.property⟩) = _
      rw [Atlas.jacobian_self Threefold.Space (achart Model x.val)
        (mem_chart_source Model x.val), one_mul]
      rfl

def canonicalSectionOnPatch (x : patch) : patchTotal :=
  ⟨canonicalSectionMap x.val, x.property⟩

def nativeSectionOnPatch (x : patch) : nativePatchTotal :=
  ⟨Sections.patchSectionMap .four x, x.property⟩

theorem patchForward_canonicalSection (x : patch) :
    patchForward (canonicalSectionOnPatch x) = nativeSectionOnPatch x := by
  apply Subtype.ext
  change (⟨x.val, patchFiberEquiv x.val (canonicalSection x.val)⟩ :
    Threefold.Canonical.bundle.TotalSpace) = ⟨x.val, Sections.patchSection .four x⟩
  rw [patchFiberEquiv_canonicalSection]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor

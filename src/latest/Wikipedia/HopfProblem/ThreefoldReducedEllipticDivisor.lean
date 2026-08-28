import Wikipedia.HopfProblem.ThreefoldReducedEllipticDivisorLocal
import Wikipedia.HopfProblem.ThreefoldLineBundleTrivialization
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The reduced elliptic divisor bundles on the original threefold

The cyclic-cover root section is clutched to a nonzero constant section
off its central fibre. This constructs the two actual holomorphic divisor
bundles. Continuous trivialization gives global continuous defining
functions, with no extra geometric hypotheses.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.ReducedEllipticDivisor

open Elliptic EllipticFilling EllipticGeometry

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace

variable (j : Kind)

abbrev Index := Option (SpecialFullFilling j)

def baseSet : Index j → Set Space
  | none => outside j
  | some i => chartSet j i

theorem isOpen_baseSet (i : Index j) : IsOpen (baseSet j i) := by
  cases i with
  | none => exact (outside j).isOpen
  | some i => exact isOpen_chartSet j i

def indexAt (x : Space) : Index j := by
  classical
  exact if x ∈ outside j then none else some ((fillingData j).indexAt (fillingPoint j x))

theorem mem_baseSet_at (x : Space) : x ∈ baseSet j (indexAt j x) := by
  classical
  unfold indexAt
  split_ifs with hx
  · exact hx
  · exact mem_chartSet_at j ((mem_outside_or_patch j x).resolve_left hx)

def coefficientUnit (i : SpecialFullFilling j) (x : Space) : ℂˣ := by
  classical
  exact if h : coefficient j i x ≠ 0 then Units.mk0 (coefficient j i x) h else 1

theorem coefficientUnit_val (i : SpecialFullFilling j) {x : Space}
    (hx : coefficient j i x ≠ 0) : (coefficientUnit j i x : ℂ) = coefficient j i x := by
  simp only [coefficientUnit, dif_pos hx, Units.val_mk0]

theorem coefficientUnit_change (i k : SpecialFullFilling j) {x : Space}
    (hi : x ∈ chartSet j i) (hk : x ∈ chartSet j k) (ho : x ∈ outside j) :
    rootTransition j i k x * coefficientUnit j i x = coefficientUnit j k x := by
  apply Units.ext
  change (rootTransition j i k x : ℂ) * (coefficientUnit j i x : ℂ) = _
  rw [coefficientUnit_val j i (coefficient_ne_zero j i hi ho),
    coefficientUnit_val j k (coefficient_ne_zero j k hk ho)]
  exact coefficient_change j i k ⟨hi, hk⟩

def transition : Index j → Index j → Space → ℂˣ
  | none, none, _ => 1
  | none, some k, x => coefficientUnit j k x
  | some i, none, x => (coefficientUnit j i x)⁻¹
  | some i, some k, x => rootTransition j i k x

theorem transition_none_some_val (k : SpecialFullFilling j) {x : Space}
    (hx : x ∈ baseSet j none ∩ baseSet j (some k)) :
    (transition j none (some k) x : ℂ) = coefficient j k x :=
  coefficientUnit_val j k (coefficient_ne_zero j k hx.2 hx.1)

theorem transition_some_none_val (i : SpecialFullFilling j) {x : Space}
    (hx : x ∈ baseSet j (some i) ∩ baseSet j none) :
    (transition j (some i) none x : ℂ) = (coefficient j i x)⁻¹ := by
  change ((coefficientUnit j i x)⁻¹ : ℂˣ).val = _
  rw [Units.val_inv_eq_inv_val, coefficientUnit_val j i (coefficient_ne_zero j i hx.1 hx.2)]

theorem transition_self (i : Index j) (x : Space) (hx : x ∈ baseSet j i) :
    transition j i i x = 1 := by
  cases i with
  | none => rfl
  | some i => exact rootTransition_self j i hx

theorem transition_comp (i k l : Index j) (x : Space)
    (hx : x ∈ baseSet j i ∩ baseSet j k ∩ baseSet j l) :
    transition j k l x * transition j i k x = transition j i l x := by
  cases i with
  | none =>
    cases k with
    | none => cases l <;> simp only [transition, mul_one]
    | some k =>
      cases l with
      | none => exact inv_mul_cancel (coefficientUnit j k x)
      | some l => exact coefficientUnit_change j k l hx.1.2 hx.2 hx.1.1
  | some i =>
    cases k with
    | none =>
      cases l with
      | none => exact one_mul _
      | some l =>
        have h := coefficientUnit_change j i l hx.1.1 hx.2 hx.1.2
        change coefficientUnit j l x * (coefficientUnit j i x)⁻¹ = _
        rw [← h, mul_assoc, mul_inv_cancel, mul_one]
        rfl
    | some k =>
      cases l with
      | none =>
        have h := coefficientUnit_change j i k hx.1.1 hx.1.2 hx.2
        change (coefficientUnit j k x)⁻¹ * rootTransition j i k x = _
        rw [← h, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        rfl
      | some l => exact rootTransition_comp j i k l hx

theorem transition_holomorphicOn (i k : Index j) :
    ContMDiffOn IF 𝓘(ℂ) ω (fun x => (transition j i k x : ℂ))
      (baseSet j i ∩ baseSet j k) := by
  cases i with
  | none =>
    cases k with
    | none => exact contMDiffOn_const
    | some k =>
      exact ((coefficient_holomorphicOn j k).mono inter_subset_right).congr
        (fun _ hx => transition_none_some_val j k hx)
  | some i =>
    cases k with
    | none =>
      exact (((coefficient_holomorphicOn j i).mono inter_subset_left).inv₀
        (fun x hx => coefficient_ne_zero j i hx.1 hx.2)).congr
          (fun _ hx => transition_some_none_val j i hx)
    | some k => exact rootTransition_holomorphicOn j i k

def transitions : HolomorphicCharacterBundle.TransitionData Space (Index j) where
  baseSet := baseSet j
  isOpen_baseSet := isOpen_baseSet j
  indexAt := indexAt j
  mem_baseSet_at := mem_baseSet_at j
  transition := transition j
  transition_self := transition_self j
  transition_comp := transition_comp j
  continuousOn_transition i k := (transition_holomorphicOn j i k).continuousOn

instance transitions_isHolomorphic : (transitions j).IsHolomorphic IF where
  contMDiffOn_transition := transition_holomorphicOn j

def localEquation : Index j → Space → ℂ
  | none, _ => 1
  | some i, x => coefficient j i x

theorem localEquation_holomorphicOn (i : Index j) :
    ContMDiffOn IF 𝓘(ℂ) ω (localEquation j i) (baseSet j i) := by
  cases i with
  | none => exact contMDiffOn_const
  | some i => exact coefficient_holomorphicOn j i

theorem localEquation_compatible : (transitions j).IsCompatible (localEquation j) := by
  intro i k x hx
  cases i with
  | none =>
    cases k with
    | none => exact one_mul _
    | some k =>
      change (transition j none (some k) x : ℂ) * 1 = coefficient j k x
      rw [transition_none_some_val j k hx, mul_one]
  | some i =>
    cases k with
    | none =>
      change (transition j (some i) none x : ℂ) * coefficient j i x = 1
      rw [transition_some_none_val j i hx]
      exact inv_mul_cancel₀ (coefficient_ne_zero j i hx.1 hx.2)
    | some k => exact coefficient_change j i k hx

def rootSection (x : Space) : (transitions j).core.Fiber x :=
  (transitions j).sectionFromLocal (localEquation j) x

theorem rootSection_holomorphic :
    ContMDiff IF ((IF).prod 𝓘(ℂ)) ω
      (fun x => (⟨x, rootSection j x⟩ : (transitions j).core.TotalSpace)) :=
  (transitions j).sectionFromLocal_holomorphic IF (localEquation j)
    (localEquation_compatible j) (localEquation_holomorphicOn j)

theorem localEquation_eq_zero_iff (i : Index j) {x : Space} (hx : x ∈ baseSet j i) :
    localEquation j i x = 0 ↔ projectionSphere x = sphereValue j := by
  cases i with
  | none => exact iff_of_false one_ne_zero hx
  | some i => exact coefficient_eq_zero_iff j i hx

theorem rootSection_eq_zero_iff (x : Space) :
    rootSection j x = 0 ↔ projectionSphere x = sphereValue j :=
  localEquation_eq_zero_iff j (indexAt j x) (mem_baseSet_at j x)

def trivialization : HolomorphicPicard.ContinuousTrivialization (transitions j).core.Fiber :=
  LineBundleTrivialization.continuousTrivialization (transitions j).core.Fiber

def definingFunction (x : Space) : ℂ := (trivialization j).fiberEquiv x (rootSection j x)

theorem definingFunction_continuous : Continuous (definingFunction j) := by
  unfold definingFunction
  have h := ((trivialization j).homeomorph.continuous.comp
    (rootSection_holomorphic j).continuous).snd
  simpa only [Function.comp_def, HolomorphicPicard.ContinuousTrivialization.map_fiber,
    ] using h

theorem definingFunction_eq_zero_iff (x : Space) :
    definingFunction j x = 0 ↔ projectionSphere x = sphereValue j := by
  rw [definingFunction, LinearEquiv.map_eq_zero_iff, rootSection_eq_zero_iff]

/-- The local power chart makes the nonzero locus dense at every point
of the central surface, for each of the two actual elliptic fibres. -/
theorem outside_dense : Dense (outside j : Set Space) := by
  have hd : Dense {u : ℂ × ComplexPlane₂ | u.1 ≠ 0} := by
    have h := (dense_compl_singleton (0 : ℂ)).prod
      (dense_univ : Dense (univ : Set ComplexPlane₂))
    convert h using 1
    ext u
    simp
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, hxU⟩ := hne
  by_cases hx : projectionSphere x = sphereValue j
  · obtain ⟨e, hxs, _, _, hp⟩ := FibreClassification.elliptic_fibre_power_chart j x hx
    have hV : IsOpen (e '' (e.source ∩ U)) :=
      e.toOpenPartialHomeomorph.isOpen_image_source_inter hU
    have hVne : (e '' (e.source ∩ U)).Nonempty := ⟨e x, ⟨x, ⟨hxs, hxU⟩, rfl⟩⟩
    obtain ⟨u, huV, hunz⟩ := hd.inter_open_nonempty _ hV hVne
    obtain ⟨w, ⟨hws, hwU⟩, rfl⟩ := huV
    refine ⟨w, hwU, ?_⟩
    intro hw
    have hpower := hp (e w) (e.map_source' hws)
    have he : e.symm (e w) = w := e.left_inv' hws
    rw [he, hw, sphereChart_value] at hpower
    exact (pow_ne_zero _ hunz) hpower.symm
  · exact ⟨x, hxU, hx⟩

theorem definingFunction_nonzero_dense : Dense {x | definingFunction j x ≠ 0} := by
  convert outside_dense j using 1
  ext x
  exact (definingFunction_eq_zero_iff j x).not

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.ReducedEllipticDivisor

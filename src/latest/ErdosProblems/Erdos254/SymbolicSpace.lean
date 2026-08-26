/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.InvariantMeasure
import ErdosProblems.Erdos254.DynamicalBohr

namespace Erdos254

open Filter MeasureTheory Set
open scoped Topology BigOperators

abbrev BinarySequence := ℤ → Bool

/-- Integer translation on the compact space of binary configurations. -/
def binaryShift (k : ℤ) : BinarySequence ≃ₜ BinarySequence where
  toFun x i := x (i + k)
  invFun x i := x (i - k)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  continuous_toFun := continuous_pi (fun i ↦ continuous_apply (i + k))
  continuous_invFun := continuous_pi (fun i ↦ continuous_apply (i - k))

@[simp] lemma binaryShift_apply (k : ℤ) (x : BinarySequence) (i : ℤ) :
    binaryShift k x i = x (i + k) := rfl

lemma binaryShift_add (k l : ℤ) (x : BinarySequence) :
    binaryShift k (binaryShift l x) = binaryShift (k + l) x := by
  ext i
  simp only [binaryShift_apply, add_assoc]

def binaryOrbitClosure (c : BinarySequence) : Set BinarySequence :=
  closure (Set.range (fun k : ℤ ↦ binaryShift k c))

instance binaryOrbitClosure_compact (c : BinarySequence) : CompactSpace (binaryOrbitClosure c) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

lemma binaryShift_mem_orbitClosure (c : BinarySequence) (k : ℤ)
    {x : BinarySequence} (hx : x ∈ binaryOrbitClosure c) :
    binaryShift k x ∈ binaryOrbitClosure c := by
  have hsub : Set.range (fun l : ℤ ↦ binaryShift l c) ⊆
      (binaryShift k) ⁻¹' binaryOrbitClosure c := by
    rintro _ ⟨l, rfl⟩
    apply subset_closure
    exact ⟨k + l, (binaryShift_add k l c).symm⟩
  exact closure_minimal hsub (isClosed_closure.preimage (binaryShift k).continuous) hx

def binaryBase (c : BinarySequence) : binaryOrbitClosure c :=
  ⟨c, subset_closure ⟨0, by ext i; simp⟩⟩

/-- The invertible shift restricted to a configuration's orbit closure. -/
def orbitShift (c : BinarySequence) : binaryOrbitClosure c ≃ₜ binaryOrbitClosure c where
  toFun x := ⟨binaryShift 1 x, binaryShift_mem_orbitClosure c 1 x.property⟩
  invFun x := ⟨binaryShift (-1) x, binaryShift_mem_orbitClosure c (-1) x.property⟩
  left_inv x := by apply Subtype.ext; ext i; simp [binaryShift_apply]
  right_inv x := by apply Subtype.ext; ext i; simp [binaryShift_apply]
  continuous_toFun := ((binaryShift 1).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((binaryShift (-1)).continuous.comp continuous_subtype_val).subtype_mk _

lemma orbitShift_iterate_apply (c : BinarySequence) (x : binaryOrbitClosure c)
    (n : ℕ) (i : ℤ) : ((orbitShift c)^[n] x).val i = x.val (i + n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((orbitShift c)^[n] x).val (i + 1) = _
    rw [ih]
    exact congrArg x.val (show i + 1 + (n : ℤ) = i + (n + 1 : ℕ) by omega)

lemma orbitShift_symm_iterate_apply (c : BinarySequence) (x : binaryOrbitClosure c)
    (n : ℕ) (i : ℤ) : ((orbitShift c).symm^[n] x).val i = x.val (i - n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((orbitShift c).symm^[n] x).val (i + (-1)) = _
    rw [ih]
    exact congrArg x.val (show i + (-1) - (n : ℤ) = i - (n + 1 : ℕ) by omega)

/-- Every finite pattern in an orbit limit occurs in the original configuration. -/
lemma orbitClosure_finite_pattern {c x : BinarySequence} (hx : x ∈ binaryOrbitClosure c)
    (F : Finset ℤ) : ∃ k : ℤ, ∀ i ∈ F, x i = c (i + k) := by
  let r : BinarySequence → (F → Bool) := fun y i ↦ y i
  have hr : Continuous r := continuous_pi (fun i ↦ continuous_apply i.val)
  let O : Set BinarySequence := r ⁻¹' {r x}
  have hO : IsOpen O := (isOpen_discrete _).preimage hr
  obtain ⟨_, hy, k, rfl⟩ := mem_closure_iff.mp hx O hO (by rfl)
  have heq : r (binaryShift k c) = r x := hy
  refine ⟨k, fun i hi ↦ ?_⟩
  exact (congrFun heq ⟨i, hi⟩).symm

def orbitCylinder (c : BinarySequence) : Set (binaryOrbitClosure c) := {x | x.val 0 = true}

lemma orbitCylinder_measurable (c : BinarySequence) : MeasurableSet (orbitCylinder c) := by
  change MeasurableSet ((fun x : binaryOrbitClosure c ↦ x.val 0) ⁻¹' {true})
  exact ((measurable_pi_apply 0).comp
    (measurable_subtype_coe : Measurable (Subtype.val : binaryOrbitClosure c → BinarySequence)))
      (measurableSet_singleton true)

def orbitObservable (c : BinarySequence) : C(binaryOrbitClosure c, ℝ) :=
  ⟨fun x ↦ (x.val 0).toNat,
    (continuous_of_discreteTopology : Continuous (fun b : Bool ↦ (b.toNat : ℝ))).comp
      ((continuous_apply 0).comp continuous_subtype_val)⟩

lemma orbitObservable_bounds (c : BinarySequence) (x : binaryOrbitClosure c) :
    0 ≤ orbitObservable c x ∧ orbitObservable c x ≤ 1 := by
  change 0 ≤ ((x.val 0).toNat : ℝ) ∧ ((x.val 0).toNat : ℝ) ≤ 1
  cases x.val 0 <;> norm_num

lemma integral_orbitObservable (c : BinarySequence) (μ : Measure (binaryOrbitClosure c)) :
    (∫ x, orbitObservable c x ∂μ) = μ.real (orbitCylinder c) := by
  have hfun : (fun x ↦ orbitObservable c x) =
      (orbitCylinder c).indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    change ((x.val 0).toNat : ℝ) = _
    cases h : x.val 0 <;> simp [orbitCylinder, h]
  rw [hfun, integral_indicator (orbitCylinder_measurable c)]
  simp [Measure.real]

end Erdos254

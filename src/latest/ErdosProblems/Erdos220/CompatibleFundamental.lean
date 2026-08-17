import ErdosProblems.Erdos220.Fourier
import ErdosProblems.Erdos220.Fundamental

/-!
# The compatible-frequency / fundamental-lemma bridge

The Fourier expansion uses six families of primitive frequencies and retains
only tuples satisfying `sixPrimeCompatible`.  `FundamentalSystem`, on the
other hand, is phrased as a contraction over a finite tensor system.  This
file gives the exact, reusable bridge between those two presentations.

The data in `CompatibleFundamentalModel` is entirely finite and structural:
it identifies the primitive value domains and the compatible state domain
inside a `FundamentalSystem`.  The analytic estimate is then a direct
consequence of `FundamentalSystem.fundamental_le`; no estimate is stored in
the model.
-/

open scoped BigOperators

namespace Erdos220

noncomputable section

/-- Six labelled primitive-frequency tuples for a fixed support family. -/
abbrev SixPrimitiveFrequencyTuple (U : Fin 6 → Finset ℕ) :=
  ∀ i, PrimitiveFrequencyTuple (U i)

/-- The finite subtype of globally compatible primitive tuples. -/
abbrev CompatiblePrimitiveTuple (s : ℕ) (U : Fin 6 → Finset ℕ) :=
  {a : SixPrimitiveFrequencyTuple U // sixPrimeCompatible s a}

/-- The compatible contraction attached to six functions on primitive
frequency tuples. -/
noncomputable def compatibleFrequencyContraction (s : ℕ) (U : Fin 6 → Finset ℕ)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ) : ℂ := by
  classical
  exact ∑ a : SixPrimitiveFrequencyTuple U,
    if sixPrimeCompatible s a then ∏ i, f i (a i) else 0

/-- The interval Fourier transform on a primitive prime-frequency tuple. -/
def primitiveIntervalFourier {T : Finset ℕ} (h : ℕ)
    (a : PrimitiveFrequencyTuple T) : ℂ :=
  ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a t

/-- The compatible sixfold interval contraction occurring after complete
period orthogonality. -/
def compatibleIntervalContraction (s h : ℕ)
    (U : Fin 6 → Finset ℕ) : ℂ :=
  compatibleFrequencyContraction s U
    (fun _ a ↦ primitiveIntervalFourier h a)

/-- A finite structural realization of compatible primitive tuples inside a
`FundamentalSystem`.

The system is allowed to contain zero/nonprimitive values and states.  The
finsets `valueDomain` select precisely the primitive values.  Consequently
the selected state domain consists of those system states all of whose six
projections are primitive. -/
structure CompatibleFundamentalModel (s : ℕ)
    (U : Fin 6 → Finset ℕ) where
  system : FundamentalSystem
  valueDomain : ∀ i, Finset (FundamentalSystem.Value system i)
  valueDomain_subset : ∀ i, valueDomain i ⊆ FundamentalSystem.valueElements system i
  valueEquiv : ∀ i,
    PrimitiveFrequencyTuple (U i) ≃
      {x : FundamentalSystem.Value system i // x ∈ valueDomain i}
  stateEquiv : CompatiblePrimitiveTuple s U ≃
    {x : FundamentalSystem.State system //
      x ∈ FundamentalSystem.stateElements system ∧
        ∀ i, FundamentalSystem.project system i x ∈ valueDomain i}
  project_encode : ∀ (a : CompatiblePrimitiveTuple s U) (i : Fin 6),
    ((valueEquiv i) (a.1 i)).1 =
      FundamentalSystem.project system i ((stateEquiv a).1)

namespace CompatibleFundamentalModel

variable {s : ℕ} {U : Fin 6 → Finset ℕ}

/-- Extend a function on primitive values by zero to the whole value space
of the tensor system. -/
noncomputable def extend (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ)
    (i : Fin 6) (x : M.system.Value i) : ℂ := by
  classical
  exact if hx : x ∈ M.valueDomain i then
      f i ((M.valueEquiv i).symm ⟨x, hx⟩)
    else 0

@[simp] theorem extend_valueEquiv (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ)
    (i : Fin 6) (a : PrimitiveFrequencyTuple (U i)) :
    M.extend f i ((M.valueEquiv i a).1) = f i a := by
  simp [extend]

theorem extend_eq_zero_of_not_mem (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ)
    (i : Fin 6) {x : M.system.Value i} (hx : x ∉ M.valueDomain i) :
    M.extend f i x = 0 := by
  simp [extend, hx]

/-- The tensor energy of the zero extension is exactly the primitive `L²`
energy, with no inactive-coordinate cardinality loss. -/
theorem energy_extend_eq (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ) (i : Fin 6) :
    M.system.energy i (M.extend f i) =
      ∑ a : PrimitiveFrequencyTuple (U i), ‖f i a‖ ^ 2 := by
  classical
  rw [FundamentalSystem.energy]
  calc
    (M.system.valueElements i).sum (fun x ↦ ‖M.extend f i x‖ ^ 2) =
        (M.valueDomain i).sum (fun x ↦ ‖M.extend f i x‖ ^ 2) := by
      symm
      apply Finset.sum_subset (M.valueDomain_subset i)
      intro x hxall hxdomain
      rw [M.extend_eq_zero_of_not_mem f i hxdomain]
      simp
    _ = ∑ x : {x : M.system.Value i // x ∈ M.valueDomain i},
          ‖M.extend f i x.1‖ ^ 2 := by
      apply Finset.sum_subtype
      intro x
      rfl
    _ = ∑ a : PrimitiveFrequencyTuple (U i), ‖f i a‖ ^ 2 := by
      symm
      apply Fintype.sum_equiv (M.valueEquiv i)
      intro a
      simp

/-- After zero extension, the full system contraction is exactly the sum
over compatible primitive tuples. -/
theorem contraction_extend_eq (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ) :
    M.system.contraction (M.extend f) = compatibleFrequencyContraction s U f := by
  classical
  let good : M.system.State → Prop := fun x ↦
    ∀ i, M.system.project i x ∈ M.valueDomain i
  have hzero {x : M.system.State} (hx : ¬ good x) :
      ∏ i, M.extend f i (M.system.project i x) = 0 := by
    have hex : ∃ i, M.system.project i x ∉ M.valueDomain i := by
      simpa [good] using hx
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact M.extend_eq_zero_of_not_mem f i hi
  have hfull_filter :
      M.system.stateElements.sum
          (fun x ↦ ∏ i, M.extend f i (M.system.project i x)) =
        (M.system.stateElements.filter good).sum
          (fun x ↦ ∏ i, M.extend f i (M.system.project i x)) := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hgood : good x
    · rw [if_pos hgood]
    · rw [if_neg hgood, hzero hgood]
  have hstate_subtype :
      (M.system.stateElements.filter good).sum
          (fun x ↦ ∏ i, M.extend f i (M.system.project i x)) =
        ∑ x : {x : M.system.State // x ∈ M.system.stateElements.filter good},
          ∏ i, M.extend f i (M.system.project i x.1) := by
    apply Finset.sum_subtype
    intro x
    rfl
  have hcompatible_subtype :
      (∑ a : CompatiblePrimitiveTuple s U, ∏ i, f i (a.1 i)) =
        ∑ x : {x : M.system.State // x ∈ M.system.stateElements.filter good},
          ∏ i, M.extend f i (M.system.project i x.1) := by
    let e : CompatiblePrimitiveTuple s U ≃
        {x : M.system.State // x ∈ M.system.stateElements.filter good} :=
      M.stateEquiv.trans
        { toFun := fun x ↦ ⟨x.1, Finset.mem_filter.mpr ⟨x.2.1, x.2.2⟩⟩
          invFun := fun x ↦ ⟨x.1, (Finset.mem_filter.mp x.2).1,
            (Finset.mem_filter.mp x.2).2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    apply Fintype.sum_equiv e
    intro a
    apply Finset.prod_congr rfl
    intro i hi
    change f i (a.1 i) =
      M.extend f i (M.system.project i (M.stateEquiv a).1)
    rw [← M.project_encode a i, M.extend_valueEquiv]
  have hite_subtype : compatibleFrequencyContraction s U f =
      ∑ a : CompatiblePrimitiveTuple s U, ∏ i, f i (a.1 i) := by
    unfold compatibleFrequencyContraction
    rw [show (∑ a : SixPrimitiveFrequencyTuple U,
        if sixPrimeCompatible s a then ∏ i, f i (a i) else 0) =
        ∑ a ∈ (Finset.univ : Finset (SixPrimitiveFrequencyTuple U)).filter
            (sixPrimeCompatible s), ∏ i, f i (a i) by
      rw [Finset.sum_filter]]
    apply Finset.sum_subtype
    intro a
    simp
  rw [FundamentalSystem.contraction, hfull_filter, hstate_subtype,
    ← hcompatible_subtype, ← hite_subtype]

/-- The arbitrary-support compatible-frequency contraction estimate.  Once
a finite CRT model is supplied, the conclusion follows solely from the
proved tensorized fundamental inequality. -/
theorem compatibleFrequencyContraction_le
    (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ) :
    ‖compatibleFrequencyContraction s U f‖ ≤
      M.system.scale *
        ∏ i, Real.sqrt (∑ a : PrimitiveFrequencyTuple (U i), ‖f i a‖ ^ 2) := by
  rw [← M.contraction_extend_eq f]
  simpa only [M.energy_extend_eq f] using
    M.system.fundamental_le (M.extend f)

/-- Specialization to the six interval Fourier transforms used in the
moment expansion. -/
theorem compatibleIntervalContraction_le
    (M : CompatibleFundamentalModel s U) (h : ℕ) :
    ‖compatibleIntervalContraction s h U‖ ≤
      M.system.scale *
        ∏ i, Real.sqrt
          (∑ a : PrimitiveFrequencyTuple (U i),
            ‖primitiveIntervalFourier h a‖ ^ 2) := by
  exact M.compatibleFrequencyContraction_le
    (fun _ a ↦ primitiveIntervalFourier h a)

end CompatibleFundamentalModel

end

end Erdos220

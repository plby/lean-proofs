import ErdosProblems.Erdos1188.SparseAssignments

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Simultaneously varying support ranges at every base coordinate
-/

namespace Erdos1188

open scoped BigOperators

universe u

variable {m : ℕ} (q : Fin m → ℕ) (P : ℕ)
variable (Pool : Fin m → Type u)
variable [(i : Fin m) → Fintype (Pool i)]
variable [(i : Fin m) → DecidableEq (Pool i)]

/-- At coordinate `i`, choose exactly one pool support per nonzero residue. -/
abbrev SparseRangeChoice (i : Fin m) [NeZero (q i)] :=
  {R : Finset (Pool i) // R.card = q i - 1}

/-- Make an independent range choice at every base coordinate. -/
abbrev SparseRangeProfile [(i : Fin m) → NeZero (q i)] :=
  (i : Fin m) → SparseRangeChoice q Pool i

/-- Turn a range profile into a frame assignment by choosing a bijection from
nonzero residues to each prescribed range. -/
noncomputable def assignmentForSparseRanges
    [(i : Fin m) → NeZero (q i)]
    (poolSupport : (i : Fin m) → Pool i ↪ Finset (Fin i.val))
    (R : SparseRangeProfile q Pool) : FrameAssignment q := fun i =>
  let hcard : Fintype.card (NonzeroResidue (q i)) = Fintype.card ↥(R i).val := by
    rw [card_nonzeroResidue, Fintype.card_coe, (R i).property]
  let e : NonzeroResidue (q i) ≃ ↥(R i).val :=
    Classical.choice (Fintype.card_eq.mp hcard)
  e.toEmbedding |>.trans
    (Function.Embedding.subtype fun s : Pool i => s ∈ (R i).val) |>.trans
    (poolSupport i)

/-- The assignment range is exactly the image of the chosen pool range. -/
@[simp] theorem assignmentForSparseRanges_range
    [(i : Fin m) → NeZero (q i)]
    (poolSupport : (i : Fin m) → Pool i ↪ Finset (Fin i.val))
    (R : SparseRangeProfile q Pool) (i : Fin m) :
    assignmentRange q (assignmentForSparseRanges q Pool poolSupport R) i =
      (R i).val.image (poolSupport i) := by
  classical
  apply Finset.ext
  intro s
  simp only [assignmentRange, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    let hcard : Fintype.card (NonzeroResidue (q i)) = Fintype.card ↥(R i).val := by
      rw [card_nonzeroResidue, Fintype.card_coe, (R i).property]
    let e : NonzeroResidue (q i) ≃ ↥(R i).val :=
      Classical.choice (Fintype.card_eq.mp hcard)
    refine ⟨e a, (e a).property, ?_⟩
    rfl
  · rintro ⟨r, hr, rfl⟩
    let hcard : Fintype.card (NonzeroResidue (q i)) = Fintype.card ↥(R i).val := by
      rw [card_nonzeroResidue, Fintype.card_coe, (R i).property]
    let e : NonzeroResidue (q i) ≃ ↥(R i).val :=
      Classical.choice (Fintype.card_eq.mp hcard)
    refine ⟨e.symm ⟨r, hr⟩, ?_⟩
    change (poolSupport i) (e (e.symm ⟨r, hr⟩)).val = (poolSupport i) r
    rw [e.apply_symm_apply]

/-- Optional ambient ranges are just images of ordinary assignment ranges. -/
theorem optionalEmbeddedAssignmentRange_eq_image
    [(i : Fin m) → NeZero (q i)]
    (A : FrameAssignment q) (i : Fin m) :
    optionalEmbeddedAssignmentRange q A i =
      (assignmentRange q A i).image
        (Finset.map ((earlierEmbedding i).trans Function.Embedding.some)) := by
  classical
  simp [optionalEmbeddedAssignmentRange, assignmentRange, Finset.image_image,
    Function.comp_def]

/-- Distinct range profiles produce distinct unordered sparse systems.  The
proof uses only modulus supports: at each coordinate the supports having that
coordinate as their greatest base coordinate recover its complete range. -/
theorem sparseSystemForRanges_injective
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i) (hP : 2 ≤ P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (closingFixed : ZMod P → Finset (Fin m))
    (poolSupport : (i : Fin m) → Pool i ↪ Finset (Fin i.val)) :
    Function.Injective (fun R : SparseRangeProfile q Pool =>
      sparseAssignmentSystem q P hq hP hcop closingFixed
        (assignmentForSparseRanges q Pool poolSupport R)) := by
  classical
  intro R T hsys
  have hsupp := sparseSupportFamily_eq_of_system_eq q P hq hP hcop closingFixed
    (assignmentForSparseRanges q Pool poolSupport R)
    (assignmentForSparseRanges q Pool poolSupport T) hsys
  funext i
  apply Subtype.ext
  have hrecover := congrArg (recoverSparseRange i) hsupp
  rw [recoverSparseRange_assignment q P closingFixed,
      recoverSparseRange_assignment q P closingFixed,
      optionalEmbeddedAssignmentRange_eq_image,
      optionalEmbeddedAssignmentRange_eq_image] at hrecover
  have hranges :
      assignmentRange q (assignmentForSparseRanges q Pool poolSupport R) i =
        assignmentRange q (assignmentForSparseRanges q Pool poolSupport T) i :=
    Finset.image_injective
      (Finset.map_injective ((earlierEmbedding i).trans Function.Embedding.some))
      hrecover
  rw [assignmentForSparseRanges_range, assignmentForSparseRanges_range] at hranges
  exact Finset.image_injective (poolSupport i).injective hranges

/-- Number of range profiles: a product of binomial coefficients. -/
theorem card_sparseRangeProfile
    [(i : Fin m) → NeZero (q i)] :
    Fintype.card (SparseRangeProfile q Pool) =
      ∏ i : Fin m, (Fintype.card (Pool i)).choose (q i - 1) := by
  classical
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact Fintype.card_finset_len (α := Pool i) (q i - 1)

/-- Every sparse range system whose moduli are bounded by `X` is counted by
`coveringCount X`. -/
theorem sparseSystemForRanges_mem_counted
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i) (hP : 2 ≤ P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (closingFixed : ZMod P → Finset (Fin m))
    (escape : Fin m → ZMod P)
    (hprotect : ClosingProtects (ZMod P) closingFixed escape)
    (hclosing : Function.Injective closingFixed)
    (poolSupport : (i : Fin m) → Pool i ↪ Finset (Fin i.val))
    (X : ℕ)
    (hbound : ∀ R : SparseRangeProfile q Pool,
      ∀ c ∈ sparseAssignmentSystem q P hq hP hcop closingFixed
        (assignmentForSparseRanges q Pool poolSupport R), c.1 ≤ X)
    (R : SparseRangeProfile q Pool) :
    sparseAssignmentSystem q P hq hP hcop closingFixed
        (assignmentForSparseRanges q Pool poolSupport R) ∈
      MinimalDistinctCoveringSystemsUpTo X := by
  classical
  have hmin := sparseAssignmentSystem_isMinimal q P hq hP hcop closingFixed
    escape hprotect hclosing (assignmentForSparseRanges q Pool poolSupport R)
  rw [MinimalDistinctCoveringSystemsUpTo, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, hmin⟩
  intro c hc
  rw [mem_classesUpTo_iff]
  have hvalid := hmin.1 c hc
  exact ⟨hvalid.1, hbound R c hc, hvalid.2⟩

/-- Generic simultaneous range-counting theorem. -/
theorem sparseRangeProfile_card_le_coveringCount
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i) (hP : 2 ≤ P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (closingFixed : ZMod P → Finset (Fin m))
    (escape : Fin m → ZMod P)
    (hprotect : ClosingProtects (ZMod P) closingFixed escape)
    (hclosing : Function.Injective closingFixed)
    (poolSupport : (i : Fin m) → Pool i ↪ Finset (Fin i.val))
    (X : ℕ)
    (hbound : ∀ R : SparseRangeProfile q Pool,
      ∀ c ∈ sparseAssignmentSystem q P hq hP hcop closingFixed
        (assignmentForSparseRanges q Pool poolSupport R), c.1 ≤ X) :
    (∏ i : Fin m, (Fintype.card (Pool i)).choose (q i - 1)) ≤
      coveringCount X := by
  classical
  let counted := MinimalDistinctCoveringSystemsUpTo X
  let f : SparseRangeProfile q Pool → ↥counted := fun R =>
    ⟨sparseAssignmentSystem q P hq hP hcop closingFixed
        (assignmentForSparseRanges q Pool poolSupport R),
      sparseSystemForRanges_mem_counted q P Pool hq hP hcop closingFixed
        escape hprotect hclosing poolSupport X hbound R⟩
  have hfinj : Function.Injective f := by
    intro R T h
    apply sparseSystemForRanges_injective q P Pool hq hP hcop closingFixed poolSupport
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hfinj
  rw [card_sparseRangeProfile q Pool] at hcard
  simpa [coveringCount, counted] using hcard

end Erdos1188

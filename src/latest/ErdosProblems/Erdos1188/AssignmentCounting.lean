import ErdosProblems.Erdos1188.Assignments

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Recovering assignment ranges and counting arithmetic frames
-/

namespace Erdos1188

open scoped BigOperators

variable {n : ℕ} (q : Fin n → ℕ)

noncomputable def assignmentSystem
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (A : FrameAssignment q) : Finset CongruenceClass :=
  Finset.univ.image
    (arithmeticFrameClass q (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i))
      hcop (assignedFixed q A))

noncomputable def assignmentSupportFamily
    [(i : Fin n) → NeZero (q i)]
    (A : FrameAssignment q) : Finset (Finset (Fin n)) :=
  Finset.univ.image (fullFrameSupport q (assignedFixed q A))

def supportProduct (J : Finset (Fin n)) : ℕ := ∏ j ∈ J, q j

@[simp] theorem arithmeticFrameClass_modulus
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (A : FrameAssignment q)
    (m : Option (FrameChoice (fun i => ZMod (q i)))) :
    (arithmeticFrameClass q (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i))
      hcop (assignedFixed q A) m).1 =
      supportProduct q (fullFrameSupport q (assignedFixed q A) m) := by
  cases m <;>
    simp [arithmeticFrameClass, fullFrameSupport, supportProduct, subsetCrtClass,
      subsetModulus_eq_prod]

/-- The set of moduli of an assignment system is exactly the set of products
of its frame supports. -/
theorem assignmentSystem_moduli
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (A : FrameAssignment q) :
    (assignmentSystem q hq hcop A).image Prod.fst =
      (assignmentSupportFamily q A).image (supportProduct q) := by
  classical
  simp only [assignmentSystem, assignmentSupportFamily, Finset.image_image]
  apply Finset.image_congr
  intro m _
  exact arithmeticFrameClass_modulus q hq hcop A m

/-- Equality of assignment systems forces equality of their support families. -/
theorem supportFamily_eq_of_system_eq
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (A B : FrameAssignment q)
    (hsys : assignmentSystem q hq hcop A = assignmentSystem q hq hcop B) :
    assignmentSupportFamily q A = assignmentSupportFamily q B := by
  have hm := congrArg (fun S : Finset CongruenceClass => S.image Prod.fst) hsys
  rw [assignmentSystem_moduli q hq hcop A,
      assignmentSystem_moduli q hq hcop B] at hm
  exact Finset.image_injective (coprime_subsetProduct_injective q hq hcop) hm

theorem earlierEmbedding_ne_self (i : Fin n) (j : Fin i.val) :
    earlierEmbedding i j ≠ i := by
  intro h
  exact (ne_of_lt j.isLt) (congrArg Fin.val h)

/-- In fact the unordered arithmetic system determines the entire assignment,
not merely the range at a greatest coordinate. -/
theorem assignment_eq_of_system_eq
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (A B : FrameAssignment q)
    (hsys : assignmentSystem q hq hcop A = assignmentSystem q hq hcop B) :
    A = B := by
  classical
  funext i
  apply Function.Embedding.ext
  intro a
  let c : FrameChoice (fun j => ZMod (q j)) := ⟨i, a.val, a.property⟩
  let clsA := arithmeticFrameClass q
    (fun j => lt_of_lt_of_le Nat.zero_lt_two (hq j)) hcop (assignedFixed q A)
  let clsB := arithmeticFrameClass q
    (fun j => lt_of_lt_of_le Nat.zero_lt_two (hq j)) hcop (assignedFixed q B)
  have hcA : clsA (some c) ∈ assignmentSystem q hq hcop A := by
    rw [assignmentSystem, Finset.mem_image]
    exact ⟨some c, Finset.mem_univ _, rfl⟩
  rw [hsys] at hcA
  rw [assignmentSystem, Finset.mem_image] at hcA
  obtain ⟨m, _, hmclass⟩ := hcA
  let e := crtFinEquiv q (fun j => lt_of_lt_of_le Nat.zero_lt_two (hq j)) hcop
  let r := e.symm (frameSpike (fun j => ZMod (q j)) c)
  have hmemA : FullFrameMember (fun j => ZMod (q j)) (assignedFixed q A)
      (some c) (e r) := by
    change FrameMember (fun j => ZMod (q j)) (assignedFixed q A) c (e r)
    rw [show e r = frameSpike (fun j => ZMod (q j)) c by
      exact Equiv.apply_symm_apply e _]
    exact frameSpike_mem (fun j => ZMod (q j)) (assignedFixed q A)
      (assignedFixed_fixesEarlier q A) c
  have hsatA : Satisfies (r.val : ℤ) (clsA (some c)) :=
    (fullFrameMember_iff_satisfies_arithmeticFrameClass q hq hcop
      (assignedFixed q A) (assignedFixed_fixesEarlier q A) (some c) r).mp hmemA
  have hsatB : Satisfies (r.val : ℤ) (clsB m) := by
    change Satisfies (r.val : ℤ)
      (arithmeticFrameClass q
        (fun j => lt_of_lt_of_le Nat.zero_lt_two (hq j)) hcop
        (assignedFixed q B) m)
    rw [hmclass]
    simpa [clsA] using hsatA
  have hmemB :=
    (fullFrameMember_iff_satisfies_arithmeticFrameClass q hq hcop
      (assignedFixed q B) (assignedFixed_fixesEarlier q B) m r).mpr hsatB
  have hm : m = some c := by
    apply (fullFrame_private (fun j => ZMod (q j)) (assignedFixed q B)
      (assignedFixed_fixesEarlier q B) (some c)).2 m
    simpa [r, e, fullFrameWitness] using hmemB
  subst m
  have hmods := congrArg Prod.fst hmclass
  have hsupports : fullFrameSupport q (assignedFixed q B) (some c) =
      fullFrameSupport q (assignedFixed q A) (some c) := by
    apply coprime_subsetProduct_injective q hq hcop
    change (arithmeticFrameClass q
      (fun j => lt_of_lt_of_le Nat.zero_lt_two (hq j)) hcop
      (assignedFixed q B) (some c)).1 =
      (arithmeticFrameClass q
        (fun j => lt_of_lt_of_le Nat.zero_lt_two (hq j)) hcop
        (assignedFixed q A) (some c)).1 at hmods
    rw [arithmeticFrameClass_modulus q hq hcop B (some c),
      arithmeticFrameClass_modulus q hq hcop A (some c)] at hmods
    exact hmods
  have hnotA : c.index ∉ assignedFixed q A c := by
    intro h
    exact (lt_irrefl _) (assignedFixed_fixesEarlier q A c c.index h)
  have hnotB : c.index ∉ assignedFixed q B c := by
    intro h
    exact (lt_irrefl _) (assignedFixed_fixesEarlier q B c c.index h)
  have hfixed : assignedFixed q B c = assignedFixed q A c := by
    have h := congrArg (fun s : Finset (Fin n) => s.erase c.index) hsupports
    simpa [fullFrameSupport, frameSupport, hnotA, hnotB] using h
  change A i a = B i a
  apply Finset.map_injective (earlierEmbedding i)
  simpa [assignedFixed, c] using hfixed.symm

/-- The raw range of subsets assigned to nonzero values in one coordinate. -/
noncomputable def assignmentRange [(i : Fin n) → NeZero (q i)]
    (A : FrameAssignment q) (i : Fin n) : Finset (Finset (Fin i.val)) :=
  Finset.univ.image (A i)

/-- The same range, embedded into the ambient coordinate type. -/
noncomputable def embeddedAssignmentRange [(i : Fin n) → NeZero (q i)]
    (A : FrameAssignment q) (i : Fin n) : Finset (Finset (Fin n)) :=
  Finset.univ.image (fun a : NonzeroResidue (q i) =>
    (A i a).map (earlierEmbedding i))

/-- From a support family, retain proper supports containing `top` and erase
`top`. At a greatest coordinate this recovers exactly its assignment range. -/
def recoverEmbeddedRange (top : Fin n) (supports : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  (supports.filter fun J => top ∈ J ∧ J ≠ Finset.univ).image
    (fun J => J.erase top)

theorem recoverEmbeddedRange_assignment
    [(i : Fin n) → NeZero (q i)]
    (A : FrameAssignment q) (top : Fin n)
    (htop : ∀ i : Fin n, i ≤ top)
    (hproper : ∀ c, frameSupport q (assignedFixed q A) c ≠ Finset.univ) :
    recoverEmbeddedRange top (assignmentSupportFamily q A) =
      embeddedAssignmentRange q A top := by
  classical
  apply Finset.ext
  intro K
  constructor
  · intro hK
    rw [recoverEmbeddedRange, Finset.mem_image] at hK
    obtain ⟨J, hJfilter, rfl⟩ := hK
    have hJfamily := (Finset.mem_filter.mp hJfilter).1
    have htopJ := (Finset.mem_filter.mp hJfilter).2.1
    rw [assignmentSupportFamily, Finset.mem_image] at hJfamily
    obtain ⟨m, _, rfl⟩ := hJfamily
    cases m with
    | none =>
        exact False.elim ((Finset.mem_filter.mp hJfilter).2.2 rfl)
    | some c =>
        have hindex : c.index = top := by
          rcases Finset.mem_insert.mp htopJ with heq | hmem
          · exact heq.symm
          · have hlt := assignedFixed_fixesEarlier q A c top hmem
            exact le_antisymm (htop c.index) (le_of_not_gt (fun h => (not_lt_of_ge (htop c.index)) hlt))
        cases c with
        | mk ci cv hcv =>
            simp only at hindex
            subst ci
            rw [embeddedAssignmentRange, Finset.mem_image]
            refine ⟨⟨cv, hcv⟩, Finset.mem_univ _, ?_⟩
            simp only [fullFrameSupport, frameSupport, assignedFixed]
            apply Eq.symm
            apply Finset.erase_insert
            intro hmem
            rw [Finset.mem_map] at hmem
            obtain ⟨k, _, hk⟩ := hmem
            exact earlierEmbedding_ne_self top k hk
  · intro hK
    rw [embeddedAssignmentRange, Finset.mem_image] at hK
    obtain ⟨a, _, rfl⟩ := hK
    rw [recoverEmbeddedRange, Finset.mem_image]
    let c : FrameChoice (fun i => ZMod (q i)) := ⟨top, a.1, a.2⟩
    let J := frameSupport q (assignedFixed q A) c
    refine ⟨J, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [assignmentSupportFamily, Finset.mem_image]
        exact ⟨some c, Finset.mem_univ _, rfl⟩
      · exact ⟨Finset.mem_insert_self _ _, hproper c⟩
    · simp only [J, c, frameSupport, assignedFixed]
      apply Finset.erase_insert
      intro hmem
      rw [Finset.mem_map] at hmem
      obtain ⟨k, _, hk⟩ := hmem
      exact earlierEmbedding_ne_self top k hk

/-- Consequently, equality of assignment systems forces equality of the ranges
used at any greatest coordinate. -/
theorem assignmentRange_eq_of_system_eq
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (A B : FrameAssignment q) (top : Fin n)
    (htop : ∀ i : Fin n, i ≤ top)
    (hproperA : ∀ c, frameSupport q (assignedFixed q A) c ≠ Finset.univ)
    (hproperB : ∀ c, frameSupport q (assignedFixed q B) c ≠ Finset.univ)
    (hsys : assignmentSystem q hq hcop A = assignmentSystem q hq hcop B) :
    assignmentRange q A top = assignmentRange q B top := by
  have hsupp := supportFamily_eq_of_system_eq q hq hcop A B hsys
  have hemb : embeddedAssignmentRange q A top = embeddedAssignmentRange q B top := by
    rw [← recoverEmbeddedRange_assignment q A top htop hproperA,
        ← recoverEmbeddedRange_assignment q B top htop hproperB, hsupp]
  apply Finset.image_injective (Finset.map_injective (earlierEmbedding top))
  simpa only [assignmentRange, Finset.image_image]

/-- An injective assignment of every nonzero top residue to a proper earlier
subset. -/
abbrev TopEmbedding [(i : Fin n) → NeZero (q i)] (top : Fin n) :=
  NonzeroResidue (q top) ↪ ProperEarlierSubsets top

noncomputable def assignmentForTopEmbedding
    [(i : Fin n) → NeZero (q i)]
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (E : TopEmbedding q top) : FrameAssignment q :=
  let base := Classical.choice (frameAssignment_nonempty q hcap)
  fun i => if h : i = top then
    h ▸ E.trans (Function.Embedding.subtype
      fun s : Finset (Fin top.val) => s ≠ Finset.univ)
  else base i

@[simp] theorem assignmentForTopEmbedding_top
    [(i : Fin n) → NeZero (q i)]
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (E : TopEmbedding q top) (a : NonzeroResidue (q top)) :
    assignmentForTopEmbedding q top hcap E top a = (E a).val := by
  simp [assignmentForTopEmbedding]

theorem assignmentForTopEmbedding_avoids
    [(i : Fin n) → NeZero (q i)]
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (E : TopEmbedding q top) :
    ∀ a, assignmentForTopEmbedding q top hcap E top a ≠ Finset.univ := by
  intro a
  rw [assignmentForTopEmbedding_top]
  exact (E a).property

theorem assignmentForTopEmbedding_injective
    [(i : Fin n) → NeZero (q i)]
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val) :
    Function.Injective (assignmentForTopEmbedding q top hcap) := by
  intro E F h
  apply Function.Embedding.ext
  intro a
  apply Subtype.ext
  have ha := congrArg (fun A : FrameAssignment q => A top a) h
  simpa using ha

noncomputable def systemForTopEmbedding
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (E : TopEmbedding q top) : Finset CongruenceClass :=
  assignmentSystem q hq hcop (assignmentForTopEmbedding q top hcap E)

theorem systemForTopEmbedding_injective
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val) :
    Function.Injective (systemForTopEmbedding q hq hcop top hcap) := by
  intro E F hsys
  apply assignmentForTopEmbedding_injective q top hcap
  exact assignment_eq_of_system_eq q hq hcop
    (assignmentForTopEmbedding q top hcap E)
    (assignmentForTopEmbedding q top hcap F) hsys

/-- Every embedding-parameter system is minimal when `top` is greatest. -/
theorem systemForTopEmbedding_isMinimal
    [(i : Fin n) → NeZero (q i)]
    (hn : 0 < n)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (htop : ∀ i : Fin n, i ≤ top)
    (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (E : TopEmbedding q top) :
    IsMinimalDistinctCoveringSystem
      (systemForTopEmbedding q hq hcop top hcap E) := by
  let A := assignmentForTopEmbedding q top hcap E
  have hproper : ∀ c, frameSupport q (assignedFixed q A) c ≠ Finset.univ :=
    assignedFrameSupport_proper_of_avoiding q A top htop
      (assignmentForTopEmbedding_avoids q top hcap E)
  unfold systemForTopEmbedding assignmentSystem
  exact arithmeticFrame_isMinimalDistinct_of_support q hn hq hcop
    (assignedFixed q A) (assignedFixed_fixesEarlier q A)
    (assignedFullFrameSupport_injective q A hproper)

/-- A choice of exactly `q top - 1` proper earlier-coordinate subsets. -/
abbrev TopRangeChoice [(i : Fin n) → NeZero (q i)] (top : Fin n) :=
  {R : Finset (ProperEarlierSubsets top) // R.card = q top - 1}

/-- The number of possible top ranges is the corresponding binomial
coefficient. -/
theorem card_topRangeChoice
    [(i : Fin n) → NeZero (q i)] (top : Fin n) :
    Fintype.card (TopRangeChoice q top) =
      (2 ^ top.val - 1).choose (q top - 1) := by
  rw [Fintype.card_finset_len, card_properEarlierSubsets]

/-- Every prescribed top range of the right size extends to a full assignment,
provided the ordinary subset capacities hold at all coordinates. -/
theorem exists_assignment_with_topRange
    [(i : Fin n) → NeZero (q i)]
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (R : TopRangeChoice q top) :
    ∃ A : FrameAssignment q,
      assignmentRange q A top = R.val.image Subtype.val ∧
      (∀ a, A top a ≠ Finset.univ) := by
  classical
  let base : FrameAssignment q := Classical.choice (frameAssignment_nonempty q hcap)
  have hcard : Fintype.card (NonzeroResidue (q top)) = Fintype.card ↥R.val := by
    rw [card_nonzeroResidue, Fintype.card_coe, R.property]
  let e : NonzeroResidue (q top) ≃ ↥R.val := Classical.choice (Fintype.card_eq.mp hcard)
  let etop : NonzeroResidue (q top) ↪ Finset (Fin top.val) :=
    e.toEmbedding |>.trans (Function.Embedding.subtype fun s : ProperEarlierSubsets top => s ∈ R.val) |>.trans
      (Function.Embedding.subtype fun s : Finset (Fin top.val) => s ≠ Finset.univ)
  let A : FrameAssignment q := fun i =>
    if h : i = top then h ▸ etop else base i
  refine ⟨A, ?_, ?_⟩
  · apply Finset.ext
    intro s
    simp only [assignmentRange, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      simp only [A, dif_pos rfl, etop, Function.Embedding.trans_apply,
        Function.Embedding.subtype_apply, Equiv.toEmbedding_apply]
      exact ⟨e a, (e a).property, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      let a := e.symm ⟨r, hr⟩
      refine ⟨a, ?_⟩
      simp [A, etop, a]
  · intro a
    simp only [A, dif_pos rfl, etop, Function.Embedding.trans_apply,
      Function.Embedding.subtype_apply, Equiv.toEmbedding_apply]
    exact (e a).val.property

noncomputable def assignmentForTopRange
    [(i : Fin n) → NeZero (q i)]
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (R : TopRangeChoice q top) : FrameAssignment q :=
  Classical.choose (exists_assignment_with_topRange q top hcap R)

@[simp] theorem assignmentForTopRange_range
    [(i : Fin n) → NeZero (q i)]
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (R : TopRangeChoice q top) :
    assignmentRange q (assignmentForTopRange q top hcap R) top =
      R.val.image Subtype.val :=
  (Classical.choose_spec (exists_assignment_with_topRange q top hcap R)).1

theorem assignmentForTopRange_avoids
    [(i : Fin n) → NeZero (q i)]
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (R : TopRangeChoice q top) :
    ∀ a, assignmentForTopRange q top hcap R top a ≠ Finset.univ :=
  (Classical.choose_spec (exists_assignment_with_topRange q top hcap R)).2

noncomputable def systemForTopRange
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (R : TopRangeChoice q top) : Finset CongruenceClass :=
  assignmentSystem q hq hcop (assignmentForTopRange q top hcap R)

/-- Distinct prescribed ranges give distinct covering systems. -/
theorem systemForTopRange_injective
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (htop : ∀ i : Fin n, i ≤ top)
    (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val) :
    Function.Injective (systemForTopRange q hq hcop top hcap) := by
  intro R T hsys
  let A := assignmentForTopRange q top hcap R
  let B := assignmentForTopRange q top hcap T
  have hproperA : ∀ c, frameSupport q (assignedFixed q A) c ≠ Finset.univ :=
    assignedFrameSupport_proper_of_avoiding q A top htop
      (assignmentForTopRange_avoids q top hcap R)
  have hproperB : ∀ c, frameSupport q (assignedFixed q B) c ≠ Finset.univ :=
    assignedFrameSupport_proper_of_avoiding q B top htop
      (assignmentForTopRange_avoids q top hcap T)
  have hrange := assignmentRange_eq_of_system_eq q hq hcop A B top htop
    hproperA hproperB hsys
  rw [assignmentForTopRange_range, assignmentForTopRange_range] at hrange
  have hRT : R.val = T.val :=
    Finset.image_injective Subtype.val_injective hrange
  exact Subtype.ext hRT

/-- Every range-parameter system is a minimal distinct covering system. -/
theorem systemForTopRange_isMinimal
    [(i : Fin n) → NeZero (q i)]
    (hn : 0 < n)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (htop : ∀ i : Fin n, i ≤ top)
    (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (R : TopRangeChoice q top) :
    IsMinimalDistinctCoveringSystem
      (systemForTopRange q hq hcop top hcap R) := by
  let A := assignmentForTopRange q top hcap R
  have hproper : ∀ c, frameSupport q (assignedFixed q A) c ≠ Finset.univ :=
    assignedFrameSupport_proper_of_avoiding q A top htop
      (assignmentForTopRange_avoids q top hcap R)
  unfold systemForTopRange assignmentSystem
  exact arithmeticFrame_isMinimalDistinct_of_support q hn hq hcop
    (assignedFixed q A) (assignedFixed_fixesEarlier q A)
    (assignedFullFrameSupport_injective q A hproper)

theorem mem_classesUpTo_iff (x : ℕ) (c : CongruenceClass) :
    c ∈ ClassesUpTo x ↔ 2 ≤ c.1 ∧ c.1 ≤ x ∧ c.2 < c.1 := by
  rcases c with ⟨m, a⟩
  simp [ClassesUpTo, and_assoc]

/-- Every modulus in an assignment system divides the full CRT period. -/
theorem assignmentSystem_modulus_dvd
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (A : FrameAssignment q) {c : CongruenceClass}
    (hc : c ∈ assignmentSystem q hq hcop A) :
    c.1 ∣ ∏ i, q i := by
  classical
  rw [assignmentSystem, Finset.mem_image] at hc
  obtain ⟨m, _, rfl⟩ := hc
  rw [arithmeticFrameClass_modulus q hq hcop A m]
  unfold supportProduct
  rw [← subsetModulus_eq_prod]
  exact subsetModulus_dvd_full q _

/-- Each parameterized system belongs to the finite collection counted at the
full CRT period. -/
theorem systemForTopRange_mem_counted
    [(i : Fin n) → NeZero (q i)]
    (hn : 0 < n)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (htop : ∀ i : Fin n, i ≤ top)
    (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (R : TopRangeChoice q top) :
    systemForTopRange q hq hcop top hcap R ∈
      MinimalDistinctCoveringSystemsUpTo (∏ i, q i) := by
  classical
  have hmin := systemForTopRange_isMinimal q hn hq hcop top htop hcap R
  rw [MinimalDistinctCoveringSystemsUpTo, Finset.mem_filter,
    Finset.mem_powerset]
  refine ⟨?_, hmin⟩
  intro c hc
  rw [mem_classesUpTo_iff]
  have hvalid := hmin.1 c hc
  refine ⟨hvalid.1, ?_, hvalid.2⟩
  exact Nat.le_of_dvd (Finset.prod_pos fun i _ => lt_of_lt_of_le Nat.zero_lt_two (hq i))
    (assignmentSystem_modulus_dvd q hq hcop
      (assignmentForTopRange q top hcap R) hc)

/-- The counting function is monotone in the modulus cutoff. -/
theorem coveringCount_mono : Monotone coveringCount := by
  classical
  intro x y hxy
  unfold coveringCount
  apply Finset.card_le_card
  intro S hS
  rw [MinimalDistinctCoveringSystemsUpTo, Finset.mem_filter,
    Finset.mem_powerset] at hS ⊢
  refine ⟨?_, hS.2⟩
  intro c hc
  have hcx := hS.1 hc
  rw [mem_classesUpTo_iff] at hcx ⊢
  exact ⟨hcx.1, le_trans hcx.2.1 hxy, hcx.2.2⟩

/-- The number of top embeddings is a descending factorial. -/
theorem card_topEmbedding
    [(i : Fin n) → NeZero (q i)] (top : Fin n) :
    Fintype.card (TopEmbedding q top) =
      (2 ^ top.val - 1).descFactorial (q top - 1) := by
  rw [Fintype.card_embedding_eq, card_properEarlierSubsets,
    card_nonzeroResidue]

/-- Each embedding-parameter system is counted at the full CRT period. -/
theorem systemForTopEmbedding_mem_counted
    [(i : Fin n) → NeZero (q i)]
    (hn : 0 < n)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (htop : ∀ i : Fin n, i ≤ top)
    (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val)
    (E : TopEmbedding q top) :
    systemForTopEmbedding q hq hcop top hcap E ∈
      MinimalDistinctCoveringSystemsUpTo (∏ i, q i) := by
  classical
  have hmin := systemForTopEmbedding_isMinimal q hn hq hcop top htop hcap E
  rw [MinimalDistinctCoveringSystemsUpTo, Finset.mem_filter,
    Finset.mem_powerset]
  refine ⟨?_, hmin⟩
  intro c hc
  rw [mem_classesUpTo_iff]
  have hvalid := hmin.1 c hc
  refine ⟨hvalid.1, ?_, hvalid.2⟩
  exact Nat.le_of_dvd (Finset.prod_pos fun i _ => lt_of_lt_of_le Nat.zero_lt_two (hq i))
    (assignmentSystem_modulus_dvd q hq hcop
      (assignmentForTopEmbedding q top hcap E) hc)

/-- Strong finite count using all injective assignments, not only their ranges. -/
theorem descFactorial_le_coveringCount
    [(i : Fin n) → NeZero (q i)]
    (hn : 0 < n)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (htop : ∀ i : Fin n, i ≤ top)
    (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val) :
    (2 ^ top.val - 1).descFactorial (q top - 1) ≤
      coveringCount (∏ i, q i) := by
  classical
  let counted := MinimalDistinctCoveringSystemsUpTo (∏ i, q i)
  let f : TopEmbedding q top → ↥counted := fun E =>
    ⟨systemForTopEmbedding q hq hcop top hcap E,
      systemForTopEmbedding_mem_counted q hn hq hcop top htop hcap E⟩
  have hfinj : Function.Injective f := by
    intro E F h
    apply systemForTopEmbedding_injective q hq hcop top hcap
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hfinj
  rw [card_topEmbedding q top] at hcard
  simpa [coveringCount, counted] using hcard

/-- Finite counting theorem: the full period admits at least one distinct
minimal system for every possible top assignment range. -/
theorem choose_le_coveringCount
    [(i : Fin n) → NeZero (q i)]
    (hn : 0 < n)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (top : Fin n) (htop : ∀ i : Fin n, i ≤ top)
    (hcap : ∀ i, q i - 1 ≤ 2 ^ i.val) :
    (2 ^ top.val - 1).choose (q top - 1) ≤ coveringCount (∏ i, q i) := by
  classical
  let counted := MinimalDistinctCoveringSystemsUpTo (∏ i, q i)
  let f : TopRangeChoice q top → ↥counted := fun R =>
    ⟨systemForTopRange q hq hcop top hcap R,
      systemForTopRange_mem_counted q hn hq hcop top htop hcap R⟩
  have hfinj : Function.Injective f := by
    intro R T h
    apply systemForTopRange_injective q hq hcop top htop hcap
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hfinj
  rw [card_topRangeChoice q top] at hcard
  simpa [coveringCount, counted] using hcard

end Erdos1188

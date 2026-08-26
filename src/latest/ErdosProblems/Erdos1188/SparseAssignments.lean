import ErdosProblems.Erdos1188.SparseArithmetic
import ErdosProblems.Erdos1188.Assignments
import ErdosProblems.Erdos1188.AssignmentCounting

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Assignments and support-range recovery for sparse frames
-/

namespace Erdos1188

open scoped BigOperators

variable {m : ℕ} (q : Fin m → ℕ) (P : ℕ)

/-- The sparse arithmetic system built from a base frame assignment and a
fixed closing support map. -/
noncomputable def sparseAssignmentSystem
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i) (hP : 2 ≤ P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (closingFixed : ZMod P → Finset (Fin m))
    (A : FrameAssignment q) : Finset CongruenceClass :=
  Finset.univ.image
    (sparseArithmeticClass q P
      (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i))
      (lt_of_lt_of_le Nat.zero_lt_two hP) hcop
      (assignedFixed q A) closingFixed)

/-- The unlabeled family of all sparse supports. -/
noncomputable def sparseAssignmentSupportFamily
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (closingFixed : ZMod P → Finset (Fin m))
    (A : FrameAssignment q) : Finset (Finset (Option (Fin m))) :=
  Finset.univ.image (sparseFrameSupport q P (assignedFixed q A) closingFixed)

@[simp] theorem sparseArithmeticClass_modulus
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i) (hP : 2 ≤ P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (closingFixed : ZMod P → Finset (Fin m))
    (A : FrameAssignment q)
    (c : SparseFrameChoice (fun i => ZMod (q i)) (ZMod P)) :
    (sparseArithmeticClass q P
      (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i))
      (lt_of_lt_of_le Nat.zero_lt_two hP) hcop
      (assignedFixed q A) closingFixed c).1 =
      ∏ j ∈ sparseFrameSupport q P (assignedFixed q A) closingFixed c,
        sparseFactors q P j := by
  simp [sparseArithmeticClass, subsetCrtClass, subsetModulus_eq_prod]

/-- The modulus set is exactly the set of products of sparse supports. -/
theorem sparseAssignmentSystem_moduli
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i) (hP : 2 ≤ P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (closingFixed : ZMod P → Finset (Fin m))
    (A : FrameAssignment q) :
    (sparseAssignmentSystem q P hq hP hcop closingFixed A).image Prod.fst =
      (sparseAssignmentSupportFamily q P closingFixed A).image
        (fun J => ∏ j ∈ J, sparseFactors q P j) := by
  classical
  simp only [sparseAssignmentSystem, sparseAssignmentSupportFamily, Finset.image_image]
  apply Finset.image_congr
  intro c _
  exact sparseArithmeticClass_modulus q P hq hP hcop closingFixed A c

/-- Equality of sparse systems forces equality of their complete support
families. -/
theorem sparseSupportFamily_eq_of_system_eq
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i) (hP : 2 ≤ P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (closingFixed : ZMod P → Finset (Fin m))
    (A B : FrameAssignment q)
    (hsys : sparseAssignmentSystem q P hq hP hcop closingFixed A =
      sparseAssignmentSystem q P hq hP hcop closingFixed B) :
    sparseAssignmentSupportFamily q P closingFixed A =
      sparseAssignmentSupportFamily q P closingFixed B := by
  have hm := congrArg (fun S : Finset CongruenceClass => S.image Prod.fst) hsys
  rw [sparseAssignmentSystem_moduli q P hq hP hcop closingFixed A,
      sparseAssignmentSystem_moduli q P hq hP hcop closingFixed B] at hm
  exact Finset.image_injective
    (coprime_subsetProduct_injective (sparseFactors q P)
      (fun j => match j with | none => hP | some i => hq i) hcop) hm

/-- Under an injective closing support map protecting every coordinate, every
assignment gives a minimal distinct covering system. -/
theorem sparseAssignmentSystem_isMinimal
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i) (hP : 2 ≤ P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (closingFixed : ZMod P → Finset (Fin m))
    (escape : Fin m → ZMod P)
    (hprotect : ClosingProtects (ZMod P) closingFixed escape)
    (hclosing : Function.Injective closingFixed)
    (A : FrameAssignment q) :
    IsMinimalDistinctCoveringSystem
      (sparseAssignmentSystem q P hq hP hcop closingFixed A) := by
  unfold sparseAssignmentSystem
  apply sparseArithmeticFrame_isMinimalDistinct_of_support q P hq hP hcop
    (assignedFixed q A) closingFixed (assignedFixed_fixesEarlier q A)
    escape hprotect
  exact sparseFrameSupport_injective_of q P (assignedFixed q A) closingFixed
    (assignedFrameSupport_injective q A) hclosing

/-- Recover supports whose distinguished (largest) base coordinate is `i`.
Closing supports are discarded by the requirement `none ∉ J`. -/
def recoverSparseRange (i : Fin m)
    (supports : Finset (Finset (Option (Fin m)))) :
    Finset (Finset (Option (Fin m))) :=
  (supports.filter fun J =>
      none ∉ J ∧ some i ∈ J ∧ ∀ j ∈ J, ∃ k : Fin m, j = some k ∧ k ≤ i).image
    (fun J => J.erase (some i))

/-- The raw range at `i`, embedded into optional ambient coordinates. -/
noncomputable def optionalEmbeddedAssignmentRange
    [(i : Fin m) → NeZero (q i)]
    (A : FrameAssignment q) (i : Fin m) :
    Finset (Finset (Option (Fin m))) :=
  Finset.univ.image (fun a : NonzeroResidue (q i) =>
    (A i a).map ((earlierEmbedding i).trans Function.Embedding.some))

/-- Sparse support recovery exactly gives the assignment range at every base
coordinate. -/
theorem recoverSparseRange_assignment
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (closingFixed : ZMod P → Finset (Fin m))
    (A : FrameAssignment q) (i : Fin m) :
    recoverSparseRange i (sparseAssignmentSupportFamily q P closingFixed A) =
      optionalEmbeddedAssignmentRange q A i := by
  classical
  apply Finset.ext
  intro K
  constructor
  · intro hK
    rw [recoverSparseRange, Finset.mem_image] at hK
    obtain ⟨J, hJfilter, rfl⟩ := hK
    have hJfamily := (Finset.mem_filter.mp hJfilter).1
    obtain ⟨hnone, hiJ, hle⟩ := (Finset.mem_filter.mp hJfilter).2
    rw [sparseAssignmentSupportFamily, Finset.mem_image] at hJfamily
    obtain ⟨c, _, rfl⟩ := hJfamily
    cases c with
    | inr a =>
        exfalso
        apply hnone
        simp [sparseFrameSupport]
    | inl c =>
        have hindex : c.index = i := by
          have hcJ : some c.index ∈
              sparseFrameSupport q P (assignedFixed q A) closingFixed (Sum.inl c) := by
            simp [sparseFrameSupport, frameSupport]
          obtain ⟨k, hkEq, hkLe⟩ := hle (some c.index) hcJ
          simp only [Option.some.injEq] at hkEq
          subst k
          rcases Finset.mem_map.mp hiJ with ⟨u, hu, hui⟩
          have hui' : u = i := Option.some.inj hui
          rcases Finset.mem_insert.mp hu with huc | hufixed
          · simpa [huc] using hui'
          · have hlt := assignedFixed_fixesEarlier q A c u hufixed
            subst u
            exact False.elim ((not_lt_of_ge hkLe) hlt)
        cases c with
        | mk ci cv hcv =>
            simp only at hindex
            subst ci
            rw [optionalEmbeddedAssignmentRange, Finset.mem_image]
            refine ⟨⟨cv, hcv⟩, Finset.mem_univ _, ?_⟩
            simp only [sparseFrameSupport, frameSupport, assignedFixed]
            have hnot : some i ∉
                ((A i ⟨cv, hcv⟩).map (earlierEmbedding i)).map
                  Function.Embedding.some := by
              intro hm
              rw [Finset.mem_map] at hm
              obtain ⟨u, hu, hum⟩ := hm
              rw [Finset.mem_map] at hu
              obtain ⟨v, hv, hvu⟩ := hu
              have hui : u = i := Option.some.inj hum
              have : v.val = i.val := by
                have hvu' := congrArg Fin.val hvu
                simpa [hui, earlierEmbedding] using hvu'
              exact (ne_of_lt v.isLt) this
            rw [Finset.map_insert]
            have hkey : Function.Embedding.some i = some i := rfl
            rw [hkey, Finset.erase_insert hnot, Finset.map_map]
  · intro hK
    rw [optionalEmbeddedAssignmentRange, Finset.mem_image] at hK
    obtain ⟨a, _, rfl⟩ := hK
    rw [recoverSparseRange, Finset.mem_image]
    let c : FrameChoice (fun j => ZMod (q j)) := ⟨i, a.1, a.2⟩
    let J := sparseFrameSupport q P (assignedFixed q A) closingFixed (Sum.inl c)
    refine ⟨J, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [sparseAssignmentSupportFamily, Finset.mem_image]
        exact ⟨Sum.inl c, Finset.mem_univ _, rfl⟩
      · refine ⟨?_, ?_, ?_⟩
        · simp [J, sparseFrameSupport]
        · simp [J, c, sparseFrameSupport, frameSupport]
        · intro j hj
          simp only [J, sparseFrameSupport, Finset.mem_map] at hj
          obtain ⟨k, hk, rfl⟩ := hj
          refine ⟨k, rfl, ?_⟩
          rcases Finset.mem_insert.mp hk with hki | hkfixed
          · simpa [hki, c]
          · exact (assignedFixed_fixesEarlier q A c k hkfixed).le
    · simp only [J, c, sparseFrameSupport, frameSupport, assignedFixed]
      have hnot : some i ∉
          ((A i a).map (earlierEmbedding i)).map Function.Embedding.some := by
        intro hm
        rw [Finset.mem_map] at hm
        obtain ⟨u, hu, hum⟩ := hm
        rw [Finset.mem_map] at hu
        obtain ⟨v, hv, hvu⟩ := hu
        have hui : u = i := Option.some.inj hum
        have : v.val = i.val := by
          have hvu' := congrArg Fin.val hvu
          simpa [hui, earlierEmbedding] using hvu'
        exact (ne_of_lt v.isLt) this
      rw [Finset.map_insert]
      have hkey : Function.Embedding.some i = some i := rfl
      rw [hkey, Finset.erase_insert hnot, Finset.map_map]

end Erdos1188

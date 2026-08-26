import ErdosProblems.Erdos1188.SparseFrame
import ErdosProblems.Erdos1188.Transport
import ErdosProblems.Erdos1188.Squarefree
import ErdosProblems.Erdos1188.ArithmeticFrame
import ErdosProblems.Erdos1188.SupportInjective

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Arithmetic realization of sparse closed frames

We index the extra closing coordinate by `none` and the base coordinates by
`some i`.  This makes the dependent CRT product split definitionally into a
base point and one closing value.
-/

namespace Erdos1188

open scoped BigOperators

variable {m : ℕ} (q : Fin m → ℕ) (P : ℕ)

/-- Add a closing factor, indexed by `none`, to the base CRT factors. -/
def sparseFactors : Option (Fin m) → ℕ
  | none => P
  | some i => q i

@[simp] theorem sparseFactors_none : sparseFactors q P none = P := rfl
@[simp] theorem sparseFactors_some (i : Fin m) : sparseFactors q P (some i) = q i := rfl

/-- The CRT coordinate product is the base product paired with the closing
coordinate. -/
def sparseCoordinatesEquiv :
    ((j : Option (Fin m)) → ZMod (sparseFactors q P j)) ≃
      SparseFramePoint (fun i => ZMod (q i)) (ZMod P) :=
  Equiv.piOptionEquivProd.trans
    (Equiv.prodComm (ZMod P) ((i : Fin m) → ZMod (q i)))

@[simp] theorem sparseCoordinatesEquiv_apply_base
    (x : (j : Option (Fin m)) → ZMod (sparseFactors q P j)) (i : Fin m) :
    (sparseCoordinatesEquiv q P x).1 i = x (some i) := rfl

@[simp] theorem sparseCoordinatesEquiv_apply_closing
    (x : (j : Option (Fin m)) → ZMod (sparseFactors q P j)) :
    (sparseCoordinatesEquiv q P x).2 = x none := rfl

@[simp] theorem sparseCoordinatesEquiv_symm_base
    (x : SparseFramePoint (fun i => ZMod (q i)) (ZMod P)) (i : Fin m) :
    (sparseCoordinatesEquiv q P).symm x (some i) = x.1 i := by
  rfl

@[simp] theorem sparseCoordinatesEquiv_symm_closing
    (x : SparseFramePoint (fun i => ZMod (q i)) (ZMod P)) :
    (sparseCoordinatesEquiv q P).symm x none = x.2 := by
  rfl

/-- Support of a sparse member in the enlarged coordinate type. -/
def sparseFrameSupport
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin m))
    (closingFixed : ZMod P → Finset (Fin m))
    (c : SparseFrameChoice (fun i => ZMod (q i)) (ZMod P)) :
    Finset (Option (Fin m)) :=
  match c with
  | Sum.inl b => (frameSupport q fixed b).map Function.Embedding.some
  | Sum.inr a => insert none ((closingFixed a).map Function.Embedding.some)

/-- Base-support and closing-support injectivity together imply injectivity of
all sparse supports.  The two kinds cannot collide because precisely the
closing supports contain `none`. -/
theorem sparseFrameSupport_injective_of
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin m))
    (closingFixed : ZMod P → Finset (Fin m))
    (hbase : Function.Injective (frameSupport q fixed))
    (hclosing : Function.Injective closingFixed) :
    Function.Injective (sparseFrameSupport q P fixed closingFixed) := by
  classical
  intro a b hab
  cases a with
  | inl c =>
      cases b with
      | inl d =>
          apply congrArg Sum.inl
          apply hbase
          apply Finset.map_injective Function.Embedding.some
          simpa [sparseFrameSupport] using hab
      | inr d =>
          have hn : none ∉ sparseFrameSupport q P fixed closingFixed (Sum.inl c) := by
            simp [sparseFrameSupport]
          have hm : none ∈ sparseFrameSupport q P fixed closingFixed (Sum.inr d) := by
            simp [sparseFrameSupport]
          exact False.elim (hn (by simpa [hab] using hm))
  | inr c =>
      cases b with
      | inl d =>
          have hm : none ∈ sparseFrameSupport q P fixed closingFixed (Sum.inr c) := by
            simp [sparseFrameSupport]
          have hn : none ∉ sparseFrameSupport q P fixed closingFixed (Sum.inl d) := by
            simp [sparseFrameSupport]
          exact False.elim (hn (by simpa [← hab] using hm))
      | inr d =>
          apply congrArg Sum.inr
          apply hclosing
          have he := congrArg (fun s : Finset (Option (Fin m)) => s.erase none) hab
          apply Finset.map_injective Function.Embedding.some
          simpa [sparseFrameSupport] using he

/-- A canonical point whose restriction to the member support gives the
coordinate values defining that member. -/
def sparseSupportPoint
    (c : SparseFrameChoice (fun i => ZMod (q i)) (ZMod P)) :
    (j : Option (Fin m)) → ZMod (sparseFactors q P j) :=
  match c with
  | Sum.inl b => fun j => match j with
      | none => 0
      | some i => frameSpike (fun k => ZMod (q k)) b i
  | Sum.inr a => fun j => match j with
      | none => a
      | some _ => 0

/-- The congruence class represented by a sparse member. -/
noncomputable def sparseArithmeticClass
    (hqpos : ∀ i, 0 < q i) (hPpos : 0 < P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin m))
    (closingFixed : ZMod P → Finset (Fin m))
    (c : SparseFrameChoice (fun i => ZMod (q i)) (ZMod P)) :
    CongruenceClass :=
  subsetCrtClass (sparseFactors q P)
    (fun j => match j with | none => hPpos | some i => hqpos i) hcop
    (sparseFrameSupport q P fixed closingFixed c)
    (fun j => sparseSupportPoint q P c j)

/-- Sparse membership is exactly agreement with the canonical point on the
member's support. -/
theorem sparseFrameMember_iff_support
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin m))
    (closingFixed : ZMod P → Finset (Fin m))
    (hfixed : FrameFixesEarlier (fun i => ZMod (q i)) fixed)
    (c : SparseFrameChoice (fun i => ZMod (q i)) (ZMod P))
    (x : SparseFramePoint (fun i => ZMod (q i)) (ZMod P)) :
    SparseFrameMember (fun i => ZMod (q i)) (ZMod P) fixed closingFixed c x ↔
      ∀ j : ↥(sparseFrameSupport q P fixed closingFixed c),
        (sparseCoordinatesEquiv q P).symm x j = sparseSupportPoint q P c j := by
  classical
  cases c with
  | inl b =>
      change FrameMember (fun i => ZMod (q i)) fixed b x.1 ↔ _
      rw [frameMember_iff_support q fixed hfixed b x.1]
      constructor
      · intro h j
        have hjp := j.property
        simp only [sparseFrameSupport, Finset.mem_map] at hjp
        obtain ⟨k, hk, hkj⟩ := hjp
        have hj : j.val = some k := hkj.symm
        cases j with
        | mk j hjmem =>
            simp only at hj
            subst j
            simpa [sparseSupportPoint, frameSupportValues] using h ⟨k, hk⟩
      · intro h k
        have hkmap : some k.val ∈
            (frameSupport q fixed b).map Function.Embedding.some :=
          Finset.mem_map.mpr ⟨k, k.property, rfl⟩
        have hh := h ⟨some k.val, by simpa [sparseFrameSupport] using hkmap⟩
        simpa [sparseSupportPoint, frameSupportValues] using hh
  | inr a =>
      change (x.2 = a ∧ ∀ j ∈ closingFixed a, x.1 j = 0) ↔ _
      constructor
      · rintro ⟨htop, hzero⟩ j
        have hjmem : j.val ∈ insert none ((closingFixed a).map Function.Embedding.some) := by
          simpa [sparseFrameSupport] using j.property
        rcases Finset.mem_insert.mp hjmem with hjnone | hjsome
        · have hj : j.val = none := hjnone
          cases j with
          | mk j hjmem =>
              simp only at hj
              subst j
              simpa [sparseSupportPoint] using htop
        · rw [Finset.mem_map] at hjsome
          obtain ⟨k, hk, hkj⟩ := hjsome
          have hj : j.val = some k := hkj.symm
          cases j with
          | mk j hjmem =>
              simp only at hj
              subst j
              change x.1 k = (0 : ZMod (q k))
              exact hzero k hk
      · intro h
        constructor
        · have hnone : none ∈ sparseFrameSupport q P fixed closingFixed (Sum.inr a) := by
            simp [sparseFrameSupport]
          have hh := h ⟨none, hnone⟩
          simpa [sparseSupportPoint] using hh
        · intro k hk
          have hkmap : some k ∈ (closingFixed a).map Function.Embedding.some :=
            Finset.mem_map.mpr ⟨k, hk, rfl⟩
          have hsupp : some k ∈ sparseFrameSupport q P fixed closingFixed (Sum.inr a) := by
            simp [sparseFrameSupport, hkmap]
          have hh := h ⟨some k, hsupp⟩
          change x.1 k = (0 : ZMod (q k)) at hh
          exact hh

/-- Pointwise correspondence between sparse product members and CRT classes. -/
theorem sparseFrameMember_iff_satisfies
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i) (hP : 2 ≤ P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin m))
    (closingFixed : ZMod P → Finset (Fin m))
    (hfixed : FrameFixesEarlier (fun i => ZMod (q i)) fixed)
    (c : SparseFrameChoice (fun i => ZMod (q i)) (ZMod P))
    (r : Fin (∏ i, sparseFactors q P i)) :
    SparseFrameMember (fun i => ZMod (q i)) (ZMod P) fixed closingFixed c
      (sparseCoordinatesEquiv q P
        (crtFinEquiv (sparseFactors q P)
          (fun j => match j with
            | none => lt_of_lt_of_le Nat.zero_lt_two hP
            | some i => lt_of_lt_of_le Nat.zero_lt_two (hq i)) hcop r)) ↔
      Satisfies (r.val : ℤ)
        (sparseArithmeticClass q P
          (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i))
          (lt_of_lt_of_le Nat.zero_lt_two hP) hcop fixed closingFixed c) := by
  rw [sparseFrameMember_iff_support q P fixed closingFixed hfixed]
  simp only [Equiv.symm_apply_apply]
  unfold sparseArithmeticClass
  rw [satisfies_subsetCrtClass_iff]

/-- If sparse supports are injective, then their squarefree arithmetic
realization is a minimal distinct covering system. -/
theorem sparseArithmeticFrame_isMinimalDistinct_of_support
    [NeZero P] [(i : Fin m) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i) (hP : 2 ≤ P)
    (hcop : Pairwise (Function.onFun Nat.Coprime (sparseFactors q P)))
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin m))
    (closingFixed : ZMod P → Finset (Fin m))
    (hfixed : FrameFixesEarlier (fun i => ZMod (q i)) fixed)
    (escape : Fin m → ZMod P)
    (hprotect : ClosingProtects (ZMod P) closingFixed escape)
    (hsupport : Function.Injective (sparseFrameSupport q P fixed closingFixed)) :
    IsMinimalDistinctCoveringSystem
      (Finset.univ.image
        (sparseArithmeticClass q P
          (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i))
          (lt_of_lt_of_le Nat.zero_lt_two hP) hcop fixed closingFixed)) := by
  classical
  let Q := sparseFactors q P
  let hQpos : ∀ i, 0 < Q i := fun j => match j with
    | none => lt_of_lt_of_le Nat.zero_lt_two hP
    | some i => lt_of_lt_of_le Nat.zero_lt_two (hq i)
  let X := SparseFramePoint (fun i => ZMod (q i)) (ZMod P)
  let M := SparseFrameChoice (fun i => ZMod (q i)) (ZMod P)
  let member := SparseFrameMember (fun i => ZMod (q i)) (ZMod P) fixed closingFixed
  let witness := sparseFrameWitness (fun i => ZMod (q i)) (ZMod P) escape
  let e := (crtFinEquiv Q hQpos hcop).trans (sparseCoordinatesEquiv q P)
  let cls := sparseArithmeticClass q P
    (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i))
    (lt_of_lt_of_le Nat.zero_lt_two hP) hcop fixed closingFixed
  apply minimalDistinctCover_of_equiv
      (N := ∏ i, Q i) (M := M) (X := X)
      (member := member) (witness := witness) (e := e) (cls := cls)
  · exact Finset.prod_pos fun i _ => hQpos i
  · exact sparseFrame_covers (fun i => ZMod (q i)) (ZMod P)
      fixed closingFixed hfixed
  · exact sparseFrame_private (fun i => ZMod (q i)) (ZMod P)
      fixed closingFixed hfixed escape hprotect
  · intro c
    apply subsetCrtClass_valid Q
      (fun j => match j with | none => hP | some i => hq i) hcop
    cases c with
    | inl b =>
        refine ⟨some b.index, ?_⟩
        simp [sparseFrameSupport, frameSupport]
    | inr a =>
        exact ⟨none, by simp [sparseFrameSupport]⟩
  · intro c
    exact subsetModulus_dvd_full Q (sparseFrameSupport q P fixed closingFixed c)
  · intro a b hab
    apply hsupport
    apply coprime_subsetProduct_injective Q
      (fun j => match j with | none => hP | some i => hq i) hcop
    simpa [cls, sparseArithmeticClass, subsetCrtClass,
      subsetModulus_eq_prod] using hab
  · intro c r
    exact sparseFrameMember_iff_satisfies q P hq hP hcop fixed closingFixed hfixed c r

end Erdos1188

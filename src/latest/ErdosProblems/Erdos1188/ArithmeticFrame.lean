import ErdosProblems.Erdos1188.Frame
import ErdosProblems.Erdos1188.Transport
import ErdosProblems.Erdos1188.Squarefree
import ErdosProblems.Erdos1188.SupportInjective

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Squarefree arithmetic frames
-/

namespace Erdos1188

open scoped BigOperators

variable {n : ℕ} (q : Fin n → ℕ)

abbrev ZModCoordinates (q : Fin n → ℕ) := (i : Fin n) → ZMod (q i)

/-- Coordinates fixed by a non-axis frame member. -/
def frameSupport
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (c : FrameChoice (fun i => ZMod (q i))) : Finset (Fin n) :=
  insert c.index (fixed c)

/-- Values prescribed on the support are the restriction of the private spike. -/
def frameSupportValues
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (c : FrameChoice (fun i => ZMod (q i)))
    (j : ↥(frameSupport q fixed c)) : ZMod (q j) :=
  frameSpike (fun i => ZMod (q i)) c j

/-- Frame membership is exactly equality to the spike on the support. -/
theorem frameMember_iff_support
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (hfixed : FrameFixesEarlier (fun i => ZMod (q i)) fixed)
    (c : FrameChoice (fun i => ZMod (q i)))
    (x : ZModCoordinates q) :
    FrameMember (fun i => ZMod (q i)) fixed c x ↔
      ∀ j : ↥(frameSupport q fixed c), x j = frameSupportValues q fixed c j := by
  constructor
  · rintro ⟨hindex, hzeros⟩ j
    rcases Finset.mem_insert.mp j.property with hji | hjfixed
    · cases j with
      | mk j hj =>
          simp only [Subtype.coe_mk] at hji ⊢
          subst j
          simpa [frameSupportValues, frameSpike] using hindex
    · have hne : (j : Fin n) ≠ c.index := ne_of_lt (hfixed c j hjfixed)
      rw [hzeros j hjfixed]
      simp [frameSupportValues, frameSpike, hne]
  · intro h
    constructor
    · have hi := h (⟨c.index, Finset.mem_insert_self _ _⟩ : ↥(frameSupport q fixed c))
      simpa [frameSupportValues, frameSpike] using hi
    · intro j hj
      have hne : j ≠ c.index := ne_of_lt (hfixed c j hj)
      have hj' := h (⟨j, Finset.mem_insert_of_mem hj⟩ : ↥(frameSupport q fixed c))
      simpa [frameSupportValues, frameSpike, hne] using hj'

/-- The coordinate support represented by a full frame member. -/
def fullFrameSupport
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (m : Option (FrameChoice (fun i => ZMod (q i)))) : Finset (Fin n) :=
  match m with
  | none => Finset.univ
  | some c => frameSupport q fixed c

/-- The arithmetic class represented by a full frame member. -/
noncomputable def arithmeticFrameClass
    (hqpos : ∀ i, 0 < q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (m : Option (FrameChoice (fun i => ZMod (q i)))) : CongruenceClass :=
  match m with
  | none => subsetCrtClass q hqpos hcop Finset.univ (fun _ => 0)
  | some c => subsetCrtClass q hqpos hcop (frameSupport q fixed c)
      (frameSupportValues q fixed c)

/-- An arithmetic squarefree frame whose support-products are all distinct is a
minimal distinct covering system of integers. -/
theorem arithmeticFrame_isMinimalDistinct
    [(i : Fin n) → NeZero (q i)]
    (hn : 0 < n)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (hfixed : FrameFixesEarlier (fun i => ZMod (q i)) fixed)
    (hmodinj : Function.Injective fun m : Option (FrameChoice (fun i => ZMod (q i))) =>
      (arithmeticFrameClass q (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)) hcop fixed m).1) :
    IsMinimalDistinctCoveringSystem
      (Finset.univ.image
        (arithmeticFrameClass q (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)) hcop fixed)) := by
  classical
  let hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)
  let S := fun i : Fin n => ZMod (q i)
  let member := FullFrameMember S fixed
  let witness := fullFrameWitness S
  let e := crtFinEquiv q hqpos hcop
  let cls := arithmeticFrameClass q hqpos hcop fixed
  let : DecidableEq (FrameChoice S) := Classical.decEq _
  apply minimalDistinctCover_of_equiv
      (N := ∏ i, q i) (M := Option (FrameChoice S))
      (X := ZModCoordinates q)
      (member := member) (witness := witness)
      (e := e) (cls := cls)
  · exact Finset.prod_pos fun i _ => hqpos i
  · exact fun x => fullFrame_covers S fixed hfixed x
  · exact fun m => fullFrame_private S fixed hfixed m
  · intro m
    cases m with
    | none =>
        apply subsetCrtClass_valid q hq hcop Finset.univ
        exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    | some c =>
        apply subsetCrtClass_valid q hq hcop (frameSupport q fixed c)
        exact ⟨c.index, Finset.mem_insert_self _ _⟩
  · intro m
    cases m with
    | none => exact subsetModulus_dvd_full q Finset.univ
    | some c => exact subsetModulus_dvd_full q (frameSupport q fixed c)
  · simpa [cls, hqpos] using hmodinj
  · intro m r
    cases m with
    | none =>
        change OnFrameAxis S (e r) ↔
          Satisfies (r.val : ℤ) (subsetCrtClass q hqpos hcop Finset.univ (fun _ => 0))
        rw [satisfies_subsetCrtClass_iff]
        constructor
        · intro h j
          exact h j
        · intro h j
          simpa [e, S, crtFinEquiv_apply] using h (⟨j, Finset.mem_univ j⟩)
    | some c =>
        change FrameMember S fixed c (e r) ↔
          Satisfies (r.val : ℤ) (subsetCrtClass q hqpos hcop
            (frameSupport q fixed c) (frameSupportValues q fixed c))
        rw [satisfies_subsetCrtClass_iff]
        exact frameMember_iff_support q fixed hfixed c (e r)

/-- An earlier-coordinate frame has injective supports as soon as choices at
the same distinguished coordinate receive different fixed sets. -/
theorem frameSupport_injective_of_local
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (hfixed : FrameFixesEarlier (fun i => ZMod (q i)) fixed)
    (hlocal : ∀ c d, c.index = d.index → fixed c = fixed d → c = d) :
    Function.Injective (frameSupport q fixed) := by
  intro c d hsupport
  have hindex : c.index = d.index := by
    rcases lt_trichotomy c.index d.index with hcd | hcd | hdc
    · have hdmem : d.index ∈ frameSupport q fixed d := Finset.mem_insert_self _ _
      rw [← hsupport] at hdmem
      rcases Finset.mem_insert.mp hdmem with heq | hmem
      · exact False.elim ((ne_of_lt hcd) heq.symm)
      · exact False.elim ((not_lt_of_ge (le_of_lt hcd)) (hfixed c d.index hmem))
    · exact hcd
    · have hcmem : c.index ∈ frameSupport q fixed c := Finset.mem_insert_self _ _
      rw [hsupport] at hcmem
      rcases Finset.mem_insert.mp hcmem with heq | hmem
      · exact False.elim ((ne_of_lt hdc) heq.symm)
      · exact False.elim ((not_lt_of_ge (le_of_lt hdc)) (hfixed d c.index hmem))
  apply hlocal c d hindex
  apply Finset.ext
  intro j
  constructor
  · intro hjc
    have hjmem : j ∈ frameSupport q fixed c := Finset.mem_insert_of_mem hjc
    rw [hsupport] at hjmem
    rcases Finset.mem_insert.mp hjmem with hjd | hjd
    · subst j
      have hcself : c.index ∈ fixed c := by simpa [hindex] using hjc
      exact False.elim ((lt_irrefl _) (hfixed c c.index hcself))
    · exact hjd
  · intro hjd
    have hjmem : j ∈ frameSupport q fixed d := Finset.mem_insert_of_mem hjd
    rw [← hsupport] at hjmem
    rcases Finset.mem_insert.mp hjmem with hjc | hjc
    · subst j
      have hdself : d.index ∈ fixed d := by simpa [hindex] using hjd
      exact False.elim ((lt_irrefl _) (hfixed d d.index hdself))
    · exact hjc

/-- If non-axis supports are injective and proper, adjoining `univ` for the
axis preserves injectivity. -/
theorem fullFrameSupport_injective_of
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (hinj : Function.Injective (frameSupport q fixed))
    (hproper : ∀ c, frameSupport q fixed c ≠ Finset.univ) :
    Function.Injective (fullFrameSupport q fixed) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some d => exact False.elim (hproper d hab.symm)
  | some c =>
      cases b with
      | none => exact False.elim (hproper c hab)
      | some d => exact congrArg some (hinj hab)

/-- Pointwise correspondence between a full abstract frame and its arithmetic
CRT classes. -/
theorem fullFrameMember_iff_satisfies_arithmeticFrameClass
    [(i : Fin n) → NeZero (q i)]
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (hfixed : FrameFixesEarlier (fun i => ZMod (q i)) fixed)
    (m : Option (FrameChoice (fun i => ZMod (q i))))
    (r : Fin (∏ i, q i)) :
    FullFrameMember (fun i => ZMod (q i)) fixed m (crtFinEquiv q
      (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)) hcop r) ↔
      Satisfies (r.val : ℤ)
        (arithmeticFrameClass q
          (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)) hcop fixed m) := by
  let hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)
  cases m with
  | none =>
      change OnFrameAxis (fun i => ZMod (q i)) (crtFinEquiv q hqpos hcop r) ↔
        Satisfies (r.val : ℤ)
          (subsetCrtClass q hqpos hcop Finset.univ (fun _ => 0))
      rw [satisfies_subsetCrtClass_iff]
      constructor
      · intro h j
        exact h j
      · intro h j
        simpa [crtFinEquiv_apply] using h (⟨j, Finset.mem_univ j⟩)
  | some c =>
      change FrameMember (fun i => ZMod (q i)) fixed c (crtFinEquiv q hqpos hcop r) ↔
        Satisfies (r.val : ℤ) (subsetCrtClass q hqpos hcop
          (frameSupport q fixed c) (frameSupportValues q fixed c))
      rw [satisfies_subsetCrtClass_iff]
      exact frameMember_iff_support q fixed hfixed c (crtFinEquiv q hqpos hcop r)

/-- For coprime factors greater than one, injectivity of frame supports
implies injectivity of the resulting arithmetic moduli. -/
theorem arithmeticFrame_modulus_injective
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (hsupport : Function.Injective (fullFrameSupport q fixed)) :
    Function.Injective fun m : Option (FrameChoice (fun i => ZMod (q i))) =>
      (arithmeticFrameClass q (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i))
        hcop fixed m).1 := by
  intro a b hab
  apply hsupport
  apply coprime_subsetProduct_injective q hq hcop
  cases a <;> cases b <;>
    simpa [arithmeticFrameClass, fullFrameSupport, subsetCrtClass,
      subsetModulus_eq_prod] using hab

/-- Support-injectivity is therefore the only distinct-modulus condition needed
for a squarefree arithmetic frame. -/
theorem arithmeticFrame_isMinimalDistinct_of_support
    [(i : Fin n) → NeZero (q i)]
    (hn : 0 < n)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q))
    (fixed : FrameChoice (fun i => ZMod (q i)) → Finset (Fin n))
    (hfixed : FrameFixesEarlier (fun i => ZMod (q i)) fixed)
    (hsupport : Function.Injective (fullFrameSupport q fixed)) :
    IsMinimalDistinctCoveringSystem
      (Finset.univ.image
        (arithmeticFrameClass q (fun i => lt_of_lt_of_le Nat.zero_lt_two (hq i)) hcop fixed)) := by
  apply arithmeticFrame_isMinimalDistinct q hn hq hcop fixed hfixed
  exact arithmeticFrame_modulus_injective q hq hcop fixed hsupport

end Erdos1188

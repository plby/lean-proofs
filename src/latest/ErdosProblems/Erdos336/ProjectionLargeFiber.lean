import ErdosProblems.Erdos336.IntegerProjectionKneser

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise BigOperators

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The fibre of a set in `ℤ × H` over an integer. -/
def integerProjectionFiber (A : Finset (ℤ × H)) (z : ℤ) : Finset (ℤ × H) :=
  A.filter (fun x => x.1 = z)

@[simp] theorem mem_integerProjectionFiber {A : Finset (ℤ × H)} {z : ℤ} {x : ℤ × H} :
    x ∈ integerProjectionFiber A z ↔ x ∈ A ∧ x.1 = z := by
  simp [integerProjectionFiber]

/-- A division-free version of Lev's Corollary 3.  The proof chooses a
largest fibre of `A`; translates of it over every fibre of `B`, together
with extreme translates of all remaining fibres of `A`, are disjoint. -/
theorem projection_large_fiber_bound
    (A B : Finset (ℤ × H)) (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.image Prod.fst).card * (A + B).card ≥
      ((A.image Prod.fst).card + (B.image Prod.fst).card - 1) * A.card := by
  classical
  let P := A.image Prod.fst
  let Q := B.image Prod.fst
  have hP : P.Nonempty := hA.image Prod.fst
  have hQ : Q.Nonempty := hB.image Prod.fst
  obtain ⟨z0, hz0P, hz0max⟩ := Finset.exists_max_image P
    (fun z => (integerProjectionFiber A z).card) hP
  let A0 := integerProjectionFiber A z0
  have hA0ne : A0.Nonempty := by
    obtain ⟨a, haA, hafst⟩ := Finset.mem_image.mp hz0P
    exact ⟨a, mem_integerProjectionFiber.mpr ⟨haA, hafst⟩⟩
  let qmin := Q.min' hQ
  let qmax := Q.max' hQ
  let chooseB : ℤ → ℤ × H := fun q =>
    if hq : q ∈ Q then (Finset.mem_image.mp hq).choose else 0
  have hchooseBmem (q : ℤ) (hq : q ∈ Q) : chooseB q ∈ B := by
    dsimp [chooseB]
    split <;> rename_i h
    · exact (Finset.mem_image.mp h).choose_spec.1
    · exact (h hq).elim
  have hchooseBfst (q : ℤ) (hq : q ∈ Q) : (chooseB q).1 = q := by
    dsimp [chooseB]
    split <;> rename_i h
    · exact (Finset.mem_image.mp h).choose_spec.2
    · exact (h hq).elim
  have hqmin : qmin ∈ Q := Finset.min'_mem Q hQ
  have hqmax : qmax ∈ Q := Finset.max'_mem Q hQ
  let bmin := chooseB qmin
  let bmax := chooseB qmax
  have hbminB : bmin ∈ B := by
    dsimp [bmin]
    exact hchooseBmem qmin hqmin
  have hbmaxB : bmax ∈ B := by
    dsimp [bmax]
    exact hchooseBmem qmax hqmax
  have hbminfst : bmin.1 = qmin := by
    dsimp [bmin]
    exact hchooseBfst qmin hqmin
  have hbmaxfst : bmax.1 = qmax := by
    dsimp [bmax]
    exact hchooseBfst qmax hqmax
  let Aout := A.filter (fun a => a.1 ≠ z0)
  let D := (↥Q × ↥A0) ⊕ ↥Aout
  let f : D → ↥(A + B) := fun u =>
    match u with
    | Sum.inl v =>
        ⟨v.2.1 + chooseB v.1.1,
          Finset.mem_add.mpr ⟨v.2.1,
            (mem_integerProjectionFiber.mp v.2.2).1,
            chooseB v.1.1, hchooseBmem v.1.1 v.1.2, rfl⟩⟩
    | Sum.inr a =>
        if ha : a.1.1 < z0 then
          ⟨a.1 + bmin, Finset.mem_add.mpr
            ⟨a.1, (Finset.mem_filter.mp a.2).1, bmin, hbminB, rfl⟩⟩
        else
          ⟨a.1 + bmax, Finset.mem_add.mpr
            ⟨a.1, (Finset.mem_filter.mp a.2).1, bmax, hbmaxB, rfl⟩⟩
  have hf : Function.Injective f := by
    intro u v huv
    rcases u with u | a <;> rcases v with v | b
    · apply congrArg Sum.inl
      have hval := congrArg (fun x : ↥(A + B) => x.1) huv
      change u.2.1 + chooseB u.1.1 =
        v.2.1 + chooseB v.1.1 at hval
      have hfst := congrArg Prod.fst hval
      have hcufst := hchooseBfst u.1.1 u.1.2
      have hcvfst := hchooseBfst v.1.1 v.1.2
      rw [Prod.fst_add, Prod.fst_add,
        (mem_integerProjectionFiber.mp u.2.2).2,
        (mem_integerProjectionFiber.mp v.2.2).2,
        hcufst, hcvfst] at hfst
      have hq : u.1.1 = v.1.1 := by omega
      have hqsub : u.1 = v.1 := Subtype.ext hq
      have hc : chooseB u.1.1 = chooseB v.1.1 :=
        congrArg chooseB hq
      rw [hc] at hval
      have ha : u.2.1 = v.2.1 := add_right_cancel hval
      exact Prod.ext hqsub (Subtype.ext ha)
    · exfalso
      dsimp [f] at huv
      split at huv <;> rename_i hb
      · have hfst := congrArg (fun x : ↥(A + B) => x.1.1) huv
        have hcufst := hchooseBfst u.1.1 u.1.2
        rw [Prod.fst_add, Prod.fst_add,
          (mem_integerProjectionFiber.mp u.2.2).2,
          hcufst, hbminfst] at hfst
        have hqle := Finset.min'_le Q u.1.1 u.1.2
        omega
      · have hbne : b.1.1 ≠ z0 := (Finset.mem_filter.mp b.2).2
        have hbgt : z0 < b.1.1 := by omega
        have hfst := congrArg (fun x : ↥(A + B) => x.1.1) huv
        have hcufst := hchooseBfst u.1.1 u.1.2
        rw [Prod.fst_add, Prod.fst_add,
          (mem_integerProjectionFiber.mp u.2.2).2,
          hcufst, hbmaxfst] at hfst
        have hqle := Finset.le_max' Q u.1.1 u.1.2
        omega
    · exfalso
      dsimp [f] at huv
      split at huv <;> rename_i ha
      · have hfst := congrArg (fun x : ↥(A + B) => x.1.1) huv
        have hcvfst := hchooseBfst v.1.1 v.1.2
        rw [Prod.fst_add, Prod.fst_add,
          (mem_integerProjectionFiber.mp v.2.2).2,
          hcvfst] at hfst
        have hqle := Finset.min'_le Q v.1.1 v.1.2
        omega
      · have hane : a.1.1 ≠ z0 := (Finset.mem_filter.mp a.2).2
        have hagt : z0 < a.1.1 := by omega
        have hfst := congrArg (fun x : ↥(A + B) => x.1.1) huv
        have hcvfst := hchooseBfst v.1.1 v.1.2
        rw [Prod.fst_add, Prod.fst_add,
          (mem_integerProjectionFiber.mp v.2.2).2,
          hcvfst] at hfst
        have hqle := Finset.le_max' Q v.1.1 v.1.2
        omega
    · apply congrArg Sum.inr
      dsimp [f] at huv
      split at huv <;> split at huv <;> rename_i ha hb
      · apply Subtype.ext
        exact add_right_cancel (congrArg (fun x : ↥(A + B) => x.1) huv)
      · exfalso
        have hbne : b.1.1 ≠ z0 := (Finset.mem_filter.mp b.2).2
        have hbgt : z0 < b.1.1 := by omega
        have hfst := congrArg (fun x : ↥(A + B) => x.1.1) huv
        rw [Prod.fst_add, Prod.fst_add, hbminfst, hbmaxfst] at hfst
        have hminmax : qmin ≤ qmax := Finset.min'_le Q qmax (Finset.max'_mem Q hQ)
        omega
      · exfalso
        have hane : a.1.1 ≠ z0 := (Finset.mem_filter.mp a.2).2
        have hagt : z0 < a.1.1 := by omega
        have hfst := congrArg (fun x : ↥(A + B) => x.1.1) huv
        rw [Prod.fst_add, Prod.fst_add, hbmaxfst, hbminfst] at hfst
        have hminmax : qmin ≤ qmax := Finset.min'_le Q qmax (Finset.max'_mem Q hQ)
        omega
      · apply Subtype.ext
        exact add_right_cancel (congrArg (fun x : ↥(A + B) => x.1) huv)
  have hcard := Fintype.card_le_of_injective f hf
  change Fintype.card (↥Q × ↥A0 ⊕ ↥Aout) ≤ Fintype.card ↥(A + B) at hcard
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_coe, Fintype.card_coe, Fintype.card_coe] at hcard
  have hA0sub : A0 ⊆ A :=
    fun _ ha => (mem_integerProjectionFiber.mp ha).1
  have hApartition : Aout.card = A.card - A0.card := by
    have hsplit : Aout = A \ A0 := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_filter,
        mem_integerProjectionFiber]
      aesop
    rw [hsplit, Finset.card_sdiff_of_subset hA0sub]
  rw [hApartition] at hcard
  have hA0le : A0.card ≤ A.card := Finset.card_le_card hA0sub
  have hlarge : P.card * A0.card ≥ A.card := by
    have hpartition : A.card =
        ∑ z ∈ P, (integerProjectionFiber A z).card := by
      simpa [P, integerProjectionFiber] using
        (Finset.card_eq_sum_card_image Prod.fst A)
    rw [hpartition]
    simpa [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul P
        (fun z => (integerProjectionFiber A z).card) A0.card hz0max)
  let p := P.card
  let q := Q.card
  let x := A0.card
  let a := A.card
  let c := (A + B).card
  have hp : 0 < p := hP.card_pos
  have hq : 0 < q := hQ.card_pos
  have hxle : x ≤ a := hA0le
  change q * x + (a - x) ≤ c at hcard
  change a ≤ p * x at hlarge
  have hqmul : q * x = (q - 1) * x + x := by
    calc
      q * x = ((q - 1) + 1) * x := by
        congr 1
        omega
      _ = (q - 1) * x + x := by ring
  have hasplit : a - x + x = a := Nat.sub_add_cancel hxle
  have hcard' : (q - 1) * x + a ≤ c := by
    calc
      (q - 1) * x + a = ((q - 1) * x + x) + (a - x) := by
        omega
      _ = q * x + (a - x) := by rw [← hqmul]
      _ ≤ c := hcard
  have hlargeMul := Nat.mul_le_mul_left (q - 1) hlarge
  have hcardMul := Nat.mul_le_mul_left p hcard'
  change (p + q - 1) * a ≤ p * c
  calc
    (p + q - 1) * a = p * a + (q - 1) * a := by
      rw [show p + q - 1 = p + (q - 1) by omega]
      ring
    _ ≤ p * a + (q - 1) * (p * x) :=
      Nat.add_le_add_left hlargeMul _
    _ = p * ((q - 1) * x + a) := by ring
    _ ≤ p * c := hcardMul

end Erdos336

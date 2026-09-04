/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorFinal
import ErdosProblems.Erdos215.SelectorComponents
import ErdosProblems.Erdos215.SelectorSeparation

/-!
Reconstruction of lift data from the line maps in the finite
Jackson--Mauldin selector construction.

The definitions in this file deliberately separate the two ingredients of
the argument.  `ResidueSolution` is the simultaneous system of line
equations (4.4), written in `ZMod d`.  Once such a solution is available,
`liftDataOfResidueSolution` chooses canonical integral representatives and
`inducedFamily_liftDataOfResidueSolution` proves that the resulting lift data
induces the prescribed family literally.
-/

namespace Erdos215.Selector.Reconstruct

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The root opposite to `lam`. -/
def negRoot {d : ℕ} (lam : Root d) : Root d :=
  ⟨-lam.1, by simpa only [neg_sq] using lam.property⟩

@[simp] lemma coe_negRoot {d : ℕ} (lam : Root d) :
    (negRoot lam : ZMod d) = -(lam : ZMod d) := rfl

/-- The cell of a line at the input coordinate `i`. -/
def lineCell {d : ℕ} (hd : d ≠ 0) (lam : Root d) (jtilde i : Fin d) :
    Fin d :=
  lineResidue hd lam jtilde i

/-- The unique canonical label of the `lam`-line through the cell `(i,j)`. -/
def cellLineLabel {d : ℕ} (hd : d ≠ 0) (lam : Root d) (i j : Fin d) :
    Fin d := by
  let _ : NeZero d := ⟨hd⟩
  exact ⟨(((j : ℕ) : ZMod d) - (lam : ZMod d) * ((i : ℕ) : ZMod d)).val,
    ZMod.val_lt _⟩

@[simp] lemma cellLineLabel_cast {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (i j : Fin d) :
    (((cellLineLabel hd lam i j : Fin d) : ℕ) : ZMod d) =
      ((j : ℕ) : ZMod d) - (lam : ZMod d) * ((i : ℕ) : ZMod d) := by
  let _ : NeZero d := ⟨hd⟩
  exact ZMod.natCast_zmod_val _

@[simp] lemma lineCell_cellLineLabel {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (i j : Fin d) :
    lineCell hd lam (cellLineLabel hd lam i j) i = j := by
  let _ : NeZero d := ⟨hd⟩
  apply Fin.ext
  have hcast :
      ((((lineCell hd lam (cellLineLabel hd lam i j) i : Fin d) : ℕ) : ZMod d)) =
        (((j : Fin d) : ℕ) : ZMod d) := by
    simp only [lineCell, lineResidue_cast, cellLineLabel_cast]
    ring
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt
      (lineCell hd lam (cellLineLabel hd lam i j) i).isLt,
    ZMod.val_natCast_of_lt j.isLt] at hv
  exact hv

lemma lineRelation_of_same_cell {d : ℕ} (hd : d ≠ 0)
    (lam₁ lam₂ : Root d) (j₁ j₂ i : Fin d)
    (hcell : lineCell hd lam₁ j₁ i = lineCell hd lam₂ j₂ i) :
    ((i : ℕ) : ZMod d) * ((lam₁ : ZMod d) - lam₂) =
      -(((j₁ : ℕ) : ZMod d) - ((j₂ : ℕ) : ZMod d)) := by
  have hcast := congrArg (fun j : Fin d ↦ (((j : ℕ) : ZMod d))) hcell
  simp only [lineCell, lineResidue_cast] at hcast
  linear_combination hcast

/-- The rearranged right hand side of (4.4).  Thus the equation imposed at
the cell `(i,lineCell ...)` is `k + lam*l = lineTarget ...`. -/
def lineTarget {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d)
    (lam : Root d) (jtilde i : Fin d) : ZMod d :=
  (((F lam jtilde i : Fin d) : ℕ) : ZMod d) - rootPhase lam * (i : ℕ) +
    (lam : ZMod d) * (lineCarry hd lam jtilde i : ZMod d)

lemma PrimaryComponent.localQuotient_mul_right {d : ℕ}
    (c : PrimaryComponent d) (z n : ℤ) (hz : (c.q : ℤ) ∣ z) :
    c.localQuotient (z * n) = c.localQuotient z * (n : ZMod c.q) := by
  rcases hz with ⟨a, rfl⟩
  simp only [PrimaryComponent.localQuotient]
  rw [mul_assoc, localizedQuotient_mul c.q c.q_ne_zero,
    localizedQuotient_mul c.q c.q_ne_zero]
  push_cast
  ring

lemma PrimaryComponent.localQuotient_add' {d : ℕ}
    (c : PrimaryComponent d) (x y : ℤ)
    (hx : (c.q : ℤ) ∣ x) (hy : (c.q : ℤ) ∣ y) :
    c.localQuotient (x + y) = c.localQuotient x + c.localQuotient y := by
  exact localizedQuotient_add c.q c.q_ne_zero _ x y hx hy

/-- The rearranged line targets must be independent of the chosen global
root whenever the two roots induce the same root on a primary component. -/
def FamilyTargetCoherent {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d) : Prop :=
  ∀ (c : PrimaryComponent d) (lam₁ lam₂ : Root d) (j₁ j₂ i : Fin d),
    c.reduce lam₁ = c.reduce lam₂ →
    ((i : ℕ) : ZMod d) * ((lam₁ : ZMod d) - lam₂) =
        -(((j₁ : ℕ) : ZMod d) - ((j₂ : ℕ) : ZMod d)) →
    c.reduce (lineTarget hd F lam₁ j₁ i) =
      c.reduce (lineTarget hd F lam₂ j₂ i)

/-- Formula (4.6), including its carry and `h_d` correction terms, says
exactly that the rearranged line target is componentwise well-defined. -/
theorem targetCoherent_of_consistent {d : ℕ} (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d) (F : RawLineFamily d)
    (hF : FamilyConsistent F) : FamilyTargetCoherent hd F := by
  intro c lam₁ lam₂ j₁ j₂ i hroot hline
  have hcell := lineResidue_eq_of_relation hd lam₁ lam₂ j₁ j₂ i hline
  have hcarry := lineCarry_sub_relation hd lam₁ lam₂ j₁ j₂ i hcell
  let delta : ℤ := (rootVal hd lam₁ : ℤ) - rootVal hd lam₂
  let jdiff : ℤ := ((j₁ : ℕ) : ℤ) - (j₂ : ℕ)
  let mdiff : ℤ := (lineCarry hd lam₁ j₁ i : ℤ) -
    lineCarry hd lam₂ j₂ i
  have hrootVal :
      ((rootVal hd lam₁ : ℤ) : ZMod c.q) =
        ((rootVal hd lam₂ : ℤ) : ZMod c.q) := by
    simp only [Int.cast_natCast, ← c.reduce_natCast, rootVal_cast]
    exact hroot
  have hdelta : (c.q : ℤ) ∣ delta := by
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub
      (rootVal hd lam₁) (rootVal hd lam₂) c.q).mp hrootVal
    simpa only [delta, neg_sub] using (dvd_neg.mpr h)
  have hlinec := congrArg c.reduce hline
  simp only [map_mul, map_sub, map_neg, c.reduce_natCast, hroot, sub_self,
    mul_zero, neg_eq_zero] at hlinec
  have hjdiffZero : (jdiff : ZMod c.q) = 0 := by
    dsimp only [jdiff]
    push_cast
    exact neg_eq_zero.mp hlinec.symm
  have hjdiff : (c.q : ℤ) ∣ jdiff :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd jdiff c.q).mp hjdiffZero
  have hdeltai : (c.q : ℤ) ∣ delta * (i : ℕ) :=
    dvd_mul_of_dvd_left hdelta _
  have hcarry' : (d : ℤ) * mdiff = jdiff + delta * (i : ℕ) := by
    simpa only [delta, jdiff, mdiff] using hcarry
  have hcarryLoc := congrArg c.localQuotient hcarry'
  rw [Erdos215.Selector.Final.PrimaryComponent.localQuotient_mul_modulus,
    Erdos215.Selector.Reconstruct.PrimaryComponent.localQuotient_add'
      c jdiff (delta * (i : ℕ)) hjdiff hdeltai,
    Erdos215.Selector.Reconstruct.PrimaryComponent.localQuotient_mul_right
      c delta (i : ℕ) hdelta] at hcarryLoc
  have hphase := two_mul_reduce_rootPhase_sub hd hodd c lam₁ lam₂
  have hphase' :
      (2 : ZMod c.q) * c.reduce (rootPhase lam₁ - rootPhase lam₂) =
        c.localQuotient delta *
          (((rootVal hd lam₁ : ℤ) + rootVal hd lam₂ : ℤ) : ZMod c.q) := by
    rw [hphase]
    exact Erdos215.Selector.Reconstruct.PrimaryComponent.localQuotient_mul_right c delta
      ((rootVal hd lam₁ : ℤ) + rootVal hd lam₂) hdelta
  have hsum :
      (((rootVal hd lam₁ : ℤ) + rootVal hd lam₂ : ℤ) : ZMod c.q) =
        (2 : ZMod c.q) * c.reduce lam₁ := by
    push_cast
    simp only [Int.cast_natCast, ← c.reduce_natCast, rootVal_cast, hroot]
    ring
  rw [hsum] at hphase'
  have htwoCoprime : Nat.Coprime 2 c.q := hodd.of_dvd_right c.q_dvd
  have htwoUnit : IsUnit (2 : ZMod c.q) := by
    exact IsUnit.of_mul_eq_one _ (ZMod.coe_mul_inv_eq_one 2 htwoCoprime)
  have hphaseCancel :
      c.reduce (rootPhase lam₁ - rootPhase lam₂) =
        c.reduce lam₁ * c.localQuotient delta := by
    apply htwoUnit.mul_left_cancel
    calc
      (2 : ZMod c.q) * c.reduce (rootPhase lam₁ - rootPhase lam₂) =
          c.localQuotient delta * ((2 : ZMod c.q) * c.reduce lam₁) := hphase'
      _ = (2 : ZMod c.q) *
          (c.reduce lam₁ * c.localQuotient delta) := by ring
  have hcons := hF c lam₁ lam₂ j₁ j₂ i hroot hline
  simp only [lineTarget, map_add, map_sub, map_mul, c.reduce_natCast,
    c.reduce_intCast]
  simp only [lineTarget, map_add, map_sub, map_mul, c.reduce_natCast,
    c.reduce_intCast] at hcons ⊢
  have hcarryLoc' := hcarryLoc
  dsimp only [mdiff, jdiff] at hcarryLoc' hcons ⊢
  push_cast at hcarryLoc'
  dsimp only [delta] at hphaseCancel
  simp only [map_sub] at hphaseCancel
  rw [← hroot]
  rw [← sub_eq_zero]
  linear_combination hcons +
    c.reduce lam₁ * hcarryLoc' - hphaseCancel * (((i : ℕ) : ZMod c.q))

/-- A solution, modulo `d`, of all the line equations attached to a raw
family. -/
structure ResidueSolution {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d) where
  k : Fin d → Fin d → ZMod d
  l : Fin d → Fin d → ZMod d
  line_eq : ∀ (lam : Root d) (jtilde i : Fin d),
    k i (lineCell hd lam jtilde i) +
        (lam : ZMod d) * l i (lineCell hd lam jtilde i) =
      lineTarget hd F lam jtilde i

/-- Equality in `ZMod d` is detected by all of its full primary
components.  This is the exact CRT separation property used below. -/
def PrimaryReductionsDetect (d : ℕ) : Prop :=
  ∀ x y : ZMod d,
    (∀ c : PrimaryComponent d, c.reduce x = c.reduce y) → x = y

/-- Every global root restricts, on each primary component, to one of the
two signs of a fixed global root. -/
def RootSignsCovered {d : ℕ} (lam₀ : Root d) : Prop :=
  ∀ (c : PrimaryComponent d) (lam : Root d),
    c.reduce lam = c.reduce lam₀ ∨ c.reduce lam = c.reduce (negRoot lam₀)

lemma primaryReductionsDetect_of_complete {d : ℕ}
    (C : CompleteComponents d) (hd : d ≠ 0) : PrimaryReductionsDetect d := by
  intro x y hxy
  exact C.eq_of_reduce_eq hd x y (fun c _hc ↦ hxy c)

lemma rootSignsCovered_of_odd {d : ℕ} (hodd : Nat.Coprime 2 d)
    (lam₀ : Root d) : RootSignsCovered lam₀ := by
  intro c lam
  have hcodd : Nat.Coprime 2 c.q := hodd.of_dvd_right c.q_dvd
  rcases c.root_eq_or_eq_neg hcodd (c.reduceRoot lam) (c.reduceRoot lam₀) with h | h
  · left
    exact h
  · right
    rw [show (negRoot lam₀ : ZMod d) = -(lam₀ : ZMod d) from rfl, map_neg]
    exact h

/-- The target attached to the unique `lam`-line through `(i,j)`. -/
def cellTarget {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d)
    (lam : Root d) (i j : Fin d) : ZMod d :=
  lineTarget hd F lam (cellLineLabel hd lam i j) i

/-- The solution of the two line equations belonging to `lam₀` and
`-lam₀`. -/
def reconstructedL {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d)
    (lam₀ : Root d) (i j : Fin d) : ZMod d :=
  ((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d))⁻¹ *
    (cellTarget hd F lam₀ i j - cellTarget hd F (negRoot lam₀) i j)

def reconstructedK {d : ℕ} (hd : d ≠ 0) (F : RawLineFamily d)
    (lam₀ : Root d) (i j : Fin d) : ZMod d :=
  cellTarget hd F lam₀ i j - (lam₀ : ZMod d) * reconstructedL hd F lam₀ i j

lemma root_sub_negRoot_isUnit {d : ℕ} (hodd : Nat.Coprime 2 d)
    (lam : Root d) :
    IsUnit ((lam : ZMod d) - (negRoot lam : ZMod d)) := by
  have htwo : IsUnit (2 : ZMod d) :=
    IsUnit.of_mul_eq_one _ (ZMod.coe_mul_inv_eq_one 2 hodd)
  have hprod : IsUnit ((2 : ZMod d) * (lam : ZMod d)) :=
    htwo.mul (root_isUnit lam)
  convert hprod using 1 <;> simp only [coe_negRoot] <;> ring

lemma reconstructed_plus {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (F : RawLineFamily d) (lam₀ : Root d) (i j : Fin d) :
    reconstructedK hd F lam₀ i j +
        (lam₀ : ZMod d) * reconstructedL hd F lam₀ i j =
      cellTarget hd F lam₀ i j := by
  simp only [reconstructedK]
  ring

lemma reconstructed_minus {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (F : RawLineFamily d) (lam₀ : Root d) (i j : Fin d) :
    reconstructedK hd F lam₀ i j +
        (negRoot lam₀ : ZMod d) * reconstructedL hd F lam₀ i j =
      cellTarget hd F (negRoot lam₀) i j := by
  have hunit := root_sub_negRoot_isUnit hodd lam₀
  have hinv := ZMod.inv_mul_of_unit
    ((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d)) hunit
  simp only [reconstructedK, reconstructedL]
  linear_combination
    cellTarget hd F lam₀ i j - cellTarget hd F (negRoot lam₀) i j -
      (cellTarget hd F lam₀ i j - cellTarget hd F (negRoot lam₀) i j) * hinv

/-- Reconstruction of every line equation from consistency.  The two
explicit hypotheses are precisely the standard primary-component CRT facts:
primary reductions detect equality, and a root of `X²+1` on an odd prime
power has one of two signs. -/
noncomputable def residueSolution_of_consistent {d : ℕ} (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d) (F : RawLineFamily d)
    (hF : FamilyConsistent F) (lam₀ : Root d)
    (hdetect : PrimaryReductionsDetect d) (hsigns : RootSignsCovered lam₀) :
    ResidueSolution hd F where
  k := reconstructedK hd F lam₀
  l := reconstructedL hd F lam₀
  line_eq := by
    intro lam jtilde i
    let j := lineCell hd lam jtilde i
    apply hdetect
    intro c
    have hcoherent := targetCoherent_of_consistent hd hodd F hF
    rcases hsigns c lam with hplus | hminus
    · have hsame :
          lineCell hd lam jtilde i =
            lineCell hd lam₀ (cellLineLabel hd lam₀ i j) i := by
        simp only [lineCell_cellLineLabel, j]
      have hrel := lineRelation_of_same_cell hd lam lam₀ jtilde
        (cellLineLabel hd lam₀ i j) i hsame
      have htarget := hcoherent c lam lam₀ jtilde
        (cellLineLabel hd lam₀ i j) i hplus hrel
      have hbase := congrArg c.reduce (reconstructed_plus hd hodd F lam₀ i j)
      calc
        c.reduce (reconstructedK hd F lam₀ i j +
            (lam : ZMod d) * reconstructedL hd F lam₀ i j) =
            c.reduce (reconstructedK hd F lam₀ i j) +
              c.reduce lam * c.reduce (reconstructedL hd F lam₀ i j) := by simp
        _ = c.reduce (reconstructedK hd F lam₀ i j) +
              c.reduce lam₀ * c.reduce (reconstructedL hd F lam₀ i j) := by
            rw [hplus]
        _ = c.reduce (reconstructedK hd F lam₀ i j +
              (lam₀ : ZMod d) * reconstructedL hd F lam₀ i j) := by simp
        _ = c.reduce (cellTarget hd F lam₀ i j) := hbase
        _ = c.reduce (lineTarget hd F lam₀ (cellLineLabel hd lam₀ i j) i) := rfl
        _ = c.reduce (lineTarget hd F lam jtilde i) := htarget.symm
    · have hsame :
          lineCell hd lam jtilde i =
            lineCell hd (negRoot lam₀) (cellLineLabel hd (negRoot lam₀) i j) i := by
        simp only [lineCell_cellLineLabel, j]
      have hrel := lineRelation_of_same_cell hd lam (negRoot lam₀) jtilde
        (cellLineLabel hd (negRoot lam₀) i j) i hsame
      have htarget := hcoherent c lam (negRoot lam₀) jtilde
        (cellLineLabel hd (negRoot lam₀) i j) i hminus hrel
      have hbase := congrArg c.reduce (reconstructed_minus hd hodd F lam₀ i j)
      calc
        c.reduce (reconstructedK hd F lam₀ i j +
            (lam : ZMod d) * reconstructedL hd F lam₀ i j) =
            c.reduce (reconstructedK hd F lam₀ i j) +
              c.reduce lam * c.reduce (reconstructedL hd F lam₀ i j) := by simp
        _ = c.reduce (reconstructedK hd F lam₀ i j) +
              c.reduce (negRoot lam₀) *
                c.reduce (reconstructedL hd F lam₀ i j) := by rw [hminus]
        _ = c.reduce (reconstructedK hd F lam₀ i j +
              (negRoot lam₀ : ZMod d) * reconstructedL hd F lam₀ i j) := by simp
        _ = c.reduce (cellTarget hd F (negRoot lam₀) i j) := hbase
        _ = c.reduce (lineTarget hd F (negRoot lam₀)
              (cellLineLabel hd (negRoot lam₀) i j) i) := rfl
        _ = c.reduce (lineTarget hd F lam jtilde i) := htarget.symm

/-- Choose the canonical integer representative of a residue. -/
def intRepresentative {d : ℕ} (x : ZMod d) : ℤ := x.val

@[simp] lemma intRepresentative_cast {d : ℕ} (hd : d ≠ 0) (x : ZMod d) :
    (intRepresentative x : ZMod d) = x := by
  let : NeZero d := ⟨hd⟩
  simpa only [intRepresentative, Int.cast_natCast] using ZMod.natCast_zmod_val x

/-- Integral lift data obtained from a modular solution. -/
def liftDataOfResidueSolution {d : ℕ} {hd : d ≠ 0} {F : RawLineFamily d}
    (r : ResidueSolution hd F) : LiftData d where
  k i j := intRepresentative (r.k i j)
  l i j := intRepresentative (r.l i j)

/-- Choose representatives while keeping prescribed integral lifts exactly
on a specified set of cells.  The hypotheses merely say that those old
integers represent the reconstructed residues. -/
def liftDataOfResidueSolutionPreserving {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) (old : LiftData d)
    (Q : Fin d → Fin d → Prop) : LiftData d := by
  classical
  exact
    { k := fun i j ↦ if Q i j then old.k i j else intRepresentative (r.k i j)
      l := fun i j ↦ if Q i j then old.l i j else intRepresentative (r.l i j) }

lemma liftDataOfResidueSolutionPreserving_cast_k {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) (old : LiftData d)
    (Q : Fin d → Fin d → Prop)
    (hk : ∀ i j, Q i j → (old.k i j : ZMod d) = r.k i j) (i j : Fin d) :
    ((liftDataOfResidueSolutionPreserving r old Q).k i j : ZMod d) = r.k i j := by
  by_cases hQ : Q i j
  · simp only [liftDataOfResidueSolutionPreserving, if_pos hQ, hk i j hQ]
  · simp only [liftDataOfResidueSolutionPreserving, if_neg hQ,
      intRepresentative_cast hd]

lemma liftDataOfResidueSolutionPreserving_cast_l {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) (old : LiftData d)
    (Q : Fin d → Fin d → Prop)
    (hl : ∀ i j, Q i j → (old.l i j : ZMod d) = r.l i j) (i j : Fin d) :
    ((liftDataOfResidueSolutionPreserving r old Q).l i j : ZMod d) = r.l i j := by
  by_cases hQ : Q i j
  · simp only [liftDataOfResidueSolutionPreserving, if_pos hQ, hl i j hQ]
  · simp only [liftDataOfResidueSolutionPreserving, if_neg hQ,
      intRepresentative_cast hd]

theorem liftDataOfResidueSolutionPreserving_eq_old {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) (old : LiftData d)
    (Q : Fin d → Fin d → Prop) (i j : Fin d) (hQ : Q i j) :
    (liftDataOfResidueSolutionPreserving r old Q).k i j = old.k i j ∧
      (liftDataOfResidueSolutionPreserving r old Q).l i j = old.l i j := by
  simp only [liftDataOfResidueSolutionPreserving, if_pos hQ, and_self]

lemma lineValue_liftDataOfResidueSolution {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) (lam : Root d)
    (jtilde i : Fin d) :
    lineValue hd (liftDataOfResidueSolution r) lam jtilde i =
      (((F lam jtilde i : Fin d) : ℕ) : ZMod d) := by
  have hline := r.line_eq lam jtilde i
  simp only [lineCell, lineTarget, lineValue, liftDataOfResidueSolution,
    intRepresentative_cast hd] at hline ⊢
  linear_combination hline

/-- A modular solution realizes the requested raw family literally. -/
theorem inducedFamily_liftDataOfResidueSolution {d : ℕ} {hd : d ≠ 0}
    {F : RawLineFamily d} (r : ResidueSolution hd F) :
    inducedFamily hd (liftDataOfResidueSolution r) = F := by
  funext lam jtilde i
  apply Fin.ext
  have hcast := inducedFamily_formula hd (liftDataOfResidueSolution r) lam jtilde i
  rw [lineValue_liftDataOfResidueSolution r lam jtilde i] at hcast
  let : NeZero d := ⟨hd⟩
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt
      (inducedFamily hd (liftDataOfResidueSolution r) lam jtilde i).isLt,
    ZMod.val_natCast_of_lt (F lam jtilde i).isLt] at hv
  exact hv

/-- The preserving representative choice still realizes the same family. -/
theorem inducedFamily_liftDataOfResidueSolutionPreserving
    {d : ℕ} {hd : d ≠ 0} {F : RawLineFamily d}
    (r : ResidueSolution hd F) (old : LiftData d)
    (Q : Fin d → Fin d → Prop)
    (hk : ∀ i j, Q i j → (old.k i j : ZMod d) = r.k i j)
    (hl : ∀ i j, Q i j → (old.l i j : ZMod d) = r.l i j) :
    inducedFamily hd (liftDataOfResidueSolutionPreserving r old Q) = F := by
  funext lam jtilde i
  apply Fin.ext
  have hline := r.line_eq lam jtilde i
  have hvalue :
      lineValue hd (liftDataOfResidueSolutionPreserving r old Q) lam jtilde i =
        (((F lam jtilde i : Fin d) : ℕ) : ZMod d) := by
    simp only [lineCell, lineTarget, lineValue] at hline ⊢
    rw [liftDataOfResidueSolutionPreserving_cast_k r old Q hk,
      liftDataOfResidueSolutionPreserving_cast_l r old Q hl]
    linear_combination hline
  have hcast := inducedFamily_formula hd
    (liftDataOfResidueSolutionPreserving r old Q) lam jtilde i
  rw [hvalue] at hcast
  let : NeZero d := ⟨hd⟩
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt
      (inducedFamily hd (liftDataOfResidueSolutionPreserving r old Q) lam jtilde i).isLt,
    ZMod.val_natCast_of_lt (F lam jtilde i).isLt] at hv
  exact hv

/-- A consistent family is realized literally by integral lift data. -/
theorem exists_liftData_of_consistent {d : ℕ} (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d) (F : RawLineFamily d)
    (hF : FamilyConsistent F) (lam₀ : Root d)
    (hdetect : PrimaryReductionsDetect d) (hsigns : RootSignsCovered lam₀) :
    ∃ s : LiftData d, inducedFamily hd s = F := by
  let r := residueSolution_of_consistent hd hodd F hF lam₀ hdetect hsigns
  exact ⟨liftDataOfResidueSolution r,
    inducedFamily_liftDataOfResidueSolution r⟩

/-- The complete reconstruction statement: a good consistent family over an
odd modulus with complete primary components is realized by separated lift
data.  `ConflictRootLineProperty` is the exact root-line consequence needed
to turn goodness into separation. -/
theorem exists_separated_liftData_of_good_consistent {d : ℕ} (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d) (C : CompleteComponents d)
    (hrootLine : Separation.ConflictRootLineProperty d)
    (F : RawLineFamily d) (hgood : FamilyGood F) (hcons : FamilyConsistent F)
    (lam₀ : Root d) :
    ∃ s : LiftData d, inducedFamily hd s = F ∧ s.Separated := by
  obtain ⟨s, hsF⟩ := exists_liftData_of_consistent hd hodd F hcons lam₀
    (primaryReductionsDetect_of_complete C hd) (rootSignsCovered_of_odd hodd lam₀)
  have hsGood : FamilyGood (inducedFamily hd s) := by
    rw [hsF]
    exact hgood
  exact ⟨s, hsF,
    Separation.separated_of_inducedFamily_good hd hodd hrootLine s hsGood⟩

end

end Erdos215.Selector.Reconstruct

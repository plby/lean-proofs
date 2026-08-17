/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorModular

/-!
The line-family interface for the nontrivial-prime part of the
Jackson--Mauldin selector construction.

This file keeps formulas (4.4) and (4.6) literal.  Line maps are constructed
as raw functions; goodness packages them into permutations only afterwards.
-/

namespace Erdos215.Selector.Final

open Erdos215.Selector
open Erdos215.Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

def rootVal {d : ℕ} (_hd : d ≠ 0) (lam : Root d) : ℕ := by
  letI : NeZero d := ⟨_hd⟩
  exact (lam : ZMod d).val

@[simp] lemma rootVal_cast {d : ℕ} (hd : d ≠ 0) (lam : Root d) :
    (rootVal hd lam : ZMod d) = lam := by
  let _ : NeZero d := ⟨hd⟩
  exact ZMod.natCast_zmod_val _

/-- The canonical residue `j` on the line with root `lam` and label `jtilde`. -/
def lineResidue {d : ℕ} (hd : d ≠ 0) (lam : Root d) (jtilde i : Fin d) : Fin d :=
  ⟨((jtilde : ℕ) + rootVal hd lam * (i : ℕ)) % d,
    Nat.mod_lt _ (Nat.pos_of_ne_zero hd)⟩

/-- The canonical integer `m` in
`j = jtilde + lam * i - m*d`. -/
def lineCarry {d : ℕ} (hd : d ≠ 0) (lam : Root d) (jtilde i : Fin d) : ℕ :=
  ((jtilde : ℕ) + rootVal hd lam * (i : ℕ)) / d

@[simp] lemma lineResidue_cast {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (jtilde i : Fin d) :
    ((lineResidue hd lam jtilde i : ℕ) : ZMod d) =
      ((jtilde : ℕ) : ZMod d) + (lam : ZMod d) * ((i : ℕ) : ZMod d) := by
  let _ : NeZero d := ⟨hd⟩
  change (((((jtilde : ℕ) + rootVal hd lam * (i : ℕ)) % d) : ℕ) : ZMod d) = _
  rw [ZMod.natCast_mod]
  push_cast
  rw [rootVal_cast]

/-- Equation (4.5) makes the two canonical line residues literally equal. -/
lemma lineResidue_eq_of_relation {d : ℕ} (hd : d ≠ 0) (lam₁ lam₂ : Root d)
    (j₁ j₂ i : Fin d)
    (hline : ((i : ℕ) : ZMod d) * ((lam₁ : ZMod d) - lam₂) =
      -(((j₁ : ℕ) : ZMod d) - ((j₂ : ℕ) : ZMod d))) :
    lineResidue hd lam₁ j₁ i = lineResidue hd lam₂ j₂ i := by
  let _ : NeZero d := ⟨hd⟩
  apply Fin.ext
  have hsum :
      ((j₁ : ℕ) : ZMod d) + (lam₁ : ZMod d) * ((i : ℕ) : ZMod d) =
        ((j₂ : ℕ) : ZMod d) + (lam₂ : ZMod d) * ((i : ℕ) : ZMod d) := by
    linear_combination hline
  have hcast :
      (((lineResidue hd lam₁ j₁ i : Fin d) : ℕ) : ZMod d) =
        (((lineResidue hd lam₂ j₂ i : Fin d) : ℕ) : ZMod d) := by
    rw [lineResidue_cast, lineResidue_cast, hsum]
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt (lineResidue hd lam₁ j₁ i).isLt,
    ZMod.val_natCast_of_lt (lineResidue hd lam₂ j₂ i).isLt] at hv
  exact hv

lemma lineResidue_add_mul_lineCarry {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (jtilde i : Fin d) :
    (lineResidue hd lam jtilde i : ℕ) + d * lineCarry hd lam jtilde i =
      (jtilde : ℕ) + rootVal hd lam * (i : ℕ) := by
  change (((jtilde : ℕ) + rootVal hd lam * (i : ℕ)) % d) +
      d * (((jtilde : ℕ) + rootVal hd lam * (i : ℕ)) / d) = _
  exact Nat.mod_add_div _ _

lemma lineResidue_int_equation {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (jtilde i : Fin d) :
    ((lineResidue hd lam jtilde i : ℕ) : ℤ) =
      (jtilde : ℕ) + (rootVal hd lam : ℤ) * (i : ℕ) -
        lineCarry hd lam jtilde i * d := by
  have h := lineResidue_add_mul_lineCarry hd lam jtilde i
  rw [mul_comm (lineCarry hd lam jtilde i : ℤ) (d : ℤ)]
  omega

/-- Subtracting the two canonical line equations gives the carry identity
used in the full substitution proof of (4.6). -/
lemma lineCarry_sub_relation {d : ℕ} (hd : d ≠ 0) (lam₁ lam₂ : Root d)
    (j₁ j₂ i : Fin d)
    (hj : lineResidue hd lam₁ j₁ i = lineResidue hd lam₂ j₂ i) :
    (d : ℤ) * ((lineCarry hd lam₁ j₁ i : ℤ) - lineCarry hd lam₂ j₂ i) =
      (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) +
        ((rootVal hd lam₁ : ℤ) - rootVal hd lam₂) * (i : ℕ) := by
  have h₁ := lineResidue_int_equation hd lam₁ j₁ i
  have h₂ := lineResidue_int_equation hd lam₂ j₂ i
  rw [hj] at h₁
  linear_combination h₁ - h₂

/-- A localized quotient of an actual multiple of the global modulus is the
corresponding integer, modulo the selected primary component. -/
lemma PrimaryComponent.localQuotient_mul_modulus {d : ℕ} (c : PrimaryComponent d)
    (a : ℤ) : c.localQuotient ((d : ℤ) * a) = (a : ZMod c.q) := by
  simp only [PrimaryComponent.localQuotient, localizedQuotient]
  have hcast : (d : ℤ) = (c.q : ℤ) * c.D := by
    exact_mod_cast c.factor_q
  rw [hcast, mul_assoc, Int.mul_ediv_cancel_left _ (Int.ofNat_ne_zero.mpr c.q_ne_zero)]
  push_cast
  calc
    ((c.D : ZMod c.q) * (a : ZMod c.q)) * (c.D : ZMod c.q)⁻¹ =
        (a : ZMod c.q) * ((c.D : ZMod c.q)⁻¹ * c.D) := by ring
    _ = (a : ZMod c.q) := by rw [ZMod.inv_mul_of_unit _ c.isUnit_D, mul_one]

lemma PrimaryComponent.localQuotient_add {d : ℕ} (c : PrimaryComponent d) (x y : ℤ)
    (hx : (c.q : ℤ) ∣ x) (hy : (c.q : ℤ) ∣ y) :
    c.localQuotient (x + y) = c.localQuotient x + c.localQuotient y := by
  exact localizedQuotient_add c.q c.q_ne_zero _ x y hx hy

lemma PrimaryComponent.localQuotient_mul_right {d : ℕ} (c : PrimaryComponent d)
    (x a : ℤ) (hx : (c.q : ℤ) ∣ x) :
    c.localQuotient (x * a) = c.localQuotient x * (a : ZMod c.q) := by
  rcases hx with ⟨b, rfl⟩
  simp only [PrimaryComponent.localQuotient]
  rw [mul_assoc, localizedQuotient_mul c.q c.q_ne_zero,
    localizedQuotient_mul c.q c.q_ne_zero]
  push_cast
  ring

/-- Difference of the two exact root quotients before modular division by
two. -/
lemma rootQuotient_sub_relation {d : ℕ} (hd : d ≠ 0) (lam₁ lam₂ : Root d) :
    (d : ℤ) * (((rootQuotient lam₁ : ℕ) : ℤ) - rootQuotient lam₂) =
      ((rootVal hd lam₁ : ℤ) - rootVal hd lam₂) *
        ((rootVal hd lam₁ : ℤ) + rootVal hd lam₂) := by
  have h₁ : (d : ℤ) * (rootQuotient lam₁ : ℕ) =
      1 + (rootVal hd lam₁ : ℤ) ^ 2 := by
    exact_mod_cast mul_rootQuotient hd lam₁
  have h₂ : (d : ℤ) * (rootQuotient lam₂ : ℕ) =
      1 + (rootVal hd lam₂ : ℤ) ^ 2 := by
    exact_mod_cast mul_rootQuotient hd lam₂
  linear_combination h₁ - h₂

/-- Primary-component form of the `h_d` subtraction in the consistency
calculation. -/
lemma two_mul_reduce_rootPhase_sub {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (c : PrimaryComponent d) (lam₁ lam₂ : Root d) :
    (2 : ZMod c.q) * c.reduce (rootPhase lam₁ - rootPhase lam₂) =
      c.localQuotient
        (((rootVal hd lam₁ : ℤ) - rootVal hd lam₂) *
          ((rootVal hd lam₁ : ℤ) + rootVal hd lam₂)) := by
  have h₁ := congrArg c.reduce (two_mul_rootPhase hodd lam₁)
  have h₂ := congrArg c.reduce (two_mul_rootPhase hodd lam₂)
  simp only [map_mul, map_ofNat, PrimaryComponent.reduce_natCast] at h₁ h₂
  rw [PrimaryComponent.reduce_sub]
  have hphase :
      (2 : ZMod c.q) * (c.reduce (rootPhase lam₁) - c.reduce (rootPhase lam₂)) =
        (((rootQuotient lam₁ : ℕ) : ℤ) - rootQuotient lam₂ : ℤ) := by
    push_cast
    linear_combination h₁ - h₂
  rw [hphase]
  have hroot := rootQuotient_sub_relation hd lam₁ lam₂
  rw [← hroot, Erdos215.Selector.Final.PrimaryComponent.localQuotient_mul_modulus]

lemma PrimaryComponent.reduce_root_eq_rootVal {d : ℕ} (hd : d ≠ 0)
    (c : PrimaryComponent d) (lam : Root d) :
    c.reduce lam = (rootVal hd lam : ZMod c.q) := by
  rw [← rootVal_cast hd lam]
  exact c.reduce_natCast _

/-- The two divisibilities implicit in the localized quotient in (4.6). -/
lemma PrimaryComponent.relation_divisibility {d : ℕ} (hd : d ≠ 0)
    (c : PrimaryComponent d) (lam₁ lam₂ : Root d) (j₁ j₂ i : Fin d)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hline : ((i : ℕ) : ZMod d) * ((lam₁ : ZMod d) - lam₂) =
      -(((j₁ : ℕ) : ZMod d) - ((j₂ : ℕ) : ZMod d))) :
    (c.q : ℤ) ∣ (rootVal hd lam₁ : ℤ) - rootVal hd lam₂ ∧
      (c.q : ℤ) ∣ (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  have hrv₁ := Erdos215.Selector.Final.PrimaryComponent.reduce_root_eq_rootVal hd c lam₁
  have hrv₂ := Erdos215.Selector.Final.PrimaryComponent.reduce_root_eq_rootVal hd c lam₂
  have hdelta0 :
      (((rootVal hd lam₁ : ℤ) - rootVal hd lam₂ : ℤ) : ZMod c.q) = 0 := by
    push_cast
    rw [← hrv₁, ← hrv₂, hr, sub_self]
  have hdelta : (c.q : ℤ) ∣ (rootVal hd lam₁ : ℤ) - rootVal hd lam₂ :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hdelta0
  constructor
  · exact hdelta
  have hred := congrArg c.reduce hline
  simp only [map_mul, map_sub, map_neg, PrimaryComponent.reduce_natCast] at hred
  rw [hr, sub_self, mul_zero] at hred
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  linear_combination hred

/-- The right side of the source's line formula (4.4). -/
def lineValue {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (lam : Root d)
    (jtilde i : Fin d) : ZMod d :=
  let j := lineResidue hd lam jtilde i
  (s.k i j : ZMod d) + (lam : ZMod d) * (s.l i j : ZMod d) -
      (lam : ZMod d) * (lineCarry hd lam jtilde i : ZMod d) +
    rootPhase lam * (i : ℕ)

/-- The raw induced line map. -/
def inducedLineMap {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (lam : Root d)
    (jtilde : Fin d) : Fin d → Fin d := by
  let _ : NeZero d := ⟨hd⟩
  exact fun i ↦ ⟨(lineValue hd s lam jtilde i).val,
    ZMod.val_lt (lineValue hd s lam jtilde i)⟩

@[simp] lemma inducedLineMap_cast {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (lam : Root d) (jtilde i : Fin d) :
    ((inducedLineMap hd s lam jtilde i : ℕ) : ZMod d) = lineValue hd s lam jtilde i := by
  let _ : NeZero d := ⟨hd⟩
  exact ZMod.natCast_zmod_val _

/-- A raw family indexed by every root and every line label. -/
abbrev RawLineFamily (d : ℕ) := Root d → Fin d → Fin d → Fin d

def FamilyGood {d : ℕ} (F : RawLineFamily d) : Prop :=
  ∀ lam jtilde, GoodMap d (F lam jtilde)

/-- Componentwise form of the source's consistency equation (4.6). -/
def FamilyConsistent {d : ℕ} (F : RawLineFamily d) : Prop :=
  ∀ (c : PrimaryComponent d) (lam₁ lam₂ : Root d) (j₁ j₂ i : Fin d),
    c.reduce lam₁ = c.reduce lam₂ →
    ((i : ℕ) : ZMod d) * ((lam₁ : ZMod d) - lam₂) =
        -(((j₁ : ℕ) : ZMod d) - ((j₂ : ℕ) : ZMod d)) →
    c.reduce (((F lam₁ j₁ i : Fin d) : ℕ) : ZMod d) -
        c.reduce (((F lam₂ j₂ i : Fin d) : ℕ) : ZMod d) =
      -(c.reduce lam₁) * c.localQuotient (((j₁ : ℕ) : ℤ) - (j₂ : ℕ))

/-- Package a good raw family into actual permutations. -/
noncomputable def FamilyGood.toPermFamily {d : ℕ} (F : RawLineFamily d)
    (hF : FamilyGood F) : Root d → Fin d → Equiv.Perm (Fin d) :=
  fun lam jtilde ↦ GoodMap.toPerm (F lam jtilde) (hF lam jtilde)

@[simp] lemma FamilyGood.toPermFamily_apply {d : ℕ} (F : RawLineFamily d)
    (hF : FamilyGood F) (lam : Root d) (jtilde i : Fin d) :
    hF.toPermFamily F lam jtilde i = F lam jtilde i := rfl

theorem FamilyGood.toPermFamily_good {d : ℕ} (F : RawLineFamily d)
    (hF : FamilyGood F) (lam : Root d) (jtilde : Fin d) :
    GoodPerm d (hF.toPermFamily F lam jtilde) :=
  GoodMap.goodPerm_toPerm (F lam jtilde) (hF lam jtilde)

/-- The line family canonically induced by a finite selector. -/
def inducedFamily {d : ℕ} (hd : d ≠ 0) (s : LiftData d) : RawLineFamily d :=
  fun lam jtilde ↦ inducedLineMap hd s lam jtilde

/-- Formula (4.4) holds definitionally for the induced raw family. -/
theorem inducedFamily_formula {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (lam : Root d) (jtilde i : Fin d) :
    (((inducedFamily hd s lam jtilde i : Fin d) : ℕ) : ZMod d) =
      lineValue hd s lam jtilde i := by
  exact inducedLineMap_cast hd s lam jtilde i

/-- The family induced by a finite selector satisfies the exact localized
consistency identity (4.6) on every primary component. -/
theorem inducedFamily_consistent {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (s : LiftData d) : FamilyConsistent (inducedFamily hd s) := by
  intro c lam₁ lam₂ j₁ j₂ i hr hline
  have hj := lineResidue_eq_of_relation hd lam₁ lam₂ j₁ j₂ i hline
  have hdiv := Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
    hd c lam₁ lam₂ j₁ j₂ i hr hline
  let delta : ℤ := (rootVal hd lam₁ : ℤ) - rootVal hd lam₂
  let J : ℤ := ((j₁ : ℕ) : ℤ) - (j₂ : ℕ)
  let mdelta : ℤ :=
    (lineCarry hd lam₁ j₁ i : ℤ) - lineCarry hd lam₂ j₂ i
  have hdelta : (c.q : ℤ) ∣ delta := by
    simpa [delta] using hdiv.1
  have hJ : (c.q : ℤ) ∣ J := by
    simpa [J] using hdiv.2
  have hdeltai : (c.q : ℤ) ∣ delta * (i : ℕ) :=
    dvd_mul_of_dvd_left hdelta _
  have hcarry := lineCarry_sub_relation hd lam₁ lam₂ j₁ j₂ i hj
  have hcarryLocal :
      (mdelta : ZMod c.q) =
        c.localQuotient J + c.localQuotient delta * ((i : ℕ) : ZMod c.q) := by
    rw [← Erdos215.Selector.Final.PrimaryComponent.localQuotient_mul_modulus c mdelta]
    rw [show (d : ℤ) * mdelta = J + delta * (i : ℕ) by
      simpa [mdelta, J, delta] using hcarry]
    rw [Erdos215.Selector.Final.PrimaryComponent.localQuotient_add c J
      (delta * (i : ℕ)) hJ hdeltai]
    rw [Erdos215.Selector.Final.PrimaryComponent.localQuotient_mul_right c delta
      ((i : ℕ) : ℤ) hdelta]
    push_cast
    ring_nf
  have hphase := two_mul_reduce_rootPhase_sub hd hodd c lam₁ lam₂
  have hphase' :
      (2 : ZMod c.q) * c.reduce (rootPhase lam₁ - rootPhase lam₂) =
        c.localQuotient delta *
          (((rootVal hd lam₁ : ℤ) + rootVal hd lam₂ : ℤ) : ZMod c.q) := by
    rw [hphase]
    exact Erdos215.Selector.Final.PrimaryComponent.localQuotient_mul_right c delta
      ((rootVal hd lam₁ : ℤ) + rootVal hd lam₂) hdelta
  have hsum :
      (((rootVal hd lam₁ : ℤ) + rootVal hd lam₂ : ℤ) : ZMod c.q) =
        (2 : ZMod c.q) * c.reduce lam₁ := by
    push_cast
    rw [← Erdos215.Selector.Final.PrimaryComponent.reduce_root_eq_rootVal hd c lam₁,
      ← Erdos215.Selector.Final.PrimaryComponent.reduce_root_eq_rootVal hd c lam₂, hr]
    ring
  rw [hsum] at hphase'
  have hleft :
      c.reduce (((inducedFamily hd s lam₁ j₁ i : Fin d) : ℕ) : ZMod d) -
          c.reduce (((inducedFamily hd s lam₂ j₂ i : Fin d) : ℕ) : ZMod d) =
        -(c.reduce lam₁) * (mdelta : ZMod c.q) +
          c.reduce (rootPhase lam₁ - rootPhase lam₂) * ((i : ℕ) : ZMod c.q) := by
    rw [inducedFamily_formula, inducedFamily_formula]
    simp only [lineValue, map_add, map_sub, map_mul,
      PrimaryComponent.reduce_natCast]
    rw [hj, hr]
    simp only [mdelta, Int.cast_sub, Int.cast_natCast]
    ring
  rw [hleft]
  have h2coprime : Nat.Coprime 2 c.q := hodd.of_dvd_right c.q_dvd
  have h2unit : IsUnit (2 : ZMod c.q) := by
    change IsUnit (((2 : ℕ) : ZMod c.q))
    rw [ZMod.isUnit_iff_coprime]
    exact h2coprime
  apply h2unit.mul_left_cancel
  linear_combination
    -(2 : ZMod c.q) * (c.reduce lam₁) * hcarryLocal +
      (((i : ℕ) : ZMod c.q)) * hphase'

end


end Erdos215.Selector.Final

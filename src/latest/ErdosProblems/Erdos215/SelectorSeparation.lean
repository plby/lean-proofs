/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorFinal
import ErdosProblems.Erdos215.SelectorComponents

/-!
The separation half of the Jackson--Mauldin finite selector reconstruction.

The only denominator-specific input is `ConflictRootLineProperty d`.  It is the exact
Hensel/CRT consequence supplied by the complete family of nontrivial primary
components.  Its antecedent is the *full* conflict divisibility, including
the cross term: the weaker condition `d ∣ A^2+B^2` does not suffice when a
coordinate difference is only partially divisible by a primary factor.
Keeping this hypothesis explicit prevents the argument below from silently
claiming the result for arbitrary moduli.
-/

namespace Erdos215.Selector.Separation

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The exact local-primary/Hensel/CRT input needed by the separation proof.
The integers `K,M` are the differences of the two integral lifts. -/
def ConflictRootLineProperty (d : ℕ) : Prop :=
  ∀ A B K M : ℤ,
    (d : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) →
    ∃ lam : Root d, (B : ZMod d) = (lam : ZMod d) * (A : ZMod d)

/-- Cancelling an integer from a divisibility by `d` leaves precisely the
source's capped-gcd quotient `d / gcd(d, |A|)`. -/
lemma survivingModulus_dvd_of_dvd_mul (d : ℕ) (hd : d ≠ 0) (A X : ℤ)
    (h : (d : ℤ) ∣ A * X) :
    (survivingModulus d A.natAbs : ℤ) ∣ X := by
  let g := Nat.gcd d A.natAbs
  let u := d / g
  let v := A.natAbs / g
  have hgpos : 0 < g := by
    exact Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hd)
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  have hgd : g ∣ d := Nat.gcd_dvd_left d A.natAbs
  have hgA : g ∣ A.natAbs := Nat.gcd_dvd_right d A.natAbs
  have hdu : g * u = d := by
    exact Nat.mul_div_cancel' hgd
  have hAv : g * v = A.natAbs := by
    exact Nat.mul_div_cancel' hgA
  have huv : u.Coprime v := by
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hAbs : (d : ℤ) ∣ (A.natAbs : ℤ) * X := by
    rcases Int.natAbs_eq A with hA | hA
    · have heq : A * X = (A.natAbs : ℤ) * X := congrArg (· * X) hA
      rw [← heq]
      exact h
    · have heq : A * X = -((A.natAbs : ℤ) * X) :=
        (congrArg (· * X) hA).trans (by ring)
      have hneg : (d : ℤ) ∣ -((A.natAbs : ℤ) * X) := by
        rw [← heq]
        exact h
      exact dvd_neg.mp hneg
  rcases hAbs with ⟨q, hq⟩
  have hcancel : (v : ℤ) * X = (u : ℤ) * q := by
    apply mul_left_cancel₀ hg0
    calc
      (g : ℤ) * ((v : ℤ) * X) = ((g * v : ℕ) : ℤ) * X := by
        push_cast
        ring
      _ = (A.natAbs : ℤ) * X := by rw [hAv]
      _ = (d : ℤ) * q := hq
      _ = (g : ℤ) * ((u : ℤ) * q) := by
        have hduZ : (g : ℤ) * (u : ℤ) = (d : ℤ) := by exact_mod_cast hdu
        rw [← hduZ]
        ring
  have hu_dvd : (u : ℤ) ∣ (v : ℤ) * X := ⟨q, hcancel⟩
  have hcop : IsCoprime (u : ℤ) (v : ℤ) := huv.isCoprime
  change (u : ℤ) ∣ X
  exact hcop.dvd_of_dvd_mul_left hu_dvd

/-- The label of the root line through a specified residue cell. -/
def lineLabel {d : ℕ} (hd : d ≠ 0) (lam : Root d) (i j : Fin d) : Fin d := by
  letI : NeZero d := ⟨hd⟩
  exact ⟨(((j : ℕ) : ZMod d) - (lam : ZMod d) * ((i : ℕ) : ZMod d)).val,
    ZMod.val_lt _⟩

@[simp] lemma lineLabel_cast {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (i j : Fin d) :
    (((lineLabel hd lam i j : Fin d) : ℕ) : ZMod d) =
      ((j : ℕ) : ZMod d) - (lam : ZMod d) * ((i : ℕ) : ZMod d) := by
  let : NeZero d := ⟨hd⟩
  exact ZMod.natCast_zmod_val _

lemma fin_eq_of_zmod_cast_eq {d : ℕ} (hd : d ≠ 0) (x y : Fin d)
    (h : (((x : Fin d) : ℕ) : ZMod d) = (((y : Fin d) : ℕ) : ZMod d)) :
    x = y := by
  let : NeZero d := ⟨hd⟩
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_natCast_of_lt x.isLt, ZMod.val_natCast_of_lt y.isLt] using hv

/-- The canonical line label really gives the chosen cell at its input. -/
lemma lineResidue_lineLabel {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (i j : Fin d) :
    lineResidue hd lam (lineLabel hd lam i j) i = j := by
  apply fin_eq_of_zmod_cast_eq hd
  rw [lineResidue_cast, lineLabel_cast]
  ring

/-- If two cells satisfy `B = lam*A` modulo `d`, the line label obtained from
the first cell also passes through the second. -/
lemma lineResidue_lineLabel_second {d : ℕ} (hd : d ≠ 0) (lam : Root d)
    (i₁ j₁ i₂ j₂ : Fin d)
    (hline :
      ((((j₁ : ℕ) : ℤ) - (j₂ : ℕ) : ℤ) : ZMod d) =
        (lam : ZMod d) *
          (((((i₁ : ℕ) : ℤ) - (i₂ : ℕ) : ℤ)) : ZMod d)) :
    lineResidue hd lam (lineLabel hd lam i₁ j₁) i₂ = j₂ := by
  apply fin_eq_of_zmod_cast_eq hd
  rw [lineResidue_cast, lineLabel_cast]
  push_cast at hline ⊢
  linear_combination hline

/-- Once a conflict pair has been placed on a root line, the full conflict
divisibility forces the two line-map values to agree modulo the precise
surviving modulus.  This is the cancellation calculation following (4.7). -/
lemma survivingModulus_dvd_inducedFamily_sub_of_conflict
    {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d) (s : LiftData d)
    (i₁ j₁ i₂ j₂ : Fin d) (lam : Root d)
    (hline :
      ((((j₁ : ℕ) : ℤ) - (j₂ : ℕ) : ℤ) : ZMod d) =
        (lam : ZMod d) *
          (((((i₁ : ℕ) : ℤ) - (i₂ : ℕ) : ℤ)) : ZMod d))
    (hdiv : (d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂)) :
    (survivingModulus d (indexDiff i₁ i₂) : ℤ) ∣
      ((((inducedFamily hd s lam (lineLabel hd lam i₁ j₁) i₁ : Fin d) : ℕ) : ℤ) -
        (((inducedFamily hd s lam (lineLabel hd lam i₁ j₁) i₂ : Fin d) : ℕ) : ℤ)) := by
  let jt := lineLabel hd lam i₁ j₁
  let A : ℤ := ((i₁ : ℕ) : ℤ) - (i₂ : ℕ)
  let B : ℤ := ((j₁ : ℕ) : ℤ) - (j₂ : ℕ)
  let K : ℤ := s.k i₁ j₁ - s.k i₂ j₂
  let M : ℤ := s.l i₁ j₁ - s.l i₂ j₂
  let c : ℤ := (lineCarry hd lam jt i₁ : ℕ) - lineCarry hd lam jt i₂
  let L : ℤ := rootVal hd lam
  let R : ℤ := rootQuotient lam
  let H : ℤ := ZMod.val (rootPhase lam)
  let T : ℤ := K + L * M - L * c
  let E : ℤ := A * H + T
  let o₁ : Fin d := inducedFamily hd s lam jt i₁
  let o₂ : Fin d := inducedFamily hd s lam jt i₂
  let O : ℤ := ((o₁ : ℕ) : ℤ) - (o₂ : ℕ)
  have hcell₁ : lineResidue hd lam jt i₁ = j₁ := lineResidue_lineLabel hd lam i₁ j₁
  have hcell₂ : lineResidue hd lam jt i₂ = j₂ :=
    lineResidue_lineLabel_second hd lam i₁ j₁ i₂ j₂ hline
  have hj₁ := lineResidue_int_equation hd lam jt i₁
  have hj₂ := lineResidue_int_equation hd lam jt i₂
  rw [hcell₁] at hj₁
  rw [hcell₂] at hj₂
  have hB : B = L * A - c * d := by
    dsimp only [A, B, L, c, jt]
    linear_combination hj₁ - hj₂
  have hrootN := mul_rootQuotient hd lam
  have hroot : (d : ℤ) * R = 1 + L ^ 2 := by
    dsimp only [R, L]
    exact_mod_cast hrootN
  have hphaseCast : (H : ZMod d) = rootPhase lam := by
    let : NeZero d := ⟨hd⟩
    dsimp only [H]
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (rootPhase lam)
  have hphaseEq : ((2 * H : ℤ) : ZMod d) = (R : ZMod d) := by
    calc
      ((2 * H : ℤ) : ZMod d) = (2 : ZMod d) * rootPhase lam := by
        push_cast
        rw [hphaseCast]
      _ = (rootQuotient lam : ZMod d) := two_mul_rootPhase hodd lam
      _ = (R : ZMod d) := by simp only [R, Int.cast_natCast]
  have hphaseD : (d : ℤ) ∣ R - 2 * H := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (2 * H) R d).mp hphaseEq
  rcases hdiv with ⟨q, hq⟩
  change A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) = (d : ℤ) ^ 2 * q at hq
  have hd0Z : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  have hinside : A * (A * R + 2 * T) + d * (c ^ 2 - 2 * c * M) = d * q := by
    apply mul_left_cancel₀ hd0Z
    calc
      (d : ℤ) * (A * (A * R + 2 * T) + d * (c ^ 2 - 2 * c * M)) =
          A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := by
            rw [hB]
            dsimp only [T]
            linear_combination A ^ 2 * hroot
      _ = (d : ℤ) ^ 2 * q := hq
      _ = (d : ℤ) * (d * q) := by ring
  have hAR : (d : ℤ) ∣ A * (A * R + 2 * T) := by
    refine ⟨q - (c ^ 2 - 2 * c * M), ?_⟩
    linear_combination hinside
  rcases hAR with ⟨q₁, hq₁⟩
  rcases hphaseD with ⟨q₂, hq₂⟩
  have htwo : (d : ℤ) ∣ 2 * (A * E) := by
    refine ⟨q₁ - A ^ 2 * q₂, ?_⟩
    dsimp only [E]
    linear_combination hq₁ - A ^ 2 * hq₂
  have hAE : (d : ℤ) ∣ A * E := by
    have htwo' : (d : ℤ) ∣ (2 : ℤ) * (A * E) := by simpa [mul_assoc] using htwo
    have hcop : IsCoprime (d : ℤ) (2 : ℤ) := hodd.symm.isCoprime
    exact hcop.dvd_of_dvd_mul_left htwo'
  have hSE : (survivingModulus d A.natAbs : ℤ) ∣ E :=
    survivingModulus_dvd_of_dvd_mul d hd A E hAE
  have hf₁ := inducedFamily_formula hd s lam jt i₁
  have hf₂ := inducedFamily_formula hd s lam jt i₂
  simp only [lineValue] at hf₁ hf₂
  rw [hcell₁] at hf₁
  rw [hcell₂] at hf₂
  have hrootValCast : (L : ZMod d) = lam := by
    simpa only [L, Int.cast_natCast] using rootVal_cast hd lam
  have hout : (O : ZMod d) = (E : ZMod d) := by
    dsimp only [O, o₁, o₂]
    push_cast
    rw [hf₁, hf₂]
    rw [← hrootValCast, ← hphaseCast]
    dsimp only [E, T, K, M, A, c, jt]
    push_cast
    ring
  have hdEO : (d : ℤ) ∣ E - O :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub O E d).mp hout
  have hSdNat : survivingModulus d A.natAbs ∣ d := survivingModulus_dvd d A.natAbs
  have hSd : (survivingModulus d A.natAbs : ℤ) ∣ (d : ℤ) := by
    exact_mod_cast hSdNat
  have hSEO : (survivingModulus d A.natAbs : ℤ) ∣ E - O := hSd.trans hdEO
  rcases hSE with ⟨a, ha⟩
  rcases hSEO with ⟨b, hb⟩
  change (survivingModulus d (indexDiff i₁ i₂) : ℤ) ∣ O
  have hindex : indexDiff i₁ i₂ = A.natAbs := rfl
  rw [hindex]
  refine ⟨a - b, ?_⟩
  linear_combination ha - hb

/-- Goodness of the induced family rules out every conflict, hence gives the
finite selector condition `(*)_d`. -/
theorem separated_of_inducedFamily_good {d : ℕ} (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d) (hroot : ConflictRootLineProperty d)
    (s : LiftData d) (hgood : FamilyGood (inducedFamily hd s)) :
    s.Separated := by
  intro i₁ j₁ i₂ j₂ hne hdiv
  let A : ℤ := ((i₁ : ℕ) : ℤ) - (i₂ : ℕ)
  let B : ℤ := ((j₁ : ℕ) : ℤ) - (j₂ : ℕ)
  let K : ℤ := s.k i₁ j₁ - s.k i₂ j₂
  let M : ℤ := s.l i₁ j₁ - s.l i₂ j₂
  have hfull : (d : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := by
    simpa only [conflictNumerator, A, B, K, M] using hdiv
  obtain ⟨lam, hline⟩ := hroot A B K M hfull
  let jt := lineLabel hd lam i₁ j₁
  have hcell₁ : lineResidue hd lam jt i₁ = j₁ := lineResidue_lineLabel hd lam i₁ j₁
  have hcell₂ : lineResidue hd lam jt i₂ = j₂ := by
    apply lineResidue_lineLabel_second hd lam i₁ j₁ i₂ j₂
    exact hline
  have hi : i₁ ≠ i₂ := by
    intro hii
    subst i₂
    have hjj : j₁ = j₂ := hcell₁.symm.trans hcell₂
    exact hne (Prod.ext rfl hjj)
  apply hgood lam jt i₁ i₂ hi
  exact survivingModulus_dvd_inducedFamily_sub_of_conflict
    hd hodd s i₁ j₁ i₂ j₂ lam hline hdiv

/-- Rewrite-friendly form used after the reconstruction module has shown
that a chosen lift realizes a prescribed good family. -/
theorem separated_of_inducedFamily_eq_good {d : ℕ} (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d) (hroot : ConflictRootLineProperty d)
    (s : LiftData d) {F : RawLineFamily d} (hrealize : inducedFamily hd s = F)
    (hgood : FamilyGood F) : s.Separated := by
  apply separated_of_inducedFamily_good hd hodd hroot s
  rw [hrealize]
  exact hgood

end

end Erdos215.Selector.Separation

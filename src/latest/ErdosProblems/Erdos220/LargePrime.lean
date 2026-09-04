/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# The large-prime occupancy bound for Erdős problem 220

This file proves the finite ``one forbidden residue per prime'' inequality
used in the Montgomery--Vaughan argument.  The proof is entirely finite.  Its
core is an induction over the prime coordinates, with Bernoulli's inequality
providing the induction step.
-/

namespace Erdos220
namespace LargePrime

open scoped BigOperators
open Finset

universe u

/-- A recursively presented product of finite residue spaces. -/
def Config : List ℕ → Type
  | [] => Unit
  | p :: ps => Fin p × Config ps

instance configFinite (ps : List ℕ) : Finite (Config ps) := by
  induction ps with
  | nil => exact Finite.of_fintype Unit
  | cons p ps ih => simpa [Config] using inferInstanceAs (Finite (Fin p × Config ps))

@[simp] theorem natCard_config : ∀ ps : List ℕ, Nat.card (Config ps) = ps.prod
  | [] => by simp [Config]
  | p :: ps => by simp [Config, Nat.card_prod, natCard_config ps]

/-- At each coordinate, every label has its own forbidden residue. -/
inductive Forbidden (α : Type u) : List ℕ → Type (u + 1)
  | nil : Forbidden α []
  | cons {p : ℕ} {ps : List ℕ} (head : α ↪ Fin p) (tail : Forbidden α ps) :
      Forbidden α (p :: ps)

namespace Forbidden

/-- Pull a forbidden-residue family back along an embedding of labels. -/
def comap {α β : Type*} (e : β ↪ α) : {ps : List ℕ} → Forbidden α ps → Forbidden β ps
  | [], .nil => .nil
  | _ :: _, .cons head tail =>
      .cons ⟨fun b => head (e b), head.injective.comp e.injective⟩ (tail.comap e)

/-- A configuration hits a label if one coordinate equals its forbidden residue. -/
def Hit {α : Type*} : {ps : List ℕ} → Forbidden α ps → Config ps → α → Prop
  | [], .nil, _, _ => False
  | _ :: _, .cons head tail, x, a => x.1 = head a ∨ tail.Hit x.2 a

@[simp] theorem hit_comap {α β : Type*} {ps : List ℕ} (e : β ↪ α)
    (f : Forbidden α ps) (x : Config ps) (b : β) :
    (f.comap e).Hit x b ↔ f.Hit x (e b) := by
  induction f with
  | nil => simp [comap, Hit]
  | cons head tail ih => simp [comap, Hit, ih]

end Forbidden

/-- Configurations which hit every label. -/
abbrev Covered {α : Type*} {ps : List ℕ} (f : Forbidden α ps) :=
  {x : Config ps // ∀ a, f.Hit x a}

/-- Number of configurations which hit every label. -/
noncomputable def coverCount {α : Type*} {ps : List ℕ} (f : Forbidden α ps) : ℕ :=
  Nat.card (Covered f)

/-- The probability that one fixed label is missed by every coordinate. -/
def avoidProb : List ℕ → ℚ
  | [] => 1
  | p :: ps => ((p - 1 : ℕ) : ℚ) / p * avoidProb ps

/-- Removing the head-forbidden label already hit by `y`. -/
def remainingEmbedding {α : Type*} {p : ℕ} (e : α ↪ Fin p) (y : Fin p) :
    {a : α // e a ≠ y} ↪ α := Function.Embedding.subtype _

/-- Splitting off the first coordinate identifies a covered configuration
with a first residue and a tail configuration covering all labels not already
hit by that residue. -/
noncomputable def coveredConsEquiv {α : Type*} {p : ℕ} {ps : List ℕ}
    (e : α ↪ Fin p) (f : Forbidden α ps) :
    Covered (.cons e f) ≃
      Σ y : Fin p, Covered (f.comap (remainingEmbedding e y)) where
  toFun x :=
    ⟨x.1.1, x.1.2, fun a => by
      rw [Forbidden.hit_comap]
      exact (x.2 a.1).resolve_left fun h => a.2 h.symm⟩
  invFun x :=
    ⟨(x.1, x.2.1), fun a => by
      by_cases h : e a = x.1
      · exact Or.inl h.symm
      · exact Or.inr ((Forbidden.hit_comap (remainingEmbedding e x.1) f x.2.1
          ⟨a, h⟩).mp (x.2.2 ⟨a, h⟩))⟩
  left_inv x := by ext <;> rfl
  right_inv x := by rcases x with ⟨y, x⟩; ext <;> rfl

@[simp] theorem coverCount_cons {α : Type*} [Fintype α] {p : ℕ} {ps : List ℕ}
    (e : α ↪ Fin p) (f : Forbidden α ps) :
    coverCount (.cons e f) =
      ∑ y : Fin p, coverCount (f.comap (remainingEmbedding e y)) := by
  classical
  rw [coverCount, Nat.card_congr (coveredConsEquiv e f), Nat.card_sigma]
  rfl

theorem natCard_remaining {α : Type*} [Fintype α] {p : ℕ}
    (e : α ↪ Fin p) (y : Fin p) :
    Nat.card {a : α // e a ≠ y} =
      if y ∈ Finset.univ.map e then Fintype.card α - 1 else Fintype.card α := by
  classical
  by_cases hy : y ∈ Finset.univ.map e
  · rw [Finset.mem_map] at hy
    obtain ⟨a, _ha, rfl⟩ := hy
    simp [Nat.card_eq_fintype_card, e.injective.eq_iff]
  · have hne : ∀ a, e a ≠ y := fun a h => hy (Finset.mem_map.mpr ⟨a, by simp, h⟩)
    simp [Nat.card_eq_fintype_card, hy, hne]

theorem card_range_embedding {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) :
    (Finset.univ.map e).card = Fintype.card α := by simp

/-- The exact two-level sum which occurs after exposing one coordinate. -/
theorem sum_pow_natCard_remaining {α : Type*} [Fintype α] {p : ℕ}
  (e : α ↪ Fin p) (q : ℚ) :
    (∑ y : Fin p, q ^ Nat.card {a : α // e a ≠ y}) =
      (Fintype.card α : ℚ) * q ^ (Fintype.card α - 1) +
        (p - Fintype.card α : ℕ) * q ^ Fintype.card α := by
  classical
  let R : Finset (Fin p) := Finset.univ.map e
  have hR : R.card = Fintype.card α := card_range_embedding e
  have hin :
      (∑ x ∈ (Finset.univ : Finset (Fin p)) with x ∈ R,
          q ^ Nat.card {a : α // e a ≠ x}) =
        (Fintype.card α : ℚ) * q ^ (Fintype.card α - 1) := by
    rw [show (Finset.univ.filter fun x => x ∈ R) = R by ext x; simp [R]]
    calc
      (∑ x ∈ R, q ^ Nat.card {a : α // e a ≠ x}) =
          ∑ _x ∈ R, q ^ (Fintype.card α - 1) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [natCard_remaining, if_pos]
            simpa [R] using hx
      _ = (Fintype.card α : ℚ) * q ^ (Fintype.card α - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul, hR]
  have hout :
      (∑ x ∈ (Finset.univ : Finset (Fin p)) with ¬x ∈ R,
          q ^ Nat.card {a : α // e a ≠ x}) =
        (p - Fintype.card α : ℕ) * q ^ Fintype.card α := by
    have hcardIn :
        ((Finset.univ : Finset (Fin p)).filter fun x => x ∈ R).card =
          Fintype.card α := by
      rw [show (Finset.univ.filter fun x => x ∈ R) = R by ext x; simp [R], hR]
    have hcardOut :
        ((Finset.univ : Finset (Fin p)).filter fun x => ¬x ∈ R).card =
          p - Fintype.card α := by
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin p))) (p := fun x => x ∈ R)
      rw [hcardIn, Finset.card_univ, Fintype.card_fin] at hpart
      omega
    calc
      (∑ x ∈ (Finset.univ : Finset (Fin p)) with ¬x ∈ R,
          q ^ Nat.card {a : α // e a ≠ x}) =
          ∑ _x ∈ (Finset.univ : Finset (Fin p)) with ¬_x ∈ R,
            q ^ Fintype.card α := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [natCard_remaining, if_neg]
              simpa [R] using (Finset.mem_filter.mp hx).2
      _ = (p - Fintype.card α : ℕ) * q ^ Fintype.card α := by
            rw [Finset.sum_const, nsmul_eq_mul, hcardOut]
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin p)))
    (p := fun y => y ∈ R) (f := fun y => q ^ Nat.card {a : α // e a ≠ y}), hin, hout]

/-- Bernoulli's inequality in the precise homogeneous form used below. -/
theorem first_two_terms_le_add_pow (q r : ℚ) (hq : 0 ≤ q) (hr : 0 ≤ r) (a : ℕ) :
    q ^ a + a * q ^ (a - 1) * r ≤ (q + r) ^ a := by
  exact pow_add_mul_le_add_pow hq (by positivity) a

theorem avoidProb_nonneg : ∀ ps : List ℕ, 0 ≤ avoidProb ps
  | [] => by simp [avoidProb]
  | p :: ps => by
      rw [avoidProb]
      exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (avoidProb_nonneg ps)

theorem avoidProb_le_one : ∀ {ps : List ℕ}, (∀ p ∈ ps, 0 < p) → avoidProb ps ≤ 1
  | [], _ => by simp [avoidProb]
  | p :: ps, hpos => by
      rw [avoidProb]
      have hp : 0 < p := hpos p (by simp)
      have htail : ∀ q ∈ ps, 0 < q := fun q hq => hpos q (by simp [hq])
      have hfac : (((p - 1 : ℕ) : ℚ) / p) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hp)]
        exact_mod_cast Nat.sub_le p 1
      exact mul_le_one₀ hfac (avoidProb_nonneg ps) (avoidProb_le_one htail)

/-- Abstract finite negative-dependence bound for independent coordinates,
each of which has one distinct forbidden residue for each label. -/
theorem cover_density_le :
    ∀ (ps : List ℕ) {α : Type*} [Fintype α]
      (hpos : ∀ p ∈ ps, 0 < p) (f : Forbidden α ps),
      (coverCount f : ℚ) / ps.prod ≤
        (1 - avoidProb ps) ^ Fintype.card α := by
  intro ps
  induction ps with
  | nil =>
      intro α _hαF hpos f
      cases f with
      | nil =>
          classical
          by_cases hα : IsEmpty α
          · let : IsEmpty α := hα
            simp [coverCount, Covered, Forbidden.Hit, avoidProb, Config]
          · let a : α := Classical.choice (not_isEmpty_iff.mp hα)
            have hempty : IsEmpty (Covered (Forbidden.nil : Forbidden α [])) :=
              ⟨fun x => False.elim (x.2 a)⟩
            simp [coverCount, avoidProb, hempty]
  | cons p ps ih =>
      intro α _hαF hpos family
      cases family with
      | cons e f =>
          classical
          have hp : 0 < p := hpos p (by simp)
          have hps : ∀ q ∈ ps, 0 < q := fun q hq => hpos q (by simp [hq])
          have hprod : 0 < ps.prod := List.prod_pos hps
          let q : ℚ := 1 - avoidProb ps
          have hav0 : 0 ≤ avoidProb ps := avoidProb_nonneg ps
          have hav1 : avoidProb ps ≤ 1 := avoidProb_le_one hps
          have hq0 : 0 ≤ q := sub_nonneg.mpr hav1
          have hpq : (0 : ℚ) < p := by exact_mod_cast hp
          have hcard : Fintype.card α ≤ p := by
            simpa using Fintype.card_le_of_injective e e.injective
          rw [coverCount_cons, List.prod_cons, Nat.cast_sum, Nat.cast_mul, sum_div]
          calc
        (∑ y : Fin p, (coverCount (f.comap (remainingEmbedding e y)) : ℚ) /
            (p * ps.prod)) =
            (1 / p) * ∑ y : Fin p,
              (coverCount (f.comap (remainingEmbedding e y)) : ℚ) / ps.prod := by
                rw [mul_sum]
                apply Finset.sum_congr rfl
                intro y _hy
                field_simp
        _ ≤ (1 / p) * ∑ y : Fin p,
              q ^ Nat.card {a : α // e a ≠ y} := by
                gcongr with y
                simpa [q, Nat.card_eq_fintype_card] using
                  ih (α := {a : α // e a ≠ y}) hps
                    (f.comap (remainingEmbedding e y))
        _ = (1 / p) * ((Fintype.card α : ℚ) * q ^ (Fintype.card α - 1) +
              (p - Fintype.card α : ℕ) * q ^ Fintype.card α) := by
                rw [sum_pow_natCard_remaining]
        _ = q ^ Fintype.card α + (Fintype.card α : ℚ) *
              q ^ (Fintype.card α - 1) * ((1 - q) / p) := by
                rw [Nat.cast_sub hcard]
                generalize Fintype.card α = a at *
                cases a with
                | zero => field_simp; ring
                | succ a =>
                    simp only [Nat.succ_sub_one]
                    rw [pow_succ]
                    field_simp
                    ring
        _ ≤ (q + (1 - q) / p) ^ Fintype.card α := by
                apply first_two_terms_le_add_pow q ((1 - q) / p) hq0
                exact div_nonneg (by dsimp [q]; linarith) hpq.le
        _ = (1 - avoidProb (p :: ps)) ^ Fintype.card α := by
                rw [avoidProb]
                dsimp [q]
                rw [Nat.cast_sub (by omega : 1 ≤ p)]
                field_simp
                congr 1
                ring

/-! ## Arithmetic realization -/

/-- The forbidden residue `-t (mod p)`, written as the representative `p-t`.
The hypotheses used below ensure `0 < t < p`. -/
def negShiftFin (p t : ℕ) (ht0 : 0 < t) (htp : t < p) : Fin p :=
  ⟨p - t, by omega⟩

theorem negShiftFin_injective {α : Type*} {p : ℕ} (t : α → ℕ)
    (ht0 : ∀ a, 0 < t a) (htp : ∀ a, t a < p) (hinj : Function.Injective t) :
    Function.Injective (fun a => negShiftFin p (t a) (ht0 a) (htp a)) := by
  intro a b hab
  apply hinj
  have heq : p - t a = p - t b := congrArg Fin.val hab
  change p - t a = p - t b at heq
  exact (tsub_right_inj (htp a).le (htp b).le).mp heq

/-- Canonical forbidden residues for shifts in `A`, over a list of moduli all
larger than the containing interval. -/
def intervalForbidden (h : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 h) :
    ∀ (ps : List ℕ), (∀ p ∈ ps, h < p) → Forbidden (↑A) ps
  | [], _ => .nil
  | p :: ps, hp =>
      have hphead : h < p := hp p (by simp)
      .cons
        ⟨fun t => negShiftFin p t.1 (Finset.mem_Icc.mp (hA t.2)).1
            ((Finset.mem_Icc.mp (hA t.2)).2.trans_lt hphead),
          negShiftFin_injective (fun t : ↑A => t.1)
            (fun t => (Finset.mem_Icc.mp (hA t.2)).1)
            (fun t => (Finset.mem_Icc.mp (hA t.2)).2.trans_lt hphead)
            Subtype.val_injective⟩
        (intervalForbidden h A hA ps (fun q hq => hp q (by simp [hq])))

/-- Recursive Chinese-remainder equivalence from one residue modulo a product
to the corresponding product of canonical finite residue spaces. -/
noncomputable def crtConfigEquiv :
    ∀ (ps : List ℕ) (hcop : ps.Pairwise Nat.Coprime)
      (hpos : ∀ p ∈ ps, 0 < p), ZMod ps.prod ≃ Config ps
  | [], _, _ => Equiv.ofUnique (ZMod 1) Unit
  | p :: ps, hcop, hpos => by
      have hp : 0 < p := hpos p (by simp)
      have htail : ∀ q ∈ ps, 0 < q := fun q hq => hpos q (by simp [hq])
      have hhead : ∀ q ∈ ps, p.Coprime q := (List.pairwise_cons.mp hcop).1
      have hprod : p.Coprime ps.prod := Nat.coprime_list_prod_right_iff.mpr hhead
      letI : NeZero p := ⟨hp.ne'⟩
      exact (ZMod.chineseRemainder hprod).toEquiv |>.trans
        (Equiv.prodCongr (ZMod.finEquiv p).symm.toEquiv
          (crtConfigEquiv ps (List.Pairwise.of_cons hcop) htail))

theorem negShiftFin_iff_dvd_add {p t : ℕ} (hp : 0 < p) (ht0 : 0 < t)
    (htp : t < p) (x : Fin p) :
    x = negShiftFin p t ht0 htp ↔ p ∣ x.1 + t := by
  constructor
  · rintro rfl
    simp [negShiftFin, Nat.sub_add_cancel htp.le]
  · intro hd
    apply Fin.ext
    have hsum0 : 0 < x.1 + t := by omega
    have hsum2 : x.1 + t < 2 * p := by omega
    have heq : x.1 + t = p :=
      Nat.eq_of_dvd_of_lt_two_mul hsum0.ne' hd (by simpa [two_mul] using hsum2)
    dsimp [negShiftFin]
    omega

theorem negShiftFin_iff_nonunit {p t : ℕ} (hp : p.Prime) (ht0 : 0 < t)
    (htp : t < p) (x : Fin p) :
    x = negShiftFin p t ht0 htp ↔
      ¬IsUnit ((x.1 + t : ℕ) : ZMod p) := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm, hp.coprime_iff_not_dvd, not_not,
    negShiftFin_iff_dvd_add hp.pos ht0 htp]

theorem natCast_finEquiv {p : ℕ} [NeZero p] (x : Fin p) :
    ((x.1 : ℕ) : ZMod p) = (ZMod.finEquiv p) x := by
  rw [← ZMod.natCast_zmod_val ((ZMod.finEquiv p) x)]
  congr 1
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
  rfl

theorem primeFactors_toList_pairwise (v : ℕ) :
    v.primeFactors.toList.Pairwise Nat.Coprime := by
  apply List.Nodup.pairwise_of_forall_ne (Finset.nodup_toList _)
  intro p hp q hq hpq
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (by simpa using hp))
    (Nat.prime_of_mem_primeFactors (by simpa using hq))).mpr hpq

/-- Under CRT, the abstract cover event is exactly simultaneous nonunitness
of all shifted residues. -/
theorem intervalForbidden_hit_crt_iff (h : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) :
    ∀ (ps : List ℕ) (hprime : ∀ p ∈ ps, p.Prime)
      (hlarge : ∀ p ∈ ps, h < p) (hcop : ps.Pairwise Nat.Coprime)
      (z : ZMod ps.prod) (t : ↑A),
      (intervalForbidden h A hA ps hlarge).Hit
          (crtConfigEquiv ps hcop (fun p hp => (hprime p hp).pos) z) t ↔
        ¬IsUnit (z + (t.1 : ZMod ps.prod)) := by
  intro ps
  induction ps with
  | nil =>
      intro hprime hlarge hcop z t
      simp only [intervalForbidden, Forbidden.Hit, false_iff, not_not]
      change IsUnit ((show ZMod 1 from z) + (t.1 : ZMod 1))
      have hz : (show ZMod 1 from z) + (t.1 : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [hz]
      exact isUnit_one
  | cons p ps ih =>
      intro hprime hlarge hcop z t
      have hp : p.Prime := hprime p (by simp)
      have hp0 : 0 < p := hp.pos
      have htailPrime : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (by simp [hq])
      have htailLarge : ∀ q ∈ ps, h < q := fun q hq => hlarge q (by simp [hq])
      have htailCop : ps.Pairwise Nat.Coprime := List.Pairwise.of_cons hcop
      have hheadCop : ∀ q ∈ ps, p.Coprime q := (List.pairwise_cons.mp hcop).1
      have hprodCop : p.Coprime ps.prod := Nat.coprime_list_prod_right_iff.mpr hheadCop
      have htp : t.1 < p :=
        (Finset.mem_Icc.mp (hA t.2)).2.trans_lt (hlarge p (by simp))
      have ht0 : 0 < t.1 := (Finset.mem_Icc.mp (hA t.2)).1
      let : NeZero p := ⟨hp.ne_zero⟩
      let cr : ZMod (p :: ps).prod ≃+* ZMod p × ZMod ps.prod :=
        ZMod.chineseRemainder hprodCop
      let x : Fin p := (ZMod.finEquiv p).symm (cr z).1
      have hxval : ((x.1 : ℕ) : ZMod p) = (cr z).1 := by
        rw [natCast_finEquiv]
        exact (ZMod.finEquiv p).apply_symm_apply (cr z).1
      have hhead :
          x = negShiftFin p t.1 ht0 htp ↔ ¬IsUnit ((cr z).1 + (t.1 : ZMod p)) := by
        rw [← hxval, ← Nat.cast_add]
        exact negShiftFin_iff_nonunit hp ht0 htp x
      have htail := ih htailPrime htailLarge htailCop (cr z).2 t
      have hunit :
          IsUnit (z + (t.1 : ZMod (p :: ps).prod)) ↔
            IsUnit ((cr z).1 + (t.1 : ZMod p)) ∧
              IsUnit ((cr z).2 + (t.1 : ZMod ps.prod)) := by
        have hmap :
            cr (z + (t.1 : ZMod (p :: ps).prod)) =
              ((cr z).1 + (t.1 : ZMod p), (cr z).2 + (t.1 : ZMod ps.prod)) := by
          rw [map_add, map_natCast]
          rfl
        calc
          IsUnit (z + (t.1 : ZMod (p :: ps).prod)) ↔
              IsUnit (cr (z + (t.1 : ZMod (p :: ps).prod))) :=
                (MulEquiv.isUnit_map cr.toMulEquiv).symm
          _ ↔ IsUnit ((cr z).1 + (t.1 : ZMod p)) ∧
                IsUnit ((cr z).2 + (t.1 : ZMod ps.prod)) := by
                  rw [hmap, Prod.isUnit_iff]
      change (x = negShiftFin p t.1 ht0 htp ∨
          (intervalForbidden h A hA ps htailLarge).Hit
            (crtConfigEquiv ps htailCop (fun q hq => (htailPrime q hq).pos) (cr z).2) t) ↔
        ¬IsUnit (z + (t.1 : ZMod (p :: ps).prod))
      rw [hhead, htail, hunit, not_and_or]

/-- Number of residue classes modulo `m` for which every shift in `A` is a
nonunit.  For positive `m` this is the ordinary cardinality of a filtered
`Finset.univ : Finset (ZMod m)`. -/
noncomputable def shiftedNonunitCount (m : ℕ) (A : Finset ℕ) : ℕ :=
  Nat.card {z : ZMod m // ∀ t : ↑A, ¬IsUnit (z + (t.1 : ZMod m))}

/-- The same count in the literal gcd/coprimality formulation on canonical
representatives `0 ≤ z < m`. -/
def shiftedNoncoprimeResidueCount (m : ℕ) (A : Finset ℕ) : ℕ :=
  ((Finset.range m).filter fun z =>
    ∀ t : ↑A, ¬Nat.Coprime (z + t.1) m).card

/-- Exact gcd version of `shiftedNoncoprimeResidueCount`. -/
def shiftedGcdResidueCount (m : ℕ) (A : Finset ℕ) : ℕ :=
  ((Finset.range m).filter fun z =>
    ∀ t : ↑A, 1 < Nat.gcd (z + t.1) m).card

theorem not_coprime_iff_one_lt_gcd_right {a m : ℕ} (hm : 0 < m) :
    ¬Nat.Coprime a m ↔ 1 < Nat.gcd a m := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hgcd : 0 < Nat.gcd a m := Nat.gcd_pos_of_pos_right a hm
  omega

theorem shiftedNoncoprimeResidueCount_eq_gcd {m : ℕ} (hm : 0 < m)
    (A : Finset ℕ) :
    shiftedNoncoprimeResidueCount m A = shiftedGcdResidueCount m A := by
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hz, hnonunit⟩
    exact ⟨hz, fun t => (not_coprime_iff_one_lt_gcd_right hm).mp (hnonunit t)⟩
  · rintro ⟨hz, hgcd⟩
    exact ⟨hz, fun t => (not_coprime_iff_one_lt_gcd_right hm).mpr (hgcd t)⟩

theorem shifted_isUnit_iff_coprime {m : ℕ} [NeZero m] (z : ZMod m) (t : ℕ) :
    IsUnit (z + (t : ZMod m)) ↔ Nat.Coprime (z.val + t) m := by
  rw [← ZMod.natCast_zmod_val z, ← Nat.cast_add, ZMod.isUnit_iff_coprime]
  rw [ZMod.val_natCast_of_lt z.val_lt]

noncomputable def shiftedNonunitEquivFilter {m : ℕ} [NeZero m] (A : Finset ℕ) :
    {z : ZMod m // ∀ t : ↑A, ¬IsUnit (z + (t.1 : ZMod m))} ≃
      {z : ℕ // z ∈ (Finset.range m).filter fun z =>
        ∀ t : ↑A, ¬Nat.Coprime (z + t.1) m} where
  toFun z := ⟨z.1.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr z.1.val_lt,
    fun t => (shifted_isUnit_iff_coprime z.1 t.1).not.mp (z.2 t)⟩⟩
  invFun z :=
    ⟨(z.1 : ZMod m), fun t => by
      rw [shifted_isUnit_iff_coprime,
        ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp z.2).1)]
      exact (Finset.mem_filter.mp z.2).2 t⟩
  left_inv z := by
    apply Subtype.ext
    exact ZMod.natCast_zmod_val z.1
  right_inv z := by
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp z.2).1)

theorem shiftedNonunitCount_eq_noncoprime {m : ℕ} (hm : 0 < m) (A : Finset ℕ) :
    shiftedNonunitCount m A = shiftedNoncoprimeResidueCount m A := by
  let : NeZero m := ⟨hm.ne'⟩
  rw [shiftedNonunitCount, shiftedNoncoprimeResidueCount,
    Nat.card_congr (shiftedNonunitEquivFilter A), Nat.card_eq_fintype_card,
    Fintype.card_coe]

noncomputable def coveredEquivShiftedNonunits (h : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hlarge : ∀ p ∈ ps, h < p)
    (hcop : ps.Pairwise Nat.Coprime) :
    Covered (intervalForbidden h A hA ps hlarge) ≃
      {z : ZMod ps.prod // ∀ t : ↑A, ¬IsUnit (z + (t.1 : ZMod ps.prod))} := by
  let E := crtConfigEquiv ps hcop (fun p hp => (hprime p hp).pos)
  refine E.symm.subtypeEquiv ?_
  intro x
  constructor
  · intro hx t
    apply (intervalForbidden_hit_crt_iff h A hA ps hprime hlarge hcop (E.symm x) t).mp
    simpa [E] using hx t
  · intro hx t
    have ht := (intervalForbidden_hit_crt_iff h A hA ps hprime hlarge hcop
      (E.symm x) t).mpr (hx t)
    simpa [E] using ht

theorem coverCount_intervalForbidden (h : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hlarge : ∀ p ∈ ps, h < p)
    (hcop : ps.Pairwise Nat.Coprime) :
    coverCount (intervalForbidden h A hA ps hlarge) =
      shiftedNonunitCount ps.prod A := by
  exact Nat.card_congr (coveredEquivShiftedNonunits h A hA ps hprime hlarge hcop)

/-- Large-prime negative dependence for a list of distinct prime moduli. -/
theorem list_largePrime_density_le (h : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hlarge : ∀ p ∈ ps, h < p)
    (hcop : ps.Pairwise Nat.Coprime) :
    (shiftedNonunitCount ps.prod A : ℚ) / ps.prod ≤
      (1 - avoidProb ps) ^ A.card := by
  rw [← coverCount_intervalForbidden h A hA ps hprime hlarge hcop]
  simpa only [Fintype.card_coe] using
    cover_density_le ps (α := ↑A) (fun p hp => (hprime p hp).pos)
      (intervalForbidden h A hA ps hlarge)

theorem avoidProb_eq_prod_div : ∀ (ps : List ℕ),
    avoidProb ps =
      (((ps.map fun p : ℕ => p - 1).prod : ℕ) : ℚ) / ps.prod
  | [] => by simp [avoidProb]
  | p :: ps => by
      rw [avoidProb, avoidProb_eq_prod_div ps]
      simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
      push_cast
      ring

theorem avoidProb_primeFactors {v : ℕ} (hsq : Squarefree v) :
    avoidProb v.primeFactors.toList = (Nat.totient v : ℚ) / v := by
  rw [avoidProb_eq_prod_div]
  have hprod : v.primeFactors.toList.prod = v := by
    simpa using Nat.prod_primeFactors_of_squarefree hsq
  have hphi : (v.primeFactors.toList.map fun p => p - 1).prod = Nat.totient v := by
    rw [Nat.totient_eq_div_primeFactors_mul,
      Nat.prod_primeFactors_of_squarefree hsq,
      Nat.div_self (Nat.pos_of_ne_zero hsq.ne_zero), one_mul]
    simp
  rw [hprod, hphi]

/-- Probability form of the large-prime lemma for a squarefree modulus. -/
theorem squarefree_largePrime_density_le {v h : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (hsq : Squarefree v)
    (hlarge : ∀ p ∈ v.primeFactors, h < p) :
    (shiftedNonunitCount v A : ℚ) / v ≤
      (1 - (Nat.totient v : ℚ) / v) ^ A.card := by
  let ps := v.primeFactors.toList
  have hprod : ps.prod = v := by
    simpa [ps] using Nat.prod_primeFactors_of_squarefree hsq
  have hprime : ∀ p ∈ ps, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (by simpa [ps] using hp)
  have hlargeList : ∀ p ∈ ps, h < p := by
    intro p hp
    exact hlarge p (by simpa [ps] using hp)
  have hcop : ps.Pairwise Nat.Coprime := by
    simpa [ps] using primeFactors_toList_pairwise v
  have hd := list_largePrime_density_le h A hA ps hprime hlargeList hcop
  simpa [hprod, ps, avoidProb_primeFactors hsq] using hd

/-- Division-free form of the large-prime negative-dependence estimate. -/
theorem squarefree_largePrime_count_mul_pow_le {v h : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (hsq : Squarefree v)
    (hlarge : ∀ p ∈ v.primeFactors, h < p) :
    shiftedNonunitCount v A * v ^ A.card ≤
      v * (v - Nat.totient v) ^ A.card := by
  have hv : (0 : ℚ) < v := by
    exact_mod_cast Nat.pos_of_ne_zero hsq.ne_zero
  have hd := squarefree_largePrime_density_le A hA hsq hlarge
  have hsub :
      1 - (Nat.totient v : ℚ) / v = ((v - Nat.totient v : ℕ) : ℚ) / v := by
    rw [Nat.cast_sub (Nat.totient_le v)]
    field_simp
  rw [hsub, div_pow] at hd
  have hcross := (div_le_div_iff₀ hv (pow_pos hv A.card)).mp hd
  exact_mod_cast (show
    (shiftedNonunitCount v A : ℚ) * (v : ℚ) ^ A.card ≤
      (v : ℚ) * ((v - Nat.totient v : ℕ) : ℚ) ^ A.card by
        simpa [mul_comm] using hcross)

/-- Literal gcd/coprimality version: this is the number of residues `z < v`
for which every `z+t` has a nontrivial common divisor with `v`. -/
theorem squarefree_largePrime_noncoprime_count_mul_pow_le {v h : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (hsq : Squarefree v)
    (hlarge : ∀ p ∈ v.primeFactors, h < p) :
    shiftedNoncoprimeResidueCount v A * v ^ A.card ≤
      v * (v - Nat.totient v) ^ A.card := by
  rw [← shiftedNonunitCount_eq_noncoprime (Nat.pos_of_ne_zero hsq.ne_zero)]
  exact squarefree_largePrime_count_mul_pow_le A hA hsq hlarge

/-- The squarefree large-prime occupancy estimate in the exact `gcd > 1`
formulation. -/
theorem squarefree_largePrime_gcd_count_mul_pow_le {v h : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (hsq : Squarefree v)
    (hlarge : ∀ p ∈ v.primeFactors, h < p) :
    shiftedGcdResidueCount v A * v ^ A.card ≤
      v * (v - Nat.totient v) ^ A.card := by
  rw [← shiftedNoncoprimeResidueCount_eq_gcd (Nat.pos_of_ne_zero hsq.ne_zero)]
  exact squarefree_largePrime_noncoprime_count_mul_pow_le A hA hsq hlarge

/-- Conditional form used after fixing the small-prime CRT coordinate.  The
surviving shifts are exactly those coprime to the small factor. -/
theorem squarefree_largePrime_conditional_count_le {v h r u : ℕ}
    (hsq : Squarefree v) (hlarge : ∀ p ∈ v.primeFactors, h < p) :
    let A := (Finset.Icc 1 h).filter fun t => Nat.Coprime (u + t) r
    shiftedNonunitCount v A * v ^ A.card ≤
      v * (v - Nat.totient v) ^ A.card := by
  dsimp
  apply squarefree_largePrime_count_mul_pow_le
  intro t ht
  exact (Finset.mem_filter.mp ht).1
  · exact hsq
  · exact hlarge

/-- Literal gcd/coprimality form of the conditional large-factor estimate.
After a residue modulo the small factor `r` is fixed, only shifts coprime to
`r` need to be covered by a prime divisor of the large factor `v`. -/
theorem squarefree_largePrime_conditional_noncoprime_count_le {v h r u : ℕ}
    (hsq : Squarefree v) (hlarge : ∀ p ∈ v.primeFactors, h < p) :
    let A := (Finset.Icc 1 h).filter fun t => Nat.Coprime (u + t) r
    shiftedNoncoprimeResidueCount v A * v ^ A.card ≤
      v * (v - Nat.totient v) ^ A.card := by
  dsimp
  apply squarefree_largePrime_noncoprime_count_mul_pow_le
  intro t ht
  exact (Finset.mem_filter.mp ht).1
  · exact hsq
  · exact hlarge

/-- Exact `gcd > 1` form of the conditional large-factor estimate. -/
theorem squarefree_largePrime_conditional_gcd_count_le {v h r u : ℕ}
    (hsq : Squarefree v) (hlarge : ∀ p ∈ v.primeFactors, h < p) :
    let A := (Finset.Icc 1 h).filter fun t => Nat.Coprime (u + t) r
    shiftedGcdResidueCount v A * v ^ A.card ≤
      v * (v - Nat.totient v) ^ A.card := by
  dsimp
  apply squarefree_largePrime_gcd_count_mul_pow_le
  intro t ht
  exact (Finset.mem_filter.mp ht).1
  · exact hsq
  · exact hlarge

end LargePrime
end Erdos220

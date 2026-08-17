/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorSeparation
import ErdosProblems.Erdos215.SelectorComponents
import ErdosProblems.Erdos215.SelectorHensel

/-!
Prime-power arithmetic for the full-conflict root-line implication.
-/

namespace Erdos215.Selector.ConflictRoot

open Erdos215.Selector.Modular
open Erdos215.Selector.Separation

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Explicit data at a nontrivial primary component.  The root is the
prime-power lift of a root modulo the prime; the congruence field records
the nontrivial (`1 mod 4`) case in which that lift exists. -/
structure ConflictPrimePowerData {d : ℕ} (c : PrimaryComponent d) where
  mod_four : c.p % 4 = 1
  root : Root c.q

/-- Package an explicitly supplied prime-power root. -/
def conflictPrimePowerDataOfRoot {d : ℕ} (c : PrimaryComponent d)
    (hp1 : c.p % 4 = 1) (root : Root c.q) : ConflictPrimePowerData c :=
  ⟨hp1, root⟩

/-- The `p`-adic order capped at the component exponent, with zero assigned
the cap.  This convention is exactly what the conflict argument needs. -/
private def cappedOrder (p a : ℕ) (z : ℤ) : ℕ :=
  if z = 0 then a else min a (padicValInt p z)

private lemma cappedOrder_le (p a : ℕ) (z : ℤ) : cappedOrder p a z ≤ a := by
  simp only [cappedOrder]
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

private lemma pow_cappedOrder_dvd {p a : ℕ} (hp : p.Prime) (z : ℤ) :
    (p : ℤ) ^ cappedOrder p a z ∣ z := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [cappedOrder]
  split_ifs with hz
  · subst z
    exact dvd_zero _
  · exact (pow_dvd_pow (p : ℤ) (min_le_right a (padicValInt p z))).trans
      (padicValInt_dvd z)

private lemma cappedOrder_eq_padicValInt_of_lt {p a : ℕ} {z : ℤ}
    (h : cappedOrder p a z < a) :
    z ≠ 0 ∧ cappedOrder p a z = padicValInt p z := by
  have hz : z ≠ 0 := by
    intro hz
    subst z
    simp [cappedOrder] at h
  refine ⟨hz, ?_⟩
  simp only [cappedOrder, if_neg hz]
  simp only [cappedOrder, if_neg hz] at h
  omega

private lemma pow_succ_cappedOrder_not_dvd {p a : ℕ} (hp : p.Prime) {z : ℤ}
    (h : cappedOrder p a z < a) :
    ¬ (p : ℤ) ^ (cappedOrder p a z + 1) ∣ z := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hz, hv⟩ := cappedOrder_eq_padicValInt_of_lt h
  rw [padicValInt_dvd_iff]
  simp [hz, hv]

private lemma pow_add_dvd_mul {p r s : ℕ} {x y : ℤ}
    (hx : (p : ℤ) ^ r ∣ x) (hy : (p : ℤ) ^ s ∣ y) :
    (p : ℤ) ^ (r + s) ∣ x * y := by
  simpa only [pow_add] using mul_dvd_mul hx hy

private lemma pow_dvd_pow_of_le (p : ℕ) {r s : ℕ} (h : r ≤ s) :
    (p : ℤ) ^ r ∣ (p : ℤ) ^ s := by
  exact pow_dvd_pow (p : ℤ) h

private lemma pow_dvd_of_le_of_pow_dvd (p : ℕ) {r s : ℕ} {z : ℤ}
    (h : r ≤ s) (hz : (p : ℤ) ^ s ∣ z) :
    (p : ℤ) ^ r ∣ z :=
  (pow_dvd_pow_of_le p h).trans hz

private lemma pow_twice_cappedOrder_succ_not_dvd_sq {p a : ℕ} (hp : p.Prime)
    {z : ℤ} (h : cappedOrder p a z < a) :
    ¬ (p : ℤ) ^ (2 * cappedOrder p a z + 1) ∣ z ^ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hz, hv⟩ := cappedOrder_eq_padicValInt_of_lt h
  intro hdvd
  have hval : 2 * cappedOrder p a z + 1 ≤ padicValInt p (z ^ 2) :=
    (padicValInt_dvd_iff (2 * cappedOrder p a z + 1) (z ^ 2)).mp hdvd |>.resolve_left
      (pow_ne_zero 2 hz)
  have hmul : padicValInt p (z ^ 2) = 2 * padicValInt p z := by
    rw [pow_two, padicValInt.mul hz hz]
    omega
  rw [hmul, ← hv] at hval
  omega

/-- In a full conflict, the two coordinates have the same capped `p`-adic
order at every primary component.  This is the point at which the cross
term in the hypothesis is essential. -/
private lemma cappedOrders_eq_of_full_conflict {d : ℕ} (c : PrimaryComponent d)
    (A B K M : ℤ)
    (hdiv : (d : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M)) :
    cappedOrder c.p c.a A = cappedOrder c.p c.a B := by
  let r := cappedOrder c.p c.a A
  let s := cappedOrder c.p c.a B
  have hrle : r ≤ c.a := cappedOrder_le _ _ _
  have hsle : s ≤ c.a := cappedOrder_le _ _ _
  have hpD : (c.p : ℤ) ^ c.a ∣ (d : ℤ) := by
    exact_mod_cast c.q_dvd
  have hA : (c.p : ℤ) ^ r ∣ A := pow_cappedOrder_dvd c.prime A
  have hB : (c.p : ℤ) ^ s ∣ B := pow_cappedOrder_dvd c.prime B
  by_contra hne
  rcases lt_or_gt_of_ne hne with hrs | hsr
  ·
    have hra : r < c.a := lt_of_lt_of_le hrs hsle
    have hrs' : r + 1 ≤ s := hrs
    have hB' : (c.p : ℤ) ^ (r + 1) ∣ B :=
      pow_dvd_of_le_of_pow_dvd c.p hrs' hB
    have hBr : (c.p : ℤ) ^ r ∣ B :=
      pow_dvd_of_le_of_pow_dvd c.p hrs.le hB
    have hBsq : (c.p : ℤ) ^ (2 * r + 1) ∣ B ^ 2 := by
      rw [pow_two]
      rw [← show (r + 1) + r = 2 * r + 1 by omega]
      exact pow_add_dvd_mul hB' hBr
    have hcrossA : (c.p : ℤ) ^ (2 * r + 1) ∣ 2 * (d : ℤ) * (A * K) := by
      have hbig : (c.p : ℤ) ^ (c.a + r) ∣ (d : ℤ) * A :=
        pow_add_dvd_mul hpD hA
      have hsmall : (c.p : ℤ) ^ (2 * r + 1) ∣ (d : ℤ) * A :=
        pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
      simpa only [mul_assoc] using
        (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsmall K) 2)
    have hcrossB : (c.p : ℤ) ^ (2 * r + 1) ∣ 2 * (d : ℤ) * (B * M) := by
      have hbig : (c.p : ℤ) ^ (c.a + s) ∣ (d : ℤ) * B :=
        pow_add_dvd_mul hpD hB
      have hsmall : (c.p : ℤ) ^ (2 * r + 1) ∣ (d : ℤ) * B :=
        pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
      simpa only [mul_assoc] using
        (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsmall M) 2)
    have hcross : (c.p : ℤ) ^ (2 * r + 1) ∣
        2 * (d : ℤ) * (A * K + B * M) := by
      simpa only [mul_add] using dvd_add hcrossA hcrossB
    have hdSq : (c.p : ℤ) ^ (2 * r + 1) ∣ (d : ℤ) ^ 2 := by
      have hbig : (c.p : ℤ) ^ (c.a + c.a) ∣ (d : ℤ) ^ 2 := by
        simpa only [pow_two] using pow_add_dvd_mul hpD hpD
      exact pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
    have hE : (c.p : ℤ) ^ (2 * r + 1) ∣
        A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := hdSq.trans hdiv
    have hAsq : (c.p : ℤ) ^ (2 * r + 1) ∣ A ^ 2 := by
      rcases hE with ⟨u, hu⟩
      rcases hcross with ⟨v, hv⟩
      rcases hBsq with ⟨w, hw⟩
      refine ⟨u - v - w, ?_⟩
      linear_combination hu - hv - hw
    exact pow_twice_cappedOrder_succ_not_dvd_sq c.prime hra hAsq
  ·
    have hsa : s < c.a := lt_of_lt_of_le hsr hrle
    have hsr' : s + 1 ≤ r := hsr
    have hA' : (c.p : ℤ) ^ (s + 1) ∣ A :=
      pow_dvd_of_le_of_pow_dvd c.p hsr' hA
    have hAs : (c.p : ℤ) ^ s ∣ A :=
      pow_dvd_of_le_of_pow_dvd c.p hsr.le hA
    have hAsq : (c.p : ℤ) ^ (2 * s + 1) ∣ A ^ 2 := by
      rw [pow_two]
      rw [← show (s + 1) + s = 2 * s + 1 by omega]
      exact pow_add_dvd_mul hA' hAs
    have hcrossA : (c.p : ℤ) ^ (2 * s + 1) ∣ 2 * (d : ℤ) * (A * K) := by
      have hbig : (c.p : ℤ) ^ (c.a + r) ∣ (d : ℤ) * A :=
        pow_add_dvd_mul hpD hA
      have hsmall : (c.p : ℤ) ^ (2 * s + 1) ∣ (d : ℤ) * A :=
        pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
      simpa only [mul_assoc] using
        (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsmall K) 2)
    have hcrossB : (c.p : ℤ) ^ (2 * s + 1) ∣ 2 * (d : ℤ) * (B * M) := by
      have hbig : (c.p : ℤ) ^ (c.a + s) ∣ (d : ℤ) * B :=
        pow_add_dvd_mul hpD hB
      have hsmall : (c.p : ℤ) ^ (2 * s + 1) ∣ (d : ℤ) * B :=
        pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
      simpa only [mul_assoc] using
        (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsmall M) 2)
    have hcross : (c.p : ℤ) ^ (2 * s + 1) ∣
        2 * (d : ℤ) * (A * K + B * M) := by
      simpa only [mul_add] using dvd_add hcrossA hcrossB
    have hdSq : (c.p : ℤ) ^ (2 * s + 1) ∣ (d : ℤ) ^ 2 := by
      have hbig : (c.p : ℤ) ^ (c.a + c.a) ∣ (d : ℤ) ^ 2 := by
        simpa only [pow_two] using pow_add_dvd_mul hpD hpD
      exact pow_dvd_of_le_of_pow_dvd c.p (by omega) hbig
    have hE : (c.p : ℤ) ^ (2 * s + 1) ∣
        A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := hdSq.trans hdiv
    have hBsq : (c.p : ℤ) ^ (2 * s + 1) ∣ B ^ 2 := by
      rcases hE with ⟨u, hu⟩
      rcases hcross with ⟨v, hv⟩
      rcases hAsq with ⟨w, hw⟩
      refine ⟨u - v - w, ?_⟩
      linear_combination hu - hv - hw
    exact pow_twice_cappedOrder_succ_not_dvd_sq c.prime hsa hBsq

private lemma component_coprime_two {d : ℕ} (c : PrimaryComponent d)
    (w : ConflictPrimePowerData c) : Nat.Coprime c.p 2 := by
  apply c.prime.coprime_iff_not_dvd.mpr
  intro hp2
  have hle : c.p ≤ 2 := Nat.le_of_dvd (by omega) hp2
  have heq : c.p = 2 := Nat.le_antisymm hle c.prime.two_le
  have := w.mod_four
  rw [heq] at this
  norm_num at this

/-- The local full-conflict implication at a single primary component. -/
theorem exists_component_root_line {d : ℕ} (c : PrimaryComponent d)
    (w : ConflictPrimePowerData c) (A B K M : ℤ)
    (hdiv : (d : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M)) :
    ∃ lam : Root c.q,
      (B : ZMod c.q) = (lam : ZMod c.q) * (A : ZMod c.q) := by
  let r := cappedOrder c.p c.a A
  have hrle : r ≤ c.a := cappedOrder_le _ _ _
  have horders := cappedOrders_eq_of_full_conflict c A B K M hdiv
  have hA : (c.p : ℤ) ^ r ∣ A := pow_cappedOrder_dvd c.prime A
  have hB : (c.p : ℤ) ^ r ∣ B := by
    change (c.p : ℤ) ^ cappedOrder c.p c.a A ∣ B
    rw [horders]
    exact pow_cappedOrder_dvd c.prime B
  have hqcast : (c.q : ℤ) = (c.p : ℤ) ^ c.a := by
    simp only [PrimaryComponent.q, Int.natCast_pow]
  letI : NeZero c.q := ⟨c.q_ne_zero⟩
  by_cases hra : r = c.a
  · have hAq : (c.q : ℤ) ∣ A := by
      rw [hqcast, ← hra]
      exact hA
    have hBq : (c.q : ℤ) ∣ B := by
      rw [hqcast, ← hra]
      exact hB
    refine ⟨w.root, ?_⟩
    have hAz : (A : ZMod c.q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd A c.q).mpr hAq
    have hBz : (B : ZMod c.q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd B c.q).mpr hBq
    rw [hAz, hBz, mul_zero]
  · have hra' : r < c.a := lt_of_le_of_ne hrle hra
    have hBord : cappedOrder c.p c.a B = r := horders.symm
    have hBsucc : ¬ (c.p : ℤ) ^ (r + 1) ∣ B := by
      simpa only [hBord] using
        (pow_succ_cappedOrder_not_dvd c.prime
          (show cappedOrder c.p c.a B < c.a by simpa only [hBord] using hra'))
    let L : ℤ := ZMod.val w.root.1
    let R : ℤ := rootQuotient w.root
    let X : ℤ := B - L * A
    let Y : ℤ := B + L * A
    have hLcast : (L : ZMod c.q) = w.root.1 := by
      dsimp only [L]
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val w.root.1
    have hroot : (c.p : ℤ) ^ c.a * R = 1 + L ^ 2 := by
      dsimp only [R, L, PrimaryComponent.q] at ⊢
      exact_mod_cast mul_rootQuotient c.q_ne_zero w.root
    have hfactor : (d : ℤ) = (c.p : ℤ) ^ c.a * c.D := by
      exact_mod_cast c.factor_q
    have hZ : (c.p : ℤ) ^ r ∣
        R * A ^ 2 + 2 * c.D * (A * K + B * M) := by
      have hRA : (c.p : ℤ) ^ r ∣ R * A ^ 2 := by
        simpa only [pow_two] using dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hA A) R
      have hlin : (c.p : ℤ) ^ r ∣ A * K + B * M :=
        dvd_add (dvd_mul_of_dvd_left hA K) (dvd_mul_of_dvd_left hB M)
      exact dvd_add hRA (dvd_mul_of_dvd_right hlin (2 * c.D))
    have hcorr : (c.p : ℤ) ^ (c.a + r) ∣
        (c.p : ℤ) ^ c.a *
          (R * A ^ 2 + 2 * c.D * (A * K + B * M)) :=
      pow_add_dvd_mul (dvd_refl _) hZ
    have hE : (c.p : ℤ) ^ (c.a + r) ∣
        A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := by
      have hpD : (c.p : ℤ) ^ c.a ∣ (d : ℤ) := by exact_mod_cast c.q_dvd
      have hdsq : (c.p : ℤ) ^ (c.a + c.a) ∣ (d : ℤ) ^ 2 := by
        simpa only [pow_two] using pow_add_dvd_mul hpD hpD
      exact (pow_dvd_of_le_of_pow_dvd c.p (by omega) hdsq).trans hdiv
    have hXY : (c.p : ℤ) ^ (c.a + r) ∣ X * Y := by
      rcases hE with ⟨u, hu⟩
      rcases hcorr with ⟨v, hv⟩
      refine ⟨u - v, ?_⟩
      dsimp only [X, Y]
      rw [hfactor] at hu
      linear_combination hu - hv + A ^ 2 * hroot
    have hXr : (c.p : ℤ) ^ r ∣ X :=
      dvd_sub hB (dvd_mul_of_dvd_right hA L)
    have hYr : (c.p : ℤ) ^ r ∣ Y :=
      dvd_add hB (dvd_mul_of_dvd_right hA L)
    by_cases hX0 : X = 0
    · refine ⟨w.root, ?_⟩
      dsimp only [X] at hX0
      rw [sub_eq_zero] at hX0
      have hc := congrArg (fun z : ℤ ↦ (z : ZMod c.q)) hX0
      push_cast at hc
      simpa only [hLcast] using hc
    by_cases hY0 : Y = 0
    · refine ⟨⟨-w.root.1, by rw [neg_sq, w.root.property]⟩, ?_⟩
      dsimp only [Y] at hY0
      have hneg : B = -L * A := by linear_combination hY0
      have hc := congrArg (fun z : ℤ ↦ (z : ZMod c.q)) hneg
      push_cast at hc
      simpa only [hLcast] using hc
    letI : Fact c.p.Prime := ⟨c.prime⟩
    have hvalXY : c.a + r ≤ padicValInt c.p X + padicValInt c.p Y := by
      have hv := (padicValInt_dvd_iff (c.a + r) (X * Y)).mp hXY
      rw [padicValInt.mul hX0 hY0] at hv
      exact hv.resolve_left (mul_ne_zero hX0 hY0)
    have hvalX : r ≤ padicValInt c.p X :=
      ((padicValInt_dvd_iff r X).mp hXr).resolve_left hX0
    have hvalY : r ≤ padicValInt c.p Y :=
      ((padicValInt_dvd_iff r Y).mp hYr).resolve_left hY0
    have hnotBoth : ¬ (r + 1 ≤ padicValInt c.p X ∧
        r + 1 ≤ padicValInt c.p Y) := by
      rintro ⟨hx, hy⟩
      have hxdiv : (c.p : ℤ) ^ (r + 1) ∣ X :=
        (padicValInt_dvd_iff (r + 1) X).mpr (Or.inr hx)
      have hydiv : (c.p : ℤ) ^ (r + 1) ∣ Y :=
        (padicValInt_dvd_iff (r + 1) Y).mpr (Or.inr hy)
      have h2B : (c.p : ℤ) ^ (r + 1) ∣ 2 * B := by
        rcases hxdiv with ⟨u, hu⟩
        rcases hydiv with ⟨v, hv⟩
        refine ⟨u + v, ?_⟩
        dsimp only [X, Y] at hu hv
        linear_combination hu + hv
      have hcopNat : Nat.Coprime (c.p ^ (r + 1)) 2 :=
        (component_coprime_two c w).pow_left _
      have hcop : IsCoprime ((c.p : ℤ) ^ (r + 1)) (2 : ℤ) := by
        exact_mod_cast hcopNat
      exact hBsucc (hcop.dvd_of_dvd_mul_left h2B)
    rcases lt_or_ge (padicValInt c.p X) (r + 1) with hxlt | hxhigh
    · have hxle : padicValInt c.p X ≤ r := by omega
      have hx : padicValInt c.p X = r := le_antisymm hxle hvalX
      have hy : c.a ≤ padicValInt c.p Y := by omega
      have hydiv : (c.q : ℤ) ∣ Y := by
        rw [hqcast]
        exact (padicValInt_dvd_iff c.a Y).mpr (Or.inr hy)
      refine ⟨⟨-w.root.1, by rw [neg_sq, w.root.property]⟩, ?_⟩
      have heq := ((ZMod.intCast_eq_intCast_iff_dvd_sub
        ((-(ZMod.val w.root.1 : ℤ)) * A) B c.q).mpr (by
          dsimp only [Y, L] at hydiv
          simpa only [sub_neg_eq_add, neg_mul] using hydiv)).symm
      calc
        (B : ZMod c.q) = (((-(ZMod.val w.root.1 : ℤ)) * A : ℤ) : ZMod c.q) := heq
        _ = (-w.root.1) * (A : ZMod c.q) := by
          push_cast
          rw [ZMod.natCast_zmod_val w.root.1]

    · have hyNot : ¬ r + 1 ≤ padicValInt c.p Y := by
        intro hy
        exact hnotBoth ⟨hxhigh, hy⟩
      have hyle : padicValInt c.p Y ≤ r := by omega
      have hy : padicValInt c.p Y = r := le_antisymm hyle hvalY
      have hx : c.a ≤ padicValInt c.p X := by omega
      have hxdiv : (c.q : ℤ) ∣ X := by
        rw [hqcast]
        exact (padicValInt_dvd_iff c.a X).mpr (Or.inr hx)
      refine ⟨w.root, ?_⟩
      have heq := ((ZMod.intCast_eq_intCast_iff_dvd_sub
        ((ZMod.val w.root.1 : ℤ) * A) B c.q).mpr (by
          dsimp only [X, L] at hxdiv
          exact hxdiv)).symm
      calc
        (B : ZMod c.q) = ((((ZMod.val w.root.1 : ℤ)) * A : ℤ) : ZMod c.q) := heq
        _ = w.root.1 * (A : ZMod c.q) := by
          push_cast
          rw [ZMod.natCast_zmod_val w.root.1]

/-- Assemble independently selected local roots by the list CRT. -/
private theorem exists_global_root_of_component_roots {d : ℕ}
    (C : CompleteComponents d) (hd : d ≠ 0)
    (roots : ∀ c ∈ C.components, Root c.q) :
    ∃ lam : Root d, ∀ c, ∀ hc : c ∈ C.components,
      c.reduce lam.1 = (roots c hc : ZMod c.q) := by
  classical
  let residue : PrimaryComponent d → ℕ := fun c ↦
    if hc : c ∈ C.components then ZMod.val (roots c hc).1 else 0
  let z := Nat.chineseRemainderOfList residue
    (fun c : PrimaryComponent d ↦ c.q) C.components C.pairwise
  have hz (c : PrimaryComponent d) (hc : c ∈ C.components) :
      c.reduce ((z : ℕ) : ZMod d) = (roots c hc : ZMod c.q) := by
    letI : NeZero c.q := ⟨c.q_ne_zero⟩
    have hmod : (z : ℕ) ≡ residue c [MOD c.q] := z.property c hc
    have hcast : ((z : ℕ) : ZMod c.q) = (residue c : ZMod c.q) :=
      (ZMod.natCast_eq_natCast_iff (z : ℕ) (residue c) c.q).mpr hmod
    rw [PrimaryComponent.reduce_natCast]
    rw [hcast]
    dsimp only [residue]
    simp only [dif_pos hc]
    exact ZMod.natCast_zmod_val (roots c hc).1
  let x : ZMod d := (z : ℕ)
  have hxroot : x ^ 2 = -1 := by
    apply C.eq_of_reduce_eq hd
    intro c hc
    rw [map_pow, map_neg, map_one]
    change (c.reduce x) ^ 2 = (-1 : ZMod c.q)
    rw [show c.reduce x = (roots c hc : ZMod c.q) by exact hz c hc]
    exact (roots c hc).property
  refine ⟨⟨x, hxroot⟩, ?_⟩
  intro c hc
  exact hz c hc

/-- Complete primary components turn their local full-conflict root lines
into one root line modulo the original denominator. -/
theorem conflictRootLineProperty_of_complete_data {d : ℕ} (hd : d ≠ 0)
    (C : CompleteComponents d)
    (data : ∀ c ∈ C.components, ConflictPrimePowerData c) :
    ConflictRootLineProperty d := by
  intro A B K M hdiv
  have hlocal : ∀ c ∈ C.components, ∃ lam : Root c.q,
      (B : ZMod c.q) = (lam : ZMod c.q) * (A : ZMod c.q) := by
    intro c hc
    exact exists_component_root_line c (data c hc) A B K M hdiv
  let roots : ∀ c ∈ C.components, Root c.q := fun c hc ↦
    Classical.choose (hlocal c hc)
  have hlocal_spec (c : PrimaryComponent d) (hc : c ∈ C.components) :
      (B : ZMod c.q) = (roots c hc : ZMod c.q) * (A : ZMod c.q) :=
    Classical.choose_spec (hlocal c hc)
  obtain ⟨lam, hlam⟩ := exists_global_root_of_component_roots C hd roots
  refine ⟨lam, ?_⟩
  apply C.eq_of_reduce_eq hd
  intro c hc
  rw [PrimaryComponent.reduce_intCast, map_mul, PrimaryComponent.reduce_intCast]
  rw [hlam c hc]
  exact hlocal_spec c hc

/-- Construct the explicit component data from the congruence `p = 1 mod
4`, using the elementary prime-power Hensel tower. -/
def primePowerDataOfModFour {d : ℕ} (c : PrimaryComponent d)
    (hp1 : c.p % 4 = 1) : ConflictPrimePowerData c where
  mod_four := hp1
  root := Classical.choice
    (root_primePower_nonempty_of_mod_four_eq_one c.p c.a c.prime hp1 c.exp_pos)

/-- Public form: for a complete factorization all of whose component
primes are `1 mod 4`, the corrected full-conflict root-line property holds. -/
theorem conflictRootLineProperty_of_complete {d : ℕ} (hd : d ≠ 0)
    (C : CompleteComponents d)
    (hp1 : ∀ c ∈ C.components, c.p % 4 = 1) :
    ConflictRootLineProperty d :=
  conflictRootLineProperty_of_complete_data hd C
    (fun c hc ↦ primePowerDataOfModFour c (hp1 c hc))

end

end Erdos215.Selector.ConflictRoot

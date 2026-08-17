import ErdosProblems.Erdos215.SelectorFinal

namespace Erdos215.Selector.PartialGood

open Erdos215.Selector

set_option autoImplicit false

/-!
# The partial-good-permutation extension (Jackson--Mauldin, Lemma 4.8)

The shift in the paper is a residue modulo `d'` which is divisible by `u`.
For formal purposes we retain its chosen quotient `q`; thus the actual shift
is `u * q i` and the correction in (4.8) is definitionally `d * q i`.
-/

/-- Add the (chosen nonnegative representative of the) shift `u * q i`
modulo `N`. -/
def partialGoodShift (N u : ℕ) (q : Fin N → ℕ) (i : Fin N) : Fin N :=
  ⟨(i.1 + u * q i) % N, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)⟩

/-- The raw extension map in formula (4.8). -/
def partialGoodExtension (N u d : ℕ) (q : Fin N → ℕ)
    (pi : Fin N → Fin N) (i : Fin N) : Fin N :=
  ⟨((pi (partialGoodShift N u q i)).1 + d * q i) % N,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)⟩

/-- The source residue of an index modulo the new prime. -/
def sourceResidue (p : ℕ) {N : ℕ} (i : Fin N) : ZMod p := i.1

/-- Goodness of the partial map on the distinguished residue class. -/
def PartialGoodOnClass (N p i₀ : ℕ) (pi : Fin N → Fin N) : Prop :=
  ∀ i j : Fin N, i.1 % p = i₀ → j.1 % p = i₀ → i ≠ j →
    ¬(survivingModulus N (indexDiff i j) : ℤ) ∣
      (((pi i).1 : ℕ) : ℤ) - (((pi j).1 : ℕ) : ℤ)

private lemma natMod_modEq (N a : ℕ) :
    ((a % N : ℕ) : ℤ) ≡ (a : ℤ) [ZMOD (N : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have h : (a : ℤ) = (a % N : ℕ) + (N : ℤ) * (a / N : ℕ) := by
    exact_mod_cast (Nat.mod_add_div a N).symm
  use (a / N : ℕ)
  omega

private lemma indexDiff_dvd_iff {N k : ℕ} (i j : Fin N) :
    k ∣ indexDiff i j ↔
      (k : ℤ) ∣ (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) := by
  change (Int.natAbs (k : ℤ)) ∣
      Int.natAbs (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) ↔ _
  rw [Int.natAbs_dvd_natAbs]

private lemma gcd_indexDiff_eq_of_modEq {N : ℕ} (i j i' j' : Fin N)
    (h : (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) ≡
      (((i'.1 : ℕ) : ℤ) - ((j'.1 : ℕ) : ℤ)) [ZMOD (N : ℤ)]) :
    Nat.gcd N (indexDiff i j) = Nat.gcd N (indexDiff i' j') := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    rw [indexDiff_dvd_iff]
    have hgN : ((Nat.gcd N (indexDiff i j) : ℕ) : ℤ) ∣ (N : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left N (indexDiff i j)
    have hgij : ((Nat.gcd N (indexDiff i j) : ℕ) : ℤ) ∣
        (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) := by
      rw [← indexDiff_dvd_iff]
      exact Nat.gcd_dvd_right _ _
    rw [Int.modEq_iff_dvd] at h
    rcases hgN with ⟨a, ha⟩
    rcases hgij with ⟨b, hb⟩
    rcases h with ⟨c, hc⟩
    rw [ha] at hc
    use b + a * c
    linear_combination hb + hc
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    rw [indexDiff_dvd_iff]
    have hgN : ((Nat.gcd N (indexDiff i' j') : ℕ) : ℤ) ∣ (N : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left N (indexDiff i' j')
    have hgij : ((Nat.gcd N (indexDiff i' j') : ℕ) : ℤ) ∣
        (((i'.1 : ℕ) : ℤ) - ((j'.1 : ℕ) : ℤ)) := by
      rw [← indexDiff_dvd_iff]
      exact Nat.gcd_dvd_right _ _
    rw [Int.modEq_iff_dvd] at h
    rcases hgN with ⟨a, ha⟩
    rcases hgij with ⟨b, hb⟩
    rcases h with ⟨c, hc⟩
    rw [ha] at hc
    use b - a * c
    linear_combination hb - hc

private lemma gcd_indexDiff_partialGoodShift_eq {N u : ℕ} (q : Fin N → ℕ)
    (i j : Fin N) (hq : q i = q j) :
    Nat.gcd N (indexDiff (partialGoodShift N u q i) (partialGoodShift N u q j)) =
      Nat.gcd N (indexDiff i j) := by
  symm
  apply gcd_indexDiff_eq_of_modEq
  have hi := natMod_modEq N (i.1 + u * q i)
  have hj := natMod_modEq N (j.1 + u * q j)
  have h := hi.sub hj
  rw [hq] at h
  simp only [partialGoodShift]
  rw [hq]
  convert h.symm using 1
  push_cast
  ring

private lemma survivingModulus_partialGoodShift_eq {N u : ℕ} (q : Fin N → ℕ)
    (i j : Fin N) (hq : q i = q j) :
    survivingModulus N
        (indexDiff (partialGoodShift N u q i) (partialGoodShift N u q j)) =
      survivingModulus N (indexDiff i j) := by
  simp only [survivingModulus]
  rw [gcd_indexDiff_partialGoodShift_eq q i j hq]

private lemma partialGoodShift_modEq (N u : ℕ) (q : Fin N → ℕ) (i : Fin N) :
    (((partialGoodShift N u q i).1 : ℕ) : ℤ) ≡
      ((i.1 : ℕ) : ℤ) + (u : ℤ) * (q i : ℕ) [ZMOD (N : ℤ)] := by
  simpa [partialGoodShift] using natMod_modEq N (i.1 + u * q i)

private lemma partialGoodExtension_modEq (N u d : ℕ) (q : Fin N → ℕ)
    (pi : Fin N → Fin N) (i : Fin N) :
    (((partialGoodExtension N u d q pi i).1 : ℕ) : ℤ) ≡
      (((pi (partialGoodShift N u q i)).1 : ℕ) : ℤ) +
        (d : ℤ) * (q i : ℕ) [ZMOD (N : ℤ)] := by
  simpa [partialGoodExtension] using
    natMod_modEq N ((pi (partialGoodShift N u q i)).1 + d * q i)

private lemma dvd_iff_of_modEq_of_dvd {N m : ℕ} {a b : ℤ}
    (hm : m ∣ N) (h : a ≡ b [ZMOD (N : ℤ)]) :
    (m : ℤ) ∣ a ↔ (m : ℤ) ∣ b := by
  have hmz : (m : ℤ) ∣ (N : ℤ) := by exact_mod_cast hm
  rw [Int.modEq_iff_dvd] at h
  have hd : (m : ℤ) ∣ b - a := hmz.trans h
  constructor
  · intro ha
    have hab := ha.add hd
    have heq : a + (b - a) = b := by ring
    rw [heq] at hab
    exact hab
  · intro hb
    have hba := hb.sub hd
    have heq : b - (b - a) = a := by ring
    rw [heq] at hba
    exact hba

private lemma sourceResidue_partialGoodShift {N p u : ℕ} (hpN : p ∣ N)
    (q : Fin N → ℕ) (i : Fin N) :
    sourceResidue p (partialGoodShift N u q i) =
      sourceResidue p i + (u : ZMod p) * (q i : ℕ) := by
  change ((((i.1 + u * q i) % N : ℕ) : ZMod p) = _)
  calc
    (((i.1 + u * q i) % N : ℕ) : ZMod p) =
        ((((i.1 + u * q i) % N) % p : ℕ) : ZMod p) := by
          symm
          exact ZMod.natCast_mod _ _
    _ = (((i.1 + u * q i) % p : ℕ) : ZMod p) := by
      rw [Nat.mod_mod_of_dvd _ hpN]
    _ = ((i.1 + u * q i : ℕ) : ZMod p) := ZMod.natCast_mod _ _
    _ = sourceResidue p i + (u : ZMod p) * (q i : ℕ) := by
      simp [sourceResidue]

private lemma partialGoodShift_ne_of_q_eq {N u : ℕ} (q : Fin N → ℕ)
    {i j : Fin N} (hij : i ≠ j) (hq : q i = q j) :
    partialGoodShift N u q i ≠ partialGoodShift N u q j := by
  intro hs
  let _ : NeZero N := ⟨Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)⟩
  have hi : (((partialGoodShift N u q i).1 : ℕ) : ZMod N) =
      (i.1 : ZMod N) + (u : ZMod N) * (q i : ℕ) := by
    simp [partialGoodShift]
  have hj : (((partialGoodShift N u q j).1 : ℕ) : ZMod N) =
      (j.1 : ZMod N) + (u : ZMod N) * (q j : ℕ) := by
    simp [partialGoodShift]
  have hc : (i.1 : ZMod N) = (j.1 : ZMod N) := by
    rw [hs] at hi
    rw [hq] at hi
    exact add_right_cancel (hi.symm.trans hj)
  apply hij
  apply Fin.ext
  have hv := congrArg ZMod.val hc
  simpa [ZMod.val_natCast_of_lt i.2, ZMod.val_natCast_of_lt j.2] using hv

/-- The equal-source-residue case in the proof of Lemma 4.8. -/
lemma partialGoodExtension_good_of_same_residue
    {N p u d i₀ : ℕ}
    (q : Fin N → ℕ) (pi : Fin N → Fin N)
    (hqconst : ∀ i j : Fin N,
      i.1 % p = j.1 % p → q i = q j)
    (hguide : ∀ i : Fin N, (partialGoodShift N u q i).1 % p = i₀)
    (hpartial : PartialGoodOnClass N p i₀ pi)
    (i j : Fin N) (hij : i ≠ j)
    (hsame : i.1 % p = j.1 % p) :
    ¬(survivingModulus N (indexDiff i j) : ℤ) ∣
      ((((partialGoodExtension N u d q pi i).1 : ℕ) : ℤ) -
        (((partialGoodExtension N u d q pi j).1 : ℕ) : ℤ)) := by
  let si := partialGoodShift N u q i
  let sj := partialGoodShift N u q j
  have hq : q i = q j := hqconst i j hsame
  have hsi : si.1 % p = i₀ := hguide i
  have hsj : sj.1 % p = i₀ := hguide j
  have hsine : si ≠ sj := partialGoodShift_ne_of_q_eq q hij hq
  have hpg := hpartial si sj hsi hsj hsine
  rw [survivingModulus_partialGoodShift_eq q i j hq] at hpg
  intro hbad
  have hmN : survivingModulus N (indexDiff i j) ∣ N :=
    survivingModulus_dvd _ _
  have hmod := (partialGoodExtension_modEq N u d q pi i).sub
    (partialGoodExtension_modEq N u d q pi j)
  have hraw := (dvd_iff_of_modEq_of_dvd hmN hmod).mp hbad
  rw [hq] at hraw
  apply hpg
  convert hraw using 1
  ring

private lemma gcd_indexDiff_dvd_u_of_cross
    {N p u n : ℕ} (hp : p.Prime) (hN : N = u * p ^ n)
    (i j : Fin N) (hcross : i.1 % p ≠ j.1 % p) :
    Nat.gcd N (indexDiff i j) ∣ u := by
  have hpnot : ¬p ∣ Nat.gcd N (indexDiff i j) := by
    intro hpg
    have hpidx : p ∣ indexDiff i j := hpg.trans (Nat.gcd_dvd_right _ _)
    have hpz : (p : ℤ) ∣
        (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) :=
      (indexDiff_dvd_iff i j).mp hpidx
    have hpz' : (p : ℤ) ∣
        (((j.1 : ℕ) : ℤ) - ((i.1 : ℕ) : ℤ)) := by
      simpa only [neg_sub] using dvd_neg.mpr hpz
    have hm : i.1 ≡ j.1 [MOD p] := by
      rw [Nat.modEq_iff_dvd]
      exact hpz'
    exact hcross hm
  have hgp : Nat.Coprime (Nat.gcd N (indexDiff i j)) p :=
    ((hp.coprime_iff_not_dvd).2 hpnot).symm
  have hgpown : Nat.Coprime (Nat.gcd N (indexDiff i j)) (p ^ n) :=
    hgp.pow_right n
  apply hgpown.dvd_of_dvd_mul_right
  rw [← hN]
  exact Nat.gcd_dvd_left _ _

private lemma natModEq_iff_dvd_indexDiff {N : ℕ} (m : ℕ) (i j : Fin N) :
    i.1 ≡ j.1 [MOD m] ↔ m ∣ indexDiff i j := by
  rw [Nat.modEq_iff_dvd, Int.natCast_dvd]
  simp only [indexDiff]
  rw [show ((j.1 : ℤ) - i.1) = -((i.1 : ℤ) - j.1) by ring, Int.natAbs_neg]

private lemma int_dvd_sub_iff_natModEq (m a b : ℕ) :
    (m : ℤ) ∣ (a : ℤ) - (b : ℤ) ↔ a ≡ b [MOD m] := by
  rw [Nat.modEq_iff_dvd]
  constructor <;> intro h <;> simpa only [neg_sub] using dvd_neg.mpr h

private lemma partialGoodShift_natModEq (N u : ℕ) (q : Fin N → ℕ) (i : Fin N) :
    (partialGoodShift N u q i).1 ≡ i.1 + u * q i [MOD N] := by
  simp [partialGoodShift, Nat.ModEq]

private lemma partialGoodExtension_natModEq (N u d : ℕ) (q : Fin N → ℕ)
    (pi : Fin N → Fin N) (i : Fin N) :
    (partialGoodExtension N u d q pi i).1 ≡
      (pi (partialGoodShift N u q i)).1 + d * q i [MOD N] := by
  simp [partialGoodExtension, Nat.ModEq]

private lemma pow_dvd_survivingModulus_of_gcd_dvd_u {N u p n a : ℕ}
    (hN : N = u * p ^ n) (hg : Nat.gcd N a ∣ u) :
    p ^ n ∣ survivingModulus N a := by
  rw [survivingModulus, Nat.dvd_div_iff_mul_dvd (Nat.gcd_dvd_left N a)]
  have hmul : Nat.gcd N a * p ^ n ∣ u * p ^ n :=
    Nat.mul_dvd_mul_right hg (p ^ n)
  have huN : u * p ^ n ∣ N := by rw [hN]
  exact hmul.trans huN

private lemma correction_not_modEq_pow {N u d p n qi qj : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hcop : Nat.Coprime p u)
    (hpd : N = p * d) (hN : N = u * p ^ n)
    (hne : ¬qi ≡ qj [MOD p]) :
    ¬d * qi ≡ d * qj [MOD p ^ n] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hd : d = u * p ^ k := by
    apply Nat.mul_left_cancel hp.pos
    calc
      p * d = N := hpd.symm
      _ = u * p ^ (k + 1) := hN
      _ = p * (u * p ^ k) := by rw [pow_succ]; ac_rfl
  intro hbad
  have hbad' : p ^ k * (u * qi) ≡ p ^ k * (u * qj) [MOD p ^ k * p] := by
    simpa [hd, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hbad
  have hu : u * qi ≡ u * qj [MOD p] :=
    hbad'.mul_left_cancel' (pow_ne_zero _ hp.ne_zero)
  exact hne (hu.cancel_left_of_coprime hcop.gcd_eq_one)

private lemma q_not_modEq_of_shift_eq_of_cross {N u p : ℕ} (q : Fin N → ℕ)
    (hpN : p ∣ N) {i j : Fin N} (hij : i.1 % p ≠ j.1 % p)
    (hshift : partialGoodShift N u q i = partialGoodShift N u q j) :
    ¬q i ≡ q j [MOD p] := by
  intro hq
  have hsi := (partialGoodShift_natModEq N u q i).of_dvd hpN
  have hsj := (partialGoodShift_natModEq N u q j).of_dvd hpN
  have hsij : (partialGoodShift N u q i).1 ≡
      (partialGoodShift N u q j).1 [MOD p] := by rw [hshift]
  have huq : u * q i ≡ u * q j [MOD p] := hq.mul_left u
  have hm : i.1 ≡ j.1 [MOD p] := by
    exact huq.add_right_cancel (hsi.symm.trans (hsij.trans hsj))
  exact hij hm

private lemma gcd_mul_p_dvd_shift_gcd {N u p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hN : N = u * p ^ n) (q : Fin N → ℕ) {i j : Fin N}
    (hij : i.1 % p ≠ j.1 % p)
    (hxi : (partialGoodShift N u q i).1 % p =
      (partialGoodShift N u q j).1 % p) :
    Nat.gcd N (indexDiff i j) * p ∣
      Nat.gcd N (indexDiff (partialGoodShift N u q i)
        (partialGoodShift N u q j)) := by
  let g := Nat.gcd N (indexDiff i j)
  have hgu : g ∣ u := gcd_indexDiff_dvd_u_of_cross hp hN i j hij
  have hgN : g ∣ N := Nat.gcd_dvd_left _ _
  have hpN : p ∣ N := by
    rw [hN]
    exact dvd_mul_of_dvd_right (dvd_pow_self p (Nat.ne_of_gt hn)) u
  have hgi : i.1 ≡ j.1 [MOD g] :=
    (natModEq_iff_dvd_indexDiff g i j).2 (Nat.gcd_dvd_right _ _)
  have hsi := (partialGoodShift_natModEq N u q i).of_dvd hgN
  have hsj := (partialGoodShift_natModEq N u q j).of_dvd hgN
  have huci : u * q i ≡ 0 [MOD g] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hgu _)
  have hucj : u * q j ≡ 0 [MOD g] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hgu _)
  have hgxy : (partialGoodShift N u q i).1 ≡
      (partialGoodShift N u q j).1 [MOD g] := by
    exact hsi.trans (((Nat.ModEq.rfl.add huci).trans (hgi.add Nat.ModEq.rfl)).trans
      ((Nat.ModEq.rfl.add hucj.symm).trans hsj.symm))
  have hgdiff : g ∣ indexDiff (partialGoodShift N u q i)
      (partialGoodShift N u q j) :=
    (natModEq_iff_dvd_indexDiff g _ _).1 hgxy
  have hpdiff : p ∣ indexDiff (partialGoodShift N u q i)
      (partialGoodShift N u q j) :=
    (natModEq_iff_dvd_indexDiff p _ _).1 hxi
  have hpg : Nat.Coprime g p :=
    (hp.coprime_iff_not_dvd.mpr (by
      intro hpg
      exact hij ((natModEq_iff_dvd_indexDiff p i j).2
        (hpg.trans (Nat.gcd_dvd_right _ _))))).symm
  apply Nat.dvd_gcd
  · exact hpg.mul_dvd_of_dvd_of_dvd hgN hpN
  · exact hpg.mul_dvd_of_dvd_of_dvd hgdiff hpdiff

private lemma gcd_indexDiff_dvd_d_of_cross {N u d p n : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hpd : N = p * d) (hN : N = u * p ^ n)
    {i j : Fin N} (hij : i.1 % p ≠ j.1 % p) :
    Nat.gcd N (indexDiff i j) ∣ d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hd : d = u * p ^ k := by
    apply Nat.mul_left_cancel hp.pos
    calc
      p * d = N := hpd.symm
      _ = u * p ^ (k + 1) := hN
      _ = p * (u * p ^ k) := by rw [pow_succ]; ac_rfl
  rw [hd]
  exact dvd_mul_of_dvd_left (gcd_indexDiff_dvd_u_of_cross hp hN _ _ hij) _

private lemma div_gcd_dvd_div_gcd_of_mul_dvd {N p d g gx : ℕ}
    (hp : 0 < p) (hpd : N = p * d) (hg : g ∣ d)
    (hxN : gx ∣ N) (hgpx : g * p ∣ gx) :
    N / gx ∣ d / g := by
  rw [Nat.dvd_div_iff_mul_dvd hg]
  have hmul : (g * p) * (N / gx) ∣ gx * (N / gx) :=
    Nat.mul_dvd_mul_right hgpx (N / gx)
  have hmulN : (g * p) * (N / gx) ∣ N := by
    convert hmul using 1
    rw [Nat.mul_comm gx, Nat.div_mul_cancel hxN]
  have hcancel : p * (g * (N / gx)) ∣ p * d := by
    simpa [hpd, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmulN
  rcases hcancel with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  apply Nat.mul_left_cancel hp
  simpa [Nat.mul_assoc] using hc

/-- Jackson--Mauldin's partial-good-permutation extension lemma (Lemma 4.8),
in raw-map form.  The actual shift is `u * q i`, so `q` is the retained
integer quotient `s(i) / u`. -/
theorem partialGoodExtension_good
    {N u d p n i₀ : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hcop : Nat.Coprime p u) (hpd : N = p * d) (hN : N = u * p ^ n)
    (q : Fin N → ℕ) (pi : Fin N → Fin N)
    (hqclass : ∀ i j : Fin N, i.1 % p = j.1 % p → q i = q j)
    (hshiftClass : ∀ i : Fin N, (partialGoodShift N u q i).1 % p = i₀)
    (hpartial : PartialGoodOnClass N p i₀ pi) :
    GoodMap N (partialGoodExtension N u d q pi) := by
  intro i j hij
  rw [int_dvd_sub_iff_natModEq]
  intro hbad
  let x := partialGoodShift N u q i
  let y := partialGoodShift N u q j
  let g := Nat.gcd N (indexDiff i j)
  let gx := Nat.gcd N (indexDiff x y)
  let M := survivingModulus N (indexDiff i j)
  let Mx := survivingModulus N (indexDiff x y)
  have hMN : M ∣ N := survivingModulus_dvd _ _
  have hxClass : x.1 % p = i₀ := hshiftClass i
  have hyClass : y.1 % p = i₀ := hshiftClass j
  by_cases hs : i.1 % p = j.1 % p
  · have hq : q i = q j := hqclass i j hs
    have hxy : x ≠ y := partialGoodShift_ne_of_q_eq q hij hq
    have hg' : Nat.gcd N (indexDiff x y) = Nat.gcd N (indexDiff i j) := by
      exact gcd_indexDiff_partialGoodShift_eq q i j hq
    have hMMx : Mx = M := by simp [M, Mx, survivingModulus, hg']
    have hnot : ¬(pi x).1 ≡ (pi y).1 [MOD Mx] := by
      rw [← int_dvd_sub_iff_natModEq]
      exact hpartial x y hxClass hyClass hxy
    have hei := (partialGoodExtension_natModEq N u d q pi i).of_dvd hMN
    have hej := (partialGoodExtension_natModEq N u d q pi j).of_dvd hMN
    have hsum : (pi x).1 + d * q i ≡ (pi y).1 + d * q j [MOD M] :=
      hei.symm.trans (hbad.trans hej)
    have hpimod : (pi x).1 ≡ (pi y).1 [MOD M] := by
      rw [hq] at hsum
      exact Nat.ModEq.add_right_cancel' (d * q j) hsum
    exact hnot (hMMx ▸ hpimod)
  · have hgu : g ∣ u := gcd_indexDiff_dvd_u_of_cross hp hN i j hs
    have hgD : g ∣ d := gcd_indexDiff_dvd_d_of_cross hp hn hpd hN hs
    have hpN : p ∣ N := by rw [hpd]; exact dvd_mul_right p d
    have hpPowN : p ^ n ∣ N := by
      rw [hN]
      exact dvd_mul_left (p ^ n) u
    have hpPowM : p ^ n ∣ M :=
      pow_dvd_survivingModulus_of_gcd_dvd_u hN hgu
    by_cases hxyEq : x = y
    · have hqne : ¬q i ≡ q j [MOD p] :=
        q_not_modEq_of_shift_eq_of_cross q hpN hs hxyEq
      have hbadPow := hbad.of_dvd hpPowM
      have hei := (partialGoodExtension_natModEq N u d q pi i).of_dvd hpPowN
      have hej := (partialGoodExtension_natModEq N u d q pi j).of_dvd hpPowN
      have hsum : (pi x).1 + d * q i ≡ (pi y).1 + d * q j [MOD p ^ n] :=
        hei.symm.trans (hbadPow.trans hej)
      rw [hxyEq] at hsum
      have hcorr : d * q i ≡ d * q j [MOD p ^ n] :=
        Nat.ModEq.add_left_cancel' (pi y).1 hsum
      exact correction_not_modEq_pow hp hn hcop hpd hN hqne hcorr
    · have hgpx : g * p ∣ gx := by
        apply gcd_mul_p_dvd_shift_gcd hp hn hN q hs
        rw [hxClass, hyClass]
      have hxN : gx ∣ N := Nat.gcd_dvd_left _ _
      have hMxDg : Mx ∣ d / g :=
        div_gcd_dvd_div_gcd_of_mul_dvd hp.pos hpd hgD hxN hgpx
      have hdN : d ∣ N := by rw [hpd]; exact dvd_mul_left d p
      have hDgM : d / g ∣ M := Nat.div_dvd_div hgD hdN
      have hbadDg := hbad.of_dvd hDgM
      have hDgN : d / g ∣ N := hDgM.trans hMN
      have hei := (partialGoodExtension_natModEq N u d q pi i).of_dvd hDgN
      have hej := (partialGoodExtension_natModEq N u d q pi j).of_dvd hDgN
      have hsum : (pi x).1 + d * q i ≡ (pi y).1 + d * q j [MOD d / g] :=
        hei.symm.trans (hbadDg.trans hej)
      have hdgi : d * q i ≡ 0 [MOD d / g] :=
        Nat.modEq_zero_iff_dvd.mpr
          (dvd_mul_of_dvd_left (Nat.div_dvd_of_dvd hgD) _)
      have hdgj : d * q j ≡ 0 [MOD d / g] :=
        Nat.modEq_zero_iff_dvd.mpr
          (dvd_mul_of_dvd_left (Nat.div_dvd_of_dvd hgD) _)
      have hpimodDg : (pi x).1 ≡ (pi y).1 [MOD d / g] :=
        hdgi.add_right_cancel (hsum.trans (Nat.ModEq.rfl.add hdgj))
      have hpimodMx : (pi x).1 ≡ (pi y).1 [MOD Mx] := hpimodDg.of_dvd hMxDg
      have hnot : ¬(pi x).1 ≡ (pi y).1 [MOD Mx] := by
        rw [← int_dvd_sub_iff_natModEq]
        exact hpartial x y hxClass hyClass hxyEq
      exact hnot hpimodMx

lemma partialGoodExtension_eq_on_distinguished
    {N u d p i₀ : ℕ} (q : Fin N → ℕ) (pi : Fin N → Fin N)
    (hqzero : ∀ i : Fin N, i.1 % p = i₀ → q i = 0)
    (i : Fin N) (hi : i.1 % p = i₀) :
    partialGoodExtension N u d q pi i = pi i := by
  have hq : q i = 0 := hqzero i hi
  apply Fin.ext
  simp [partialGoodExtension, partialGoodShift, hq, Nat.mod_eq_of_lt i.2,
    Nat.mod_eq_of_lt (pi i).2]

/-- Permutation packaging of `partialGoodExtension_good`.  It is literally
value-identical to the given partial map on the distinguished class. -/
theorem exists_goodPerm_extending_partial
    {N u d p n i₀ : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hcop : Nat.Coprime p u) (hpd : N = p * d) (hN : N = u * p ^ n)
    (q : Fin N → ℕ) (pi : Fin N → Fin N)
    (hqclass : ∀ i j : Fin N, i.1 % p = j.1 % p → q i = q j)
    (hqzero : ∀ i : Fin N, i.1 % p = i₀ → q i = 0)
    (hshiftClass : ∀ i : Fin N, (partialGoodShift N u q i).1 % p = i₀)
    (hpartial : PartialGoodOnClass N p i₀ pi) :
    ∃ sigma : Equiv.Perm (Fin N), GoodPerm N sigma ∧
      ∀ i : Fin N, i.1 % p = i₀ → sigma i = pi i := by
  have hg : GoodMap N (partialGoodExtension N u d q pi) :=
    partialGoodExtension_good hp hn hcop hpd hN q pi hqclass hshiftClass hpartial
  refine ⟨GoodMap.toPerm (partialGoodExtension N u d q pi) hg,
    GoodMap.goodPerm_toPerm _ hg, ?_⟩
  intro i hi
  rw [GoodMap.toPerm_apply,
    partialGoodExtension_eq_on_distinguished q pi hqzero i hi]

end Erdos215.Selector.PartialGood

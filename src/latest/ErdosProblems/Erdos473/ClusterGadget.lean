import Mathlib
import ErdosProblems.Erdos473.PrimeCluster

namespace Erdos473

open Function

def PrimeAdjacent (x y : ℕ+) : Prop := Nat.Prime ((x : ℕ) + (y : ℕ))


namespace PrimeCluster

variable {H : ℕ} (C : PrimeCluster H)

private lemma D_pos : 0 < C.D := lt_of_le_of_lt (Nat.zero_le _) C.D_large

private def ResidueStep (z w : ZMod C.D) : Prop :=
  ∃ d ∈ C.gaps, w = z + d ∨ z = w + d

private lemma residueStep_symm {z w : ZMod C.D} :
    C.ResidueStep z w → C.ResidueStep w z := by
  rintro ⟨d, hd, h | h⟩
  · exact ⟨d, hd, Or.inr h⟩
  · exact ⟨d, hd, Or.inl h⟩

private lemma residueStep_add_left (c : ZMod C.D) {z w : ZMod C.D}
    (h : C.ResidueStep z w) : C.ResidueStep (c + z) (c + w) := by
  rcases h with ⟨d, hd, h | h⟩
  · refine ⟨d, hd, Or.inl ?_⟩
    rw [h]
    abel
  · refine ⟨d, hd, Or.inr ?_⟩
    rw [h]
    abel

private lemma residueStep_neg {z w : ZMod C.D}
    (h : C.ResidueStep z w) : C.ResidueStep (-z) (-w) := by
  rcases h with ⟨d, hd, h | h⟩
  · refine ⟨d, hd, Or.inr ?_⟩
    rw [h]
    abel
  · refine ⟨d, hd, Or.inl ?_⟩
    rw [h]
    abel

private lemma residueReach_add_left (c : ZMod C.D) {z w : ZMod C.D}
    (h : Relation.ReflTransGen C.ResidueStep z w) :
    Relation.ReflTransGen C.ResidueStep (c + z) (c + w) := by
  exact Relation.ReflTransGen.lift (c + ·) (fun _ _ => C.residueStep_add_left c) z w h

private lemma residueReach_neg {z w : ZMod C.D}
    (h : Relation.ReflTransGen C.ResidueStep z w) :
    Relation.ReflTransGen C.ResidueStep (-z) (-w) := by
  exact Relation.ReflTransGen.lift (- ·) (fun _ _ => C.residueStep_neg) z w h

private def reachableSubgroup : AddSubgroup (ZMod C.D) where
  carrier := {z | Relation.ReflTransGen C.ResidueStep 0 z}
  zero_mem' := Relation.ReflTransGen.refl
  add_mem' := by
    intro z w hz hw
    exact hz.trans (by simpa using C.residueReach_add_left z hw)
  neg_mem' := by
    intro z hz
    simpa using C.residueReach_neg hz

private lemma gap_mem_reachable {d : ℕ} (hd : d ∈ C.gaps) :
    (d : ZMod C.D) ∈ C.reachableSubgroup := by
  exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨d, hd, Or.inl (by simp)⟩

private lemma two_mem_reachable : (2 : ZMod C.D) ∈ C.reachableSubgroup := by
  obtain ⟨coeff, hcoeff⟩ := Finset.gcd_eq_sum_mul C.gaps (fun d => (d : ℤ))
  have hsum : (∑ d ∈ C.gaps, coeff d • (d : ZMod C.D)) ∈ C.reachableSubgroup := by
    apply C.reachableSubgroup.sum_mem
    intro d hd
    exact C.reachableSubgroup.zsmul_mem (C.gap_mem_reachable hd) (coeff d)
  have heq : (2 : ZMod C.D) = ∑ d ∈ C.gaps, coeff d • (d : ZMod C.D) := by
    have hz := congrArg (fun x : ℤ => (x : ZMod C.D))
      (C.gcd_eq_two.symm.trans hcoeff)
    simpa [smul_eq_mul, mul_comm] using hz
  rwa [heq]

private lemma residueReach_of_even_difference {z w : ZMod C.D} (k : ℤ)
    (h : w - z = k • (2 : ZMod C.D)) :
    Relation.ReflTransGen C.ResidueStep z w := by
  have hd : w - z ∈ C.reachableSubgroup := by
    rw [h]
    exact C.reachableSubgroup.zsmul_mem C.two_mem_reachable k
  have ht := C.residueReach_add_left z hd
  simpa using ht

private instance : NeZero C.D := ⟨C.D_pos.ne'⟩

private def band (z : ZMod C.D) : ℕ+ :=
  ⟨H + 1 + z.val, by omega⟩

@[simp] private lemma coe_band (z : ZMod C.D) :
    (C.band z : ℕ) = H + 1 + z.val := rfl

private lemma band_gt (z : ZMod C.D) : H < (C.band z : ℕ) := by
  simp only [C.coe_band]
  omega

private def Allowed (H : ℕ) (x y v : ℕ+) : Prop :=
  v = x ∨ v = y ∨ H < (v : ℕ)

private def AvoidRel (H : ℕ) (x y u v : ℕ+) : Prop :=
  PrimeAdjacent u v ∧ Allowed H x y u ∧ Allowed H x y v

private lemma avoidRel_symm (x y : ℕ+) {u v : ℕ+} :
    AvoidRel H x y u v → AvoidRel H x y v u := by
  rintro ⟨hp, hu, hv⟩
  exact ⟨by simpa [PrimeAdjacent, Nat.add_comm] using hp, hv, hu⟩

private lemma avoidReach_symm (x y : ℕ+) {u v : ℕ+}
    (h : Relation.ReflTransGen (AvoidRel H x y) u v) :
    Relation.ReflTransGen (AvoidRel H x y) v u := by
  exact Relation.ReflTransGen.mono (fun _ _ => avoidRel_symm (H := H) x y) v u h.swap

private lemma avoidRel_of_gt (x y u v : ℕ+) (hu : H < (u : ℕ))
    (hv : H < (v : ℕ)) (hp : PrimeAdjacent u v) : AvoidRel H x y u v := by
  exact ⟨hp, Or.inr (Or.inr hu), Or.inr (Or.inr hv)⟩

private lemma val_add_gap {z w : ZMod C.D} {d : ℕ}
    (h : w = z + d) : w.val = (z.val + d) % C.D := by
  subst w
  rw [ZMod.val_add, ZMod.val_natCast]
  calc
    (z.val + d % C.D) % C.D = (z.val % C.D + d % C.D) % C.D := by
      rw [Nat.mod_eq_of_lt z.val_lt]
    _ = (z.val + d) % C.D := (Nat.add_mod z.val d C.D).symm

private lemma band_step_forward (x y : ℕ+) {z w : ZMod C.D} {d : ℕ}
    (hd : d ∈ C.gaps) (hw : w = z + d) :
    Relation.ReflTransGen (AvoidRel H x y) (C.band z) (C.band w) := by
  have hdle : d ≤ C.D := C.gap_le d hd
  have hzlt : z.val < C.D := z.val_lt
  have hleft := C.left_large
  have hwval := C.val_add_gap hw
  by_cases hnowrap : z.val + d < C.D
  · have hwval' : w.val = z.val + d := by
      rw [hwval, Nat.mod_eq_of_lt hnowrap]
    have hub : H + 1 + z.val ≤ C.q0 := by omega
    have hmgt : H < C.q0 - (H + 1 + z.val) := by omega
    let m : ℕ+ := ⟨C.q0 - (H + 1 + z.val), by omega⟩
    have he1 : PrimeAdjacent (C.band z) m := by
      have hp0 := C.prime 0 C.zero_mem
      change Nat.Prime ((H + 1 + z.val) + (C.q0 - (H + 1 + z.val)))
      rw [Nat.add_sub_of_le hub]
      simpa using hp0
    have he2 : PrimeAdjacent m (C.band w) := by
      have hpd := C.prime d hd
      change Nat.Prime ((C.q0 - (H + 1 + z.val)) + (H + 1 + w.val))
      rw [hwval']
      have heq : C.q0 - (H + 1 + z.val) + (H + 1 + (z.val + d)) = C.q0 + d := by
        omega
      rwa [heq]
    exact (Relation.ReflTransGen.single
      (avoidRel_of_gt (H := H) x y (C.band z) m (C.band_gt z) hmgt he1)).tail
      (avoidRel_of_gt (H := H) x y m (C.band w) hmgt (C.band_gt w) he2)
  · have hwrap : C.D ≤ z.val + d := Nat.le_of_not_gt hnowrap
    have hsum_lt : z.val + d < C.D + C.D := by omega
    have hwval' : w.val = z.val + d - C.D := by
      rw [hwval, Nat.mod_eq_sub_mod hwrap,
        Nat.mod_eq_of_lt (by omega)]
    have hub : H + 1 + z.val ≤ C.q0 + C.D := by omega
    have hmgt : H < C.q0 + C.D - (H + 1 + z.val) := by omega
    let m : ℕ+ := ⟨C.q0 + C.D - (H + 1 + z.val), by omega⟩
    have he1 : PrimeAdjacent (C.band z) m := by
      have hpD := C.prime C.D C.D_mem
      change Nat.Prime ((H + 1 + z.val) +
        (C.q0 + C.D - (H + 1 + z.val)))
      rw [Nat.add_sub_of_le hub]
      exact hpD
    have he2 : PrimeAdjacent m (C.band w) := by
      have hpd := C.prime d hd
      change Nat.Prime ((C.q0 + C.D - (H + 1 + z.val)) +
        (H + 1 + w.val))
      rw [hwval']
      have heq : C.q0 + C.D - (H + 1 + z.val) +
          (H + 1 + (z.val + d - C.D)) = C.q0 + d := by
        omega
      rwa [heq]
    exact (Relation.ReflTransGen.single
      (avoidRel_of_gt (H := H) x y (C.band z) m (C.band_gt z) hmgt he1)).tail
      (avoidRel_of_gt (H := H) x y m (C.band w) hmgt (C.band_gt w) he2)

private lemma band_step (x y : ℕ+) {z w : ZMod C.D}
    (h : C.ResidueStep z w) :
    Relation.ReflTransGen (AvoidRel H x y) (C.band z) (C.band w) := by
  rcases h with ⟨d, hd, hw | hz⟩
  · exact C.band_step_forward x y hd hw
  · exact avoidReach_symm (H := H) x y (C.band_step_forward x y hd hz)

private lemma band_reach (x y : ℕ+) {z w : ZMod C.D}
    (h : Relation.ReflTransGen C.ResidueStep z w) :
    Relation.ReflTransGen (AvoidRel H x y) (C.band z) (C.band w) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hstep ih => exact ih.trans (C.band_step x y hstep)

private def endpointResidue (a : ℕ+) : ZMod C.D :=
  (C.D + (a : ℕ) - (H + 1) : ℕ)

private lemma endpoint_offset_lt (a : ℕ+) (ha : (a : ℕ) ≤ H) :
    C.D + (a : ℕ) - (H + 1) < C.D := by
  have hD := C.D_large
  have apos := a.prop
  have hbase : H + 1 ≤ C.D + (a : ℕ) := by omega
  omega

private lemma endpointResidue_val (a : ℕ+) (ha : (a : ℕ) ≤ H) :
    (C.endpointResidue a).val = C.D + (a : ℕ) - (H + 1) := by
  rw [endpointResidue, ZMod.val_natCast,
    Nat.mod_eq_of_lt (C.endpoint_offset_lt a ha)]

private lemma band_endpointResidue (a : ℕ+) (ha : (a : ℕ) ≤ H) :
    C.band (C.endpointResidue a) =
      (⟨C.D + (a : ℕ), Nat.add_pos_right C.D a.prop⟩ : ℕ+) := by
  apply Subtype.ext
  change H + 1 + (C.endpointResidue a).val = C.D + (a : ℕ)
  rw [C.endpointResidue_val a ha]
  have hD := C.D_large
  have apos := a.prop
  have hbase : H + 1 ≤ C.D + (a : ℕ) := by omega
  omega

private lemma endpointResidue_sub {a b : ℕ+}
    (_ha : (a : ℕ) ≤ H) (_hb : (b : ℕ) ≤ H) (k : ℤ)
    (hk : (b : ℤ) - (a : ℤ) = 2 * k) :
    C.endpointResidue b - C.endpointResidue a =
      k • (2 : ZMod C.D) := by
  have haBase : H + 1 ≤ C.D + (a : ℕ) := by
    have hD := C.D_large
    omega
  have hbBase : H + 1 ≤ C.D + (b : ℕ) := by
    have hD := C.D_large
    omega
  change ((C.D + (b : ℕ) - (H + 1) : ℕ) : ZMod C.D) -
    ((C.D + (a : ℕ) - (H + 1) : ℕ) : ZMod C.D) = _
  push_cast [haBase, hbBase]
  have hcast := congrArg (fun z : ℤ => (z : ZMod C.D)) hk
  simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_mul] at hcast
  simpa [smul_eq_mul, mul_comm] using hcast

private lemma endpoint_to_band (x y a : ℕ+) (ha : (a : ℕ) ≤ H)
    (haend : a = x ∨ a = y) :
    Relation.ReflTransGen (AvoidRel H x y) a (C.band (C.endpointResidue a)) := by
  have hleft := C.left_large
  have hD := C.D_large
  have aleq0 : (a : ℕ) ≤ C.q0 := by omega
  have hmgt : H < C.q0 - (a : ℕ) := by omega
  let m : ℕ+ := ⟨C.q0 - (a : ℕ), by omega⟩
  have he1 : PrimeAdjacent a m := by
    have hp0 := C.prime 0 C.zero_mem
    change Nat.Prime ((a : ℕ) + (C.q0 - (a : ℕ)))
    rw [Nat.add_sub_of_le aleq0]
    simpa using hp0
  have he2raw : PrimeAdjacent m
      (⟨C.D + (a : ℕ), by omega⟩ : ℕ+) := by
    have hpD := C.prime C.D C.D_mem
    change Nat.Prime ((C.q0 - (a : ℕ)) + (C.D + (a : ℕ)))
    have heq : C.q0 - (a : ℕ) + (C.D + (a : ℕ)) = C.q0 + C.D := by omega
    rwa [heq]
  have he2 : PrimeAdjacent m (C.band (C.endpointResidue a)) := by
    rw [C.band_endpointResidue a ha]
    exact he2raw
  have haAllowed : Allowed H x y a := by
    rcases haend with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hmAllowed : Allowed H x y m := Or.inr (Or.inr hmgt)
  have hbandAllowed : Allowed H x y (C.band (C.endpointResidue a)) :=
    Or.inr (Or.inr (C.band_gt _))
  exact (Relation.ReflTransGen.single ⟨he1, haAllowed, hmAllowed⟩).tail
    ⟨he2, hmAllowed, hbandAllowed⟩

private lemma connect_same_parity (C : PrimeCluster H) (x y : ℕ+) (hx : (x : ℕ) ≤ H)
    (hy : (y : ℕ) ≤ H) (hpar : (x : ℕ) % 2 = (y : ℕ) % 2) :
    Relation.ReflTransGen (AvoidRel H x y) x y := by
  have hmod : Nat.ModEq 2 (x : ℕ) (y : ℕ) := hpar
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd.mp hmod)
  have hk' : (y : ℤ) - (x : ℤ) = 2 * k := by simpa using hk
  have hres := residueReach_of_even_difference (C := C) k
    (C.endpointResidue_sub hx hy k hk')
  have hband := C.band_reach x y hres
  exact (C.endpoint_to_band x y x hx (Or.inl rfl)).trans <|
    hband.trans <| avoidReach_symm (H := H) x y
      (C.endpoint_to_band x y y hy (Or.inr rfl))

private def lowerResidue (z : ℕ) : ZMod C.D :=
  (z - (H + 1) : ℕ)

private lemma lowerResidue_val_of_band {z : ℕ} (hz : H < z)
    (hzband : z ≤ H + C.D) :
    (C.lowerResidue z).val = z - (H + 1) := by
  rw [lowerResidue, ZMod.val_natCast, Nat.mod_eq_of_lt]
  omega

private lemma band_lowerResidue_of_band {z : ℕ} (hz : H < z)
    (hzband : z ≤ H + C.D) :
    C.band (C.lowerResidue z) = (⟨z, by omega⟩ : ℕ+) := by
  apply Subtype.ext
  change H + 1 + (C.lowerResidue z).val = z
  rw [C.lowerResidue_val_of_band hz hzband]
  omega

private lemma lowerResidue_sub_D {z : ℕ} (hz : H + C.D < z) :
    C.lowerResidue (z - C.D) = C.lowerResidue z := by
  have hDz : C.D ≤ z := by omega
  have hbasez : H + 1 ≤ z := by omega
  have hbasezd : H + 1 ≤ z - C.D := by omega
  change ((z - C.D - (H + 1) : ℕ) : ZMod C.D) =
    ((z - (H + 1) : ℕ) : ZMod C.D)
  push_cast [hDz, hbasez, hbasezd]
  simp

private lemma descend_to_band (C : PrimeCluster H) (x y : ℕ+) (z : ℕ)
    (hz : H < z) (hzq : z ≤ C.q0) :
    Relation.ReflTransGen (AvoidRel H x y) (⟨z, by omega⟩ : ℕ+)
      (C.band (C.lowerResidue z)) := by
  induction z using Nat.strong_induction_on with
  | h z ih =>
      by_cases hzband : z ≤ H + C.D
      · rw [C.band_lowerResidue_of_band hz hzband]
        exact Relation.ReflTransGen.refl
      · have hzbig : H + C.D < z := Nat.lt_of_not_ge hzband
        have hDpos := C.D_pos
        have hDlarge := C.D_large
        have hzDgt : H < z - C.D := by omega
        have hzDlt : z - C.D < z := Nat.sub_lt (by omega) hDpos
        have hzDq : z - C.D ≤ C.q0 := by omega
        have hmgt : H < C.q0 + C.D - z := by omega
        let m : ℕ+ := ⟨C.q0 + C.D - z, by omega⟩
        let z' : ℕ+ := ⟨z - C.D, by omega⟩
        have he1 : PrimeAdjacent (⟨z, by omega⟩ : ℕ+) m := by
          have hpD := C.prime C.D C.D_mem
          change Nat.Prime (z + (C.q0 + C.D - z))
          have hle : z ≤ C.q0 + C.D := by omega
          rw [Nat.add_sub_of_le hle]
          exact hpD
        have he2 : PrimeAdjacent m z' := by
          have hp0 := C.prime 0 C.zero_mem
          change Nat.Prime ((C.q0 + C.D - z) + (z - C.D))
          have heq : C.q0 + C.D - z + (z - C.D) = C.q0 := by omega
          rw [heq]
          simpa using hp0
        have hzAllowed : Allowed H x y (⟨z, by omega⟩ : ℕ+) :=
          Or.inr (Or.inr hz)
        have hmAllowed : Allowed H x y m := Or.inr (Or.inr hmgt)
        have hz'Allowed : Allowed H x y z' := Or.inr (Or.inr hzDgt)
        have htwo : Relation.ReflTransGen (AvoidRel H x y)
            (⟨z, by omega⟩ : ℕ+) z' :=
          (Relation.ReflTransGen.single ⟨he1, hzAllowed, hmAllowed⟩).tail
            ⟨he2, hmAllowed, hz'Allowed⟩
        have hrec := ih (z - C.D) hzDlt hzDgt hzDq
        have hresEq := C.lowerResidue_sub_D hzbig
        exact htwo.trans (by simpa [z', hresEq] using hrec)

private lemma two_dvd_D : 2 ∣ C.D := by
  have hd := Finset.gcd_dvd (s := C.gaps) (f := fun d => (d : ℤ)) C.D_mem
  rw [C.gcd_eq_two] at hd
  exact Int.natCast_dvd_natCast.mp (by simpa using hd)

private lemma D_mod_two : C.D % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp C.two_dvd_D

private lemma q0_mod_two : C.q0 % 2 = 1 := by
  have hp0 : Nat.Prime C.q0 := by simpa using C.prime 0 C.zero_mem
  apply hp0.mod_two_eq_one_iff_ne_two.mpr
  have hleft := C.left_large
  have hD := C.D_large
  have hDtwo : 2 ≤ C.D := Nat.le_of_dvd C.D_pos C.two_dvd_D
  omega

private lemma odd_sub_mod_two {q a b : ℕ} (haq : a ≤ q) (hq : q % 2 = 1)
    (hab : a % 2 ≠ b % 2) : (q - a) % 2 = b % 2 := by
  have hamod : a % 2 < 2 := Nat.mod_lt _ (by decide)
  have hbmod : b % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

private lemma band_lowerResidue_modEq {z : ℕ} (hz : H < z) :
    Nat.ModEq C.D (C.band (C.lowerResidue z) : ℕ) z := by
  change Nat.ModEq C.D (H + 1 + (C.lowerResidue z).val) z
  rw [lowerResidue, ZMod.val_natCast]
  have hm := (Nat.mod_modEq (z - (H + 1)) C.D).add_left (H + 1)
  have hsum : H + 1 + (z - (H + 1)) = z := by omega
  simpa [hsum] using hm

private lemma residue_sub_of_band_difference {z w : ZMod C.D} (k : ℤ)
    (hk : ((C.band w : ℕ) : ℤ) - ((C.band z : ℕ) : ℤ) = 2 * k) :
    w - z = k • (2 : ZMod C.D) := by
  have hcast := congrArg (fun t : ℤ => (t : ZMod C.D)) hk
  simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_mul] at hcast
  simp only [C.coe_band, Nat.cast_add, Nat.cast_one] at hcast
  simpa [smul_eq_mul, mul_comm] using hcast

private lemma connect_band_same_parity (C : PrimeCluster H) (x y : ℕ+)
    (z w : ZMod C.D)
    (hpar : (C.band z : ℕ) % 2 = (C.band w : ℕ) % 2) :
    Relation.ReflTransGen (AvoidRel H x y) (C.band z) (C.band w) := by
  have hmod : Nat.ModEq 2 (C.band z : ℕ) (C.band w : ℕ) := hpar
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hmod
  have hk' : ((C.band w : ℕ) : ℤ) - ((C.band z : ℕ) : ℤ) = 2 * k := by
    simpa using hk
  exact C.band_reach x y <| residueReach_of_even_difference (C := C) k <|
    C.residue_sub_of_band_difference k hk'

private lemma connect_opposite_parity (C : PrimeCluster H) (x y : ℕ+)
    (hx : (x : ℕ) ≤ H) (hy : (y : ℕ) ≤ H)
    (hpar : (x : ℕ) % 2 ≠ (y : ℕ) % 2) :
    Relation.ReflTransGen (AvoidRel H x y) x y := by
  have hleft := C.left_large
  have hD := C.D_large
  have hxq : (x : ℕ) ≤ C.q0 := by omega
  have hzgt : H < C.q0 - (x : ℕ) := by omega
  have hzq : C.q0 - (x : ℕ) ≤ C.q0 := Nat.sub_le _ _
  let z : ℕ+ := ⟨C.q0 - (x : ℕ), by omega⟩
  have hex : PrimeAdjacent x z := by
    have hp0 := C.prime 0 C.zero_mem
    change Nat.Prime ((x : ℕ) + (C.q0 - (x : ℕ)))
    rw [Nat.add_sub_of_le hxq]
    simpa using hp0
  have hxAllowed : Allowed H x y x := Or.inl rfl
  have hzAllowed : Allowed H x y z := Or.inr (Or.inr hzgt)
  have hfirst : Relation.ReflTransGen (AvoidRel H x y) x z :=
    Relation.ReflTransGen.single ⟨hex, hxAllowed, hzAllowed⟩
  have hdesc := C.descend_to_band x y (C.q0 - (x : ℕ)) hzgt hzq
  have hbandzParity : (C.band (C.lowerResidue (C.q0 - (x : ℕ))) : ℕ) % 2 =
      (C.q0 - (x : ℕ)) % 2 := by
    exact (C.band_lowerResidue_modEq hzgt).of_dvd C.two_dvd_D
  have hzParityY : (C.q0 - (x : ℕ)) % 2 = (y : ℕ) % 2 := by
    exact odd_sub_mod_two hxq C.q0_mod_two hpar
  have htargetParity : (C.band (C.endpointResidue y) : ℕ) % 2 = (y : ℕ) % 2 := by
    rw [C.band_endpointResidue y hy]
    change (C.D + (y : ℕ)) % 2 = (y : ℕ) % 2
    rw [Nat.add_mod, C.D_mod_two]
    simp
  have hbands : Relation.ReflTransGen (AvoidRel H x y)
      (C.band (C.lowerResidue (C.q0 - (x : ℕ))))
      (C.band (C.endpointResidue y)) :=
    C.connect_band_same_parity x y _ _ (hbandzParity.trans (hzParityY.trans htargetParity.symm))
  exact hfirst.trans <| hdesc.trans <| hbands.trans <|
    avoidReach_symm (H := H) x y
      (C.endpoint_to_band x y y hy (Or.inr rfl))

/-- The finite cluster connects any two positive integers at most `H`, while
all other vertices of the walk are larger than `H`. -/
theorem avoiding_reach (C : PrimeCluster H) (x y : ℕ+)
    (hx : (x : ℕ) ≤ H) (hy : (y : ℕ) ≤ H) :
    Relation.ReflTransGen (AvoidRel H x y) x y := by
  by_cases hpar : (x : ℕ) % 2 = (y : ℕ) % 2
  · exact C.connect_same_parity x y hx hy hpar
  · exact C.connect_opposite_parity x y hx hy hpar

end PrimeCluster

private lemma nonempty_walk_of_reflTransGen {α : Type*}
    {R : α → α → Prop} {a b : α} (h : Relation.ReflTransGen R a b) :
    Nonempty ((SimpleGraph.fromRel R).Walk a b) := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil⟩
  | @tail b c hab hbc ih =>
      obtain ⟨p⟩ := ih
      by_cases hEq : b = c
      · subst c
        exact ⟨p⟩
      · exact ⟨p.append <| SimpleGraph.Walk.cons
          ((SimpleGraph.fromRel_adj R b c).mpr ⟨hEq, Or.inl hbc⟩)
          SimpleGraph.Walk.nil⟩

private lemma chain_tail_forall {α : Type*} {R : α → α → Prop} {P : α → Prop}
    (hP : ∀ ⦃u v⦄, R u v → P v) :
    ∀ (a : α) (t : List α), (a :: t).IsChain R → ∀ z ∈ t, P z := by
  intro a t
  induction t generalizing a with
  | nil => simp
  | cons b t ih =>
      intro hchain z hz
      have hab := hchain.rel
      have hrest := hchain.tail
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hP hab
      · exact ih b hrest z hz

/-- Cycle erasure for a symmetric relation, packaged in the tail-list format
used by `FinitelyAvoidablyConnected`. -/
private lemma simple_chain_of_reflTransGen {α : Type*}
    {R : α → α → Prop} (hsymm : ∀ ⦃u v⦄, R u v → R v u) {a b : α}
    (h : Relation.ReflTransGen R a b) :
    ∃ t : List α, (a :: t).Nodup ∧ (a :: t).IsChain R ∧
      (a :: t).getLast? = some b := by
  classical
  let p := (Classical.choice (nonempty_walk_of_reflTransGen h)).toPath
  let l := (p : (SimpleGraph.fromRel R).Walk a b).support
  have hlne : l ≠ [] := (p : (SimpleGraph.fromRel R).Walk a b).support_ne_nil
  have hlhead : l.head hlne = a := (p : (SimpleGraph.fromRel R).Walk a b).head_support
  have hcons : a :: l.tail = l := by
    rw [← hlhead]
    exact List.cons_head_tail hlne
  refine ⟨l.tail, ?_, ?_, ?_⟩
  · rw [hcons]
    exact p.nodup_support
  · rw [hcons]
    apply (p : (SimpleGraph.fromRel R).Walk a b).isChain_adj_support.imp
    intro u v huv
    exact ((SimpleGraph.fromRel_adj R u v).mp huv).2.elim id (fun hvu => @hsymm v u hvu)
  · rw [hcons, List.getLast?_eq_some_getLast hlne,
      (p : (SimpleGraph.fromRel R).Walk a b).getLast_support]

/-- After deleting any finite set, every two surviving vertices have a finite
simple prime-sum path. -/
def FinitelyAvoidablyConnected {α : Type*} (R : α → α → Prop) : Prop :=
  ∀ (F : Finset α) (x y : α), x ∉ F → y ∉ F →
    ∃ t : List α, (x :: t).Nodup ∧ (x :: t).IsChain R ∧
      (x :: t).getLast? = some y ∧ ∀ z ∈ t, z ∉ F

/-- Prime clusters with arbitrarily large safety parameter imply finite-deletion
connectivity of the prime-sum graph. -/
theorem finitelyAvoidablyConnected_of_clusters
    (clusters : ∀ H : ℕ, Nonempty (PrimeCluster H)) :
    FinitelyAvoidablyConnected PrimeAdjacent := by
  intro F x y hxF hyF
  classical
  let H := max (max (x : ℕ) (y : ℕ)) (F.sup fun z => (z : ℕ))
  have hxH : (x : ℕ) ≤ H := by simp [H]
  have hyH : (y : ℕ) ≤ H := by simp [H]
  have hFH : ∀ z ∈ F, (z : ℕ) ≤ H := by
    intro z hz
    exact le_trans (Finset.le_sup (f := fun z : ℕ+ => (z : ℕ)) hz) (le_max_right _ _)
  let C : PrimeCluster H := (clusters H).some
  have hreach := C.avoiding_reach x y hxH hyH
  let R : ℕ+ → ℕ+ → Prop := fun u v =>
    PrimeAdjacent u v ∧ u ∉ F ∧ v ∉ F
  have allowed_not_mem : ∀ {v : ℕ+}, PrimeCluster.Allowed H x y v → v ∉ F := by
    intro v hv
    rcases hv with rfl | rfl | hv
    · exact hxF
    · exact hyF
    · intro hvF
      exact (not_lt_of_ge (hFH v hvF)) hv
  have hrestricted : Relation.ReflTransGen R x y := by
    exact Relation.ReflTransGen.mono
      (r := PrimeCluster.AvoidRel H x y) (p := R)
      (fun _ _ huv => ⟨huv.1, allowed_not_mem huv.2.1, allowed_not_mem huv.2.2⟩)
      x y hreach
  have hsymm : ∀ ⦃u v⦄, R u v → R v u := by
    rintro u v ⟨hp, hu, hv⟩
    exact ⟨by simpa [PrimeAdjacent, Nat.add_comm] using hp, hv, hu⟩
  obtain ⟨t, hnodup, hchainR, hlast⟩ :=
    simple_chain_of_reflTransGen hsymm hrestricted
  have hchain : (x :: t).IsChain PrimeAdjacent :=
    hchainR.imp (fun ⦃_ _⦄ h => h.1)
  have havoid : ∀ z ∈ t, z ∉ F :=
    chain_tail_forall (R := R) (P := fun z => z ∉ F)
      (fun ⦃_ _⦄ h => h.2.2) x t hchainR
  exact ⟨t, hnodup, hchain, hlast, havoid⟩

end Erdos473

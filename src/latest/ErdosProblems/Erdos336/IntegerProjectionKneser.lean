import ErdosProblems.Erdos336.KneserConsequences
import ErdosProblems.Erdos336.VerticalStabilizer

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

/-- The elementary torsion-free sumset bound for finite integer sets. -/
theorem card_add_int_ge
    (P Q : Finset ℤ) (hP : P.Nonempty) (hQ : Q.Nonempty) :
    P.card + Q.card - 1 ≤ (P + Q).card := by
  let pmax := P.max' hP
  let qmin := Q.min' hQ
  let D := ↥P ⊕ ↥(Q.erase qmin)
  let f : D → ↥(P + Q) := fun u =>
    match u with
    | Sum.inl p => ⟨p.1 + qmin,
        Finset.mem_add.mpr ⟨p.1, p.2, qmin, Finset.min'_mem Q hQ, rfl⟩⟩
    | Sum.inr q => ⟨pmax + q.1,
        Finset.mem_add.mpr ⟨pmax, Finset.max'_mem P hP, q.1,
          Finset.mem_of_mem_erase q.2, rfl⟩⟩
  have hf : Function.Injective f := by
    intro u v huv
    rcases u with p | q <;> rcases v with p' | q'
    · apply congrArg Sum.inl
      apply Subtype.ext
      have h := congrArg (fun x : ↥(P + Q) => x.1) huv
      exact add_right_cancel h
    · exfalso
      have h := congrArg (fun x : ↥(P + Q) => x.1) huv
      change p.1 + qmin = pmax + q'.1 at h
      have hp : p.1 ≤ pmax := Finset.le_max' P p.1 p.2
      have hq : qmin < q'.1 := by
        have hle := Finset.min'_le Q q'.1 (Finset.mem_of_mem_erase q'.2)
        have hne : q'.1 ≠ qmin := (Finset.mem_erase.mp q'.2).1
        omega
      omega
    · exfalso
      have h := congrArg (fun x : ↥(P + Q) => x.1) huv
      change pmax + q.1 = p'.1 + qmin at h
      have hp : p'.1 ≤ pmax := Finset.le_max' P p'.1 p'.2
      have hq : qmin < q.1 := by
        have hle := Finset.min'_le Q q.1 (Finset.mem_of_mem_erase q.2)
        have hne : q.1 ≠ qmin := (Finset.mem_erase.mp q.2).1
        omega
      omega
    · apply congrArg Sum.inr
      apply Subtype.ext
      have h := congrArg (fun x : ↥(P + Q) => x.1) huv
      exact add_left_cancel h
  have hc := Fintype.card_le_of_injective f hf
  change Fintype.card (↥P ⊕ ↥(Q.erase qmin)) ≤
    Fintype.card ↥(P + Q) at hc
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe,
    Fintype.card_coe] at hc
  have herase : (Q.erase qmin).card = Q.card - 1 := by
    rw [Finset.card_erase_of_mem]
    exact Finset.min'_mem Q hQ
  rw [herase] at hc
  have hQpos := hQ.card_pos
  change P.card + Q.card - 1 ≤ (P + Q).card
  omega

/-- Integer projection is an additive homomorphism. -/
def fstAddHom (H : Type*) [AddMonoid H] : (ℤ × H) →+ ℤ where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem fstAddHom_apply {H : Type*} [AddMonoid H] (x : ℤ × H) :
    fstAddHom H x = x.1 := rfl

/-- A finite sumset contains one full stabilizer coset in every occupied
integer fibre. -/
theorem card_image_fst_mul_card_addStab_le
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (S : Finset (ℤ × H)) (hS : S.Nonempty) :
    (S.image Prod.fst).card * S.addStab.card ≤ S.card := by
  let P := S.image Prod.fst
  let F := S.addStab
  let rep : (z : ℤ) → z ∈ P → ℤ × H := fun z hz =>
    (Finset.mem_image.mp hz).choose
  have hrepS (z : ℤ) (hz : z ∈ P) : rep z hz ∈ S :=
    (Finset.mem_image.mp hz).choose_spec.1
  have hrepfst (z : ℤ) (hz : z ∈ P) : (rep z hz).1 = z :=
    (Finset.mem_image.mp hz).choose_spec.2
  let f : ↥P × ↥F → ↥S := fun u =>
    ⟨u.2.1 + rep u.1.1 u.1.2, by
      have hmem := (Finset.mem_addStab' hS).mp u.2.2 (hrepS u.1.1 u.1.2)
      simpa [vadd_eq_add] using hmem⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hval := congrArg (fun x : ↥S => x.1) huv
    change u.2.1 + rep u.1.1 u.1.2 =
      v.2.1 + rep v.1.1 v.1.2 at hval
    have hu0 : u.2.1.1 = 0 :=
      fst_eq_zero_of_mem_addStab S hS u.2.2
    have hv0 : v.2.1.1 = 0 :=
      fst_eq_zero_of_mem_addStab S hS v.2.2
    have hfirst := congrArg Prod.fst hval
    rw [Prod.fst_add, Prod.fst_add, hu0, hv0,
      zero_add, zero_add] at hfirst
    have hru := hrepfst u.1.1 u.1.2
    have hrv := hrepfst v.1.1 v.1.2
    rw [hru, hrv] at hfirst
    have hidx : u.1 = v.1 := Subtype.ext hfirst
    have hrep : rep u.1.1 u.1.2 = rep v.1.1 v.1.2 :=
      congrArg (fun z : ↥P => rep z.1 z.2) hidx
    rw [hrep] at hval
    have hstab : u.2.1 = v.2.1 := add_right_cancel hval
    exact Prod.ext hidx (Subtype.ext hstab)
  have hc := Fintype.card_le_of_injective f hf
  change Fintype.card (↥P × ↥F) ≤ Fintype.card ↥S at hc
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Fintype.card_coe] at hc
  simpa [P, F] using hc

/-- Kneser plus the torsion-free projection bound, in a division-free form. -/
theorem projection_kneser_mixed_bound
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (A B : Finset (ℤ × H)) (hA : A.Nonempty) (hB : B.Nonempty) :
    ((A.image Prod.fst).card + (B.image Prod.fst).card) * (A + B).card ≥
      ((A.image Prod.fst).card + (B.image Prod.fst).card - 1) *
        (A.card + B.card) := by
  let p := (A.image Prod.fst).card
  let q := (B.image Prod.fst).card
  let S := A + B
  let F := S.addStab
  have hp : 0 < p := (hA.image Prod.fst).card_pos
  have hq : 0 < q := (hB.image Prod.fst).card_pos
  have hsupportImage : S.image Prod.fst =
      A.image Prod.fst + B.image Prod.fst := by
    change (A + B).image (fstAddHom H) =
      A.image (fstAddHom H) + B.image (fstAddHom H)
    exact Finset.image_add (fstAddHom H)
  have hsupport : p + q - 1 ≤ (S.image Prod.fst).card := by
    rw [hsupportImage]
    exact card_add_int_ge _ _ (hA.image Prod.fst) (hB.image Prod.fst)
  have hfiber := card_image_fst_mul_card_addStab_le S (hA.add hB)
  have hperiod : (p + q - 1) * F.card ≤ S.card := by
    exact le_trans (Nat.mul_le_mul_right F.card hsupport) (by simpa [F] using hfiber)
  have hkneser := Finset.add_kneser A B
  have hzeroF : 0 ∈ F := Finset.zero_mem_addStab.mpr (hA.add hB)
  have hAsub : A ⊆ A + F := by
    intro a ha
    exact Finset.mem_add.mpr ⟨a, ha, 0, hzeroF, by simp⟩
  have hBsub : B ⊆ B + F := by
    intro b hb
    exact Finset.mem_add.mpr ⟨b, hb, 0, hzeroF, by simp⟩
  have hAle := Finset.card_le_card hAsub
  have hBle := Finset.card_le_card hBsub
  change (A + F).card + (B + F).card ≤ S.card + F.card at hkneser
  have htotal : A.card + B.card ≤ S.card + F.card := by omega
  have hmul := Nat.mul_le_mul_left (p + q - 1) htotal
  calc
    (p + q - 1) * (A.card + B.card) ≤
        (p + q - 1) * (S.card + F.card) := hmul
    _ = (p + q - 1) * S.card + (p + q - 1) * F.card := by ring
    _ ≤ (p + q - 1) * S.card + S.card :=
      Nat.add_le_add_left hperiod _
    _ = ((p + q - 1) + 1) * S.card := by ring
    _ = (p + q) * S.card := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ p + q)]

/-- Symmetric specialization. -/
theorem projection_kneser_double_bound
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (A : Finset (ℤ × H)) (hA : A.Nonempty) :
    (A.image Prod.fst).card * (A + A).card ≥
      (2 * (A.image Prod.fst).card - 1) * A.card := by
  have h := projection_kneser_mixed_bound A A hA hA
  let p := (A.image Prod.fst).card
  let d := (A + A).card
  let a := A.card
  have hp : 0 < p := (hA.image Prod.fst).card_pos
  have hpadd : p + p = 2 * p := by omega
  have hpcoef : p + p - 1 = 2 * p - 1 := by omega
  have haadd : a + a = 2 * a := by omega
  change (p + p) * d ≥ (p + p - 1) * (a + a) at h
  rw [hpadd, haadd] at h
  have hleft : (2 * p) * d = 2 * (p * d) := by ring
  have hright : (2 * p - 1) * (2 * a) =
      2 * ((2 * p - 1) * a) := by ring
  rw [hleft, hright] at h
  change p * d ≥ (2 * p - 1) * a
  exact Nat.le_of_mul_le_mul_left h (by omega)

end Erdos336

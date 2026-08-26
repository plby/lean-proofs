import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N m : ℕ} [NeZero N] [NeZero m]

/-- The unique short nonnegative label of a point in a translated strict
half-interval, defaulting to zero outside that interval. -/
noncomputable def halfIntervalLabel
    (π : ZMod N →+ ZMod m) (α : ZMod m) (x : ZMod N) : ℕ := by
  classical
  exact if h : ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m) then h.choose else 0

theorem halfIntervalLabel_spec
    (π : ZMod N →+ ZMod m) (α : ZMod m) (x : ZMod N)
    (h : ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m)) :
    2 * halfIntervalLabel π α x < m ∧
      π x = α + (halfIntervalLabel π α x : ZMod m) := by
  rw [halfIntervalLabel, dif_pos h]
  exact h.choose_spec

lemma short_zmod_cast_injective {q r : ℕ}
    (hq : 2 * q < m) (hr : 2 * r < m)
    (h : (q : ZMod m) = (r : ZMod m)) : q = r := by
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
  exact hv

/-- Graph the short quotient label over the original point. -/
noncomputable def rectifiedLift
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m) :
    Finset (ℤ × ZMod N) :=
  A.image fun x => (Int.ofNat (halfIntervalLabel π α x), x)

@[simp] theorem mem_rectifiedLift
    {A : Finset (ZMod N)} {π : ZMod N →+ ZMod m} {α : ZMod m}
    {y : ℤ × ZMod N} :
    y ∈ rectifiedLift A π α ↔
      ∃ x ∈ A, y = (Int.ofNat (halfIntervalLabel π α x), x) := by
  simp [rectifiedLift, eq_comm]

/-- The lift is cardinality preserving. -/
theorem card_rectifiedLift
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m) :
    (rectifiedLift A π α).card = A.card := by
  apply Finset.card_image_of_injective
  intro x y h
  exact congrArg Prod.snd h

/-- Projection back to the cyclic coordinate recovers the original set. -/
theorem image_snd_rectifiedLift
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m) :
    (rectifiedLift A π α).image Prod.snd = A := by
  ext x
  simp [rectifiedLift]

/-- On a strict-half-supported set, the number of integer fibres in the lift
is exactly the number of quotient fibres of the original set. -/
theorem card_image_fst_rectifiedLift
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m)
    (houter : ∀ x ∈ A,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m)) :
    ((rectifiedLift A π α).image Prod.fst).card = (A.image π).card := by
  let label : ZMod N → ℕ := halfIntervalLabel π α
  let Q : Finset ℕ := A.image label
  let Z : Finset ℤ := Q.image (fun q : ℕ => (q : ℤ))
  let P : Finset (ZMod m) := Q.image (fun q : ℕ => α + (q : ZMod m))
  have hLiftImage : (rectifiedLift A π α).image Prod.fst = Z := by
    ext z
    simp [rectifiedLift, Z, Q, label]
  have hP : P = A.image π := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, hqQ, hqz⟩ := Finset.mem_image.mp hz
      obtain ⟨x, hxA, hxq⟩ := Finset.mem_image.mp hqQ
      apply Finset.mem_image.mpr
      refine ⟨x, hxA, ?_⟩
      have hs := (halfIntervalLabel_spec π α x (houter x hxA)).2
      rw [← hqz, ← hxq]
      exact hs
    · intro hz
      obtain ⟨x, hxA, hxz⟩ := Finset.mem_image.mp hz
      apply Finset.mem_image.mpr
      refine ⟨label x, Finset.mem_image.mpr ⟨x, hxA, rfl⟩, ?_⟩
      have hs := (halfIntervalLabel_spec π α x (houter x hxA)).2
      rw [← hxz]
      exact hs.symm
  have hZcard : Z.card = Q.card := by
    change (Q.image (fun q : ℕ => (q : ℤ))).card = Q.card
    exact Finset.card_image_of_injective Q Int.ofNat_injective
  have hPcard : P.card = Q.card := by
    change (Q.image (fun q : ℕ => α + (q : ZMod m))).card = Q.card
    rw [Finset.card_image_iff]
    intro q hq r hr hqr
    obtain ⟨x, hxA, hxq⟩ := Finset.mem_image.mp hq
    obtain ⟨y, hyA, hyr⟩ := Finset.mem_image.mp hr
    have hqshort := (halfIntervalLabel_spec π α x (houter x hxA)).1
    have hrshort := (halfIntervalLabel_spec π α y (houter y hyA)).1
    apply short_zmod_cast_injective (m := m)
    · simpa [label, ← hxq] using hqshort
    · simpa [label, ← hyr] using hrshort
    · exact add_left_cancel hqr
  rw [hLiftImage, hP.symm, hZcard, hPcard]

/-- Equality of cyclic pair-sums is equivalent to equality of lifted
pair-sums, because both short label sums lie below the modulus. -/
theorem rectifiedLift_pair_sum_iff
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m)
    (houter : ∀ x ∈ A,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m))
    {a b c d : ZMod N} (ha : a ∈ A) (hb : b ∈ A)
    (hc : c ∈ A) (hd : d ∈ A) :
    ((Int.ofNat (halfIntervalLabel π α a), a) +
        (Int.ofNat (halfIntervalLabel π α b), b) =
      (Int.ofNat (halfIntervalLabel π α c), c) +
        (Int.ofNat (halfIntervalLabel π α d), d)) ↔
      a + b = c + d := by
  constructor
  · intro h
    exact congrArg Prod.snd h
  · intro habcd
    apply Prod.ext
    · dsimp
      norm_cast
      have haS := halfIntervalLabel_spec π α a (houter a ha)
      have hbS := halfIntervalLabel_spec π α b (houter b hb)
      have hcS := halfIntervalLabel_spec π α c (houter c hc)
      have hdS := halfIntervalLabel_spec π α d (houter d hd)
      have hcast : ((halfIntervalLabel π α a + halfIntervalLabel π α b : ℕ) : ZMod m) =
          ((halfIntervalLabel π α c + halfIntervalLabel π α d : ℕ) : ZMod m) := by
        have hmap := congrArg π habcd
        rw [map_add, map_add, haS.2, hbS.2, hcS.2, hdS.2] at hmap
        have hchars :
            (halfIntervalLabel π α a : ZMod m) +
                (halfIntervalLabel π α b : ZMod m) =
              (halfIntervalLabel π α c : ZMod m) +
                (halfIntervalLabel π α d : ZMod m) := by
          apply add_left_cancel (a := α + α)
          calc
            (α + α) + ((halfIntervalLabel π α a : ZMod m) +
                (halfIntervalLabel π α b : ZMod m)) =
                (α + (halfIntervalLabel π α a : ZMod m)) +
                  (α + (halfIntervalLabel π α b : ZMod m)) := by abel
            _ = (α + (halfIntervalLabel π α c : ZMod m)) +
                  (α + (halfIntervalLabel π α d : ZMod m)) := hmap
            _ = (α + α) + ((halfIntervalLabel π α c : ZMod m) +
                (halfIntervalLabel π α d : ZMod m)) := by abel
        simpa using hchars
      have hv := congrArg ZMod.val hcast
      rw [ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
      exact hv
    · exact habcd

/-- Rectification preserves the double-sumset cardinality exactly. -/
theorem card_add_rectifiedLift
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m)
    (houter : ∀ x ∈ A,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m)) :
    (rectifiedLift A π α + rectifiedLift A π α).card = (A + A).card := by
  let T := rectifiedLift A π α
  have himage : (T + T).image Prod.snd = A + A := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hz
      obtain ⟨a, ha, hua⟩ := mem_rectifiedLift.mp hu
      obtain ⟨b, hb, hvb⟩ := mem_rectifiedLift.mp hv
      apply Finset.mem_add.mpr
      refine ⟨a, ha, b, hb, ?_⟩
      rw [← hzx, ← huv, hua, hvb]
      rfl
    · intro hx
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hx
      apply Finset.mem_image.mpr
      let u : ℤ × ZMod N := (Int.ofNat (halfIntervalLabel π α a), a)
      let v : ℤ × ZMod N := (Int.ofNat (halfIntervalLabel π α b), b)
      refine ⟨u + v, Finset.mem_add.mpr ⟨u, ?_, v, ?_, rfl⟩, ?_⟩
      · exact mem_rectifiedLift.mpr ⟨a, ha, rfl⟩
      · exact mem_rectifiedLift.mpr ⟨b, hb, rfl⟩
      · dsimp [u, v]
        exact hab
  have hinj : Set.InjOn Prod.snd (↑(T + T) : Set (ℤ × ZMod N)) := by
    intro x hx y hy hxy
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    obtain ⟨u', hu', v', hv', hu'v'⟩ := Finset.mem_add.mp hy
    obtain ⟨a, ha, hua⟩ := mem_rectifiedLift.mp hu
    obtain ⟨b, hb, hvb⟩ := mem_rectifiedLift.mp hv
    obtain ⟨c, hc, hu'c⟩ := mem_rectifiedLift.mp hu'
    obtain ⟨d, hd, hv'd⟩ := mem_rectifiedLift.mp hv'
    have habcd : a + b = c + d := by
      calc
        a + b = (u + v).2 := by rw [hua, hvb]; rfl
        _ = x.2 := congrArg Prod.snd huv
        _ = y.2 := hxy
        _ = (u' + v').2 := (congrArg Prod.snd hu'v').symm
        _ = c + d := by rw [hu'c, hv'd]; rfl
    have hlift := (rectifiedLift_pair_sum_iff A π α houter ha hb hc hd).2 habcd
    calc
      x = u + v := huv.symm
      _ = (Int.ofNat (halfIntervalLabel π α a), a) +
          (Int.ofNat (halfIntervalLabel π α b), b) := by rw [hua, hvb]
      _ = (Int.ofNat (halfIntervalLabel π α c), c) +
          (Int.ofNat (halfIntervalLabel π α d), d) := hlift
      _ = u' + v' := by rw [hu'c, hv'd]
      _ = y := hu'v'
  have hcardImage : ((T + T).image Prod.snd).card = (T + T).card :=
    Finset.card_image_iff.mpr hinj
  rw [himage] at hcardImage
  exact hcardImage.symm

end Erdos336

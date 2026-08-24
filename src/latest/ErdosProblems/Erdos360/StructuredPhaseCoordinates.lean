/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.PrimeStructuredQuotientNormalForm
import ErdosProblems.Erdos360.SharpModular

/-!
# Canonical coordinates for structured modular phases

The abstract equivalence between a cyclic subgroup and a `ZMod` does not
remember which integer represents a structured pivot.  This file uses the
canonical coordinates instead.  If `P ⊂ [0,t)` and

`q = closureModulus (P mod t)`,

then `q ∣ p` for every `p ∈ P`, and the coordinate of `p` in the generated
subgroup is the literal quotient `p / q` modulo `t / q`.

The last theorem is the sieve-facing bridge.  It says that the interval
representatives at base zero are exactly those literal quotients and hence
remain coprime to the missing-prime product.  In particular, no arbitrary
choice of an additive equivalence can alter the arithmetic representatives.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- The ordinary residue set associated to an integer pivot set. -/
def ordinaryResidues (t : ℕ) (P : Finset ℕ) : Finset (ZMod t) :=
  P.image fun p : ℕ ↦ (p : ZMod t)

/-- Literal division coordinates modulo `m`.  Applications take
`q = closureModulus` and `m = t / q`. -/
def dividedResidues {m : ℕ} [NeZero m] (q : ℕ)
    (P : Finset ℕ) : Finset (ZMod m) :=
  P.image fun p : ℕ ↦ ((p / q : ℕ) : ZMod m)

/-- Elements whose standard values are divisible by a fixed divisor of the
ambient modulus form a subgroup. -/
private def valDivisibleSubgroup {t : ℕ} [NeZero t]
    (a : ℕ) (hat : a ∣ t) : AddSubgroup (ZMod t) where
  carrier := {x | a ∣ x.val}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change a ∣ x.val at hx
    change a ∣ y.val at hy
    change a ∣ (x + y).val
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    obtain ⟨w, hw⟩ := hat
    rw [ZMod.val_add, hu, hv, hw]
    rw [← Nat.mul_add, Nat.mul_mod_mul_left]
    exact dvd_mul_right a _
  neg_mem' := by
    intro x hx
    change a ∣ x.val at hx
    change a ∣ (-x).val
    rw [ZMod.neg_val]
    split
    · simp
    · exact Nat.dvd_sub hat hx

@[simp] private lemma mem_valDivisibleSubgroup
    {t : ℕ} [NeZero t] {a : ℕ} {hat : a ∣ t} {x : ZMod t} :
    x ∈ valDivisibleSubgroup a hat ↔ a ∣ x.val :=
  Iff.rfl

@[simp] lemma mem_ordinaryResidues {t p : ℕ} {P : Finset ℕ} :
    (p : ZMod t) ∈ ordinaryResidues t P ↔
      ∃ a ∈ P, (a : ZMod t) = (p : ZMod t) := by
  simp [ordinaryResidues]

@[simp] lemma mem_dividedResidues {m q x : ℕ} [NeZero m]
    {P : Finset ℕ} :
    (x : ZMod m) ∈ dividedResidues q P ↔
      ∃ p ∈ P, ((p / q : ℕ) : ZMod m) = (x : ZMod m) := by
  simp [dividedResidues]

/-- The actual closure modulus divides every ordinary pivot, provided no
reduction modulo the ambient modulus has occurred. -/
lemma closureModulus_dvd_of_mem_ordinary
    {t : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    (hPt : ∀ p ∈ P, p < t) {p : ℕ} (hp : p ∈ P) :
    closureModulus ht (ordinaryResidues t P) ∣ p := by
  let q := closureModulus ht (ordinaryResidues t P)
  have hpR : (p : ZMod t) ∈ ordinaryResidues t P :=
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hqval : q ∣ (p : ZMod t).val :=
    (closureModulus_spec ht (ordinaryResidues t P)).2.2.1
      (p : ZMod t) (AddSubgroup.subset_closure hpR)
  simpa [q, ZMod.val_natCast, Nat.mod_eq_of_lt (hPt p hp)] using hqval

/-- The closure quotient `t / q` is positive. -/
lemma closureQuotient_pos
    {t : ℕ} [NeZero t] (ht : 0 < t) (P : Finset ℕ) :
    0 < t / closureModulus ht (ordinaryResidues t P) := by
  exact Nat.div_pos
    (Nat.le_of_dvd ht (closureModulus_dvd ht (ordinaryResidues t P)))
    (closureModulus_pos ht (ordinaryResidues t P))

/-- Dividing a pivot by the closure modulus places it strictly below the
closure quotient. -/
lemma div_closureModulus_lt_closureQuotient
    {t : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    (hPt : ∀ p ∈ P, p < t) {p : ℕ} (hp : p ∈ P) :
    p / closureModulus ht (ordinaryResidues t P) <
      t / closureModulus ht (ordinaryResidues t P) := by
  exact (Nat.div_lt_div_right
    (closureModulus_pos ht (ordinaryResidues t P)).ne'
    (closureModulus_dvd_of_mem_ordinary ht hPt hp)
    (closureModulus_dvd ht (ordinaryResidues t P))).2 (hPt p hp)

/-- Multiplying the literal quotient coordinate back by the closure modulus
recovers the original residue. -/
lemma closureCoordinate_lifts_to_ordinary
    {t : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    (hPt : ∀ p ∈ P, p < t) {p : ℕ} (hp : p ∈ P) :
    let q := closureModulus ht (ordinaryResidues t P)
    (((q * (p / q) : ℕ) : ZMod t)) = (p : ZMod t) := by
  dsimp only
  rw [Nat.mul_div_cancel'
    (closureModulus_dvd_of_mem_ordinary ht hPt hp)]

/-- Canonical closure division loses no pivots. -/
theorem card_dividedResidues_closure
    {t : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    (hPt : ∀ p ∈ P, p < t) :
    let q := closureModulus ht (ordinaryResidues t P)
    let m := t / q
    letI : NeZero m := ⟨(closureQuotient_pos ht P).ne'⟩
    (dividedResidues (m := m) q P).card = P.card := by
  dsimp only
  let q := closureModulus ht (ordinaryResidues t P)
  let m := t / q
  letI : NeZero m := ⟨(closureQuotient_pos ht P).ne'⟩
  rw [dividedResidues, Finset.card_image_iff]
  intro a ha b hb hab
  have haDiv : a / q < m :=
    div_closureModulus_lt_closureQuotient ht hPt ha
  have hbDiv : b / q < m :=
    div_closureModulus_lt_closureQuotient ht hPt hb
  have hdiv : a / q = b / q := by
    change ((a / q : ℕ) : ZMod m) = ((b / q : ℕ) : ZMod m) at hab
    have hval := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt haDiv,
      Nat.mod_eq_of_lt hbDiv] using hval
  have hqa : q ∣ a := closureModulus_dvd_of_mem_ordinary ht hPt ha
  have hqb : q ∣ b := closureModulus_dvd_of_mem_ordinary ht hPt hb
  calc
    a = q * (a / q) := (Nat.mul_div_cancel' hqa).symm
    _ = q * (b / q) := by rw [hdiv]
    _ = b := Nat.mul_div_cancel' hqb

/-- Literal division by the actual closure modulus generates the entire
quotient cyclic group.  This is the canonical replacement for choosing an
arbitrary equivalence from the generated subgroup to a `ZMod`. -/
theorem closure_dividedResidues_eq_top
    {t : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    (hPt : ∀ p ∈ P, p < t) :
    let q := closureModulus ht (ordinaryResidues t P)
    let m := t / q
    letI : NeZero m := ⟨(closureQuotient_pos ht P).ne'⟩
    AddSubgroup.closure
      ((dividedResidues (m := m) q P : Finset (ZMod m)) : Set (ZMod m)) =
        ⊤ := by
  dsimp only
  let q := closureModulus ht (ordinaryResidues t P)
  let m := t / q
  letI : NeZero m := ⟨(closureQuotient_pos ht P).ne'⟩
  let C : Finset (ZMod m) := dividedResidues (m := m) q P
  let e := closureModulus (closureQuotient_pos ht P) C
  have hqpos : 0 < q := closureModulus_pos ht (ordinaryResidues t P)
  have hqt : q ∣ t := closureModulus_dvd ht (ordinaryResidues t P)
  have hepos : 0 < e := closureModulus_pos (closureQuotient_pos ht P) C
  have hem : e ∣ m := closureModulus_dvd (closureQuotient_pos ht P) C
  have hqem : q * e ∣ t := by
    obtain ⟨k, hk⟩ := hem
    refine ⟨k, ?_⟩
    calc
      t = q * m := (Nat.mul_div_cancel' hqt).symm
      _ = (q * e) * k := by rw [hk]; ring
  have hqeP : ∀ p ∈ P, q * e ∣ p := by
    intro p hp
    have hqp : q ∣ p := closureModulus_dvd_of_mem_ordinary ht hPt hp
    have hpdivlt : p / q < m :=
      div_closureModulus_lt_closureQuotient ht hPt hp
    have hpC : ((p / q : ℕ) : ZMod m) ∈ C := by
      change ((p / q : ℕ) : ZMod m) ∈ dividedResidues (m := m) q P
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have heval : e ∣ ((p / q : ℕ) : ZMod m).val :=
      (closureModulus_spec (closureQuotient_pos ht P) C).2.2.1 _
        (AddSubgroup.subset_closure hpC)
    have hediv : e ∣ p / q := by
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hpdivlt] using heval
    exact (Nat.dvd_div_iff_mul_dvd hqp).mp hediv
  have hRsub : (ordinaryResidues t P : Set (ZMod t)) ⊆
      valDivisibleSubgroup (q * e) hqem := by
    intro x hx
    change x ∈ P.image (fun p : ℕ ↦ (p : ZMod t)) at hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    change q * e ∣ (p : ZMod t).val
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (hPt p hp)] using hqeP p hp
  have hclosureSub :
      AddSubgroup.closure ((ordinaryResidues t P : Finset (ZMod t)) :
        Set (ZMod t)) ≤ valDivisibleSubgroup (q * e) hqem :=
    (AddSubgroup.closure_le _).mpr hRsub
  have hqmem : (q : ZMod t) ∈
      AddSubgroup.closure ((ordinaryResidues t P : Finset (ZMod t)) :
        Set (ZMod t)) := by
    simpa using
      (closureModulus_spec ht (ordinaryResidues t P)).2.2.2 1
  have hqedivqval : q * e ∣ (q : ZMod t).val :=
    mem_valDivisibleSubgroup.mp (hclosureSub hqmem)
  have heone : e = 1 := by
    by_cases hqtEq : q = t
    · have hm : m = 1 := by
        dsimp [m]
        rw [hqtEq]
        exact Nat.div_self ht
      have hedivone : e ∣ 1 := by simpa [hm] using hem
      exact Nat.dvd_one.mp hedivone
    · have hqlt : q < t := lt_of_le_of_ne (Nat.le_of_dvd ht hqt) hqtEq
      have hqedivq : q * e ∣ q := by
        simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hqlt] using hqedivqval
      have hle : q * e ≤ q := Nat.le_of_dvd hqpos hqedivq
      have he_le : e ≤ 1 := by
        apply Nat.le_of_mul_le_mul_left (c := q) (by simpa using hle) hqpos
      omega
  rw [closure_eq_zmultiples_modulus (closureQuotient_pos ht P) C]
  change AddSubgroup.zmultiples (e : ZMod m) = ⊤
  rw [heone]
  apply top_unique
  intro x _
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨(x.val : ℤ), ?_⟩
  simpa using (ZMod.natCast_zmod_val x).symm

/-! ## Preservation of the structured normal form under a phase divisor -/

/-- If a phase divisor is smaller than the retained prime coordinate, then
literal division updates only the target-divisor coordinate. -/
def PrimeStructuredQuotientNormalForm.divide_small
    {n y U d z B e : ℕ}
    (h : PrimeStructuredQuotientNormalForm n y U d z)
    (hepos : 0 < e) (hBq : B < h.q) (heB : e ≤ B) (hez : e ∣ z) :
    PrimeStructuredQuotientNormalForm n y U (d * e) (z / e) := by
  have heu : e ∣ h.u' := h.small_dvd_reduced hBq heB hez
  have hrecover : e * (h.u' / e) = h.u' := Nat.mul_div_cancel' heu
  refine
    { u := h.u
      u' := h.u' / e
      q := h.q
      u_dvd_target := h.u_dvd_target
      target_ne_zero := h.target_ne_zero
      u_le_cutoff := h.u_le_cutoff
      quotient_lower := h.quotient_lower
      quotient_upper := h.quotient_upper
      quotient_prime := h.quotient_prime
      quotient_not_target_factor := h.quotient_not_target_factor
      u_eq_scale_mul := ?_
      z_eq := ?_ }
  · calc
      h.u = d * h.u' := h.u_eq_scale_mul
      _ = d * (e * (h.u' / e)) :=
        congrArg (fun v : ℕ => d * v) hrecover.symm
      _ = (d * e) * (h.u' / e) := by ring
  · have hzfactor : z = e * ((h.u' / e) * h.q) := by
      calc
        z = h.u' * h.q := h.z_eq
        _ = (e * (h.u' / e)) * h.q := by rw [hrecover]
        _ = e * ((h.u' / e) * h.q) := by ring
    calc
      z / e = (e * ((h.u' / e) * h.q)) / e :=
        congrArg (fun w : ℕ => w / e) hzfactor
      _ = (h.u' / e) * h.q := Nat.mul_div_cancel_left _ hepos

/-- Initial-prime-cutoff form of `divide_small`. -/
noncomputable def PrimeStructuredQuotientNormalForm.divide_of_le_primeAt
    {n y U d z r e : ℕ}
    (hU : 0 < U) (hcut : primeAt (r - 1) ≤ y / U)
    (h : PrimeStructuredQuotientNormalForm n y U d z)
    (hepos : 0 < e) (he : e ≤ primeAt (r - 1)) (hez : e ∣ z) :
    PrimeStructuredQuotientNormalForm n y U (d * e) (z / e) :=
  h.divide_small hepos (h.primeAt_lt_quotient hU hcut) he hez

/-- Every element of the canonical phase-coordinate set retains the exact
prime-structured normal form.  The new accumulated scale is `d*q`, where
`q` is the actual closure modulus of the current ordinary remainder. -/
theorem primeStructured_closureCoordinate_normalForm
    {n y U d r t : ℕ} [NeZero t] (ht : 0 < t)
    {W Z : Finset ℕ}
    (hU : 0 < U) (hcut : primeAt (r - 1) ≤ y / U)
    (hdn : d ∣ n)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W)
    (hZt : ∀ z ∈ Z, z < t)
    (hqcut : closureModulus ht (ordinaryResidues t Z) ≤
      primeAt (r - 1)) :
    let q := closureModulus ht (ordinaryResidues t Z)
    ∀ z ∈ Z,
      Nonempty (PrimeStructuredQuotientNormalForm n y U (d * q) (z / q)) := by
  dsimp only
  intro z hz
  let h := Classical.choice
    (primeStructured_extracted_set_normalForm hdn hW hscale z hz)
  exact ⟨h.divide_of_le_primeAt hU hcut
    (closureModulus_pos ht (ordinaryResidues t Z)) hqcut
    (closureModulus_dvd_of_mem_ordinary ht hZt hz)⟩

/-- Representatives in one half-open interval recover the original
integers when the residues were obtained from integers in that interval. -/
lemma intervalZmodValues_image_natCast
    {m : ℕ} [NeZero m] {base : ℕ} (X : Finset ℕ)
    (hlo : ∀ x ∈ X, base ≤ x)
    (hhi : ∀ x ∈ X, x < base + m) :
    intervalZmodValues base
      (X.image fun x : ℕ ↦ (x : ZMod m)) = X := by
  ext y
  constructor
  · intro hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
    have hbase : base ≤ x := hlo x hx
    have hdiff : x - base < m := by
      have := hhi x hx
      omega
    have hz : (x : ZMod m) - (base : ZMod m) =
        ((x - base : ℕ) : ZMod m) := by
      rw [Nat.cast_sub hbase]
    rw [hz, ZMod.val_natCast, Nat.mod_eq_of_lt hdiff]
    simpa [Nat.add_sub_of_le hbase] using hx
  · intro hy
    apply Finset.mem_image.mpr
    refine ⟨(y : ZMod m), Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    have hbase : base ≤ y := hlo y hy
    have hdiff : y - base < m := by
      have := hhi y hy
      omega
    have hz : (y : ZMod m) - (base : ZMod m) =
        ((y - base : ℕ) : ZMod m) := by
      rw [Nat.cast_sub hbase]
    rw [hz, ZMod.val_natCast, Nat.mod_eq_of_lt hdiff]
    omega

/-- Base-zero interval representatives of the canonical coordinates are
exactly the literal divided pivots. -/
lemma intervalZmodValues_dividedResidues_zero
    {m q : ℕ} [NeZero m] {P : Finset ℕ}
    (hquot : ∀ p ∈ P, p / q < m) :
    intervalZmodValues 0 (dividedResidues (m := m) q P) =
      P.image fun p : ℕ ↦ p / q := by
  simpa only [dividedResidues, Finset.image_image, Function.comp_def] using
    (intervalZmodValues_image_natCast
      (P.image fun p : ℕ ↦ p / q)
      (fun _ _ ↦ Nat.zero_le _)
      (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        simpa using hquot p hp))

/-- A literal quotient divides the original pivot whenever the divisor is
positive and actually divides that pivot. -/
lemma div_dvd_self_of_pos_of_dvd {q p : ℕ} (hq : 0 < q) (hqp : q ∣ p) :
    p / q ∣ p := by
  refine ⟨q, ?_⟩
  simpa [Nat.mul_comm] using (Nat.div_mul_cancel hqp).symm

/-- Coprimality is inherited by canonical division coordinates. -/
lemma coprime_div_of_coprime_of_dvd
    {M q p : ℕ} (hq : 0 < q) (hqp : q ∣ p)
    (hcop : Nat.Coprime M p) :
    Nat.Coprime M (p / q) :=
  Nat.Coprime.of_dvd_right (div_dvd_self_of_pos_of_dvd hq hqp) hcop

/-- The canonical closure coordinates of any coprime ordinary pivot set
have coprime base-zero interval representatives. -/
theorem intervalClosureCoordinates_coprime
    {t M : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    (hPt : ∀ p ∈ P, p < t)
    (hcop : ∀ p ∈ P, Nat.Coprime M p) :
    let q := closureModulus ht (ordinaryResidues t P)
    let m := t / q
    letI : NeZero m := ⟨(closureQuotient_pos ht P).ne'⟩
    ∀ x ∈ intervalZmodValues 0 (dividedResidues (m := m) q P),
      Nat.Coprime M x := by
  dsimp only
  let q := closureModulus ht (ordinaryResidues t P)
  let m := t / q
  letI : NeZero m := ⟨(closureQuotient_pos ht P).ne'⟩
  have hquot : ∀ p ∈ P, p / q < m := by
    intro p hp
    exact div_closureModulus_lt_closureQuotient ht hPt hp
  rw [intervalZmodValues_dividedResidues_zero hquot]
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact coprime_div_of_coprime_of_dvd
    (closureModulus_pos ht (ordinaryResidues t P))
    (closureModulus_dvd_of_mem_ordinary ht hPt hp) (hcop p hp)

/-- Prime-structured extraction supplies the coprimality premise of the
canonical coordinate theorem under the explicit initial-prime cutoff. -/
theorem primeStructured_intervalClosureCoordinates_coprime
    {n y U d r t : ℕ} [NeZero t] (ht : 0 < t)
    {W Z : Finset ℕ}
    (hU : 0 < U)
    (hcut : primeAt (r - 1) ≤ y / U)
    (hdn : d ∣ n)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W)
    (hZt : ∀ z ∈ Z, z < t) :
    let q := closureModulus ht (ordinaryResidues t Z)
    let m := t / q
    letI : NeZero m := ⟨(closureQuotient_pos ht Z).ne'⟩
    ∀ x ∈ intervalZmodValues 0 (dividedResidues (m := m) q Z),
      Nat.Coprime (missingPrimeProduct n (primeAt (r - 1))) x := by
  apply intervalClosureCoordinates_coprime ht hZt
  exact primeStructured_extracted_set_coprime_missingPrimeProduct
    hU hcut hdn hW hscale

end Erdos360

#print axioms Erdos360.closureModulus_dvd_of_mem_ordinary
#print axioms Erdos360.card_dividedResidues_closure
#print axioms Erdos360.closure_dividedResidues_eq_top
#print axioms Erdos360.primeStructured_closureCoordinate_normalForm
#print axioms Erdos360.intervalClosureCoordinates_coprime
#print axioms Erdos360.primeStructured_intervalClosureCoordinates_coprime

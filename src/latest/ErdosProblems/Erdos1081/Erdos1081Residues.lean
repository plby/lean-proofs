import ErdosProblems.Erdos1081.Erdos1081OrderCounting

namespace Erdos1081

open scoped nonZeroDivisors
open Filter

noncomputable section

noncomputable def splitCoordinateEquiv
    (q : ℕ) [Fact q.Prime] (r : ZMod q)
    (h2r : (2 : ZMod q) * r ≠ 0) :
    ZMod q × ZMod q ≃ ZMod q × ZMod q where
  toFun x := (x.1 - r * x.2, x.1 + r * x.2)
  invFun y := ((y.1 + y.2) / 2, (y.2 - y.1) / (2 * r))
  left_inv := by
    intro x
    have h2 : (2 : ZMod q) ≠ 0 := by
      intro hz
      exact h2r (by rw [hz, zero_mul])
    have hr : r ≠ 0 := by
      intro hz
      exact h2r (by rw [hz, mul_zero])
    apply Prod.ext <;> dsimp
    · field_simp [h2]
      ring
    · field_simp [h2, hr]
      ring
  right_inv := by
    intro y
    have h2 : (2 : ZMod q) ≠ 0 := by
      intro hz
      exact h2r (by rw [hz, zero_mul])
    have hr : r ≠ 0 := by
      intro hz
      exact h2r (by rw [hz, mul_zero])
    apply Prod.ext <;> dsimp
    · field_simp [h2, hr]
      ring
    · field_simp [h2, hr]
      ring

def splitAllowedPairs (q : ℕ) (r : ZMod q) :=
  {x : ZMod q × ZMod q //
    x.1 - r * x.2 ≠ 0 ∧ x.1 + r * x.2 ≠ 0}

noncomputable def splitAllowedPairsEquiv
    (q : ℕ) [Fact q.Prime] (r : ZMod q)
    (h2r : (2 : ZMod q) * r ≠ 0) :
    splitAllowedPairs q r ≃
      {u : ZMod q // u ≠ 0} × {v : ZMod q // v ≠ 0} :=
  (Equiv.subtypeEquiv (splitCoordinateEquiv q r h2r)
    (fun _ ↦ Iff.rfl)).trans
  { toFun := fun (y : {y : ZMod q × ZMod q //
        y.1 ≠ 0 ∧ y.2 ≠ 0}) ↦
      (⟨y.1.1, y.2.1⟩, ⟨y.1.2, y.2.2⟩)
    invFun := fun (y : {u : ZMod q // u ≠ 0} ×
        {v : ZMod q // v ≠ 0}) ↦
      ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
    left_inv := by intro y; rfl
    right_inv := by intro y; rfl }

theorem natCard_zmod_ne_zero (q : ℕ) [Fact q.Prime] :
    Nat.card {u : ZMod q // u ≠ 0} = q - 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp

theorem natCard_splitAllowedPairs
    (q : ℕ) [Fact q.Prime] (r : ZMod q)
    (h2r : (2 : ZMod q) * r ≠ 0) :
    Nat.card (splitAllowedPairs q r) = (q - 1) ^ 2 := by
  rw [Nat.card_congr (splitAllowedPairsEquiv q r h2r), Nat.card_prod,
    natCard_zmod_ne_zero, pow_two]

noncomputable def SpecialSplitPrimeData.root
    {p : ℕ} [Fact p.Prime] (s : SpecialSplitPrimeData p) : ZMod s.q :=
  specialSplitRoot p s.q s.split

theorem SpecialSplitPrimeData.two_mul_root_ne_zero
    {p : ℕ} [Fact p.Prime] (s : SpecialSplitPrimeData p) :
    (2 : ZMod s.q) * s.root ≠ 0 := by
  let : Fact s.q.Prime := ⟨s.prime⟩
  have hcop := specialSplitRoot_coprime_two_val
    (Fact.out : Nat.Prime p) s.prime s.ne_two s.ne_p s.split
  have hu : IsUnit (((2 * s.root.val : ℕ) : ZMod s.q)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hcop.symm
  have heq : (((2 * s.root.val : ℕ) : ZMod s.q)) =
      (2 : ZMod s.q) * s.root := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    norm_num
  exact heq ▸ hu.ne_zero

theorem specialSplitPrimeData_pairwise_coprime
    {p : ℕ} (S : Finset (SpecialSplitPrimeData p)) :
    Pairwise (fun a b : {s // s ∈ S} ↦ Nat.Coprime a.1.q b.1.q) := by
  intro a b hab
  apply (Nat.coprime_primes a.1.prime b.1.prime).mpr
  intro hq
  apply hab
  apply Subtype.ext
  apply SpecialSplitPrimeData.ext
  exact hq

noncomputable def splitResidueEquivPi
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p)) :
    ZMod (∏ s ∈ S, s.q) ≃+*
      (∀ s : {s // s ∈ S}, ZMod s.1.q) := by
  have hprod : (∏ s : {s // s ∈ S}, s.1.q) = ∏ s ∈ S, s.q := by
    simpa only [Finset.attach_eq_univ] using
      S.prod_attach (fun s ↦ s.q)
  exact (ZMod.ringEquivCongr hprod.symm).trans
    (ZMod.prodEquivPi (fun s : {s // s ∈ S} ↦ s.1.q)
      (specialSplitPrimeData_pairwise_coprime S))

@[simp] theorem splitResidueEquivPi_apply
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : ZMod (∏ s ∈ S, s.q)) (s : {s // s ∈ S}) :
    splitResidueEquivPi S x s = (x.val : ZMod s.1.q) := by
  have hM : (∏ s ∈ S, s.q) ≠ 0 := by
    exact (Finset.prod_pos fun t ht ↦ t.prime.pos).ne'
  let : NeZero (∏ s ∈ S, s.q) := ⟨hM⟩
  have hdiv : s.1.q ∣ ∏ t ∈ S, t.q :=
    Finset.dvd_prod_of_mem (fun t ↦ t.q) s.2
  let f : ZMod (∏ t ∈ S, t.q) →+* ZMod s.1.q :=
    (Pi.evalRingHom (fun s : {s // s ∈ S} ↦ ZMod s.1.q) s).comp
      (splitResidueEquivPi S).toRingHom
  have hf : f = ZMod.castHom hdiv (ZMod s.1.q) := Subsingleton.elim _ _
  change f x = _
  rw [hf, ZMod.castHom_apply, ZMod.cast_eq_val]

noncomputable def splitResiduePairEquivPi
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p)) :
    (ZMod (∏ s ∈ S, s.q) × ZMod (∏ s ∈ S, s.q)) ≃
      (∀ s : {s // s ∈ S}, ZMod s.1.q × ZMod s.1.q) := by
  let e := splitResidueEquivPi S
  exact
    { toFun := fun x s ↦ (e x.1 s, e x.2 s)
      invFun := fun y ↦ (e.symm (fun s ↦ (y s).1),
        e.symm (fun s ↦ (y s).2))
      left_inv := by
        intro x
        apply Prod.ext
        · exact e.symm_apply_apply x.1
        · exact e.symm_apply_apply x.2
      right_inv := by
        intro y
        funext s
        apply Prod.ext
        · exact congrFun (e.apply_symm_apply (fun s ↦ (y s).1)) s
        · exact congrFun (e.apply_symm_apply (fun s ↦ (y s).2)) s }

def splitAllowedResiduePairs
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p)) :=
  {x : ZMod (∏ s ∈ S, s.q) × ZMod (∏ s ∈ S, s.q) //
    ∀ s : {s // s ∈ S},
      (splitResiduePairEquivPi S x s).1 - s.1.root *
          (splitResiduePairEquivPi S x s).2 ≠ 0 ∧
        (splitResiduePairEquivPi S x s).1 + s.1.root *
          (splitResiduePairEquivPi S x s).2 ≠ 0}

noncomputable def splitAllowedResiduePairsEquivPi
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p)) :
    splitAllowedResiduePairs S ≃
      (∀ s : {s // s ∈ S}, splitAllowedPairs s.1.q s.1.root) := by
  let e := splitResiduePairEquivPi S
  exact
    { toFun := fun x s ↦ ⟨e x.1 s, x.2 s⟩
      invFun := fun y ↦ ⟨e.symm (fun s ↦ (y s).1),
        by
          intro s
          simpa only [e, Equiv.apply_symm_apply] using (y s).2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact e.symm_apply_apply x.1
      right_inv := by
        intro y
        funext s
        apply Subtype.ext
        exact congrFun (e.apply_symm_apply (fun s ↦ (y s).1)) s }

theorem splitResiduePairEquivPi_apply
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : ZMod (∏ s ∈ S, s.q) × ZMod (∏ s ∈ S, s.q))
    (s : {s // s ∈ S}) :
    splitResiduePairEquivPi S x s =
      ((x.1.val : ZMod s.1.q), (x.2.val : ZMod s.1.q)) := by
  apply Prod.ext <;> simp [splitResiduePairEquivPi]

theorem natCard_splitAllowedResiduePairs
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p)) :
    Nat.card (splitAllowedResiduePairs S) =
      ∏ s ∈ S, (s.q - 1) ^ 2 := by
  rw [Nat.card_congr (splitAllowedResiduePairsEquivPi S), Nat.card_pi]
  have hlocal : ∀ s : {s // s ∈ S},
      Nat.card (splitAllowedPairs s.1.q s.1.root) = (s.1.q - 1) ^ 2 := by
    intro s
    let : Fact s.1.q.Prime := ⟨s.1.prime⟩
    exact natCard_splitAllowedPairs s.1.q s.1.root
      s.1.two_mul_root_ne_zero
  simp_rw [hlocal]
  simpa only [Finset.attach_eq_univ] using
    S.prod_attach (fun s ↦ (s.q - 1) ^ 2)

theorem span_singleton_isCoprime_of_not_mem_isMaximal
    {R : Type*} [CommRing R] {M : Ideal R} (hM : M.IsMaximal)
    {z : R} (hz : z ∉ M) :
    IsCoprime (Ideal.span ({z} : Set R)) M := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  have heq : M = Ideal.span ({z} : Set R) ⊔ M :=
    hM.eq_of_le htop le_sup_right
  apply hz
  rw [heq]
  exact (show Ideal.span ({z} : Set R) ≤
      Ideal.span ({z} : Set R) ⊔ M from le_sup_left)
    (Ideal.mem_span_singleton_self z)

theorem splitEval_eq_re_add_im_mul
    (d : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r * r = (d : ZMod q)) (z : Zsqrtd d) :
    splitEval d q r hr z =
      (z.re : ZMod q) + (z.im : ZMod q) * r := by
  change Zsqrtd.lift ⟨r, hr⟩ z = _
  rfl

/-- Nonvanishing of both split coordinates makes a principal ideal
coprime to either oriented prime above `s.q`. -/
theorem SpecialSplitPrimeData.span_isCoprime_oriented
    {p : ℕ} [Fact p.Prime] (s : SpecialSplitPrimeData p)
    (z : Zsqrtd (-(p : ℤ) ^ 3))
    (hminus : (z.re : ZMod s.q) - s.root * (z.im : ZMod s.q) ≠ 0)
    (hplus : (z.re : ZMod s.q) + s.root * (z.im : ZMod s.q) ≠ 0)
    (b : Bool) :
    IsCoprime (Ideal.span ({z} : Set (Zsqrtd (-(p : ℤ) ^ 3))))
      (s.integralUnitIdeal b : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
  let : NeZero s.q := ⟨s.prime.ne_zero⟩
  have hrs : s.root * s.root =
      ((-(p : ℤ) ^ 3 : ℤ) : ZMod s.q) := by
    simpa [SpecialSplitPrimeData.root] using
      specialSplitRoot_sq p s.q s.split
  apply span_singleton_isCoprime_of_not_mem_isMaximal
    (specialOrientedIntegralUnitIdeal_isMaximal p s.q s.prime
      s.ne_two s.ne_p s.split b)
  cases b
  · change z ∉ splitPrimeIdeal (-(p : ℤ) ^ 3) s.q s.root
    rw [splitPrimeIdeal_eq_ker (-(p : ℤ) ^ 3) s.q s.root
        hrs, RingHom.mem_ker]
    rw [splitEval_eq_re_add_im_mul (-(p : ℤ) ^ 3) s.q s.root hrs z]
    simpa [mul_comm] using hplus
  · change z ∉ splitConjugateIdeal (-(p : ℤ) ^ 3) s.q s.root
    rw [splitConjugateIdeal_eq_ker (-(p : ℤ) ^ 3) s.q s.root
        hrs, RingHom.mem_ker]
    rw [splitEval_eq_re_add_im_mul (-(p : ℤ) ^ 3) s.q (-s.root)
      (by simpa using hrs) z]
    simpa [mul_comm, sub_eq_add_neg] using hminus

def specialSieveModulus
    {p : ℕ} (S : Finset (SpecialSplitPrimeData p)) : ℕ :=
  ∏ s ∈ S, s.q

theorem specialSieveModulus_pos
    {p : ℕ} (S : Finset (SpecialSplitPrimeData p)) :
    0 < specialSieveModulus S := by
  exact Finset.prod_pos fun s hs ↦ s.prime.pos

/-- A positive lift of a globally admissible pair of CRT residues.  The
extra `+ 1` in the real lift selects one representative from each pair
of associates `z, -z`. -/
def specialSieveElement
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) (a b : ℕ) :
    Zsqrtd (-(p : ℤ) ^ 3) :=
  ⟨(x.1.1.val + specialSieveModulus S * (a + 1) : ℕ),
    (x.1.2.val + specialSieveModulus S * b : ℕ)⟩

@[simp] theorem specialSieveElement_re
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) (a b : ℕ) :
    (specialSieveElement S x a b).re =
      (x.1.1.val + specialSieveModulus S * (a + 1) : ℕ) := rfl

@[simp] theorem specialSieveElement_im
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) (a b : ℕ) :
    (specialSieveElement S x a b).im =
      (x.1.2.val + specialSieveModulus S * b : ℕ) := rfl

theorem specialSieveElement_ne_zero
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) (a b : ℕ) :
    specialSieveElement S x a b ≠ 0 := by
  intro hz
  have hre := congrArg Zsqrtd.re hz
  simp only [specialSieveElement_re, Zsqrtd.re_zero] at hre
  have hM := specialSieveModulus_pos S
  have : 0 < x.1.1.val + specialSieveModulus S * (a + 1) := by
    positivity
  omega

theorem specialSieveElement_cast_coordinates
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) (a b : ℕ)
    (s : {s // s ∈ S}) :
    ((specialSieveElement S x a b).re : ZMod s.1.q) =
        (splitResiduePairEquivPi S x.1 s).1 ∧
      ((specialSieveElement S x a b).im : ZMod s.1.q) =
        (splitResiduePairEquivPi S x.1 s).2 := by
  have hdiv : s.1.q ∣ specialSieveModulus S :=
    Finset.dvd_prod_of_mem (fun t ↦ t.q) s.2
  have hzero : (specialSieveModulus S : ZMod s.1.q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  rw [splitResiduePairEquivPi_apply]
  constructor
  · simp only [specialSieveElement_re, Int.cast_natCast, Prod.fst]
    push_cast
    simp only [hzero, zero_mul, add_zero]
  · simp only [specialSieveElement_im, Int.cast_natCast, Prod.snd]
    push_cast
    simp only [hzero, zero_mul, add_zero]

theorem specialSieveElement_span_isCoprime_oriented
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) (a b : ℕ)
    (s : {s // s ∈ S}) (c : Bool) :
    IsCoprime
      (Ideal.span ({specialSieveElement S x a b} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))))
      (s.1.integralUnitIdeal c : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
  have hcoord := specialSieveElement_cast_coordinates S x a b s
  apply s.1.span_isCoprime_oriented (specialSieveElement S x a b)
  · rw [hcoord.1, hcoord.2]
    exact (x.2 s).1
  · rw [hcoord.1, hcoord.2]
    exact (x.2 s).2

theorem specialSieveElement_eq_of_associated
    {p : ℕ} [Fact p.Prime] {S : Finset (SpecialSplitPrimeData p)}
    {x y : splitAllowedResiduePairs S} {a b c e : ℕ}
    (h : Associated (specialSieveElement S x a b)
      (specialSieveElement S y c e)) :
    x = y ∧ a = c ∧ b = e := by
  let : NeZero (∏ s ∈ S, s.q) :=
    ⟨by simpa [specialSieveModulus] using
      (specialSieveModulus_pos S).ne'⟩
  obtain ⟨u, hu⟩ := h
  have hunit : IsUnit (u : Zsqrtd (-(p : ℤ) ^ 3)) := u.isUnit
  have hd : (-(p : ℤ) ^ 3 : ℤ) ≤ -2 := by
    have hp := (Fact.out : Nat.Prime p).two_le
    have hp3 : 2 ≤ p ^ 3 := hp.trans
      (Nat.le_self_pow (by norm_num : 3 ≠ 0) p)
    have hp3Z : (2 : ℤ) ≤ (p : ℤ) ^ 3 := by exact_mod_cast hp3
    omega
  have hzeq : specialSieveElement S x a b =
      specialSieveElement S y c e := by
    rcases (zsqrtd_isUnit_iff_eq_one_or_neg_one hd (u :
        Zsqrtd (-(p : ℤ) ^ 3))).mp hunit with hu1 | huneg
    · simpa [hu1] using hu
    · have hleft : 0 < (specialSieveElement S x a b).re := by
        simp only [specialSieveElement_re]
        have hM := specialSieveModulus_pos S
        positivity
      have hright : 0 < (specialSieveElement S y c e).re := by
        simp only [specialSieveElement_re]
        have hM := specialSieveModulus_pos S
        positivity
      have hu' : specialSieveElement S x a b *
          (-1 : Zsqrtd (-(p : ℤ) ^ 3)) =
            specialSieveElement S y c e := by simpa [huneg] using hu
      have hre := congrArg Zsqrtd.re hu'
      have : -(specialSieveElement S x a b).re =
          (specialSieveElement S y c e).re := by simpa using hre
      omega
  have hreZ := congrArg Zsqrtd.re hzeq
  have himZ := congrArg Zsqrtd.im hzeq
  simp only [specialSieveElement_re] at hreZ
  simp only [specialSieveElement_im] at himZ
  have hreN : x.1.1.val + specialSieveModulus S * (a + 1) =
      y.1.1.val + specialSieveModulus S * (c + 1) := by
    exact_mod_cast hreZ
  have himN : x.1.2.val + specialSieveModulus S * b =
      y.1.2.val + specialSieveModulus S * e := by
    exact_mod_cast himZ
  have hxval : x.1.1.val = y.1.1.val := by
    have hmod := congrArg (fun n : ℕ ↦ n % specialSieveModulus S) hreN
    have hxlt : x.1.1.val < specialSieveModulus S := by
      simpa [specialSieveModulus] using x.1.1.val_lt
    have hylt : y.1.1.val < specialSieveModulus S := by
      simpa [specialSieveModulus] using y.1.1.val_lt
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hxlt,
      Nat.mod_eq_of_lt hylt] using hmod
  have hyval : x.1.2.val = y.1.2.val := by
    have hmod := congrArg (fun n : ℕ ↦ n % specialSieveModulus S) himN
    have hxlt : x.1.2.val < specialSieveModulus S := by
      simpa [specialSieveModulus] using x.1.2.val_lt
    have hylt : y.1.2.val < specialSieveModulus S := by
      simpa [specialSieveModulus] using y.1.2.val_lt
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hxlt,
      Nat.mod_eq_of_lt hylt] using hmod
  have hxy : x = y := by
    apply Subtype.ext
    apply Prod.ext
    · exact ZMod.val_injective _ hxval
    · exact ZMod.val_injective _ hyval
  have hac : a = c := by
    have hmul : specialSieveModulus S * (a + 1) =
        specialSieveModulus S * (c + 1) := by
      rw [hxval] at hreN
      exact Nat.add_left_cancel hreN
    have := Nat.mul_left_cancel (specialSieveModulus_pos S) hmul
    omega
  have hbe : b = e := by
    have hmul : specialSieveModulus S * b =
        specialSieveModulus S * e := by
      rw [hyval] at himN
      exact Nat.add_left_cancel himN
    exact Nat.mul_left_cancel (specialSieveModulus_pos S) hmul
  exact ⟨hxy, hac, hbe⟩

theorem specialSieveElement_norm_natAbs_le
    {p L a b : ℕ} [Fact p.Prime]
    {S : Finset (SpecialSplitPrimeData p)}
    (x : splitAllowedResiduePairs S) (ha : a < L) (hb : b < L) :
    (specialSieveElement S x a b).norm.natAbs ≤
      4 * (1 + p ^ 3) * (specialSieveModulus S) ^ 2 * L ^ 2 := by
  let : NeZero (∏ s ∈ S, s.q) :=
    ⟨by simpa [specialSieveModulus] using
      (specialSieveModulus_pos S).ne'⟩
  have hL : 1 ≤ L := by omega
  have hM : 0 < specialSieveModulus S := specialSieveModulus_pos S
  have hML : specialSieveModulus S ≤ specialSieveModulus S * L := by
    simpa using Nat.mul_le_mul_left (specialSieveModulus S) hL
  have hxre : x.1.1.val < specialSieveModulus S := by
    simpa [specialSieveModulus] using x.1.1.val_lt
  have hxim : x.1.2.val < specialSieveModulus S := by
    simpa [specialSieveModulus] using x.1.2.val_lt
  have hre : x.1.1.val + specialSieveModulus S * (a + 1) ≤
      2 * specialSieveModulus S * L := by
    calc
      x.1.1.val + specialSieveModulus S * (a + 1) ≤
          specialSieveModulus S + specialSieveModulus S * L := by
        apply Nat.add_le_add hxre.le
        exact Nat.mul_le_mul_left _ (by omega)
      _ ≤ specialSieveModulus S * L + specialSieveModulus S * L :=
        Nat.add_le_add_right hML _
      _ = 2 * specialSieveModulus S * L := by ring
  have him : x.1.2.val + specialSieveModulus S * b ≤
      2 * specialSieveModulus S * L := by
    calc
      x.1.2.val + specialSieveModulus S * b ≤
          specialSieveModulus S + specialSieveModulus S * L := by
        apply Nat.add_le_add hxim.le
        exact Nat.mul_le_mul_left _ hb.le
      _ ≤ specialSieveModulus S * L + specialSieveModulus S * L :=
        Nat.add_le_add_right hML _
      _ = 2 * specialSieveModulus S * L := by ring
  have hnorm : (specialSieveElement S x a b).norm.natAbs =
      (x.1.1.val + specialSieveModulus S * (a + 1)) ^ 2 +
        p ^ 3 * (x.1.2.val + specialSieveModulus S * b) ^ 2 := by
    have hnormZ : (specialSieveElement S x a b).norm =
        (((x.1.1.val + specialSieveModulus S * (a + 1)) ^ 2 +
          p ^ 3 * (x.1.2.val + specialSieveModulus S * b) ^ 2 : ℕ) :
            ℤ) := by
      simp only [Zsqrtd.norm_def, specialSieveElement_re,
        specialSieveElement_im]
      push_cast
      ring
    rw [hnormZ, Int.natAbs_natCast]
  rw [hnorm]
  calc
    (x.1.1.val + specialSieveModulus S * (a + 1)) ^ 2 +
          p ^ 3 * (x.1.2.val + specialSieveModulus S * b) ^ 2 ≤
        (2 * specialSieveModulus S * L) ^ 2 +
          p ^ 3 * (2 * specialSieveModulus S * L) ^ 2 := by gcongr
    _ = 4 * (1 + p ^ 3) * (specialSieveModulus S) ^ 2 * L ^ 2 := by
      ring

def SpecialSieveClassBall
    (p N : ℕ) [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))
    (S : Finset (SpecialSplitPrimeData p)) :=
  {I : SpecialClassBall p N C //
    ∀ s : {s // s ∈ S}, ∀ b : Bool,
      IsCoprime (I.1 : Ideal (Zsqrtd (-(p : ℤ) ^ 3)))
        (s.1.integralUnitIdeal b : Ideal (Zsqrtd (-(p : ℤ) ^ 3)))}

/-- Sharp finite sieve in one ring-class.  The numerator is the exact
number of admissible CRT residue pairs; the norm ceiling contains only
the square of their common modulus. -/
theorem specialSieveClassBall_lower
    {p : ℕ} [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))
    (S : Finset (SpecialSplitPrimeData p))
    (I : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (hIclass : IntegralUnitIdeal.idealClass I = C)
    (hIcop : ∀ s : {s // s ∈ S}, ∀ b : Bool,
      IsCoprime (I : Ideal (Zsqrtd (-(p : ℤ) ^ 3)))
        (s.1.integralUnitIdeal b : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (L : ℕ) (hL : 0 < L) :
    (∏ s ∈ S, (s.q - 1) ^ 2) * L ^ 2 ≤
      Nat.card (SpecialSieveClassBall p
        ((4 * (1 + p ^ 3) * (specialSieveModulus S) ^ 2 *
          (I : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).cardQuot) * L ^ 2)
        C S) := by
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  let : Module.Free ℤ O :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ O :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Ring.HasFiniteQuotients O := inferInstance
  have hIne : (I : Ideal O) ≠ ⊥ := by
    intro hbot
    have hz : (((I : Ideal O) :
        FractionalIdeal O⁰ (FractionRing O))) = 0 := by rw [hbot]; rfl
    exact I.2.ne_zero hz
  let n := (I : Ideal O).cardQuot
  let B := 4 * (1 + p ^ 3) * (specialSieveModulus S) ^ 2 * n
  let z : splitAllowedResiduePairs S × (Fin L × Fin L) → O :=
    fun x ↦ specialSieveElement S x.1 x.2.1 x.2.2
  have hz0 (x : splitAllowedResiduePairs S × (Fin L × Fin L)) :
      z x ≠ 0 := specialSieveElement_ne_zero S x.1 x.2.1 x.2.2
  let Q : splitAllowedResiduePairs S × (Fin L × Fin L) →
      IntegralUnitIdeal O := fun x ↦
    principalIntegralUnitIdeal
      (Ideal.span ({z x} : Set O)) inferInstance (by
        intro hbot
        have hzmem : z x ∈ (⊥ : Ideal O) := by
          rw [← hbot]
          exact Ideal.mem_span_singleton_self _
        exact hz0 x (by simpa using hzmem))
  have hQclass (x : splitAllowedResiduePairs S × (Fin L × Fin L)) :
      IntegralUnitIdeal.idealClass (Q x) = 1 := by
    apply principalIntegralUnitIdeal_idealClass
  have hQIclass (x : splitAllowedResiduePairs S × (Fin L × Fin L)) :
      IntegralUnitIdeal.idealClass (Q x * I) = C := by
    rw [IntegralUnitIdeal.idealClass_mul, hQclass, hIclass, one_mul]
  have hQIcard (x : splitAllowedResiduePairs S × (Fin L × Fin L)) :
      ((Q x * I : IntegralUnitIdeal O) : Ideal O).cardQuot ≤
        B * L ^ 2 := by
    have hzbound := specialSieveElement_norm_natAbs_le x.1
      x.2.1.isLt x.2.2.isLt
    have hcard : ((Q x * I : IntegralUnitIdeal O) : Ideal O).cardQuot =
        (z x).norm.natAbs * n := by
      change (Ideal.span ({z x} : Set O) * (I : Ideal O)).cardQuot = _
      rw [cardQuot_span_singleton_mul_of_ne_bot
        (zsqrtdBasis (-(p : ℤ) ^ 3)) (I : Ideal O) hIne (hz0 x),
        algebraNorm_zsqrtd]
    rw [hcard]
    calc
      (z x).norm.natAbs * n ≤
          (4 * (1 + p ^ 3) * (specialSieveModulus S) ^ 2 * L ^ 2) * n :=
        Nat.mul_le_mul_right n hzbound
      _ = B * L ^ 2 := by dsimp only [B]; ring
  have hQIcop (x : splitAllowedResiduePairs S × (Fin L × Fin L))
      (s : {s // s ∈ S}) (b : Bool) :
      IsCoprime (((Q x * I : IntegralUnitIdeal O) : Ideal O))
        (s.1.integralUnitIdeal b : Ideal O) := by
    change IsCoprime (Ideal.span ({z x} : Set O) * (I : Ideal O))
      (s.1.integralUnitIdeal b : Ideal O)
    exact (specialSieveElement_span_isCoprime_oriented S x.1
      x.2.1 x.2.2 s b).mul_left (hIcop s b)
  let f : splitAllowedResiduePairs S × (Fin L × Fin L) →
      SpecialSieveClassBall p (B * L ^ 2) C S := fun x ↦
    ⟨⟨Q x * I, hQIclass x, hQIcard x⟩, hQIcop x⟩
  let : Finite (SpecialClassBall p (B * L ^ 2) C) :=
    finiteSpecialClassBall C
  let : Finite (SpecialSieveClassBall p (B * L ^ 2) C S) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hf : Function.Injective f := by
    intro x y hxy
    have hprod : Q x * I = Q y * I :=
      congrArg (fun V : SpecialSieveClassBall p (B * L ^ 2) C S ↦
        V.1.1) hxy
    have hQ : Q x = Q y :=
      IntegralUnitIdeal.mul_right_cancel (Q x) (Q y) I hprod
    have hspan : Ideal.span ({z x} : Set O) =
        Ideal.span ({z y} : Set O) := by
      exact congrArg (fun J : IntegralUnitIdeal O ↦ (J : Ideal O)) hQ
    have hassoc : Associated (z x) (z y) :=
      Ideal.span_singleton_eq_span_singleton.mp hspan
    have hcoords := specialSieveElement_eq_of_associated hassoc
    apply Prod.ext
    · exact hcoords.1
    · apply Prod.ext
      · exact Fin.ext hcoords.2.1
      · exact Fin.ext hcoords.2.2
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod,
    natCard_splitAllowedResiduePairs] at hcard
  simpa [B, pow_two, Nat.mul_assoc] using hcard

/-- An invertible ideal is cyclic after reduction modulo a nonzero ideal.
This is the generator half of semilocal triviality, retained separately so
that many lifts of all residue classes can be counted. -/
theorem exists_integralUnitIdeal_generator_mod_mul
    {R : Type*} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]
    (J : IntegralUnitIdeal R) (F : Ideal R) (hFne : F ≠ ⊥) :
    ∃ x : (J : Ideal R),
      (J : Ideal R) ≤ Ideal.span ({(x : R)} : Set R) +
        F * (J : Ideal R) := by
  classical
  by_cases hFtop : F = ⊤
  · have hJne : (J : Ideal R) ≠ ⊥ := by
      intro hbot
      have hz : (((J : Ideal R) :
          FractionalIdeal R⁰ (FractionRing R))) = 0 := by rw [hbot]; rfl
      exact J.2.ne_zero hz
    have hn : 0 < (J : Ideal R).cardQuot :=
      Ring.HasFiniteQuotients.cardQuot_pos _ hJne
    have hxmem : (((J : Ideal R).cardQuot : ℕ) : R) ∈
        (J : Ideal R) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact Ideal.Quotient.index_eq_zero (J : Ideal R)
    let x : (J : Ideal R) := ⟨((J : Ideal R).cardQuot : R), hxmem⟩
    refine ⟨x, ?_⟩
    rw [hFtop, Ideal.top_mul]
    exact le_sup_right
  · let A := R ⧸ F
    let M := (J : Ideal R)
    let T := TensorProduct R A M
    let : Nontrivial A :=
      (Ideal.Quotient.nontrivial_iff (R := R) (I := F)).mpr hFtop
    let : Finite A := Ring.HasFiniteQuotients.finiteQuotient hFne
    let : IsArtinianRing A := isArtinian_of_finite
    let : Module.Invertible R M :=
      moduleInvertibleIdealOfIsUnit (J : Ideal R) J.2
    let : Module.Invertible A T := inferInstance
    let : Module.Free A T := inferInstance
    let e : T ≃ₗ[A] A :=
      (Module.Invertible.free_iff_linearEquiv.mp
        (inferInstance : Module.Free A T)).some
    obtain ⟨x, hx⟩ := TensorProduct.mk_surjective R M A
      Ideal.Quotient.mk_surjective (e.symm 1)
    have hmod : (J : Ideal R) ≤
        Ideal.span ({(x : R)} : Set R) + F * (J : Ideal R) := by
      intro y hy
      let ys : M := ⟨y, hy⟩
      let a : A := e (TensorProduct.mk R A M 1 ys)
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
      let v : M := ys - r • x
      have hvzero : TensorProduct.mk R A M 1 v = 0 := by
        dsimp only [v]
        rw [map_sub, map_smul, hx]
        apply e.injective
        rw [map_sub, map_zero]
        change a - e (r • e.symm 1) = 0
        rw [← IsScalarTower.algebraMap_smul A r (e.symm 1), map_smul,
          e.apply_symm_apply]
        rw [smul_eq_mul, mul_one]
        change a - algebraMap R A r = 0
        rw [← hr]
        simp [A, Ideal.Quotient.algebraMap_eq]
      have hvker : v ∈ LinearMap.ker (TensorProduct.mk R A M 1) :=
        LinearMap.mem_ker.mpr hvzero
      rw [LinearMap.ker_tensorProductMk] at hvker
      have hvprod : (v : R) ∈ F * (J : Ideal R) := by
        rw [← Ideal.smul_eq_mul]
        exact Submodule.smul_induction_on hvker
          (fun r hrF w _ ↦ by
            change r * (w : R) ∈ F • (J : Ideal R)
            rw [Ideal.smul_eq_mul]
            exact Ideal.mul_mem_mul hrF w.2)
          (fun _ _ ha hb ↦ add_mem ha hb)
      have hspan : (r : R) * (x : R) ∈
          Ideal.span ({(x : R)} : Set R) :=
        (Ideal.span ({(x : R)} : Set R)).mul_mem_left r
          (Ideal.mem_span_singleton_self (x : R))
      have hvval : (v : R) = y - r * (x : R) := rfl
      have hspan' : r * (x : R) ∈
          Ideal.span ({(x : R)} : Set R) + F * (J : Ideal R) :=
        (show Ideal.span ({(x : R)} : Set R) ≤
          Ideal.span ({(x : R)} : Set R) + F * (J : Ideal R)
            from le_sup_left) hspan
      have hvprod' : (v : R) ∈
          Ideal.span ({(x : R)} : Set R) + F * (J : Ideal R) :=
        (show F * (J : Ideal R) ≤
          Ideal.span ({(x : R)} : Set R) + F * (J : Ideal R)
            from le_sup_right) hvprod
      have hadd := add_mem hspan' hvprod'
      convert hadd using 1
      rw [hvval]
      abel
    exact ⟨x, hmod⟩

theorem ideal_le_of_mul_le_mul_left_integralUnitIdeal
    {R : Type*} [CommRing R] [IsDomain R]
    (J : IntegralUnitIdeal R) {A B : Ideal R}
    (h : (J : Ideal R) * A ≤ (J : Ideal R) * B) : A ≤ B := by
  have hfrac :
      (((J : Ideal R) * A : Ideal R) :
          FractionalIdeal R⁰ (FractionRing R)) ≤
        (((J : Ideal R) * B : Ideal R) :
          FractionalIdeal R⁰ (FractionRing R)) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing R)).mpr h
  have hfrac' :
      ((J.unit : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
          FractionalIdeal R⁰ (FractionRing R)) *
          ((A : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) ≤
        ((J.unit : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
          FractionalIdeal R⁰ (FractionRing R)) *
          ((B : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) := by
    simpa only [FractionalIdeal.coeIdeal_mul,
      IntegralUnitIdeal.unit_coe] using hfrac
  have hcancel := mul_le_mul_right hfrac'
    (((J.unit)⁻¹ : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
      FractionalIdeal R⁰ (FractionRing R))
  have hAB : ((A : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) ≤
      ((B : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) := by
    simpa only [← mul_assoc, Units.val_inv_eq_inv_val, Units.inv_mul,
      one_mul] using hcancel
  exact (FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing R)).mp hAB

theorem generator_lift_not_mem_mul
    {R : Type*} [CommRing R] [IsDomain R]
    (J P : IntegralUnitIdeal R) (F : Ideal R) (x : (J : Ideal R))
    (hgen : (J : Ideal R) ≤ Ideal.span ({(x : R)} : Set R) +
      F * (J : Ideal R))
    (hFP : F ≤ (P : Ideal R)) {w u : R}
    (hw : w ∉ (P : Ideal R)) (hu : u ∈ F * (J : Ideal R)) :
    w * (x : R) + u ∉ (J : Ideal R) * (P : Ideal R) := by
  intro hz
  have hux : u ∈ (J : Ideal R) * (P : Ideal R) := by
    have hle : F * (J : Ideal R) ≤ (J : Ideal R) * (P : Ideal R) := by
      calc
        F * (J : Ideal R) = (J : Ideal R) * F := mul_comm _ _
        _ ≤ (J : Ideal R) * (P : Ideal R) :=
          Ideal.mul_mono_right hFP
    exact hle hu
  have hwx : w * (x : R) ∈ (J : Ideal R) * (P : Ideal R) := by
    have := sub_mem hz hux
    simpa using this
  have hmul : (J : Ideal R) * Ideal.span ({w} : Set R) ≤
      (J : Ideal R) * (P : Ideal R) := by
    calc
      (J : Ideal R) * Ideal.span ({w} : Set R) =
          Ideal.span ({w} : Set R) * (J : Ideal R) := mul_comm _ _
      _ ≤ Ideal.span ({w} : Set R) *
          (Ideal.span ({(x : R)} : Set R) + F * (J : Ideal R)) :=
        Ideal.mul_mono_right hgen
      _ = Ideal.span ({w * (x : R)} : Set R) +
          Ideal.span ({w} : Set R) * (F * (J : Ideal R)) := by
        rw [mul_add, Ideal.span_singleton_mul_span_singleton]
      _ ≤ (J : Ideal R) * (P : Ideal R) := by
        apply sup_le
        · exact (Ideal.span_singleton_le_iff_mem _).mpr hwx
        · calc
            Ideal.span ({w} : Set R) * (F * (J : Ideal R)) =
                F * ((J : Ideal R) * Ideal.span ({w} : Set R)) := by
              ac_rfl
            _ ≤ (P : Ideal R) * (J : Ideal R) := by
              have hJw : (J : Ideal R) * Ideal.span ({w} : Set R) ≤
                  (J : Ideal R) := Ideal.mul_le_left
              exact Ideal.mul_mono hFP hJw
            _ = (J : Ideal R) * (P : Ideal R) := mul_comm _ _
  have hspan : Ideal.span ({w} : Set R) ≤ (P : Ideal R) :=
    ideal_le_of_mul_le_mul_left_integralUnitIdeal J hmul
  exact hw (hspan (Ideal.mem_span_singleton_self w))

theorem generator_mem_of_mul_mem
    {R : Type*} [CommRing R] [IsDomain R]
    (J : IntegralUnitIdeal R) (F : Ideal R) (x : (J : Ideal R))
    (hgen : (J : Ideal R) ≤ Ideal.span ({(x : R)} : Set R) +
      F * (J : Ideal R)) {w : R}
    (hwx : w * (x : R) ∈ F * (J : Ideal R)) : w ∈ F := by
  have hmul : (J : Ideal R) * Ideal.span ({w} : Set R) ≤
      (J : Ideal R) * F := by
    calc
      (J : Ideal R) * Ideal.span ({w} : Set R) =
          Ideal.span ({w} : Set R) * (J : Ideal R) := mul_comm _ _
      _ ≤ Ideal.span ({w} : Set R) *
          (Ideal.span ({(x : R)} : Set R) + F * (J : Ideal R)) :=
        Ideal.mul_mono_right hgen
      _ = Ideal.span ({w * (x : R)} : Set R) +
          Ideal.span ({w} : Set R) * (F * (J : Ideal R)) := by
        rw [mul_add, Ideal.span_singleton_mul_span_singleton]
      _ ≤ (J : Ideal R) * F := by
        apply sup_le
        · rw [mul_comm (J : Ideal R) F]
          exact (Ideal.span_singleton_le_iff_mem _).mpr hwx
        · calc
            Ideal.span ({w} : Set R) * (F * (J : Ideal R)) =
                F * ((J : Ideal R) * Ideal.span ({w} : Set R)) := by
              ac_rfl
            _ ≤ F * (J : Ideal R) := by
              exact Ideal.mul_mono_right Ideal.mul_le_left
            _ = (J : Ideal R) * F := mul_comm _ _
  have hspan : Ideal.span ({w} : Set R) ≤ F :=
    ideal_le_of_mul_le_mul_left_integralUnitIdeal J hmul
  exact hspan (Ideal.mem_span_singleton_self w)

theorem specialSieveModulus_span_le_oriented
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (s : {s // s ∈ S}) (b : Bool) :
    Ideal.span ({Zsqrtd.ofInt (specialSieveModulus S : ℤ)} :
      Set (Zsqrtd (-(p : ℤ) ^ 3))) ≤
        (s.1.integralUnitIdeal b : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
  rw [Ideal.span_singleton_le_iff_mem]
  have hdiv : s.1.q ∣ specialSieveModulus S :=
    Finset.dvd_prod_of_mem (fun t ↦ t.q) s.2
  obtain ⟨k, hk⟩ := hdiv
  rw [hk]
  have hqmem : Zsqrtd.ofInt (s.1.q : ℤ) ∈
      (s.1.integralUnitIdeal b : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
    cases b <;>
      exact Ideal.subset_span (by
        simp [SpecialSplitPrimeData.integralUnitIdeal,
          specialOrientedIntegralUnitIdeal, specialOrientedSplitIdeal,
          splitPrimeIdeal, splitConjugateIdeal])
  rw [show Zsqrtd.ofInt ((s.1.q * k : ℕ) : ℤ) =
      Zsqrtd.ofInt (k : ℤ) * Zsqrtd.ofInt (s.1.q : ℤ) by
    ext <;> simp [mul_comm]]
  exact (s.1.integralUnitIdeal b :
    Ideal (Zsqrtd (-(p : ℤ) ^ 3))).mul_mem_left _ hqmem

theorem specialSieveElement_not_mem_oriented
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) (a b : ℕ)
    (s : {s // s ∈ S}) (c : Bool) :
    specialSieveElement S x a b ∉
      (s.1.integralUnitIdeal c : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
  intro hz
  have hspan : Ideal.span ({specialSieveElement S x a b} :
      Set (Zsqrtd (-(p : ℤ) ^ 3))) ≤
        (s.1.integralUnitIdeal c : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hz
  have hcop := specialSieveElement_span_isCoprime_oriented S x a b s c
  have htop : (⊤ : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) ≤
      (s.1.integralUnitIdeal c : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
    rw [← hcop.sup_eq]
    exact sup_le hspan le_rfl
  exact (specialOrientedIntegralUnitIdeal_isMaximal p s.1.q s.1.prime
    s.1.ne_two s.1.ne_p s.1.split c).ne_top (top_unique htop)

theorem isCoprime_of_mul_eq_span_not_mem
    {R : Type*} [CommRing R] [IsDomain R]
    (J K P : IntegralUnitIdeal R) (hP : (P : Ideal R).IsMaximal)
    {z : R} (hmul : (J : Ideal R) * (K : Ideal R) =
      Ideal.span ({z} : Set R))
    (hnot : z ∉ (J : Ideal R) * (P : Ideal R)) :
    IsCoprime (K : Ideal R) (P : Ideal R) := by
  have hKnot : ¬(K : Ideal R) ≤ (P : Ideal R) := by
    intro hKP
    apply hnot
    have hz : z ∈ (J : Ideal R) * (K : Ideal R) := by
      rw [hmul]
      exact Ideal.mem_span_singleton_self z
    exact (Ideal.mul_mono_right hKP) hz
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  have heq : (P : Ideal R) = (K : Ideal R) ⊔ (P : Ideal R) :=
    hP.eq_of_le htop le_sup_right
  apply hKnot
  exact le_sup_left.trans_eq heq.symm

def specialShiftedGenerator
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) (m R : ℕ)
    (x : splitAllowedResiduePairs S) (a b : ℕ) :
    Zsqrtd (-(p : ℤ) ^ 3) :=
  specialSieveElement S x 0 0 * g +
    ⟨specialSieveModulus S * m * (R + 1 + a),
      specialSieveModulus S * m * b⟩

noncomputable def specialGeneratorRadius
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) : ℕ := by
  letI : NeZero (∏ s ∈ S, s.q) :=
    ⟨by simpa [specialSieveModulus] using
      (specialSieveModulus_pos S).ne'⟩
  letI : Fintype (splitAllowedResiduePairs S) := by
    unfold splitAllowedResiduePairs
    infer_instance
  exact Finset.univ.sup fun x : splitAllowedResiduePairs S ↦
    max (specialSieveElement S x 0 0 * g).re.natAbs
      (specialSieveElement S x 0 0 * g).im.natAbs

theorem specialGeneratorRadius_re
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) (x : splitAllowedResiduePairs S) :
    (specialSieveElement S x 0 0 * g).re.natAbs ≤
      specialGeneratorRadius S g := by
  let : NeZero (∏ s ∈ S, s.q) :=
    ⟨by simpa [specialSieveModulus] using
      (specialSieveModulus_pos S).ne'⟩
  let : Fintype (splitAllowedResiduePairs S) := by
    unfold splitAllowedResiduePairs
    infer_instance
  exact le_trans (le_max_left _ _)
    (Finset.le_sup (f := fun y : splitAllowedResiduePairs S ↦
      max (specialSieveElement S y 0 0 * g).re.natAbs
        (specialSieveElement S y 0 0 * g).im.natAbs)
      (Finset.mem_univ x))

theorem specialGeneratorRadius_im
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) (x : splitAllowedResiduePairs S) :
    (specialSieveElement S x 0 0 * g).im.natAbs ≤
      specialGeneratorRadius S g := by
  let : NeZero (∏ s ∈ S, s.q) :=
    ⟨by simpa [specialSieveModulus] using
      (specialSieveModulus_pos S).ne'⟩
  let : Fintype (splitAllowedResiduePairs S) := by
    unfold splitAllowedResiduePairs
    infer_instance
  exact le_trans (le_max_right _ _)
    (Finset.le_sup (f := fun y : splitAllowedResiduePairs S ↦
      max (specialSieveElement S y 0 0 * g).re.natAbs
        (specialSieveElement S y 0 0 * g).im.natAbs)
      (Finset.mem_univ x))

theorem specialShiftedGenerator_re_pos
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) (m : ℕ) (hm : 0 < m)
    (x : splitAllowedResiduePairs S) (a b : ℕ) :
    0 < (specialShiftedGenerator S g m (specialGeneratorRadius S g)
      x a b).re := by
  have hM := specialSieveModulus_pos S
  have hbase := specialGeneratorRadius_re S g x
  have hneg : -((specialGeneratorRadius S g : ℕ) : ℤ) ≤
      (specialSieveElement S x 0 0 * g).re := by
    have hraw : -((specialSieveElement S x 0 0 * g).re.natAbs : ℤ) ≤
        (specialSieveElement S x 0 0 * g).re := by
      by_cases hpos : 0 ≤ (specialSieveElement S x 0 0 * g).re
      · exact (neg_nonpos.mpr (by positivity)).trans hpos
      · have hnon : (specialSieveElement S x 0 0 * g).re ≤ 0 :=
          le_of_not_ge hpos
        rw [Int.ofNat_natAbs_of_nonpos hnon]
        simp
    exact (neg_le_neg (by exact_mod_cast hbase)).trans hraw
  simp only [specialShiftedGenerator, Zsqrtd.re_add]
  change 0 < (specialSieveElement S x 0 0 * g).re +
    ((specialSieveModulus S * m *
      (specialGeneratorRadius S g + 1 + a) : ℕ) : ℤ)
  have hshift : (specialGeneratorRadius S g : ℤ) <
      ((specialSieveModulus S * m *
        (specialGeneratorRadius S g + 1 + a) : ℕ) : ℤ) := by
    exact_mod_cast (show specialGeneratorRadius S g <
      specialSieveModulus S * m *
        (specialGeneratorRadius S g + 1 + a) by
      exact (show specialGeneratorRadius S g <
        specialGeneratorRadius S g + 1 + a by omega).trans_le
          (Nat.le_mul_of_pos_left _ (mul_pos hM hm)))
  omega

theorem specialShiftedGenerator_norm_natAbs_le
    {p L : ℕ} [Fact p.Prime]
    (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) (m : ℕ) (hm : 0 < m)
    (x : splitAllowedResiduePairs S) {a b : ℕ}
    (ha : a < L) (hb : b < L)
    (hR : specialGeneratorRadius S g < L) :
    (specialShiftedGenerator S g m (specialGeneratorRadius S g)
      x a b).norm.natAbs ≤
      9 * (1 + p ^ 3) * (specialSieveModulus S * m) ^ 2 * L ^ 2 := by
  let d := specialSieveModulus S * m
  have hd : 0 < d := mul_pos (specialSieveModulus_pos S) hm
  let z₀ := specialSieveElement S x 0 0 * g
  let R := specialGeneratorRadius S g
  have hre0 : z₀.re.natAbs ≤ R := specialGeneratorRadius_re S g x
  have him0 : z₀.im.natAbs ≤ R := specialGeneratorRadius_im S g x
  have hRL : R ≤ L := hR.le
  have hdL : L ≤ d * L := by
    simpa using Nat.mul_le_mul_right L hd
  have hshiftRe : d * (R + 1 + a) ≤ d * (R + L) := by
    exact Nat.mul_le_mul_left d (by omega)
  have hre : (specialShiftedGenerator S g m R x a b).re.natAbs ≤
      3 * d * L := by
    have hadd := Int.natAbs_add_le z₀.re
      ((d * (R + 1 + a) : ℕ) : ℤ)
    have hcast : (((d * (R + 1 + a) : ℕ) : ℤ)).natAbs =
        d * (R + 1 + a) := by
      exact Int.natAbs_natCast _
    simp only [specialShiftedGenerator, Zsqrtd.re_add] at hadd ⊢
    change (z₀.re + ((d * (R + 1 + a) : ℕ) : ℤ)).natAbs ≤ _
    rw [hcast] at hadd
    calc
      (z₀.re + ((d * (R + 1 + a) : ℕ) : ℤ)).natAbs ≤
          z₀.re.natAbs + d * (R + 1 + a) := hadd
      _ ≤ R + d * (R + L) := Nat.add_le_add hre0 hshiftRe
      _ ≤ d * L + (d * L + d * L) := by
        apply Nat.add_le_add (hRL.trans hdL)
        rw [mul_add]
        exact Nat.add_le_add (Nat.mul_le_mul_left d hRL) le_rfl
      _ = 3 * d * L := by ring
  have him : (specialShiftedGenerator S g m R x a b).im.natAbs ≤
      3 * d * L := by
    have hadd := Int.natAbs_add_le z₀.im ((d * b : ℕ) : ℤ)
    have hcast : (((d * b : ℕ) : ℤ)).natAbs = d * b := by
      exact Int.natAbs_natCast _
    simp only [specialShiftedGenerator, Zsqrtd.im_add] at hadd ⊢
    change (z₀.im + ((d * b : ℕ) : ℤ)).natAbs ≤ _
    rw [hcast] at hadd
    calc
      (z₀.im + ((d * b : ℕ) : ℤ)).natAbs ≤
          z₀.im.natAbs + d * b := hadd
      _ ≤ R + d * L := Nat.add_le_add him0 (Nat.mul_le_mul_left d hb.le)
      _ ≤ d * L + d * L := Nat.add_le_add_right (hRL.trans hdL) _
      _ ≤ 3 * d * L := by nlinarith
  have hnorm : (specialShiftedGenerator S g m R x a b).norm.natAbs =
      (specialShiftedGenerator S g m R x a b).re.natAbs ^ 2 +
        p ^ 3 * (specialShiftedGenerator S g m R x a b).im.natAbs ^ 2 := by
    have hnormZ : (specialShiftedGenerator S g m R x a b).norm =
        (((specialShiftedGenerator S g m R x a b).re.natAbs ^ 2 +
          p ^ 3 *
            (specialShiftedGenerator S g m R x a b).im.natAbs ^ 2 : ℕ) :
              ℤ) := by
      rw [Zsqrtd.norm_def]
      push_cast
      simp only [Int.natCast_natAbs, sq_abs]
      ring
    rw [hnormZ, Int.natAbs_natCast]
  rw [hnorm]
  calc
    (specialShiftedGenerator S g m R x a b).re.natAbs ^ 2 +
          p ^ 3 * (specialShiftedGenerator S g m R x a b).im.natAbs ^ 2 ≤
        (3 * d * L) ^ 2 + p ^ 3 * (3 * d * L) ^ 2 := by gcongr
    _ = 9 * (1 + p ^ 3) *
        (specialSieveModulus S * m) ^ 2 * L ^ 2 := by
      dsimp only [d]
      ring

theorem splitAllowedResiduePair_eq_of_base_sub_mem
    {p : ℕ} [Fact p.Prime]
    (S : Finset (SpecialSplitPrimeData p))
    (x y : splitAllowedResiduePairs S)
    (hmem : specialSieveElement S x 0 0 - specialSieveElement S y 0 0 ∈
      Ideal.span ({Zsqrtd.ofInt (specialSieveModulus S : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3)))) : x = y := by
  let : NeZero (∏ s ∈ S, s.q) :=
    ⟨by simpa [specialSieveModulus] using
      (specialSieveModulus_pos S).ne'⟩
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hre := congrArg Zsqrtd.re hc
  have him := congrArg Zsqrtd.im hc
  have hreMod : ((specialSieveElement S x 0 0 -
      specialSieveElement S y 0 0).re :
        ZMod (∏ s ∈ S, s.q)) = 0 := by
    rw [hre]
    simp only [Zsqrtd.re_mul, Zsqrtd.re_ofInt, Zsqrtd.im_ofInt,
      mul_zero, zero_mul, add_zero]
    change (((specialSieveModulus S : ℤ) * c.re : ℤ) :
      ZMod (∏ s ∈ S, s.q)) = 0
    have hmod : (((specialSieveModulus S : ℤ) :
        ZMod (∏ s ∈ S, s.q))) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp [specialSieveModulus]
    rw [Int.cast_mul, hmod, zero_mul]
  have himMod : ((specialSieveElement S x 0 0 -
      specialSieveElement S y 0 0).im :
        ZMod (∏ s ∈ S, s.q)) = 0 := by
    rw [him]
    simp only [Zsqrtd.im_mul, Zsqrtd.re_ofInt, Zsqrtd.im_ofInt,
      mul_zero, zero_mul, add_zero]
    have hmod : (((specialSieveModulus S : ℤ) :
        ZMod (∏ s ∈ S, s.q))) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp [specialSieveModulus]
    rw [Int.cast_mul, hmod, zero_mul]
  have hx1 : x.1.1 = y.1.1 := by
    apply sub_eq_zero.mp
    simpa [specialSieveElement, specialSieveModulus] using hreMod
  have hx2 : x.1.2 = y.1.2 := by
    apply sub_eq_zero.mp
    simpa [specialSieveElement, specialSieveModulus] using himMod
  apply Subtype.ext
  exact Prod.ext hx1 hx2

theorem specialShiftedGenerator_eq_of_associated
    {p m a b c e : ℕ} [Fact p.Prime] (hm : 0 < m)
    (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3))
    (x y : splitAllowedResiduePairs S)
    (h : Associated
      (specialShiftedGenerator S g m (specialGeneratorRadius S g) x a b)
      (specialShiftedGenerator S g m (specialGeneratorRadius S g) y c e)) :
    specialShiftedGenerator S g m (specialGeneratorRadius S g) x a b =
      specialShiftedGenerator S g m (specialGeneratorRadius S g) y c e := by
  obtain ⟨u, hu⟩ := h
  have hunit : IsUnit (u : Zsqrtd (-(p : ℤ) ^ 3)) := u.isUnit
  have hd : (-(p : ℤ) ^ 3 : ℤ) ≤ -2 := by
    have hp := (Fact.out : Nat.Prime p).two_le
    have hp3 : 2 ≤ p ^ 3 := hp.trans
      (Nat.le_self_pow (by norm_num : 3 ≠ 0) p)
    have hp3Z : (2 : ℤ) ≤ (p : ℤ) ^ 3 := by exact_mod_cast hp3
    omega
  rcases (zsqrtd_isUnit_iff_eq_one_or_neg_one hd
      (u : Zsqrtd (-(p : ℤ) ^ 3))).mp hunit with hu1 | huneg
  · simpa [hu1] using hu
  · have hleft := specialShiftedGenerator_re_pos S g m hm x a b
    have hright := specialShiftedGenerator_re_pos S g m hm y c e
    have hu' :
        specialShiftedGenerator S g m (specialGeneratorRadius S g) x a b *
            (-1 : Zsqrtd (-(p : ℤ) ^ 3)) =
          specialShiftedGenerator S g m (specialGeneratorRadius S g) y c e := by
      simpa [huneg] using hu
    have hre := congrArg Zsqrtd.re hu'
    have hneg :
        -(specialShiftedGenerator S g m (specialGeneratorRadius S g)
            x a b).re =
          (specialShiftedGenerator S g m (specialGeneratorRadius S g)
            y c e).re := by
      simpa using hre
    omega

theorem specialShiftedGenerator_sub_base_mem
    {p m a b : ℕ} [Fact p.Prime]
    (S : Finset (SpecialSplitPrimeData p))
    (J : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (g : (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (hm_mem : (m : Zsqrtd (-(p : ℤ) ^ 3)) ∈
      (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (x : splitAllowedResiduePairs S) :
    specialShiftedGenerator S (g : Zsqrtd (-(p : ℤ) ^ 3)) m
        (specialGeneratorRadius S g) x a b -
        specialSieveElement S x 0 0 * (g : Zsqrtd (-(p : ℤ) ^ 3)) ∈
      Ideal.span ({Zsqrtd.ofInt (specialSieveModulus S : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) *
          (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
  let v : Zsqrtd (-(p : ℤ) ^ 3) :=
    ⟨(m * (specialGeneratorRadius S g + 1 + a) : ℕ), (m * b : ℕ)⟩
  have hv : v ∈ (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
    have hprod := (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).mul_mem_right
      (⟨(specialGeneratorRadius S g + 1 + a : ℕ), (b : ℕ)⟩ :
        Zsqrtd (-(p : ℤ) ^ 3)) hm_mem
    convert hprod using 1 <;> ext <;> simp [v] <;> ring
  have hM : Zsqrtd.ofInt (specialSieveModulus S : ℤ) ∈
      Ideal.span ({Zsqrtd.ofInt (specialSieveModulus S : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) :=
    Ideal.mem_span_singleton_self _
  have hmul := Ideal.mul_mem_mul hM hv
  convert hmul using 1 <;> ext <;>
    simp [specialShiftedGenerator, v] <;> ring

theorem specialShiftedGenerator_mem
    {p m a b : ℕ} [Fact p.Prime]
    (S : Finset (SpecialSplitPrimeData p))
    (J : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (g : (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (hm_mem : (m : Zsqrtd (-(p : ℤ) ^ 3)) ∈
      (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (x : splitAllowedResiduePairs S) :
    specialShiftedGenerator S (g : Zsqrtd (-(p : ℤ) ^ 3)) m
        (specialGeneratorRadius S g) x a b ∈
      (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
  have hbase : specialSieveElement S x 0 0 *
      (g : Zsqrtd (-(p : ℤ) ^ 3)) ∈
        (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) :=
    (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).mul_mem_left _ g.2
  have hshift := specialShiftedGenerator_sub_base_mem
    (a := a) (b := b) S J g hm_mem x
  have hmulLe : Ideal.span
      ({Zsqrtd.ofInt (specialSieveModulus S : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) *
          (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) ≤
        (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := Ideal.mul_le_right
  have := add_mem hbase (hmulLe hshift)
  convert this using 1 <;> ring

/-- A class-independent sharp finite sieve.  The fixed ideal representative
only enters through its index; the admissible density is the exact CRT
product and is therefore uniform in the finite set of split primes. -/
theorem exists_specialSieveClassBall_lower_uniform
    {p : ℕ} [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))
    (S : Finset (SpecialSplitPrimeData p))
    (J : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (hJclass : IntegralUnitIdeal.idealClass J = C⁻¹) :
    ∃ R : ℕ, ∀ L : ℕ, R < L →
      (∏ s ∈ S, (s.q - 1) ^ 2) * L ^ 2 ≤
        Nat.card (SpecialSieveClassBall p
          (9 * (1 + p ^ 3) *
            (specialSieveModulus S *
              (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).cardQuot) ^ 2 * L ^ 2)
          C S) := by
  classical
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  let : Module.Free ℤ O :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ O :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Ring.HasFiniteQuotients O := inferInstance
  let m := (J : Ideal O).cardQuot
  have hJne : (J : Ideal O) ≠ ⊥ := by
    intro hbot
    have hz : (((J : Ideal O) :
        FractionalIdeal O⁰ (FractionRing O))) = 0 := by rw [hbot]; rfl
    exact J.2.ne_zero hz
  have hm : 0 < m := Ring.HasFiniteQuotients.cardQuot_pos _ hJne
  have hm_mem : (m : O) ∈ (J : Ideal O) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero (J : Ideal O)
  let F : Ideal O := Ideal.span
    ({Zsqrtd.ofInt (specialSieveModulus S : ℤ)} : Set O)
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hmem : Zsqrtd.ofInt (specialSieveModulus S : ℤ) ∈
        (⊥ : Ideal O) := by
      rw [← hbot]
      exact Ideal.mem_span_singleton_self _
    have hre := congrArg Zsqrtd.re (show
      Zsqrtd.ofInt (specialSieveModulus S : ℤ) = (0 : O) by
        simpa using hmem)
    have hreZ : (specialSieveModulus S : ℤ) = 0 := by
      simpa only [Zsqrtd.re_ofInt, Zsqrtd.re_zero] using hre
    have : specialSieveModulus S = 0 := by exact_mod_cast hreZ
    exact (specialSieveModulus_pos S).ne' this
  obtain ⟨g, hgen⟩ :=
    exists_integralUnitIdeal_generator_mod_mul J F hFne
  let R := specialGeneratorRadius S (g : O)
  refine ⟨R, ?_⟩
  intro L hRL
  let X := splitAllowedResiduePairs S × (Fin L × Fin L)
  let z : X → O := fun x ↦
    specialShiftedGenerator S (g : O) m R x.1 x.2.1 x.2.2
  have hzpos (x : X) : 0 < (z x).re := by
    simpa [z, R] using (specialShiftedGenerator_re_pos S (g : O) m hm
      x.1 x.2.1 x.2.2)
  have hz0 (x : X) : z x ≠ 0 := by
    intro hzero
    have hre := congrArg Zsqrtd.re hzero
    simp only [Zsqrtd.re_zero] at hre
    have hp := hzpos x
    omega
  have hzmem (x : X) : z x ∈ (J : Ideal O) := by
    exact specialShiftedGenerator_mem S J g hm_mem x.1
  let Q : X → IntegralUnitIdeal O := fun x ↦
    principalIntegralUnitIdeal (Ideal.span ({z x} : Set O))
      inferInstance (by
        intro hbot
        have hmem : z x ∈ (⊥ : Ideal O) := by
          rw [← hbot]
          exact Ideal.mem_span_singleton_self _
        exact hz0 x (by simpa using hmem))
  have hQle (x : X) : (Q x : Ideal O) ≤ (J : Ideal O) := by
    exact (Ideal.span_singleton_le_iff_mem _).mpr (hzmem x)
  let factor (x : X) :=
    IntegralUnitIdeal.exists_mul_eq_of_le J (Q x) (hQle x)
  let K : X → IntegralUnitIdeal O := fun x ↦ (factor x).choose
  have hJK (x : X) : J * K x = Q x := (factor x).choose_spec
  have hspan (x : X) : (J : Ideal O) * (K x : Ideal O) =
      Ideal.span ({z x} : Set O) :=
    congrArg (fun I : IntegralUnitIdeal O ↦ (I : Ideal O)) (hJK x)
  have hQclass (x : X) : IntegralUnitIdeal.idealClass (Q x) = 1 := by
    apply principalIntegralUnitIdeal_idealClass
  have hKclass (x : X) : IntegralUnitIdeal.idealClass (K x) = C := by
    have hclasses := congrArg IntegralUnitIdeal.idealClass (hJK x)
    rw [IntegralUnitIdeal.idealClass_mul, hQclass] at hclasses
    calc
      IntegralUnitIdeal.idealClass (K x) =
          C * (C⁻¹ * IntegralUnitIdeal.idealClass (K x)) := by simp
      _ = C * (IntegralUnitIdeal.idealClass J *
          IntegralUnitIdeal.idealClass (K x)) := by rw [hJclass]
      _ = C := by rw [hclasses, mul_one]
  have hKcard (x : X) : (K x : Ideal O).cardQuot ≤
      9 * (1 + p ^ 3) * (specialSieveModulus S * m) ^ 2 * L ^ 2 := by
    have hspanLe : Ideal.span ({z x} : Set O) ≤ (K x : Ideal O) := by
      rw [← hspan x]
      exact Ideal.mul_le_right
    have hspanNe : Ideal.span ({z x} : Set O) ≠ ⊥ := by
      intro hbot
      have hmem : z x ∈ (⊥ : Ideal O) := by
        rw [← hbot]
        exact Ideal.mem_span_singleton_self _
      exact hz0 x (by simpa using hmem)
    have hmono := cardQuot_mono_of_le hspanNe hspanLe
    have htopNe : (⊤ : Ideal O) ≠ ⊥ := by simp
    have hspanCard := cardQuot_span_singleton_mul_of_ne_bot
      (zsqrtdBasis (-(p : ℤ) ^ 3)) (⊤ : Ideal O) htopNe (hz0 x)
    have hcardEq : (Ideal.span ({z x} : Set O)).cardQuot =
        (z x).norm.natAbs := by
      simpa [Ideal.mul_top, algebraNorm_zsqrtd] using hspanCard
    rw [hcardEq] at hmono
    exact hmono.trans (specialShiftedGenerator_norm_natAbs_le S
      (g : O) m hm x.1 x.2.1.isLt x.2.2.isLt hRL)
  have hKcop (x : X) (s : {s // s ∈ S}) (b : Bool) :
      IsCoprime (K x : Ideal O)
        (s.1.integralUnitIdeal b : Ideal O) := by
    let P := s.1.integralUnitIdeal b
    have hFP : F ≤ (P : Ideal O) := by
      exact specialSieveModulus_span_le_oriented S s b
    have hw : specialSieveElement S x.1 0 0 ∉ (P : Ideal O) :=
      specialSieveElement_not_mem_oriented S x.1 0 0 s b
    have hu : z x - specialSieveElement S x.1 0 0 * (g : O) ∈
        F * (J : Ideal O) := by
      exact specialShiftedGenerator_sub_base_mem
        (a := x.2.1) (b := x.2.2) S J g hm_mem x.1
    have hnot : z x ∉ (J : Ideal O) * (P : Ideal O) := by
      have hlift := generator_lift_not_mem_mul J P F g hgen hFP hw hu
      simpa [z, R] using hlift
    exact isCoprime_of_mul_eq_span_not_mem J (K x) P
      (specialOrientedIntegralUnitIdeal_isMaximal p s.1.q s.1.prime
        s.1.ne_two s.1.ne_p s.1.split b) (hspan x) hnot
  let f : X → SpecialSieveClassBall p
      (9 * (1 + p ^ 3) * (specialSieveModulus S * m) ^ 2 * L ^ 2)
      C S := fun x ↦ ⟨⟨K x, hKclass x, hKcard x⟩, hKcop x⟩
  let : Finite (SpecialClassBall p
      (9 * (1 + p ^ 3) * (specialSieveModulus S * m) ^ 2 * L ^ 2) C) :=
    finiteSpecialClassBall C
  let : Finite (SpecialSieveClassBall p
      (9 * (1 + p ^ 3) * (specialSieveModulus S * m) ^ 2 * L ^ 2) C S) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hf : Function.Injective f := by
    intro x y hxy
    have hK : K x = K y := congrArg
      (fun I : SpecialSieveClassBall p
        (9 * (1 + p ^ 3) * (specialSieveModulus S * m) ^ 2 * L ^ 2)
        C S ↦ I.1.1) hxy
    have hQ : Q x = Q y := by
      calc
        Q x = J * K x := (hJK x).symm
        _ = J * K y := by rw [hK]
        _ = Q y := hJK y
    have hspanEq : Ideal.span ({z x} : Set O) =
        Ideal.span ({z y} : Set O) :=
      congrArg (fun I : IntegralUnitIdeal O ↦ (I : Ideal O)) hQ
    have hassoc : Associated (z x) (z y) :=
      Ideal.span_singleton_eq_span_singleton.mp hspanEq
    have hzeq : z x = z y :=
      specialShiftedGenerator_eq_of_associated hm S (g : O) x.1 y.1 hassoc
    have hux := specialShiftedGenerator_sub_base_mem
      (a := x.2.1) (b := x.2.2) S J g hm_mem x.1
    have huy := specialShiftedGenerator_sub_base_mem
      (a := y.2.1) (b := y.2.2) S J g hm_mem y.1
    have hdiff : (specialSieveElement S x.1 0 0 -
        specialSieveElement S y.1 0 0) * (g : O) ∈ F * (J : Ideal O) := by
      have hsub := sub_mem hux huy
      have hneg := neg_mem hsub
      have hzeq' :
          specialShiftedGenerator S (g : O) m
              (specialGeneratorRadius S g) x.1 x.2.1 x.2.2 =
            specialShiftedGenerator S (g : O) m
              (specialGeneratorRadius S g) y.1 y.2.1 y.2.2 := by
        simpa [z, R] using hzeq
      convert hneg using 1
      rw [hzeq']
      ring
    have hbaseF : specialSieveElement S x.1 0 0 -
        specialSieveElement S y.1 0 0 ∈ F :=
      generator_mem_of_mul_mem J F g hgen hdiff
    have hres : x.1 = y.1 :=
      splitAllowedResiduePair_eq_of_base_sub_mem S x.1 y.1 hbaseF
    have hre := congrArg Zsqrtd.re hzeq
    have him := congrArg Zsqrtd.im hzeq
    apply Prod.ext hres
    simp only [z, R, specialShiftedGenerator, Zsqrtd.re_add] at hre
    simp only [z, R, specialShiftedGenerator, Zsqrtd.im_add] at him
    rw [hres] at hre him
    have hdpos : 0 < specialSieveModulus S * m :=
      mul_pos (specialSieveModulus_pos S) hm
    have haeq : x.2.1 = y.2.1 := by
      apply Fin.ext
      have hreN : specialSieveModulus S * m *
          (specialGeneratorRadius S (g : O) + 1 + x.2.1.val) =
        specialSieveModulus S * m *
          (specialGeneratorRadius S (g : O) + 1 + y.2.1.val) := by
        exact_mod_cast (add_left_cancel hre)
      have hsum := Nat.mul_left_cancel hdpos hreN
      omega
    have hbeq : x.2.2 = y.2.2 := by
      apply Fin.ext
      have himN : specialSieveModulus S * m * x.2.2.val =
          specialSieveModulus S * m * y.2.2.val := by
        exact_mod_cast (add_left_cancel him)
      exact Nat.mul_left_cancel hdpos himN
    exact Prod.ext haeq hbeq
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod, natCard_splitAllowedResiduePairs] at hcard
  simpa [X, m, pow_two, Nat.mul_assoc] using hcard

def specialConductor (p : ℕ) : ℕ := 2 * p

theorem specialSieveModulus_coprime_conductor
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p)) :
    (specialSieveModulus S).Coprime (specialConductor p) := by
  unfold specialSieveModulus specialConductor
  apply Nat.Coprime.prod_left
  intro s hs
  apply s.prime.coprime_iff_not_dvd.mpr
  intro hdiv
  rcases s.prime.dvd_mul.mp hdiv with h2 | hp
  · exact s.ne_two
      ((Nat.prime_dvd_prime_iff_eq s.prime (by norm_num)).mp h2)
  · exact s.ne_p
      ((Nat.prime_dvd_prime_iff_eq s.prime (Fact.out : Nat.Prime p)).mp hp)

noncomputable def specialConductorSieveElement
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) : Zsqrtd (-(p : ℤ) ^ 3) := by
  let c := specialConductor p
  let w := specialSieveElement S x 0 0
  let kRe : ZMod c :=
    (specialSieveModulus S : ZMod c)⁻¹ * (1 - (w.re : ZMod c))
  let kIm : ZMod c :=
    (specialSieveModulus S : ZMod c)⁻¹ * (-(w.im : ZMod c))
  exact ⟨w.re + specialSieveModulus S * kRe.val,
    w.im + specialSieveModulus S * kIm.val⟩

theorem specialConductorSieveElement_sub_mem
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) :
    specialConductorSieveElement S x - specialSieveElement S x 0 0 ∈
      Ideal.span ({Zsqrtd.ofInt (specialSieveModulus S : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) := by
  let c := specialConductor p
  let w := specialSieveElement S x 0 0
  let kRe : ZMod c :=
    (specialSieveModulus S : ZMod c)⁻¹ * (1 - (w.re : ZMod c))
  let kIm : ZMod c :=
    (specialSieveModulus S : ZMod c)⁻¹ * (-(w.im : ZMod c))
  rw [Ideal.mem_span_singleton]
  refine ⟨⟨(kRe.val : ℤ), (kIm.val : ℤ)⟩, ?_⟩
  ext <;> simp [specialConductorSieveElement, c, w, kRe, kIm] <;> ring

theorem specialConductorSieveElement_not_mem_oriented
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S)
    (s : {s // s ∈ S}) (b : Bool) :
    specialConductorSieveElement S x ∉
      (s.1.integralUnitIdeal b : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
  intro hz
  have hcorr := specialConductorSieveElement_sub_mem S x
  have hcorrP := (specialSieveModulus_span_le_oriented S s b) hcorr
  have hold : specialSieveElement S x 0 0 ∈
      (s.1.integralUnitIdeal b : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
    have := sub_mem hz hcorrP
    convert this using 1 <;> ring
  exact specialSieveElement_not_mem_oriented S x 0 0 s b hold

theorem specialConductorSieveElement_mod_conductor
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) :
    ((specialConductorSieveElement S x).re : ZMod (specialConductor p)) = 1 ∧
      ((specialConductorSieveElement S x).im : ZMod (specialConductor p)) = 0 := by
  let c := specialConductor p
  have hc : 0 < c := by
    dsimp [c, specialConductor]
    exact mul_pos (by norm_num) (Fact.out : Nat.Prime p).pos
  let : NeZero c := ⟨hc.ne'⟩
  let w := specialSieveElement S x 0 0
  have hunit : IsUnit (specialSieveModulus S : ZMod c) :=
    (ZMod.isUnit_iff_coprime _ _).mpr
      (specialSieveModulus_coprime_conductor S)
  constructor
  · simp only [specialConductorSieveElement]
    push_cast
    rw [ZMod.natCast_zmod_val, ← mul_assoc,
      ZMod.mul_inv_of_unit _ hunit, one_mul]
    ring
  · simp only [specialConductorSieveElement]
    push_cast
    rw [ZMod.natCast_zmod_val, ← mul_assoc,
      ZMod.mul_inv_of_unit _ hunit, one_mul]
    ring

theorem specialConductorSieveElement_sub_one_mem
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) :
    specialConductorSieveElement S x - 1 ∈
      Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) := by
  have hmod := specialConductorSieveElement_mod_conductor S x
  have hre0 : ((specialConductorSieveElement S x - 1).re :
      ZMod (specialConductor p)) = 0 := by
    simp only [Zsqrtd.re_sub, Zsqrtd.re_one]
    push_cast
    rw [hmod.1]
    simp
  have him0 : ((specialConductorSieveElement S x - 1).im :
      ZMod (specialConductor p)) = 0 := by
    simp only [Zsqrtd.im_sub, Zsqrtd.im_one]
    push_cast
    rw [hmod.2]
    simp
  have hreD : (specialConductor p : ℤ) ∣
      (specialConductorSieveElement S x - 1).re :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hre0
  have himD : (specialConductor p : ℤ) ∣
      (specialConductorSieveElement S x - 1).im :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp him0
  rw [Ideal.mem_span_singleton]
  exact (Zsqrtd.intCast_dvd (specialConductor p : ℤ)
    (specialConductorSieveElement S x - 1)).mpr ⟨hreD, himD⟩

theorem specialConductorSieveElement_span_isCoprime
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (x : splitAllowedResiduePairs S) :
    IsCoprime
      (Ideal.span ({specialConductorSieveElement S x} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))))
      (Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3)))) := by
  rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.add_eq_sup,
    Ideal.eq_top_iff_one]
  have hz : specialConductorSieveElement S x ∈
      Ideal.span ({specialConductorSieveElement S x} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) :=
    Ideal.mem_span_singleton_self _
  have hcorr := specialConductorSieveElement_sub_one_mem S x
  have hneg := neg_mem hcorr
  have hz' := (show Ideal.span ({specialConductorSieveElement S x} :
      Set (Zsqrtd (-(p : ℤ) ^ 3))) ≤
        Ideal.span ({specialConductorSieveElement S x} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) +
        Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) from le_sup_left) hz
  have hneg' := (show Ideal.span ({Zsqrtd.ofInt
      (specialConductor p : ℤ)} : Set (Zsqrtd (-(p : ℤ) ^ 3))) ≤
        Ideal.span ({specialConductorSieveElement S x} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) +
        Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) from le_sup_right) hneg
  have := add_mem hz' hneg'
  convert this using 1 <;> ring

def specialFullSieveModulus
    {p : ℕ} (S : Finset (SpecialSplitPrimeData p)) : ℕ :=
  specialConductor p * specialSieveModulus S

theorem specialFullSieveModulus_pos
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p)) :
    0 < specialFullSieveModulus S := by
  exact mul_pos (mul_pos (by norm_num) (Fact.out : Nat.Prime p).pos)
    (specialSieveModulus_pos S)

noncomputable def specialConductorGeneratorRadius
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) : ℕ := by
  letI : NeZero (∏ s ∈ S, s.q) :=
    ⟨by simpa [specialSieveModulus] using
      (specialSieveModulus_pos S).ne'⟩
  letI : Fintype (splitAllowedResiduePairs S) := by
    unfold splitAllowedResiduePairs
    infer_instance
  exact Finset.univ.sup fun x : splitAllowedResiduePairs S ↦
    max (specialConductorSieveElement S x * g).re.natAbs
      (specialConductorSieveElement S x * g).im.natAbs

theorem specialConductorGeneratorRadius_re
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) (x : splitAllowedResiduePairs S) :
    (specialConductorSieveElement S x * g).re.natAbs ≤
      specialConductorGeneratorRadius S g := by
  let : NeZero (∏ s ∈ S, s.q) :=
    ⟨by simpa [specialSieveModulus] using
      (specialSieveModulus_pos S).ne'⟩
  let : Fintype (splitAllowedResiduePairs S) := by
    unfold splitAllowedResiduePairs
    infer_instance
  exact le_trans (le_max_left _ _)
    (Finset.le_sup (f := fun y : splitAllowedResiduePairs S ↦
      max (specialConductorSieveElement S y * g).re.natAbs
        (specialConductorSieveElement S y * g).im.natAbs)
      (Finset.mem_univ x))

theorem specialConductorGeneratorRadius_im
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) (x : splitAllowedResiduePairs S) :
    (specialConductorSieveElement S x * g).im.natAbs ≤
      specialConductorGeneratorRadius S g := by
  let : NeZero (∏ s ∈ S, s.q) :=
    ⟨by simpa [specialSieveModulus] using
      (specialSieveModulus_pos S).ne'⟩
  let : Fintype (splitAllowedResiduePairs S) := by
    unfold splitAllowedResiduePairs
    infer_instance
  exact le_trans (le_max_right _ _)
    (Finset.le_sup (f := fun y : splitAllowedResiduePairs S ↦
      max (specialConductorSieveElement S y * g).re.natAbs
        (specialConductorSieveElement S y * g).im.natAbs)
      (Finset.mem_univ x))

def specialConductorShiftedGenerator
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) (m R : ℕ)
    (x : splitAllowedResiduePairs S) (a b : ℕ) :
    Zsqrtd (-(p : ℤ) ^ 3) :=
  specialConductorSieveElement S x * g +
    ⟨specialFullSieveModulus S * m * (R + 1 + a),
      specialFullSieveModulus S * m * b⟩

theorem specialConductorShiftedGenerator_re_pos
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) (m : ℕ) (hm : 0 < m)
    (x : splitAllowedResiduePairs S) (a b : ℕ) :
    0 < (specialConductorShiftedGenerator S g m
      (specialConductorGeneratorRadius S g) x a b).re := by
  have hM := specialFullSieveModulus_pos S
  have hbase := specialConductorGeneratorRadius_re S g x
  have hneg : -((specialConductorGeneratorRadius S g : ℕ) : ℤ) ≤
      (specialConductorSieveElement S x * g).re := by
    have hraw : -((specialConductorSieveElement S x * g).re.natAbs : ℤ) ≤
        (specialConductorSieveElement S x * g).re := by
      by_cases hpos : 0 ≤ (specialConductorSieveElement S x * g).re
      · exact (neg_nonpos.mpr (by positivity)).trans hpos
      · have hnon : (specialConductorSieveElement S x * g).re ≤ 0 :=
          le_of_not_ge hpos
        rw [Int.ofNat_natAbs_of_nonpos hnon]
        simp
    exact (neg_le_neg (by exact_mod_cast hbase)).trans hraw
  simp only [specialConductorShiftedGenerator, Zsqrtd.re_add]
  change 0 < (specialConductorSieveElement S x * g).re +
    ((specialFullSieveModulus S * m *
      (specialConductorGeneratorRadius S g + 1 + a) : ℕ) : ℤ)
  have hshift : (specialConductorGeneratorRadius S g : ℤ) <
      ((specialFullSieveModulus S * m *
        (specialConductorGeneratorRadius S g + 1 + a) : ℕ) : ℤ) := by
    exact_mod_cast (show specialConductorGeneratorRadius S g <
      specialFullSieveModulus S * m *
        (specialConductorGeneratorRadius S g + 1 + a) by
      exact (show specialConductorGeneratorRadius S g <
        specialConductorGeneratorRadius S g + 1 + a by omega).trans_le
          (Nat.le_mul_of_pos_left _ (mul_pos hM hm)))
  omega

theorem specialConductorShiftedGenerator_norm_natAbs_le
    {p L : ℕ} [Fact p.Prime]
    (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3)) (m : ℕ) (hm : 0 < m)
    (x : splitAllowedResiduePairs S) {a b : ℕ}
    (ha : a < L) (hb : b < L)
    (hR : specialConductorGeneratorRadius S g < L) :
    (specialConductorShiftedGenerator S g m
      (specialConductorGeneratorRadius S g) x a b).norm.natAbs ≤
      9 * (1 + p ^ 3) *
        (specialFullSieveModulus S * m) ^ 2 * L ^ 2 := by
  let d := specialFullSieveModulus S * m
  have hd : 0 < d := mul_pos (specialFullSieveModulus_pos S) hm
  let z₀ := specialConductorSieveElement S x * g
  let R := specialConductorGeneratorRadius S g
  have hre0 : z₀.re.natAbs ≤ R := specialConductorGeneratorRadius_re S g x
  have him0 : z₀.im.natAbs ≤ R := specialConductorGeneratorRadius_im S g x
  have hRL : R ≤ L := hR.le
  have hdL : L ≤ d * L := by simpa using Nat.mul_le_mul_right L hd
  have hshiftRe : d * (R + 1 + a) ≤ d * (R + L) := by
    exact Nat.mul_le_mul_left d (by omega)
  have hre : (specialConductorShiftedGenerator S g m R x a b).re.natAbs ≤
      3 * d * L := by
    have hadd := Int.natAbs_add_le z₀.re ((d * (R + 1 + a) : ℕ) : ℤ)
    have hcast : (((d * (R + 1 + a) : ℕ) : ℤ)).natAbs =
        d * (R + 1 + a) := Int.natAbs_natCast _
    simp only [specialConductorShiftedGenerator, Zsqrtd.re_add] at hadd ⊢
    change (z₀.re + ((d * (R + 1 + a) : ℕ) : ℤ)).natAbs ≤ _
    rw [hcast] at hadd
    calc
      (z₀.re + ((d * (R + 1 + a) : ℕ) : ℤ)).natAbs ≤
          z₀.re.natAbs + d * (R + 1 + a) := hadd
      _ ≤ R + d * (R + L) := Nat.add_le_add hre0 hshiftRe
      _ ≤ d * L + (d * L + d * L) := by
        apply Nat.add_le_add (hRL.trans hdL)
        rw [mul_add]
        exact Nat.add_le_add (Nat.mul_le_mul_left d hRL) le_rfl
      _ = 3 * d * L := by ring
  have him : (specialConductorShiftedGenerator S g m R x a b).im.natAbs ≤
      3 * d * L := by
    have hadd := Int.natAbs_add_le z₀.im ((d * b : ℕ) : ℤ)
    have hcast : (((d * b : ℕ) : ℤ)).natAbs = d * b :=
      Int.natAbs_natCast _
    simp only [specialConductorShiftedGenerator, Zsqrtd.im_add] at hadd ⊢
    change (z₀.im + ((d * b : ℕ) : ℤ)).natAbs ≤ _
    rw [hcast] at hadd
    calc
      (z₀.im + ((d * b : ℕ) : ℤ)).natAbs ≤
          z₀.im.natAbs + d * b := hadd
      _ ≤ R + d * L := Nat.add_le_add him0 (Nat.mul_le_mul_left d hb.le)
      _ ≤ d * L + d * L := Nat.add_le_add_right (hRL.trans hdL) _
      _ ≤ 3 * d * L := by nlinarith
  have hnorm : (specialConductorShiftedGenerator S g m R x a b).norm.natAbs =
      (specialConductorShiftedGenerator S g m R x a b).re.natAbs ^ 2 +
        p ^ 3 * (specialConductorShiftedGenerator S g m R x a b).im.natAbs ^ 2 := by
    have hnormZ : (specialConductorShiftedGenerator S g m R x a b).norm =
        (((specialConductorShiftedGenerator S g m R x a b).re.natAbs ^ 2 +
          p ^ 3 *
            (specialConductorShiftedGenerator S g m R x a b).im.natAbs ^ 2 : ℕ) :
              ℤ) := by
      rw [Zsqrtd.norm_def]
      push_cast
      simp only [Int.natCast_natAbs, sq_abs]
      ring
    rw [hnormZ, Int.natAbs_natCast]
  rw [hnorm]
  calc
    (specialConductorShiftedGenerator S g m R x a b).re.natAbs ^ 2 +
          p ^ 3 * (specialConductorShiftedGenerator S g m R x a b).im.natAbs ^ 2 ≤
        (3 * d * L) ^ 2 + p ^ 3 * (3 * d * L) ^ 2 := by gcongr
    _ = 9 * (1 + p ^ 3) *
        (specialFullSieveModulus S * m) ^ 2 * L ^ 2 := by
      dsimp only [d]
      ring

theorem specialFullSieveModulus_span_le_sieve
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p)) :
    Ideal.span ({Zsqrtd.ofInt (specialFullSieveModulus S : ℤ)} :
      Set (Zsqrtd (-(p : ℤ) ^ 3))) ≤
        Ideal.span ({Zsqrtd.ofInt (specialSieveModulus S : ℤ)} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) := by
  rw [Ideal.span_singleton_le_iff_mem]
  rw [show Zsqrtd.ofInt (specialFullSieveModulus S : ℤ) =
      Zsqrtd.ofInt (specialConductor p : ℤ) *
        Zsqrtd.ofInt (specialSieveModulus S : ℤ) by
    ext <;> simp [specialFullSieveModulus] <;> ring]
  exact (Ideal.span ({Zsqrtd.ofInt (specialSieveModulus S : ℤ)} :
    Set (Zsqrtd (-(p : ℤ) ^ 3)))).mul_mem_left _
      (Ideal.mem_span_singleton_self _)

theorem specialFullSieveModulus_span_le_conductor
    {p : ℕ} [Fact p.Prime] (S : Finset (SpecialSplitPrimeData p)) :
    Ideal.span ({Zsqrtd.ofInt (specialFullSieveModulus S : ℤ)} :
      Set (Zsqrtd (-(p : ℤ) ^ 3))) ≤
        Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) := by
  rw [Ideal.span_singleton_le_iff_mem]
  rw [show Zsqrtd.ofInt (specialFullSieveModulus S : ℤ) =
      Zsqrtd.ofInt (specialSieveModulus S : ℤ) *
        Zsqrtd.ofInt (specialConductor p : ℤ) by
    ext <;> simp [specialFullSieveModulus] <;> ring]
  exact (Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
    Set (Zsqrtd (-(p : ℤ) ^ 3)))).mul_mem_left _
      (Ideal.mem_span_singleton_self _)

theorem specialConductorShiftedGenerator_sub_base_mem
    {p m a b : ℕ} [Fact p.Prime]
    (S : Finset (SpecialSplitPrimeData p))
    (J : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (g : (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (hm_mem : (m : Zsqrtd (-(p : ℤ) ^ 3)) ∈
      (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (x : splitAllowedResiduePairs S) :
    specialConductorShiftedGenerator S (g : Zsqrtd (-(p : ℤ) ^ 3)) m
        (specialConductorGeneratorRadius S g) x a b -
        specialConductorSieveElement S x * (g : Zsqrtd (-(p : ℤ) ^ 3)) ∈
      Ideal.span ({Zsqrtd.ofInt (specialFullSieveModulus S : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) *
          (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
  let v : Zsqrtd (-(p : ℤ) ^ 3) :=
    ⟨(m * (specialConductorGeneratorRadius S g + 1 + a) : ℕ),
      (m * b : ℕ)⟩
  have hv : v ∈ (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
    have hprod := (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).mul_mem_right
      (⟨(specialConductorGeneratorRadius S g + 1 + a : ℕ), (b : ℕ)⟩ :
        Zsqrtd (-(p : ℤ) ^ 3)) hm_mem
    convert hprod using 1 <;> ext <;> simp [v] <;> ring
  have hM : Zsqrtd.ofInt (specialFullSieveModulus S : ℤ) ∈
      Ideal.span ({Zsqrtd.ofInt (specialFullSieveModulus S : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) := Ideal.mem_span_singleton_self _
  have hmul := Ideal.mul_mem_mul hM hv
  convert hmul using 1 <;> ext <;>
    simp [specialConductorShiftedGenerator, v] <;> ring

theorem specialConductorShiftedGenerator_mem
    {p m a b : ℕ} [Fact p.Prime]
    (S : Finset (SpecialSplitPrimeData p))
    (J : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (g : (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (hm_mem : (m : Zsqrtd (-(p : ℤ) ^ 3)) ∈
      (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (x : splitAllowedResiduePairs S) :
    specialConductorShiftedGenerator S (g : Zsqrtd (-(p : ℤ) ^ 3)) m
        (specialConductorGeneratorRadius S g) x a b ∈
      (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
  have hbase : specialConductorSieveElement S x *
      (g : Zsqrtd (-(p : ℤ) ^ 3)) ∈
        (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) :=
    (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).mul_mem_left _ g.2
  have hshift := specialConductorShiftedGenerator_sub_base_mem
    (a := a) (b := b) S J g hm_mem x
  have hle : Ideal.span
      ({Zsqrtd.ofInt (specialFullSieveModulus S : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) *
          (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) ≤
        (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := Ideal.mul_le_right
  have := add_mem hbase (hle hshift)
  convert this using 1 <;> ring

theorem specialConductorShiftedGenerator_eq_of_associated
    {p m a b c e : ℕ} [Fact p.Prime] (hm : 0 < m)
    (S : Finset (SpecialSplitPrimeData p))
    (g : Zsqrtd (-(p : ℤ) ^ 3))
    (x y : splitAllowedResiduePairs S)
    (h : Associated
      (specialConductorShiftedGenerator S g m
        (specialConductorGeneratorRadius S g) x a b)
      (specialConductorShiftedGenerator S g m
        (specialConductorGeneratorRadius S g) y c e)) :
    specialConductorShiftedGenerator S g m
        (specialConductorGeneratorRadius S g) x a b =
      specialConductorShiftedGenerator S g m
        (specialConductorGeneratorRadius S g) y c e := by
  obtain ⟨u, hu⟩ := h
  have hunit : IsUnit (u : Zsqrtd (-(p : ℤ) ^ 3)) := u.isUnit
  have hd : (-(p : ℤ) ^ 3 : ℤ) ≤ -2 := by
    have hp := (Fact.out : Nat.Prime p).two_le
    have hp3 : 2 ≤ p ^ 3 := hp.trans
      (Nat.le_self_pow (by norm_num : 3 ≠ 0) p)
    have hp3Z : (2 : ℤ) ≤ (p : ℤ) ^ 3 := by exact_mod_cast hp3
    omega
  rcases (zsqrtd_isUnit_iff_eq_one_or_neg_one hd
      (u : Zsqrtd (-(p : ℤ) ^ 3))).mp hunit with hu1 | huneg
  · simpa [hu1] using hu
  · have hleft := specialConductorShiftedGenerator_re_pos S g m hm x a b
    have hright := specialConductorShiftedGenerator_re_pos S g m hm y c e
    have hu' : specialConductorShiftedGenerator S g m
          (specialConductorGeneratorRadius S g) x a b *
            (-1 : Zsqrtd (-(p : ℤ) ^ 3)) =
        specialConductorShiftedGenerator S g m
          (specialConductorGeneratorRadius S g) y c e := by
      simpa [huneg] using hu
    have hre := congrArg Zsqrtd.re hu'
    have hneg : -(specialConductorShiftedGenerator S g m
        (specialConductorGeneratorRadius S g) x a b).re =
      (specialConductorShiftedGenerator S g m
        (specialConductorGeneratorRadius S g) y c e).re := by simpa using hre
    omega

theorem splitAllowedResiduePair_eq_of_conductor_base_sub_mem
    {p : ℕ} [Fact p.Prime]
    (S : Finset (SpecialSplitPrimeData p))
    (x y : splitAllowedResiduePairs S)
    (hmem : specialConductorSieveElement S x -
        specialConductorSieveElement S y ∈
      Ideal.span ({Zsqrtd.ofInt (specialFullSieveModulus S : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3)))) : x = y := by
  let P : Ideal (Zsqrtd (-(p : ℤ) ^ 3)) :=
    Ideal.span ({Zsqrtd.ofInt (specialSieveModulus S : ℤ)} :
      Set (Zsqrtd (-(p : ℤ) ^ 3)))
  have hbase : specialConductorSieveElement S x -
      specialConductorSieveElement S y ∈ P :=
    specialFullSieveModulus_span_le_sieve S hmem
  have hcx : specialConductorSieveElement S x -
      specialSieveElement S x 0 0 ∈ P :=
    specialConductorSieveElement_sub_mem S x
  have hcy : specialConductorSieveElement S y -
      specialSieveElement S y 0 0 ∈ P :=
    specialConductorSieveElement_sub_mem S y
  have hold : specialSieveElement S x 0 0 -
      specialSieveElement S y 0 0 ∈ P := by
    have := add_mem (sub_mem hbase hcx) hcy
    convert this using 1 <;> ring
  exact splitAllowedResiduePair_eq_of_base_sub_mem S x y hold

theorem integralUnitIdeal_factor_isCoprime_of_generator_mod
    {R : Type*} [CommRing R] [IsDomain R]
    (J K : IntegralUnitIdeal R) (F : Ideal R) (g z : R)
    (hgen : (J : Ideal R) ≤
      Ideal.span ({g} : Set R) + F * (J : Ideal R))
    (hzg : z - g ∈ F * (J : Ideal R))
    (hmul : (J : Ideal R) * (K : Ideal R) =
      Ideal.span ({z} : Set R)) :
    IsCoprime (K : Ideal R) F := by
  have hgmem : g ∈ Ideal.span ({z} : Set R) + F * (J : Ideal R) := by
    have hzmem : z ∈ Ideal.span ({z} : Set R) + F * (J : Ideal R) := by
      rw [Ideal.add_eq_sup]
      exact (show Ideal.span ({z} : Set R) ≤
        Ideal.span ({z} : Set R) ⊔ F * (J : Ideal R) from le_sup_left)
          (Ideal.mem_span_singleton_self z)
    have hneg : -(z - g) ∈
        Ideal.span ({z} : Set R) + F * (J : Ideal R) := by
      apply neg_mem
      rw [Ideal.add_eq_sup]
      exact (show F * (J : Ideal R) ≤
        Ideal.span ({z} : Set R) ⊔ F * (J : Ideal R) from le_sup_right) hzg
    have := add_mem hzmem hneg
    convert this using 1 <;> ring
  have hgLe : Ideal.span ({g} : Set R) ≤
      Ideal.span ({z} : Set R) + F * (J : Ideal R) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgmem
  have hJLe : (J : Ideal R) ≤
      Ideal.span ({z} : Set R) + F * (J : Ideal R) :=
    hgen.trans (by
      rw [Ideal.add_eq_sup]
      exact sup_le hgLe le_sup_right)
  have hmulLe : (J : Ideal R) * (⊤ : Ideal R) ≤
      (J : Ideal R) * ((K : Ideal R) + F) := by
    rw [Ideal.mul_top, mul_add, hmul]
    simpa [mul_comm] using hJLe
  have htopLe : (⊤ : Ideal R) ≤ (K : Ideal R) + F :=
    ideal_le_of_mul_le_mul_left_integralUnitIdeal J hmulLe
  rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.add_eq_sup]
  exact top_unique htopLe

theorem sub_generator_mem_of_congruent_one
    {R : Type*} [CommRing R]
    (Ft Fc J : Ideal R) (z w g : R)
    (hFtFc : Ft ≤ Fc) (hg : g ∈ J)
    (hshift : z - w * g ∈ Ft * J)
    (hwone : w - 1 ∈ Fc) : z - g ∈ Fc * J := by
  have hshiftFc : z - w * g ∈ Fc * J :=
    (Ideal.mul_mono hFtFc le_rfl) hshift
  have hwg : (w - 1) * g ∈ Fc * J := Ideal.mul_mem_mul hwone hg
  have := add_mem hshiftFc hwg
  convert this using 1 <;> ring

theorem specialConductorShiftedGenerator_sub_generator_mem
    {p m a b : ℕ} [Fact p.Prime]
    (S : Finset (SpecialSplitPrimeData p))
    (J : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (g : (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (hm_mem : (m : Zsqrtd (-(p : ℤ) ^ 3)) ∈
      (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (x : splitAllowedResiduePairs S) :
    specialConductorShiftedGenerator S g m
        (specialConductorGeneratorRadius S g) x a b - g ∈
      Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) *
        (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
  apply sub_generator_mem_of_congruent_one
    (Ideal.span ({Zsqrtd.ofInt (specialFullSieveModulus S : ℤ)} :
      Set (Zsqrtd (-(p : ℤ) ^ 3))))
    (Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
      Set (Zsqrtd (-(p : ℤ) ^ 3))))
    (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) _
    (specialConductorSieveElement S x) g
  · exact specialFullSieveModulus_span_le_conductor S
  · exact g.2
  · exact specialConductorShiftedGenerator_sub_base_mem
      (a := a) (b := b) S J g hm_mem x
  · exact specialConductorSieveElement_sub_one_mem S x

theorem specialConductor_factor_isCoprime
    {p m a b : ℕ} [Fact p.Prime]
    (S : Finset (SpecialSplitPrimeData p))
    (J K : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (g : (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (hm_mem : (m : Zsqrtd (-(p : ℤ) ^ 3)) ∈
      (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (hgen : (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) ≤
      Ideal.span ({(g : Zsqrtd (-(p : ℤ) ^ 3))} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) +
      Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) *
        (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))))
    (x : splitAllowedResiduePairs S)
    (hmul : (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) *
        (K : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) =
      Ideal.span ({specialConductorShiftedGenerator S g m
        (specialConductorGeneratorRadius S g) x a b} :
          Set (Zsqrtd (-(p : ℤ) ^ 3)))) :
    IsCoprime (K : Ideal (Zsqrtd (-(p : ℤ) ^ 3)))
      (Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3)))) := by
  apply integralUnitIdeal_factor_isCoprime_of_generator_mod J K _ g _ hgen
  · exact specialConductorShiftedGenerator_sub_generator_mem
      (a := a) (b := b) S J g hm_mem x
  · exact hmul

def SpecialFullSieveClassBall
    (p N : ℕ) [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))
    (S : Finset (SpecialSplitPrimeData p)) :=
  {I : SpecialSieveClassBall p N C S //
    IsCoprime (I.1.1 : Ideal (Zsqrtd (-(p : ℤ) ^ 3)))
      (Ideal.span ({Zsqrtd.ofInt (specialConductor p : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))))}

/-- The sharp finite CRT lower bound, with the ideals also coprime to the
conductor.  This is the finite counting input for the ring-class tail
argument. -/
theorem exists_specialFullSieveClassBall_lower_uniform
    {p : ℕ} [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))
    (S : Finset (SpecialSplitPrimeData p))
    (J : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (hJclass : IntegralUnitIdeal.idealClass J = C⁻¹) :
    ∃ R : ℕ, ∀ L : ℕ, R < L →
      (∏ s ∈ S, (s.q - 1) ^ 2) * L ^ 2 ≤
        Nat.card (SpecialFullSieveClassBall p
          (9 * (1 + p ^ 3) *
            (specialFullSieveModulus S *
              (J : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).cardQuot) ^ 2 * L ^ 2)
          C S) := by
  classical
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  let : Module.Free ℤ O :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ O :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Ring.HasFiniteQuotients O := inferInstance
  let m := (J : Ideal O).cardQuot
  have hJne : (J : Ideal O) ≠ ⊥ := by
    intro hbot
    have hz : (((J : Ideal O) :
        FractionalIdeal O⁰ (FractionRing O))) = 0 := by rw [hbot]; rfl
    exact J.2.ne_zero hz
  have hm : 0 < m := Ring.HasFiniteQuotients.cardQuot_pos _ hJne
  have hm_mem : (m : O) ∈ (J : Ideal O) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero (J : Ideal O)
  let F : Ideal O := Ideal.span
    ({Zsqrtd.ofInt (specialFullSieveModulus S : ℤ)} : Set O)
  let Fc : Ideal O := Ideal.span
    ({Zsqrtd.ofInt (specialConductor p : ℤ)} : Set O)
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hmem : Zsqrtd.ofInt (specialFullSieveModulus S : ℤ) ∈
        (⊥ : Ideal O) := by
      rw [← hbot]
      exact Ideal.mem_span_singleton_self _
    have hre := congrArg Zsqrtd.re (show
      Zsqrtd.ofInt (specialFullSieveModulus S : ℤ) = (0 : O) by
        simpa using hmem)
    have hreZ : (specialFullSieveModulus S : ℤ) = 0 := by
      simpa only [Zsqrtd.re_ofInt, Zsqrtd.re_zero] using hre
    have : specialFullSieveModulus S = 0 := by exact_mod_cast hreZ
    exact (specialFullSieveModulus_pos S).ne' this
  obtain ⟨g, hgen⟩ :=
    exists_integralUnitIdeal_generator_mod_mul J F hFne
  have hFFc : F ≤ Fc := specialFullSieveModulus_span_le_conductor S
  have hgenFc : (J : Ideal O) ≤
      Ideal.span ({(g : O)} : Set O) + Fc * (J : Ideal O) :=
    hgen.trans (add_le_add le_rfl (Ideal.mul_mono hFFc le_rfl))
  let R := specialConductorGeneratorRadius S (g : O)
  refine ⟨R, ?_⟩
  intro L hRL
  let X := splitAllowedResiduePairs S × (Fin L × Fin L)
  let z : X → O := fun x ↦
    specialConductorShiftedGenerator S (g : O) m R x.1 x.2.1 x.2.2
  have hzpos (x : X) : 0 < (z x).re := by
    simpa [z, R] using (specialConductorShiftedGenerator_re_pos
      S (g : O) m hm x.1 x.2.1 x.2.2)
  have hz0 (x : X) : z x ≠ 0 := by
    intro hzero
    have hre := congrArg Zsqrtd.re hzero
    simp only [Zsqrtd.re_zero] at hre
    have hp := hzpos x
    omega
  have hzmem (x : X) : z x ∈ (J : Ideal O) := by
    exact specialConductorShiftedGenerator_mem S J g hm_mem x.1
  let Q : X → IntegralUnitIdeal O := fun x ↦
    principalIntegralUnitIdeal (Ideal.span ({z x} : Set O))
      inferInstance (by
        intro hbot
        have hmem : z x ∈ (⊥ : Ideal O) := by
          rw [← hbot]
          exact Ideal.mem_span_singleton_self _
        exact hz0 x (by simpa using hmem))
  have hQle (x : X) : (Q x : Ideal O) ≤ (J : Ideal O) :=
    (Ideal.span_singleton_le_iff_mem _).mpr (hzmem x)
  let factor (x : X) :=
    IntegralUnitIdeal.exists_mul_eq_of_le J (Q x) (hQle x)
  let K : X → IntegralUnitIdeal O := fun x ↦ (factor x).choose
  have hJK (x : X) : J * K x = Q x := (factor x).choose_spec
  have hspan (x : X) : (J : Ideal O) * (K x : Ideal O) =
      Ideal.span ({z x} : Set O) :=
    congrArg (fun I : IntegralUnitIdeal O ↦ (I : Ideal O)) (hJK x)
  have hQclass (x : X) : IntegralUnitIdeal.idealClass (Q x) = 1 := by
    apply principalIntegralUnitIdeal_idealClass
  have hKclass (x : X) : IntegralUnitIdeal.idealClass (K x) = C := by
    have hclasses := congrArg IntegralUnitIdeal.idealClass (hJK x)
    rw [IntegralUnitIdeal.idealClass_mul, hQclass] at hclasses
    calc
      IntegralUnitIdeal.idealClass (K x) =
          C * (C⁻¹ * IntegralUnitIdeal.idealClass (K x)) := by simp
      _ = C * (IntegralUnitIdeal.idealClass J *
          IntegralUnitIdeal.idealClass (K x)) := by rw [hJclass]
      _ = C := by rw [hclasses, mul_one]
  have hKcard (x : X) : (K x : Ideal O).cardQuot ≤
      9 * (1 + p ^ 3) *
        (specialFullSieveModulus S * m) ^ 2 * L ^ 2 := by
    have hspanLe : Ideal.span ({z x} : Set O) ≤ (K x : Ideal O) := by
      rw [← hspan x]
      exact Ideal.mul_le_right
    have hspanNe : Ideal.span ({z x} : Set O) ≠ ⊥ := by
      intro hbot
      have hmem : z x ∈ (⊥ : Ideal O) := by
        rw [← hbot]
        exact Ideal.mem_span_singleton_self _
      exact hz0 x (by simpa using hmem)
    have hmono := cardQuot_mono_of_le hspanNe hspanLe
    have htopNe : (⊤ : Ideal O) ≠ ⊥ := by simp
    have hspanCard := cardQuot_span_singleton_mul_of_ne_bot
      (zsqrtdBasis (-(p : ℤ) ^ 3)) (⊤ : Ideal O) htopNe (hz0 x)
    have hcardEq : (Ideal.span ({z x} : Set O)).cardQuot =
        (z x).norm.natAbs := by
      simpa [Ideal.mul_top, algebraNorm_zsqrtd] using hspanCard
    rw [hcardEq] at hmono
    exact hmono.trans (specialConductorShiftedGenerator_norm_natAbs_le
      S (g : O) m hm x.1 x.2.1.isLt x.2.2.isLt hRL)
  have hKcop (x : X) (s : {s // s ∈ S}) (b : Bool) :
      IsCoprime (K x : Ideal O)
        (s.1.integralUnitIdeal b : Ideal O) := by
    let P := s.1.integralUnitIdeal b
    have hFP : F ≤ (P : Ideal O) :=
      (specialFullSieveModulus_span_le_sieve S).trans
        (specialSieveModulus_span_le_oriented S s b)
    have hw : specialConductorSieveElement S x.1 ∉ (P : Ideal O) :=
      specialConductorSieveElement_not_mem_oriented S x.1 s b
    have hu : z x - specialConductorSieveElement S x.1 * (g : O) ∈
        F * (J : Ideal O) := by
      exact specialConductorShiftedGenerator_sub_base_mem
        (a := x.2.1) (b := x.2.2) S J g hm_mem x.1
    have hnot : z x ∉ (J : Ideal O) * (P : Ideal O) := by
      have hlift := generator_lift_not_mem_mul J P F g hgen hFP hw hu
      simpa [z, R] using hlift
    exact isCoprime_of_mul_eq_span_not_mem J (K x) P
      (specialOrientedIntegralUnitIdeal_isMaximal p s.1.q s.1.prime
        s.1.ne_two s.1.ne_p s.1.split b) (hspan x) hnot
  have hKcond (x : X) : IsCoprime (K x : Ideal O) Fc := by
    exact specialConductor_factor_isCoprime
      (a := x.2.1) (b := x.2.2) S J (K x) g hm_mem hgenFc x.1 (hspan x)
  let f : X → SpecialFullSieveClassBall p
      (9 * (1 + p ^ 3) *
        (specialFullSieveModulus S * m) ^ 2 * L ^ 2) C S := fun x ↦
    ⟨⟨⟨K x, hKclass x, hKcard x⟩, hKcop x⟩, hKcond x⟩
  let : Finite (SpecialClassBall p
      (9 * (1 + p ^ 3) *
        (specialFullSieveModulus S * m) ^ 2 * L ^ 2) C) :=
    finiteSpecialClassBall C
  let : Finite (SpecialSieveClassBall p
      (9 * (1 + p ^ 3) *
        (specialFullSieveModulus S * m) ^ 2 * L ^ 2) C S) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let : Finite (SpecialFullSieveClassBall p
      (9 * (1 + p ^ 3) *
        (specialFullSieveModulus S * m) ^ 2 * L ^ 2) C S) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hf : Function.Injective f := by
    intro x y hxy
    have hK : K x = K y := congrArg
      (fun I : SpecialFullSieveClassBall p
        (9 * (1 + p ^ 3) *
          (specialFullSieveModulus S * m) ^ 2 * L ^ 2) C S ↦ I.1.1.1) hxy
    have hQ : Q x = Q y := by
      calc
        Q x = J * K x := (hJK x).symm
        _ = J * K y := by rw [hK]
        _ = Q y := hJK y
    have hspanEq : Ideal.span ({z x} : Set O) =
        Ideal.span ({z y} : Set O) :=
      congrArg (fun I : IntegralUnitIdeal O ↦ (I : Ideal O)) hQ
    have hassoc : Associated (z x) (z y) :=
      Ideal.span_singleton_eq_span_singleton.mp hspanEq
    have hzeq : z x = z y :=
      specialConductorShiftedGenerator_eq_of_associated
        hm S (g : O) x.1 y.1 hassoc
    have hux := specialConductorShiftedGenerator_sub_base_mem
      (a := x.2.1) (b := x.2.2) S J g hm_mem x.1
    have huy := specialConductorShiftedGenerator_sub_base_mem
      (a := y.2.1) (b := y.2.2) S J g hm_mem y.1
    have hdiff : (specialConductorSieveElement S x.1 -
        specialConductorSieveElement S y.1) * (g : O) ∈ F * (J : Ideal O) := by
      have hsub := sub_mem hux huy
      have hneg := neg_mem hsub
      have hzeq' :
          specialConductorShiftedGenerator S (g : O) m
              (specialConductorGeneratorRadius S g) x.1 x.2.1 x.2.2 =
            specialConductorShiftedGenerator S (g : O) m
              (specialConductorGeneratorRadius S g) y.1 y.2.1 y.2.2 := by
        simpa [z, R] using hzeq
      convert hneg using 1
      rw [hzeq']
      ring
    have hbaseF : specialConductorSieveElement S x.1 -
        specialConductorSieveElement S y.1 ∈ F :=
      generator_mem_of_mul_mem J F g hgen hdiff
    have hres : x.1 = y.1 :=
      splitAllowedResiduePair_eq_of_conductor_base_sub_mem S x.1 y.1 hbaseF
    have hre := congrArg Zsqrtd.re hzeq
    have him := congrArg Zsqrtd.im hzeq
    apply Prod.ext hres
    simp only [z, R, specialConductorShiftedGenerator, Zsqrtd.re_add] at hre
    simp only [z, R, specialConductorShiftedGenerator, Zsqrtd.im_add] at him
    rw [hres] at hre him
    have hdpos : 0 < specialFullSieveModulus S * m :=
      mul_pos (specialFullSieveModulus_pos S) hm
    have haeq : x.2.1 = y.2.1 := by
      apply Fin.ext
      have hreN : specialFullSieveModulus S * m *
          (specialConductorGeneratorRadius S (g : O) + 1 + x.2.1.val) =
        specialFullSieveModulus S * m *
          (specialConductorGeneratorRadius S (g : O) + 1 + y.2.1.val) := by
        exact_mod_cast (add_left_cancel hre)
      have hsum := Nat.mul_left_cancel hdpos hreN
      omega
    have hbeq : x.2.2 = y.2.2 := by
      apply Fin.ext
      have himN : specialFullSieveModulus S * m * x.2.2.val =
          specialFullSieveModulus S * m * y.2.2.val := by
        exact_mod_cast (add_left_cancel him)
      exact Nat.mul_left_cancel hdpos himN
    exact Prod.ext haeq hbeq
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod, natCard_splitAllowedResiduePairs] at hcard
  simpa [X, m, pow_two, Nat.mul_assoc] using hcard

/-- A finite covering by explicit split-prime divisors bounds the
conductor-coprime sieve ball by divisible-class balls. -/
theorem natCard_specialFullSieveClassBall_le_sum_divisible
    {p N : ℕ} [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))
    (S T : Finset (SpecialSplitPrimeData p))
    (hcover : ∀ I : SpecialFullSieveClassBall p N C S,
      ∃ s : SpecialSplitPrimeData p, ∃ hs : s ∈ T, ∃ b : Bool,
        ∃ J : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)),
          s.integralUnitIdeal b * J = I.1.1.1) :
    Nat.card (SpecialFullSieveClassBall p N C S) ≤
      ∑ s ∈ T, ∑ b : Bool,
        Nat.card (SpecialDivisibleClassBall p N C
          (s.integralUnitIdeal b)) := by
  classical
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  choose s hs b J hfactor using hcover
  let Target := Σ t : {s : SpecialSplitPrimeData p // s ∈ T},
    Σ c : Bool, SpecialDivisibleClassBall p N C
      (t.1.integralUnitIdeal c)
  let f : SpecialFullSieveClassBall p N C S → Target := fun I ↦
    ⟨⟨s I, hs I⟩, b I, ⟨I.1.1, J I, hfactor I⟩⟩
  have hf : Function.Injective f := by
    intro I K hIK
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun V : Target ↦ V.2.2.1) hIK
  let : Finite (SpecialClassBall p N C) := finiteSpecialClassBall C
  let (t : {s : SpecialSplitPrimeData p // s ∈ T}) (c : Bool) :
      Finite (SpecialDivisibleClassBall p N C
        (t.1.integralUnitIdeal c)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hcard := Nat.card_le_card_of_injective f hf
  calc
    Nat.card (SpecialFullSieveClassBall p N C S) ≤ Nat.card Target := hcard
    _ = ∑ t : {s : SpecialSplitPrimeData p // s ∈ T},
        ∑ c : Bool, Nat.card (SpecialDivisibleClassBall p N C
          (t.1.integralUnitIdeal c)) := by
      dsimp only [Target]
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Nat.card_sigma]
    _ = ∑ s ∈ T, ∑ c : Bool,
        Nat.card (SpecialDivisibleClassBall p N C
          (s.integralUnitIdeal c)) := by
      simpa only [Finset.attach_eq_univ] using
        T.sum_attach (fun s ↦ ∑ c : Bool,
          Nat.card (SpecialDivisibleClassBall p N C
            (s.integralUnitIdeal c)))

noncomputable def specialBadSplitPrimeWeight
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))
    (s : SpecialSplitPrimeData p) : ℝ := by
  classical
  exact if s.idealClass ∉ H then (s.q : ℝ)⁻¹ else 0

theorem specialBadSplitPrimeWeight_nonneg
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))
    (s : SpecialSplitPrimeData p) :
    0 ≤ specialBadSplitPrimeWeight H s := by
  unfold specialBadSplitPrimeWeight
  split_ifs <;> positivity

theorem specialBadSplitPrimeWeight_eq_inv
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))
    (s : SpecialSplitPrimeData p) (hs : s.idealClass ∉ H) :
    specialBadSplitPrimeWeight H s = (s.q : ℝ)⁻¹ := by
  simp [specialBadSplitPrimeWeight, hs]

theorem specialSplitPrime_inv_le_half
    {p : ℕ} [Fact p.Prime] (s : SpecialSplitPrimeData p) :
    (s.q : ℝ)⁻¹ ≤ 1 / 2 := by
  have hq : 2 ≤ s.q := s.prime.two_le
  have hqR : (2 : ℝ) ≤ s.q := by exact_mod_cast hq
  simpa [one_div] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hqR)

theorem neg_two_mul_le_log_one_sub_special
    {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  have hden : 0 < 1 - x := by linarith
  have hbase := Real.one_sub_inv_le_log_of_pos hden
  have heq : 1 - (1 - x)⁻¹ = -x / (1 - x) := by
    field_simp [hden.ne']
    ring
  rw [heq] at hbase
  have hfrac : x / (1 - x) ≤ 2 * x :=
    (div_le_iff₀ hden).2 (by nlinarith)
  calc
    -2 * x = -(2 * x) := by ring
    _ ≤ -(x / (1 - x)) := neg_le_neg hfrac
    _ = -x / (1 - x) := by ring
    _ ≤ Real.log (1 - x) := hbase

theorem exp_neg_two_sum_le_prod_one_sub_special
    {I : Type*} (S : Finset I) (a : I → ℝ)
    (ha0 : ∀ i ∈ S, 0 ≤ a i)
    (hahalf : ∀ i ∈ S, a i ≤ 1 / 2) :
    Real.exp (-2 * ∑ i ∈ S, a i) ≤
      ∏ i ∈ S, (1 - a i) := by
  have hpos : ∀ i ∈ S, 0 < 1 - a i := by
    intro i hi
    linarith [hahalf i hi]
  have hlog : -2 * ∑ i ∈ S, a i ≤
      ∑ i ∈ S, Real.log (1 - a i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦
      neg_two_mul_le_log_one_sub_special (ha0 i hi) (hahalf i hi)
  calc
    Real.exp (-2 * ∑ i ∈ S, a i) ≤
        Real.exp (∑ i ∈ S, Real.log (1 - a i)) :=
      Real.exp_le_exp.mpr hlog
    _ = Real.exp (Real.log (∏ i ∈ S, (1 - a i))) := by
      rw [Real.log_prod]
      intro i hi
      exact (hpos i hi).ne'
    _ = ∏ i ∈ S, (1 - a i) := by
      rw [Real.exp_log]
      exact Finset.prod_pos hpos

theorem exp_neg_two_tsum_specialBadSplitPrimeWeight_le_headProduct
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))
    (hsum : Summable (specialBadSplitPrimeWeight H))
    (S : Finset (SpecialSplitPrimeData p))
    (hbad : ∀ s ∈ S, s.idealClass ∉ H) :
    Real.exp (-2 * ∑' s, specialBadSplitPrimeWeight H s) ≤
      ∏ s ∈ S, (1 - (s.q : ℝ)⁻¹) := by
  have hfinite := exp_neg_two_sum_le_prod_one_sub_special S
    (fun s ↦ (s.q : ℝ)⁻¹)
    (fun s hs ↦ by positivity)
    (fun s hs ↦ specialSplitPrime_inv_le_half s)
  have hsumEq : (∑ s ∈ S, (s.q : ℝ)⁻¹) =
      ∑ s ∈ S, specialBadSplitPrimeWeight H s := by
    apply Finset.sum_congr rfl
    intro s hs
    symm
    exact specialBadSplitPrimeWeight_eq_inv H s (hbad s hs)
  have hsumLe : (∑ s ∈ S, (s.q : ℝ)⁻¹) ≤
      ∑' s, specialBadSplitPrimeWeight H s := by
    rw [hsumEq]
    exact hsum.sum_le_tsum S fun s hs ↦
      specialBadSplitPrimeWeight_nonneg H s
  exact (Real.exp_le_exp.mpr (by linarith)).trans hfinite

noncomputable def boundedSpecialSplitPrimeData
    (p N : ℕ) : Finset (SpecialSplitPrimeData p) := by
  classical
  let e : {s : SpecialSplitPrimeData p // s.q ≤ N} ↪ Fin (N + 1) :=
    ⟨fun s ↦ ⟨s.1.q, Nat.lt_succ_of_le s.2⟩, by
      intro s t h
      apply Subtype.ext
      apply SpecialSplitPrimeData.ext
      exact congrArg Fin.val h⟩
  letI : Finite {s : SpecialSplitPrimeData p // s.q ≤ N} :=
    Finite.of_injective e e.injective
  letI : Fintype {s : SpecialSplitPrimeData p // s.q ≤ N} :=
    Fintype.ofFinite _
  exact Finset.univ.image
    (fun s : {s : SpecialSplitPrimeData p // s.q ≤ N} ↦ s.1)

theorem mem_boundedSpecialSplitPrimeData_iff
    {p N : ℕ} (s : SpecialSplitPrimeData p) :
    s ∈ boundedSpecialSplitPrimeData p N ↔ s.q ≤ N := by
  classical
  unfold boundedSpecialSplitPrimeData
  let e : {t : SpecialSplitPrimeData p // t.q ≤ N} ↪ Fin (N + 1) :=
    ⟨fun t ↦ ⟨t.1.q, Nat.lt_succ_of_le t.2⟩, by
      intro t u h
      apply Subtype.ext
      apply SpecialSplitPrimeData.ext
      exact congrArg Fin.val h⟩
  let : Finite {t : SpecialSplitPrimeData p // t.q ≤ N} :=
    Finite.of_injective e e.injective
  let : Fintype {t : SpecialSplitPrimeData p // t.q ≤ N} :=
    Fintype.ofFinite _
  simp [Finset.mem_image]

theorem cast_prod_specialSplitPrime_sub_one_sq
    {p : ℕ} (S : Finset (SpecialSplitPrimeData p)) :
    ((∏ s ∈ S, (s.q - 1) ^ 2 : ℕ) : ℝ) =
      ((∏ s ∈ S, s.q : ℕ) : ℝ) ^ 2 *
        (∏ s ∈ S, (1 - (s.q : ℝ)⁻¹)) ^ 2 := by
  have hterm (s : SpecialSplitPrimeData p) :
      (((s.q - 1) ^ 2 : ℕ) : ℝ) =
        (s.q : ℝ) ^ 2 * (1 - (s.q : ℝ)⁻¹) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub s.prime.one_le, Nat.cast_one]
    have hq : (s.q : ℝ) ≠ 0 := by exact_mod_cast s.prime.ne_zero
    field_simp [hq]
  calc
    ((∏ s ∈ S, (s.q - 1) ^ 2 : ℕ) : ℝ) =
        ∏ s ∈ S, (((s.q - 1) ^ 2 : ℕ) : ℝ) := by push_cast; rfl
    _ = ∏ s ∈ S,
        ((s.q : ℝ) ^ 2 * (1 - (s.q : ℝ)⁻¹) ^ 2) := by
      apply Finset.prod_congr rfl
      intro s hs
      exact hterm s
    _ = (∏ s ∈ S, (s.q : ℝ) ^ 2) *
        (∏ s ∈ S, (1 - (s.q : ℝ)⁻¹) ^ 2) := by
      rw [Finset.prod_mul_distrib]
    _ = ((∏ s ∈ S, s.q : ℕ) : ℝ) ^ 2 *
        (∏ s ∈ S, (1 - (s.q : ℝ)⁻¹)) ^ 2 := by
      rw [Finset.prod_pow, Finset.prod_pow]
      push_cast
      ring

/-- In the quadratic order of discriminant `-4p³`, split primes whose
Picard classes lie outside any proper subgroup have divergent reciprocal
sum. -/
theorem not_summable_specialBadSplitPrimeWeight
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))
    (hH : H ≠ ⊤) :
    ¬ Summable (specialBadSplitPrimeWeight H) := by
  classical
  intro hsum
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  obtain ⟨B, hBpos, hB⟩ := exists_uniform_natCard_specialClassBall_le
    (p := p)
  have hExists : ∃ C : ClassGroup O, C ∉ H := by
    by_contra hnone
    simp only [not_exists, not_not] at hnone
    apply hH
    ext C
    simp [hnone C]
  obtain ⟨C, hC⟩ := hExists
  obtain ⟨J, hJclass⟩ :=
    IntegralUnitIdeal.idealClass_surjective (S := O) (C⁻¹)
  let m := (J : Ideal O).cardQuot
  have hJne : (J : Ideal O) ≠ ⊥ := by
    intro hbot
    have hz : (((J : Ideal O) :
        FractionalIdeal O⁰ (FractionRing O))) = 0 := by rw [hbot]; rfl
    exact J.2.ne_zero hz
  let : Module.Free ℤ O :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ O :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Ring.HasFiniteQuotients O := inferInstance
  have hm : 0 < m := Ring.HasFiniteQuotients.cardQuot_pos _ hJne
  let E : ℝ := Real.exp
    (-2 * ∑' s, specialBadSplitPrimeWeight H s)
  have hEpos : 0 < E := by dsimp [E]; positivity
  let K₀ : ℝ :=
    9 * (1 + p ^ 3) * (specialConductor p * m) ^ 2
  have hK₀pos : 0 < K₀ := by
    have hc : 0 < specialConductor p := by
      exact mul_pos (by norm_num) (Fact.out : Nat.Prime p).pos
    have hpterm : 0 < 1 + p ^ 3 := by omega
    have hnat : 0 < 9 * (1 + p ^ 3) * (specialConductor p * m) ^ 2 := by
      exact mul_pos (mul_pos (by norm_num) hpterm)
        (pow_pos (mul_pos hc hm) _)
    dsimp [K₀]
    exact_mod_cast hnat
  let ε : ℝ := E ^ 2 / (8 * B * K₀)
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have htailTendsto :=
    tendsto_tsum_compl_atTop_zero (specialBadSplitPrimeWeight H)
  have htailEventually : ∀ᶠ F : Finset (SpecialSplitPrimeData p) in atTop,
      (∑' s : {s : SpecialSplitPrimeData p // s ∉ F},
        specialBadSplitPrimeWeight H s) < ε :=
    htailTendsto.eventually (Iio_mem_nhds hεpos)
  obtain ⟨F, hFtail⟩ := htailEventually.exists
  let S : Finset (SpecialSplitPrimeData p) :=
    F.filter fun s ↦ s.idealClass ∉ H
  have hSbad : ∀ s ∈ S, s.idealClass ∉ H := by
    intro s hs
    exact (Finset.mem_filter.mp hs).2
  have hhead :=
    exp_neg_two_tsum_specialBadSplitPrimeWeight_le_headProduct
      H hsum S hSbad
  obtain ⟨R, hlower⟩ :=
    exists_specialFullSieveClassBall_lower_uniform C S J hJclass
  let L := R + 1
  have hRL : R < L := by simp [L]
  have hLpos : 0 < L := by simp [L]
  let N := 9 * (1 + p ^ 3) *
    (specialFullSieveModulus S * m) ^ 2 * L ^ 2
  have hNpos : 0 < N := by
    dsimp [N]
    have hpterm : 0 < 1 + p ^ 3 := by omega
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) hpterm)
        (pow_pos (mul_pos (specialFullSieveModulus_pos S) hm) _))
      (pow_pos hLpos _)
  have hlowerNat : (∏ s ∈ S, (s.q - 1) ^ 2) * L ^ 2 ≤
      Nat.card (SpecialFullSieveClassBall p N C S) := by
    simpa [N] using hlower L hRL
  let T : Finset (SpecialSplitPrimeData p) :=
    (boundedSpecialSplitPrimeData p N).filter fun s ↦
      s.idealClass ∉ H ∧ s ∉ S
  have hTdata : ∀ s ∈ T,
      s.q ≤ N ∧ s.idealClass ∉ H ∧ s ∉ S := by
    intro s hs
    have h := Finset.mem_filter.mp hs
    exact ⟨(mem_boundedSpecialSplitPrimeData_iff s).mp h.1, h.2⟩
  have hcover : ∀ I : SpecialFullSieveClassBall p N C S,
      ∃ s : SpecialSplitPrimeData p, ∃ hs : s ∈ T, ∃ b : Bool,
        ∃ K : IntegralUnitIdeal O,
          s.integralUnitIdeal b * K = I.1.1.1 := by
    intro I
    have hIclass : IntegralUnitIdeal.idealClass I.1.1.1 ∉ H := by
      simpa [I.1.1.2.1] using hC
    obtain ⟨q, hq, hq2, hqp, hsplit, hclass, hqle, b, K, hfactor⟩ :=
      exists_specialSplitPrimeClass_not_mem_of_idealClass_not_mem
        H I.1.1.1 hIclass I.2
    let s : SpecialSplitPrimeData p := ⟨q, hq, hq2, hqp, hsplit⟩
    have hsclass : s.idealClass ∉ H := by
      simpa [s, SpecialSplitPrimeData.idealClass] using hclass
    have hqN : s.q ≤ N := hqle.trans I.1.1.2.2
    have hsnotS : s ∉ S := by
      intro hsS
      have hcop := I.1.2 ⟨s, hsS⟩ b
      have hcoe : (s.integralUnitIdeal b : Ideal O) * (K : Ideal O) =
          (I.1.1.1 : Ideal O) :=
        congrArg (fun A : IntegralUnitIdeal O ↦ (A : Ideal O)) hfactor
      have hIle : (I.1.1.1 : Ideal O) ≤
          (s.integralUnitIdeal b : Ideal O) := by
        rw [← hcoe]
        exact Ideal.mul_le_left
      have htop : (s.integralUnitIdeal b : Ideal O) = ⊤ := by
        rw [Ideal.isCoprime_iff_sup_eq] at hcop
        rw [sup_eq_right.mpr hIle] at hcop
        exact hcop
      exact (specialOrientedIntegralUnitIdeal_isMaximal p s.q s.prime
        s.ne_two s.ne_p s.split b).ne_top htop
    refine ⟨s, ?_, b, K, hfactor⟩
    apply Finset.mem_filter.mpr
    exact ⟨(mem_boundedSpecialSplitPrimeData_iff s).mpr hqN,
      hsclass, hsnotS⟩
  have hcountUpperNat :=
    natCard_specialFullSieveClassBall_le_sum_divisible C S T hcover
  have hdivUpperNat :
      (∑ s ∈ T, ∑ b : Bool,
        Nat.card (SpecialDivisibleClassBall p N C
          (s.integralUnitIdeal b))) ≤
      ∑ s ∈ T, ∑ b : Bool, B * (N / s.q) := by
    apply Finset.sum_le_sum
    intro s hs
    apply Finset.sum_le_sum
    intro b hb
    exact natCard_specialDivisibleClassBall_le C (s.integralUnitIdeal b)
      (specialOrientedIntegralUnitIdeal_isMaximal p s.q s.prime
        s.ne_two s.ne_p s.split b)
      (specialOrientedIntegralUnitIdeal_cardQuot p s.q s.prime
        s.ne_two s.ne_p s.split b) hB
  have hTnotF : ∀ s ∈ T, s ∉ F := by
    intro s hsT hsF
    exact (hTdata s hsT).2.2
      (Finset.mem_filter.mpr ⟨hsF, (hTdata s hsT).2.1⟩)
  let eT : {s : SpecialSplitPrimeData p // s ∈ T} ↪
      {s : SpecialSplitPrimeData p // s ∉ F} :=
    ⟨fun s ↦ ⟨s.1, hTnotF s.1 s.2⟩, by
      intro s t h
      apply Subtype.ext
      exact congrArg
        (fun u : {s : SpecialSplitPrimeData p // s ∉ F} ↦ u.1) h⟩
  let Ttail : Finset {s : SpecialSplitPrimeData p // s ∉ F} :=
    Finset.univ.map eT
  have hsumTail : Summable
      (fun s : {s : SpecialSplitPrimeData p // s ∉ F} ↦
        specialBadSplitPrimeWeight H s) :=
    (Finset.summable_compl_iff F).2 hsum
  have hTweightLe :
      (∑ s ∈ T, specialBadSplitPrimeWeight H s) ≤
        ∑' s : {s : SpecialSplitPrimeData p // s ∉ F},
          specialBadSplitPrimeWeight H s := by
    have htailFinite := hsumTail.sum_le_tsum Ttail (fun s hs ↦
      specialBadSplitPrimeWeight_nonneg H s)
    have hsumEq :
        (∑ s ∈ T, specialBadSplitPrimeWeight H s) =
          ∑ s ∈ Ttail, specialBadSplitPrimeWeight H s := by
      dsimp [Ttail]
      rw [Finset.sum_map]
      exact (T.sum_attach
        (fun s ↦ specialBadSplitPrimeWeight H s)).symm
    rw [hsumEq]
    exact htailFinite
  have hTreciprocalLt :
      (∑ s ∈ T, (s.q : ℝ)⁻¹) < ε := by
    calc
      (∑ s ∈ T, (s.q : ℝ)⁻¹) =
          ∑ s ∈ T, specialBadSplitPrimeWeight H s := by
        apply Finset.sum_congr rfl
        intro s hs
        symm
        exact specialBadSplitPrimeWeight_eq_inv H s (hTdata s hs).2.1
      _ ≤ ∑' s : {s : SpecialSplitPrimeData p // s ∉ F},
          specialBadSplitPrimeWeight H s := hTweightLe
      _ < ε := hFtail
  have hcountUpper :
      (Nat.card (SpecialFullSieveClassBall p N C S) : ℝ) ≤
        ∑ s ∈ T, ∑ b : Bool, ((B * (N / s.q) : ℕ) : ℝ) := by
    exact_mod_cast hcountUpperNat.trans hdivUpperNat
  have hdivCast (s : SpecialSplitPrimeData p) :
      ((B * (N / s.q) : ℕ) : ℝ) ≤
        (B : ℝ) * (N : ℝ) * (s.q : ℝ)⁻¹ := by
    rw [Nat.cast_mul]
    have hdiv : ((N / s.q : ℕ) : ℝ) ≤
        (N : ℝ) / (s.q : ℝ) := Nat.cast_div_le
    calc
      (B : ℝ) * ((N / s.q : ℕ) : ℝ) ≤
          (B : ℝ) * ((N : ℝ) / (s.q : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (B : ℝ) * (N : ℝ) * (s.q : ℝ)⁻¹ := by
        rw [div_eq_mul_inv]
        ring
  have hsumDiv :
      (∑ s ∈ T, ∑ b : Bool, ((B * (N / s.q) : ℕ) : ℝ)) ≤
        2 * (B : ℝ) * (N : ℝ) * ∑ s ∈ T, (s.q : ℝ)⁻¹ := by
    calc
      (∑ s ∈ T, ∑ b : Bool, ((B * (N / s.q) : ℕ) : ℝ)) ≤
          ∑ s ∈ T, ∑ b : Bool,
            ((B : ℝ) * (N : ℝ) * (s.q : ℝ)⁻¹) := by
        exact Finset.sum_le_sum fun s hs ↦
          Finset.sum_le_sum fun b hb ↦ hdivCast s
      _ = ∑ s ∈ T,
          (2 * (B : ℝ) * (N : ℝ)) * (s.q : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Fintype.sum_bool]
        ring
      _ = 2 * (B : ℝ) * (N : ℝ) *
          ∑ s ∈ T, (s.q : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
  have hcountLt :
      (Nat.card (SpecialFullSieveClassBall p N C S) : ℝ) <
        2 * (B : ℝ) * (N : ℝ) * ε :=
    (hcountUpper.trans hsumDiv).trans_lt
      (mul_lt_mul_of_pos_left hTreciprocalLt
        (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hBpos))
          (by exact_mod_cast hNpos)))
  let Q : ℕ := ∏ s ∈ S, s.q
  let A : ℕ := ∏ s ∈ S, (s.q - 1) ^ 2
  have hheadSq : E ^ 2 ≤
      (∏ s ∈ S, (1 - (s.q : ℝ)⁻¹)) ^ 2 := by
    have hright : 0 ≤ ∏ s ∈ S, (1 - (s.q : ℝ)⁻¹) :=
      hEpos.le.trans hhead
    nlinarith
  have hAQ : E ^ 2 * (Q : ℝ) ^ 2 ≤ (A : ℝ) := by
    have hQnonneg : 0 ≤ (Q : ℝ) ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hheadSq hQnonneg
    calc
      E ^ 2 * (Q : ℝ) ^ 2 ≤
          (∏ s ∈ S, (1 - (s.q : ℝ)⁻¹)) ^ 2 * (Q : ℝ) ^ 2 := hmul
      _ = (Q : ℝ) ^ 2 *
          (∏ s ∈ S, (1 - (s.q : ℝ)⁻¹)) ^ 2 := mul_comm _ _
      _ = (A : ℝ) := by
        simpa [A, Q] using (cast_prod_specialSplitPrime_sub_one_sq S).symm
  have hNcast : (N : ℝ) = K₀ * (Q : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
    dsimp [N, K₀, Q, specialFullSieveModulus, specialSieveModulus]
    push_cast
    ring
  have hscale : 2 * (B : ℝ) * (N : ℝ) * ε =
      E ^ 2 * (Q : ℝ) ^ 2 * (L : ℝ) ^ 2 / 4 := by
    rw [hNcast]
    dsimp [ε]
    have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
    field_simp [hBne, hK₀pos.ne']
    ring
  have hquarter :
      E ^ 2 * (Q : ℝ) ^ 2 * (L : ℝ) ^ 2 / 4 ≤
        (A : ℝ) * (L : ℝ) ^ 2 / 4 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right hAQ (sq_nonneg _)
  have hlowerReal : (A : ℝ) * (L : ℝ) ^ 2 ≤
      (Nat.card (SpecialFullSieveClassBall p N C S) : ℝ) := by
    exact_mod_cast hlowerNat
  have hApos : 0 < A := by
    dsimp [A]
    apply Finset.prod_pos
    intro s hs
    exact pow_pos (Nat.sub_pos_iff_lt.mpr s.prime.one_lt) _
  have hALpos : 0 < (A : ℝ) * (L : ℝ) ^ 2 := by
    exact mul_pos (by exact_mod_cast hApos)
      (pow_pos (by exact_mod_cast hLpos) _)
  have hfinal : (A : ℝ) * (L : ℝ) ^ 2 <
      (A : ℝ) * (L : ℝ) ^ 2 / 4 :=
    hlowerReal.trans_lt (hcountLt.trans_le (hscale.le.trans hquarter))
  nlinarith

end

end Erdos1081

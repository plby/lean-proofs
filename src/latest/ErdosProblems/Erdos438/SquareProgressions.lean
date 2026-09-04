import Mathlib

/-!
# Squares in residue-class progressions

This file contains the finite counting facts used in the Khalfalah--Lodha--
Szemerédi argument for Erdős Problem 438.  The statements deliberately keep
all endpoint errors explicit.  In particular, no equidistribution assertion is
made about the individual quadratic-residue lifts: only their total root
multiplicity is used.
-/

namespace Erdos438

open scoped BigOperators
open Finset

/-- The canonical roots of `c` modulo `q`, represented by `Fin q`. -/
def squareRootsMod (q c : ℕ) : Finset (Fin q) :=
  Finset.univ.filter fun u => u.val * u.val % q = c % q

/-- The number of roots of `c` modulo `q`. -/
def rootMultiplicity (q c : ℕ) : ℕ :=
  (squareRootsMod q c).card

@[simp]
theorem mem_squareRootsMod {q c : ℕ} {u : Fin q} :
    u ∈ squareRootsMod q c ↔ u.val * u.val % q = c % q := by
  simp [squareRootsMod]

theorem rootMultiplicity_pos {q c : ℕ} {u : Fin q}
    (hu : u.val * u.val % q = c % q) :
    0 < rootMultiplicity q c := by
  rw [rootMultiplicity, Finset.card_pos]
  exact ⟨u, by simpa using hu⟩

/-- A square in `ZMod q` has positive root multiplicity in the canonical
natural-number model. -/
theorem rootMultiplicity_pos_of_isSquare_zmod {q c : ℕ} (hq : 0 < q)
    (hc : IsSquare (c : ZMod q)) :
    0 < rootMultiplicity q c := by
  let : NeZero q := ⟨hq.ne'⟩
  obtain ⟨z, hz⟩ := hc
  let u : Fin q := ⟨z.val, ZMod.val_lt z⟩
  apply rootMultiplicity_pos (u := u)
  have hzval := congrArg ZMod.val hz
  simpa only [ZMod.val_natCast, ZMod.val_mul, u] using hzval.symm

/-- The members of a half-open interval belonging to one residue class. -/
def residueClassIco (q a H : ℕ) (u : Fin q) : Finset ℕ :=
  (Finset.Ico a (a + H * q)).filter fun z => z ≡ u.val [MOD q]

/-- Every residue occurs exactly `H` times in an interval of length `H*q`.

This is the endpoint-exact finite form of the elementary ``length divided by
the modulus'' estimate used in the paper.
-/
theorem card_residueClassIco {q a H : ℕ} (hq : 0 < q) (u : Fin q) :
    (residueClassIco q a H u).card = H := by
  have hs : residueClassIco q a H u =
      {x ∈ Finset.range (a + H * q) | x ≡ u.val [MOD q]} \
        {x ∈ Finset.range a | x ≡ u.val [MOD q]} := by
    ext x
    simp only [residueClassIco, Finset.mem_filter, Finset.mem_Ico,
      Finset.mem_sdiff, Finset.mem_range, not_and]
    constructor
    · rintro ⟨⟨hax, hxb⟩, hmod⟩
      exact ⟨⟨hxb, hmod⟩, fun hxa _ => (not_lt_of_ge hax) hxa⟩
    · rintro ⟨⟨hxb, hmod⟩, hnot⟩
      exact ⟨⟨not_lt.mp (fun hxa => hnot hxa hmod), hxb⟩, hmod⟩
  rw [hs, Finset.card_sdiff]
  have hinter :
      {x ∈ Finset.range a | x ≡ u.val [MOD q]} ∩
          {x ∈ Finset.range (a + H * q) | x ≡ u.val [MOD q]} =
        {x ∈ Finset.range a | x ≡ u.val [MOD q]} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.1
    · rintro ⟨hxa, hmod⟩
      exact ⟨⟨hxa, hmod⟩,
        ⟨hxa.trans_le (Nat.le_add_right _ _), hmod⟩⟩
  rw [hinter, ← Nat.count_eq_card_filter_range,
    ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hq,
    Nat.count_modEq_card _ hq]
  rw [Nat.add_mul_div_right _ _ hq, Nat.add_mul_mod_self_right]
  omega

/-- The roots of `c` in an interval consisting of `H` complete periods. -/
def squareRootsInIco (q c a H : ℕ) : Finset ℕ :=
  (squareRootsMod q c).biUnion (residueClassIco q a H)

theorem mem_squareRootsInIco {q c a H z : ℕ} (hq : 0 < q) :
    z ∈ squareRootsInIco q c a H ↔
      z ∈ Finset.Ico a (a + H * q) ∧ z * z % q = c % q := by
  constructor
  · intro hz
    rw [squareRootsInIco, Finset.mem_biUnion] at hz
    obtain ⟨u, hu, hzu⟩ := hz
    have hzu' := Finset.mem_filter.mp hzu
    have hmod : z % q = u.val :=
      Nat.mod_eq_of_modEq hzu'.2 u.isLt
    refine ⟨hzu'.1, ?_⟩
    rw [Nat.mul_mod, hmod, mem_squareRootsMod.mp hu]
  · rintro ⟨hzIco, hzsq⟩
    let u : Fin q := ⟨z % q, Nat.mod_lt z hq⟩
    rw [squareRootsInIco, Finset.mem_biUnion]
    refine ⟨u, ?_, ?_⟩
    · rw [mem_squareRootsMod]
      simpa [u, Nat.mul_mod] using hzsq
    · simp only [residueClassIco, Finset.mem_filter]
      refine ⟨hzIco, ?_⟩
      simp [Nat.ModEq, u]

/-- The exact root count in `H` complete periods. -/
theorem card_squareRootsInIco {q c a H : ℕ} (hq : 0 < q) :
    (squareRootsInIco q c a H).card = rootMultiplicity q c * H := by
  have hpair : (squareRootsMod q c : Set (Fin q)).PairwiseDisjoint
      (residueClassIco q a H) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro u _ v _ huv
    obtain ⟨z, hz⟩ := huv
    have hzu' := Finset.mem_filter.mp (Finset.mem_inter.mp hz).1
    have hzv' := Finset.mem_filter.mp (Finset.mem_inter.mp hz).2
    have huMod : z % q = u.val := by
      exact Nat.mod_eq_of_modEq hzu'.2 u.isLt
    have hvMod : z % q = v.val := by
      exact Nat.mod_eq_of_modEq hzv'.2 v.isLt
    exact Fin.ext (huMod.symm.trans hvMod)
  rw [squareRootsInIco, Finset.card_biUnion hpair]
  calc
    ∑ u ∈ squareRootsMod q c, (residueClassIco q a H u).card =
        ∑ _u ∈ squareRootsMod q c, H := by
          apply Finset.sum_congr rfl
          intro u _
          exact card_residueClassIco hq u
    _ = (squareRootsMod q c).card * H := Finset.sum_const_nat (fun _ _ => rfl)
    _ = rootMultiplicity q c * H := by rw [rootMultiplicity]

/-- Square the roots occurring in a complete-period interval. -/
def squareValuesInIco (q c a H : ℕ) : Finset ℕ :=
  (squareRootsInIco q c a H).image fun z => z * z

/-- Squaring is injective on natural numbers, so root multiplicity is retained. -/
theorem card_squareValuesInIco {q c a H : ℕ} (hq : 0 < q) :
    (squareValuesInIco q c a H).card = rootMultiplicity q c * H := by
  rw [squareValuesInIco,
    Finset.card_image_of_injective _ (fun _ _ h => Nat.mul_self_inj.mp h),
    card_squareRootsInIco hq]

theorem mem_squareValuesInIco {q c a H n : ℕ} (hq : 0 < q) :
    n ∈ squareValuesInIco q c a H ↔
      ∃ z ∈ Finset.Ico a (a + H * q),
        z * z % q = c % q ∧ n = z * z := by
  simp only [squareValuesInIco, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, (mem_squareRootsInIco hq).mp hz |>.1,
      (mem_squareRootsInIco hq).mp hz |>.2, rfl⟩
  · rintro ⟨z, hzIco, hzmod, rfl⟩
    exact ⟨z, (mem_squareRootsInIco hq).mpr ⟨hzIco, hzmod⟩, rfl⟩

/-- A fully finite square-count lower bound.  Any complete block of root
residues contained in the square-root interval supplies exactly
`rootMultiplicity q c * H` distinct square values. -/
theorem rootMultiplicity_mul_le_card_squaresInIco
    {q c a H L U : ℕ} (hq : 0 < q) (hL : L ≤ a * a)
    (hU : (a + H * q) * (a + H * q) ≤ U) :
    rootMultiplicity q c * H ≤
      ((Finset.Ico L U).filter fun n => IsSquare n ∧ n % q = c % q).card := by
  rw [← card_squareValuesInIco hq]
  apply Finset.card_le_card
  intro n hn
  obtain ⟨z, hzIco, hzmod, rfl⟩ := (mem_squareValuesInIco hq).mp hn
  have hzlo : a ≤ z := (Finset.mem_Ico.mp hzIco).1
  have hzhi : z < a + H * q := (Finset.mem_Ico.mp hzIco).2
  simp only [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨?_, ?_⟩, IsSquare.mul_self z, hzmod⟩
  · exact hL.trans (Nat.mul_le_mul hzlo hzlo)
  · exact (Nat.mul_self_lt_mul_self hzhi).trans_le hU

/-- Shift indices at which the translate of `x+y` is a square. -/
def shiftedSquareIndices (x y Q J : ℕ) : Finset ℕ :=
  (Finset.range (J + 1)).filter fun j => IsSquare (x + y + j * Q)

/-- Inject a complete block of square roots into square-valued shift indices.

The hypotheses are purely finite endpoint conditions.  Taking `H = 1` is the
particularly useful KLS application: one complete root period already retains
the full root multiplicity of the refined square residue.
-/
theorem rootMultiplicity_mul_le_card_shiftedSquareIndices
    {Q c x y a H J : ℕ} (hQ : 0 < Q)
    (hresidue : (x + y) % Q = c % Q) (hlower : x + y ≤ a * a)
    (hupper : (a + H * Q) * (a + H * Q) ≤ x + y + (J + 1) * Q) :
    rootMultiplicity Q c * H ≤ (shiftedSquareIndices x y Q J).card := by
  rw [← card_squareValuesInIco hQ]
  let f : ℕ → ℕ := fun n => (n - (x + y)) / Q
  have hdata : ∀ n ∈ squareValuesInIco Q c a H,
      x + y ≤ n ∧ n % Q = c % Q ∧ IsSquare n ∧
        n < x + y + (J + 1) * Q := by
    intro n hn
    obtain ⟨z, hzIco, hzmod, rfl⟩ := (mem_squareValuesInIco hQ).mp hn
    have hzlo := (Finset.mem_Ico.mp hzIco).1
    have hzhi := (Finset.mem_Ico.mp hzIco).2
    exact ⟨hlower.trans (Nat.mul_le_mul hzlo hzlo), hzmod, IsSquare.mul_self z,
      (Nat.mul_self_lt_mul_self hzhi).trans_le hupper⟩
  have heq : ∀ n ∈ squareValuesInIco Q c a H,
      x + y + Q * f n = n := by
    intro n hn
    have hn := hdata n hn
    have hmodeq : x + y ≡ n [MOD Q] := by
      rw [Nat.ModEq, hresidue, hn.2.1]
    have hdvd : Q ∣ n - (x + y) :=
      (Nat.modEq_iff_dvd' hn.1).mp hmodeq
    dsimp only [f]
    rw [Nat.mul_div_cancel' hdvd, Nat.add_sub_of_le hn.1]
  apply Finset.card_le_card_of_injOn f
  · intro n hn
    have hn' := hdata n hn
    have hnEq := heq n hn
    have hshift : f n < J + 1 := by
      have hmul : Q * f n < Q * (J + 1) := by
        have hnupper := hn'.2.2.2
        rw [← hnEq] at hnupper
        rw [Nat.mul_comm (J + 1) Q] at hnupper
        exact Nat.add_lt_add_iff_left.mp hnupper
      exact (Nat.mul_lt_mul_left hQ).mp hmul
    change f n ∈ shiftedSquareIndices x y Q J
    rw [shiftedSquareIndices, Finset.mem_filter, Finset.mem_range]
    refine ⟨hshift, ?_⟩
    rw [Nat.mul_comm, hnEq]
    exact hn'.2.2.1
  · intro n hn m hm hnm
    have hnEq := heq n hn
    have hmEq := heq m hm
    calc
      n = x + y + Q * f n := hnEq.symm
      _ = x + y + Q * f m := by rw [hnm]
      _ = m := hmEq

theorem rootMultiplicity_le_card_shiftedSquareIndices
    {Q c x y a J : ℕ} (hQ : 0 < Q)
    (hresidue : (x + y) % Q = c % Q) (hlower : x + y ≤ a * a)
    (hupper : (a + Q) * (a + Q) ≤ x + y + (J + 1) * Q) :
    rootMultiplicity Q c ≤ (shiftedSquareIndices x y Q J).card := by
  simpa using rootMultiplicity_mul_le_card_shiftedSquareIndices
    (Q := Q) (c := c) (x := x) (y := y) (a := a) (H := 1) (J := J)
    hQ hresidue hlower (by simpa using hupper)

/-- An explicit `O(√N+Q)` shift cutoff large enough to contain one complete
root period whenever `x,y ≤ N`. -/
def squareShiftCutoff (N Q : ℕ) : ℕ :=
  4 * Nat.sqrt (2 * N) + 2 * Q + 4

theorem one_root_period_endpoint_le
    {N Q x y : ℕ} (hQ : 0 < Q) (hx : x ≤ N) (hy : y ≤ N) :
    (Nat.sqrt (x + y) + 1 + Q) * (Nat.sqrt (x + y) + 1 + Q) ≤
      x + y + (squareShiftCutoff N Q + 1) * Q := by
  let a := Nat.sqrt (x + y)
  let s := Nat.sqrt (2 * N)
  have ht : x + y ≤ 2 * N := by omega
  have has : a ≤ s := Nat.sqrt_le_sqrt ht
  have ha2 : a * a ≤ x + y := Nat.sqrt_le (x + y)
  have hasQ : a * Q ≤ s * Q := Nat.mul_le_mul_right Q has
  have haQ : a ≤ a * Q := by nlinarith
  dsimp [a, s] at *
  dsimp [squareShiftCutoff]
  nlinarith

/-- One complete root period gives a direct lower bound on the number of
square-valued shifts up to the explicit cutoff. -/
theorem rootMultiplicity_le_card_shiftedSquareIndices_cutoff
    {N Q c x y : ℕ} (hQ : 0 < Q) (hx : x ≤ N) (hy : y ≤ N)
    (hresidue : (x + y) % Q = c % Q) :
    rootMultiplicity Q c ≤
      (shiftedSquareIndices x y Q (squareShiftCutoff N Q)).card := by
  apply rootMultiplicity_le_card_shiftedSquareIndices hQ hresidue
  · exact (Nat.lt_succ_sqrt (x + y)).le
  · exact one_root_period_endpoint_le hQ hx hy

/-! ## Root multiplicity after refining the modulus -/

/-- All roots modulo `q*r` whose reduction modulo `q` is a root of `c`. -/
def rootsAbove (q r c : ℕ) : Finset (Fin (q * r)) :=
  Finset.univ.filter fun x => x.val * x.val % q = c % q

@[simp]
theorem mem_rootsAbove {q r c : ℕ} {x : Fin (q * r)} :
    x ∈ rootsAbove q r c ↔ x.val * x.val % q = c % q := by
  simp [rootsAbove]

/-- The canonical equivalence `(j,u) ↦ u+qj` between a refined residue
and its coarse residue plus lift index. -/
def liftResidueEquiv (q r : ℕ) : Fin r × Fin q ≃ Fin (q * r) :=
  finProdFinEquiv.trans (Fin.castOrderIso (Nat.mul_comm r q)).toEquiv

@[simp]
theorem liftResidueEquiv_val (q r : ℕ) (x : Fin r × Fin q) :
    (liftResidueEquiv q r x).val = x.2.val + q * x.1.val := by
  rfl

/-- Every coarse root has exactly `r` lifts modulo `q*r`. -/
theorem card_rootsAbove {q r c : ℕ} :
    (rootsAbove q r c).card = r * rootMultiplicity q c := by
  classical
  have hcard : (rootsAbove q r c).card =
      ((Finset.univ : Finset (Fin r)) ×ˢ squareRootsMod q c).card := by
    symm
    apply Finset.card_bij
        (fun x _ => liftResidueEquiv q r x)
    · intro x hx
      have hx' := Finset.mem_product.mp hx
      rw [mem_rootsAbove, liftResidueEquiv_val]
      have hmod : (x.2.val + q * x.1.val) % q = x.2.val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.2.isLt]
      calc
        (x.2.val + q * x.1.val) * (x.2.val + q * x.1.val) % q =
            ((x.2.val + q * x.1.val) % q) *
              ((x.2.val + q * x.1.val) % q) % q := Nat.mul_mod _ _ _
        _ = x.2.val * x.2.val % q := by rw [hmod]
        _ = c % q := mem_squareRootsMod.mp hx'.2
    · intro x _ y _ hxy
      exact (liftResidueEquiv q r).injective hxy
    · intro y hy
      let x := (liftResidueEquiv q r).symm y
      refine ⟨x, ?_, (liftResidueEquiv q r).apply_symm_apply y⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and]
      rw [mem_squareRootsMod]
      have hy' := mem_rootsAbove.mp hy
      have hval : y.val = x.2.val + q * x.1.val := by
        have hval' : (liftResidueEquiv q r x).val = y.val :=
          congrArg Fin.val ((liftResidueEquiv q r).apply_symm_apply y)
        rw [liftResidueEquiv_val] at hval'
        exact hval'.symm
      rw [hval] at hy'
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.2.isLt,
        Nat.mul_mod] using hy'
  rw [hcard, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    rootMultiplicity]

/-- The lift index of the quadratic residue represented by `x²` modulo
`q*r`. -/
def squareLiftIndex (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (x : Fin (q * r)) : Fin r :=
  ⟨(x.val * x.val % (q * r)) / q,
    (Nat.div_lt_iff_lt_mul hq).2 <| by
      simpa [Nat.mul_comm] using Nat.mod_lt (x.val * x.val) (Nat.mul_pos hq hr)⟩

/-- Root multiplicity in one particular quadratic-residue lift. -/
def liftedRootMultiplicity (q r c : ℕ) (hq : 0 < q) (hr : 0 < r)
    (w : Fin r) : ℕ :=
  ((rootsAbove q r c).filter fun x => squareLiftIndex q r hq hr x = w).card

/-- Root multiplicity is conserved in aggregate over all refined residue
classes.  This is the corrected replacement for an unjustified uniformity
claim about quadratic residues in the informal argument. -/
theorem sum_liftedRootMultiplicity {q r c : ℕ} (hq : 0 < q) (hr : 0 < r) :
    ∑ w : Fin r, liftedRootMultiplicity q r c hq hr w =
      r * rootMultiplicity q c := by
  rw [← card_rootsAbove]
  convert (Finset.sum_fiberwise (rootsAbove q r c)
    (squareLiftIndex q r hq hr) (fun _ => (1 : ℕ))) using 1 <;>
    simp [liftedRootMultiplicity]

/-- For a canonical coarse residue `c`, the square residue of a root in fiber
`w` is exactly `c+q*w`. -/
theorem square_mod_refinedMod_eq_add_mul_liftIndex
    {q r c : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : c < q)
    {x : Fin (q * r)} (hx : x ∈ rootsAbove q r c) :
    x.val * x.val % (q * r) =
      c + q * (squareLiftIndex q r hq hr x).val := by
  have hcoarse : (x.val * x.val % (q * r)) % q = c := by
    rw [Nat.mod_mod_of_dvd (x.val * x.val) (dvd_mul_right q r),
      mem_rootsAbove.mp hx, Nat.mod_eq_of_lt hc]
  have hdivmod := Nat.div_add_mod (x.val * x.val % (q * r)) q
  dsimp only [squareLiftIndex]
  omega

/-- The fiber multiplicity is exactly the ordinary root multiplicity of the
corresponding canonical residue modulo the refined modulus. -/
theorem liftedRootMultiplicity_eq_rootMultiplicity
    {q r c : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : c < q) (w : Fin r) :
    liftedRootMultiplicity q r c hq hr w =
      rootMultiplicity (q * r) (c + q * w.val) := by
  have hres : c + q * w.val < q * r := by
    have hw := w.isLt
    nlinarith
  rw [liftedRootMultiplicity, rootMultiplicity]
  congr 1
  ext x
  simp only [Finset.mem_filter, mem_rootsAbove, mem_squareRootsMod]
  constructor
  · rintro ⟨hxroot, hxindex⟩
    rw [Nat.mod_eq_of_lt hres]
    exact square_mod_refinedMod_eq_add_mul_liftIndex hq hr hc
      (mem_rootsAbove.mpr hxroot) |>.trans (by rw [hxindex])
  · intro hx
    have hxres : x.val * x.val % (q * r) = c + q * w.val := by
      simpa [Nat.mod_eq_of_lt hres] using hx
    have hxroot : x.val * x.val % q = c % q := by
      rw [← Nat.mod_mod_of_dvd (x.val * x.val) (dvd_mul_right q r), hxres,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    refine ⟨hxroot, Fin.ext ?_⟩
    dsimp only [squareLiftIndex]
    rw [hxres, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hc, zero_add]

theorem card_refinedSquareValuesInIco
    {q r c a H : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : c < q) (w : Fin r) :
    (squareValuesInIco (q * r) (c + q * w.val) a H).card =
      liftedRootMultiplicity q r c hq hr w * H := by
  rw [card_squareValuesInIco (Nat.mul_pos hq hr),
    ← liftedRootMultiplicity_eq_rootMultiplicity hq hr hc]

/-! ## Compatible refined classes and the carry -/

/-- The unique partner of `u` in the congruence `u+v+κ=w (mod r)`. -/
def cyclicPartner {r : ℕ} (hr : 0 < r) (κ w u : Fin r) : Fin r := by
  letI : NeZero r := ⟨hr.ne'⟩
  exact w - u - κ

theorem cyclicPartner_involutive {r : ℕ} (hr : 0 < r) (κ w u : Fin r) :
    cyclicPartner hr κ w (cyclicPartner hr κ w u) = u := by
  let : NeZero r := ⟨hr.ne'⟩
  simp only [cyclicPartner]
  abel

/-- The admissible first indices `u`; their unique partners lie in `G₂`. -/
def compatibleIndices {r : ℕ} (hr : 0 < r)
    (G₁ G₂ : Finset (Fin r)) (κ w : Fin r) : Finset (Fin r) :=
  G₁.filter fun u => cyclicPartner hr κ w u ∈ G₂

/-- Preimage of a set under the cyclic partner involution. -/
def translatedPreimage {r : ℕ} (hr : 0 < r)
    (G : Finset (Fin r)) (κ w : Fin r) : Finset (Fin r) :=
  Finset.univ.filter fun u => cyclicPartner hr κ w u ∈ G

/-- Translation/reflection of a subset of `Fin r` has the same cardinality. -/
theorem card_translatedPreimage {r : ℕ} (hr : 0 < r)
    (G : Finset (Fin r)) (κ w : Fin r) :
    (translatedPreimage hr G κ w).card = G.card := by
  classical
  apply Finset.card_bij (fun u _ => cyclicPartner hr κ w u)
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u _ v _ huv
    have huv' := congrArg (cyclicPartner hr κ w) huv
    simpa only [cyclicPartner_involutive] using huv'
  · intro v hv
    refine ⟨cyclicPartner hr κ w v, ?_, ?_⟩
    · simp only [translatedPreimage, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [cyclicPartner_involutive] using hv
    · exact cyclicPartner_involutive hr κ w v

/-- Inclusion--exclusion lower bound for compatible refined-class pairs. -/
theorem card_add_card_le_add_card_compatibleIndices
    {r : ℕ} (hr : 0 < r) (G₁ G₂ : Finset (Fin r)) (κ w : Fin r) :
    G₁.card + G₂.card ≤
      r + (compatibleIndices hr G₁ G₂ κ w).card := by
  let T : Finset (Fin r) := translatedPreimage hr G₂ κ w
  have hT : T.card = G₂.card := card_translatedPreimage hr G₂ κ w
  have hcompat : compatibleIndices hr G₁ G₂ κ w = G₁ ∩ T := by
    ext u
    simp [compatibleIndices, translatedPreimage, T]
  have hunion : (G₁ ∪ T).card ≤ r := by
    simpa using (Finset.card_le_card (Finset.subset_univ (G₁ ∪ T)))
  have hinter := Finset.card_inter_add_card_union G₁ T
  rw [hcompat, ← hT]
  omega

/-- If each dense index set omits at most the stated error, compatible pairs
still occupy the complementary proportion. -/
theorem sub_add_le_card_compatibleIndices
    {r e₁ e₂ : ℕ} (hr : 0 < r) (G₁ G₂ : Finset (Fin r)) (κ w : Fin r)
    (h₁ : r - G₁.card ≤ e₁) (h₂ : r - G₂.card ≤ e₂) :
    r - (e₁ + e₂) ≤ (compatibleIndices hr G₁ G₂ κ w).card := by
  have hG₁ : G₁.card ≤ r := by
    simpa using (Finset.card_le_card (Finset.subset_univ G₁))
  have hG₂ : G₂.card ≤ r := by
    simpa using (Finset.card_le_card (Finset.subset_univ G₂))
  have hcompat := card_add_card_le_add_card_compatibleIndices hr G₁ G₂ κ w
  omega

/-- The numerical `7/8 + 7/8 - 1 = 3/4` form used in the KLS proof. -/
theorem three_mul_le_four_mul_card_compatibleIndices
    {r : ℕ} (hr : 0 < r) (G₁ G₂ : Finset (Fin r)) (κ w : Fin r)
    (h₁ : 7 * r ≤ 8 * G₁.card) (h₂ : 7 * r ≤ 8 * G₂.card) :
    3 * r ≤ 4 * (compatibleIndices hr G₁ G₂ κ w).card := by
  have hcompat := card_add_card_le_add_card_compatibleIndices hr G₁ G₂ κ w
  omega

/-- The aggregate root multiplicity, weighted by the number of compatible
refined-class pairs above each square-residue lift. -/
def weightedCompatibleRootCount
    (q r c : ℕ) (hq : 0 < q) (hr : 0 < r)
    (G₁ G₂ : Finset (Fin r)) (κ : Fin r) : ℕ :=
  ∑ w : Fin r,
    (compatibleIndices hr G₁ G₂ κ w).card *
      liftedRootMultiplicity q r c hq hr w

/-- Aggregate `3/4` lower bound.  This is the finite weighted form needed to
combine compatibility with root-multiplicity conservation; it does not assume
that multiplicity is uniform over the refined quadratic residues. -/
theorem three_mul_mul_le_four_mul_weightedCompatibleRootCount
    {q r c : ℕ} (hq : 0 < q) (hr : 0 < r)
    (G₁ G₂ : Finset (Fin r)) (κ : Fin r)
    (h₁ : 7 * r ≤ 8 * G₁.card) (h₂ : 7 * r ≤ 8 * G₂.card) :
    (3 * r) * (r * rootMultiplicity q c) ≤
      4 * weightedCompatibleRootCount q r c hq hr G₁ G₂ κ := by
  have hsum :
      ∑ w : Fin r, (3 * r) * liftedRootMultiplicity q r c hq hr w ≤
        ∑ w : Fin r,
          (4 * (compatibleIndices hr G₁ G₂ κ w).card) *
            liftedRootMultiplicity q r c hq hr w := by
    apply Finset.sum_le_sum
    intro w _
    exact Nat.mul_le_mul_right _
      (three_mul_le_four_mul_card_compatibleIndices hr G₁ G₂ κ w h₁ h₂)
  have hleft :
      ∑ w : Fin r, (3 * r) * liftedRootMultiplicity q r c hq hr w =
        (3 * r) * (r * rootMultiplicity q c) := by
    rw [← Finset.mul_sum, sum_liftedRootMultiplicity hq hr]
  have hright :
      ∑ w : Fin r,
          (4 * (compatibleIndices hr G₁ G₂ κ w).card) *
            liftedRootMultiplicity q r c hq hr w =
        4 * weightedCompatibleRootCount q r c hq hr G₁ G₂ κ := by
    rw [weightedCompatibleRootCount, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rwa [hleft, hright] at hsum

/-- The corresponding aggregate count of square values in an interval of
`H` complete periods for every refined square-residue lift. -/
def aggregateRefinedSquareValueCount
    (q r c : ℕ) (hq : 0 < q) (hr : 0 < r) (a H : ℕ)
    (G₁ G₂ : Finset (Fin r)) (κ : Fin r) : ℕ :=
  ∑ w : Fin r,
    (compatibleIndices hr G₁ G₂ κ w).card *
      (squareValuesInIco (q * r) (c + q * w.val) a H).card

theorem aggregateRefinedSquareValueCount_eq
    {q r c a H : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : c < q)
    (G₁ G₂ : Finset (Fin r)) (κ : Fin r) :
    aggregateRefinedSquareValueCount q r c hq hr a H G₁ G₂ κ =
      weightedCompatibleRootCount q r c hq hr G₁ G₂ κ * H := by
  rw [aggregateRefinedSquareValueCount, weightedCompatibleRootCount,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  rw [card_refinedSquareValuesInIco hq hr hc]
  ring

theorem three_mul_mul_mul_le_four_mul_aggregateRefinedSquareValueCount
    {q r c a H : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : c < q)
    (G₁ G₂ : Finset (Fin r)) (κ : Fin r)
    (h₁ : 7 * r ≤ 8 * G₁.card) (h₂ : 7 * r ≤ 8 * G₂.card) :
    ((3 * r) * (r * rootMultiplicity q c)) * H ≤
      4 * aggregateRefinedSquareValueCount q r c hq hr a H G₁ G₂ κ := by
  rw [aggregateRefinedSquareValueCount_eq hq hr hc]
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right H
    (three_mul_mul_le_four_mul_weightedCompatibleRootCount (c := c)
      hq hr G₁ G₂ κ h₁ h₂)

/-- Carry from adding two canonical residues modulo `q`. -/
def residueCarry (q a b : ℕ) : ℕ := (a + b) / q

theorem residueCarry_le_one {q a b : ℕ} (hq : 0 < q)
    (ha : a < q) (hb : b < q) :
    residueCarry q a b ≤ 1 := by
  dsimp only [residueCarry]
  rw [Nat.div_le_iff_le_mul hq]
  omega

/-- Exact carry identity for addition of two refined residue classes. -/
theorem refinedResidue_add_eq
    {q a b u v : ℕ} (hq : 0 < q) :
    (a + q * u) + (b + q * v) =
      (a + b) % q + q * (u + v + residueCarry q a b) := by
  dsimp only [residueCarry]
  have hdivmod := Nat.div_add_mod (a + b) q
  calc
    (a + q * u) + (b + q * v) = (a + b) + q * (u + v) := by ring
    _ = (q * ((a + b) / q) + (a + b) % q) + q * (u + v) := by
      rw [hdivmod]
    _ = (a + b) % q + q * (u + v + (a + b) / q) := by ring

/-- Reducing the carry identity modulo `q*r` leaves precisely the cyclic
compatibility equation on the lift indices. -/
theorem refinedResidue_add_mod
    {q r a b : ℕ} (hq : 0 < q) (hr : 0 < r) (u v : Fin r) :
    ((a + q * u.val) + (b + q * v.val)) % (q * r) =
      (a + b) % q + q * ((u.val + v.val + residueCarry q a b) % r) := by
  rw [refinedResidue_add_eq hq]
  have hc : (a + b) % q < q := Nat.mod_lt _ hq
  have hw : (u.val + v.val + residueCarry q a b) % r < r := Nat.mod_lt _ hr
  have hsmall :
      (a + b) % q + q * ((u.val + v.val + residueCarry q a b) % r) < q * r := by
    nlinarith
  have hcqr : (a + b) % q < q * r := by nlinarith
  calc
    ((a + b) % q + q * (u.val + v.val + residueCarry q a b)) % (q * r) =
        (((a + b) % q) % (q * r) +
          (q * (u.val + v.val + residueCarry q a b)) % (q * r)) % (q * r) :=
      Nat.add_mod _ _ _
    _ = ((a + b) % q +
          q * ((u.val + v.val + residueCarry q a b) % r)) % (q * r) := by
      rw [Nat.mod_eq_of_lt hcqr, Nat.mul_mod_mul_left]
    _ = (a + b) % q +
          q * ((u.val + v.val + residueCarry q a b) % r) :=
      Nat.mod_eq_of_lt hsmall

end Erdos438

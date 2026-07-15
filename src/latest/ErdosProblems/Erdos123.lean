import Mathlib

open Combinatorics
open Filter Asymptotics

namespace Erdos123

/-- The positive integers representable as `a^k b^l c^m` with natural exponents. -/
def Smooth3 (a b c : ℕ) : Set ℕ :=
  {x | ∃ k l m : ℕ, x = a ^ k * b ^ l * c ^ m}

/-- No two distinct members of `s` are comparable in the divisibility order. -/
def IsPrimitive (s : Finset ℕ) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ¬x ∣ y

/-- One target has a primitive representation using terms of `A`. -/
def IsRepresentable (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ A) ∧ IsPrimitive s ∧ s.sum id = n

/-- Every sufficiently large natural number is the sum of a finite primitive
set of distinct members of `A`. Distinctness is built into `Finset`. -/
def IsDComplete (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Finset ℕ,
      (∀ x ∈ s, x ∈ A) ∧ IsPrimitive s ∧ s.sum id = n

/-- Pairwise coprimality of three bases. -/
def PairwiseCoprime3 (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c

/-- The intended nondegenerate Erdős Problem 123. -/
def IntendedStatement : Prop :=
  ∀ a b c : ℕ, 1 < a → 1 < b → 1 < c → PairwiseCoprime3 a b c →
    IsDComplete (Smooth3 a b c)

noncomputable section

/-- A positive near-relation `p*α-q*β=d` produces an eventually dense
nonnegative additive semigroup: every sufficiently large `x` has a semigroup
point in `(x-ε,x]`. -/
theorem additiveSemigroup_eventually_leftDense
    {α β d ε : ℝ} {p q : ℕ}
    (_hα : 0 < α) (hβ : 0 < β) (_hp : 0 < p) (hq : 0 < q)
    (hd : d = (p : ℝ) * α - (q : ℝ) * β)
    (hdPos : 0 < d) (hdε : d < ε) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ u v : ℕ, x - ε < (u : ℝ) * α + (v : ℝ) * β ∧
        (u : ℝ) * α + (v : ℝ) * β ≤ x := by
  let s : ℝ := (q : ℝ) * β
  have hsPos : 0 < s := mul_pos (by exact_mod_cast hq) hβ
  rcases Archimedean.arch s hdPos with ⟨K₀, hK₀⟩
  refine ⟨((K₀ : ℝ) + 1) * s, ?_⟩
  intro x hx
  rcases existsUnique_zsmul_near_of_pos hsPos x with ⟨K, hK, _hKuniq⟩
  simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one] at hK
  have hKnonneg : 0 ≤ K := by
    by_contra hneg
    have hKle : (K : ℝ) + 1 ≤ 0 := by exact_mod_cast (show K + 1 ≤ 0 by omega)
    nlinarith
  let k : ℕ := K.toNat
  have hkCast : (k : ℝ) = (K : ℝ) := by
    have hkInt : (k : ℤ) = K := Int.toNat_of_nonneg hKnonneg
    exact_mod_cast hkInt
  have hK₀le : K₀ ≤ k := by
    have hcast : (K₀ : ℝ) ≤ (k : ℝ) := by
      rw [hkCast]
      nlinarith
    exact_mod_cast hcast
  have hsOverlap : s ≤ (k : ℝ) * d := by
    have hK₀' : s ≤ (K₀ : ℝ) * d := by simpa [nsmul_eq_mul] using hK₀
    have hNat : (K₀ : ℝ) * d ≤ (k : ℝ) * d := by
      gcongr
    exact hK₀'.trans hNat
  have hkLower : (k : ℝ) * s ≤ x := by
    rw [hkCast]
    exact hK.1
  have hkUpper : x < ((k : ℝ) + 1) * s := by
    rw [hkCast]
    exact hK.2
  have hgNonneg : 0 ≤ x - (k : ℝ) * s := by linarith
  have hgLt : x - (k : ℝ) * s < (k : ℝ) * d := by linarith
  rcases existsUnique_zsmul_near_of_pos hdPos (x - (k : ℝ) * s) with
    ⟨T, hT, _hTuniq⟩
  simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one] at hT
  have hTnonneg : 0 ≤ T := by
    by_contra hneg
    have hTle : (T : ℝ) + 1 ≤ 0 := by exact_mod_cast (show T + 1 ≤ 0 by omega)
    nlinarith
  let t : ℕ := T.toNat
  have htCast : (t : ℝ) = (T : ℝ) := by
    have htInt : (t : ℤ) = T := Int.toNat_of_nonneg hTnonneg
    exact_mod_cast htInt
  have htLe : t ≤ k := by
    have hcast : (T : ℝ) < (k : ℝ) := by
      by_contra hnot
      have hge : (k : ℝ) ≤ (T : ℝ) := le_of_not_gt hnot
      nlinarith
    have hint : T < (k : ℤ) := by exact_mod_cast hcast
    have htInt : (t : ℤ) = T := Int.toNat_of_nonneg hTnonneg
    omega
  refine ⟨p * t, q * (k - t), ?_, ?_⟩
  · have hcastSub : ((k - t : ℕ) : ℝ) = (k : ℝ) - (t : ℝ) :=
      Nat.cast_sub htLe
    rw [Nat.cast_mul, Nat.cast_mul, hcastSub, htCast]
    have hExpr :
        (p : ℝ) * (T : ℝ) * α + (q : ℝ) * ((k : ℝ) - (T : ℝ)) * β =
          (k : ℝ) * s + (T : ℝ) * d := by
      rw [hd]
      dsimp [s]
      ring
    rw [hExpr]
    nlinarith [hT.2]
  · have hcastSub : ((k - t : ℕ) : ℝ) = (k : ℝ) - (t : ℝ) :=
      Nat.cast_sub htLe
    rw [Nat.cast_mul, Nat.cast_mul, hcastSub, htCast]
    have hExpr :
        (p : ℝ) * (T : ℝ) * α + (q : ℝ) * ((k : ℝ) - (T : ℝ)) * β =
          (k : ℝ) * s + (T : ℝ) * d := by
      rw [hd]
      dsimp [s]
      ring
    rw [hExpr]
    nlinarith [hT.1]

private def encodeWord {ι : Type*} [Fintype ι] (L : ℕ)
    (x : ι → Fin L) : ℕ :=
  Nat.ofDigits L (List.ofFn (fun j : Fin (Fintype.card ι) =>
    (x ((Fintype.equivFin ι).symm j) : ℕ)))

private theorem encodeWord_lt {ι : Type*} [Fintype ι] {L : ℕ} (hL : 1 < L)
    (x : ι → Fin L) : encodeWord L x < L ^ Fintype.card ι := by
  have h := Nat.ofDigits_lt_base_pow_length (b := L)
    (l := List.ofFn (fun j : Fin (Fintype.card ι) =>
      (x ((Fintype.equivFin ι).symm j) : ℕ))) hL
  have hh := h (by
    intro d hd
    simp only [List.mem_ofFn] at hd
    rcases hd with ⟨j, rfl⟩
    exact (x ((Fintype.equivFin ι).symm j)).isLt)
  simpa [encodeWord] using hh

private def lineOptions {α ι : Type*} [Fintype ι] (l : Line α ι) :
    List (Option α) :=
  List.ofFn (fun j : Fin (Fintype.card ι) =>
    l.idxFun ((Fintype.equivFin ι).symm j))

private def optionMask {α : Type*} : Option α → ℕ
  | none => 1
  | some _ => 0

private def optionBase {L : ℕ} : Option (Fin L) → ℕ
  | none => 0
  | some x => (x : ℕ)

private theorem ofDigits_option_line {L : ℕ} (r : Fin L)
    (opts : List (Option (Fin L))) :
    Nat.ofDigits L (opts.map (fun o : Option (Fin L) => (o.getD r : ℕ))) =
      Nat.ofDigits L (opts.map optionBase) +
        (r : ℕ) * Nat.ofDigits L (opts.map optionMask) := by
  induction opts with
  | nil => simp
  | cons o opts ih =>
      cases o <;> simp [Nat.ofDigits_cons, optionMask, optionBase, ih] <;> ring

private theorem line_step_pos {ι : Type*} [Fintype ι] {L : ℕ} (hL : 1 < L)
    (l : Line (Fin L) ι) :
    0 < Nat.ofDigits L ((lineOptions l).map optionMask) := by
  by_contra h
  have hz : Nat.ofDigits L ((lineOptions l).map optionMask) = 0 := by omega
  rcases l.proper with ⟨i, hi⟩
  have hmemOpt : (none : Option (Fin L)) ∈ lineOptions l := by
    unfold lineOptions
    simp only [List.mem_ofFn]
    refine ⟨(Fintype.equivFin ι) i, ?_⟩
    simp [hi]
  have hmemOne : 1 ∈ (lineOptions l).map optionMask := by
    exact List.mem_map.mpr ⟨none, hmemOpt, rfl⟩
  have hallzero := Nat.digits_zero_of_eq_zero (by omega : L ≠ 0) hz 1 hmemOne
  omega

private theorem encode_line_affine {ι : Type*} [Fintype ι] {L : ℕ}
    (hL : 1 < L) (l : Line (Fin L) ι) (r : Fin L) :
    let zero : Fin L := ⟨0, by omega⟩
    encodeWord L (l r) =
      encodeWord L (l zero) + (r : ℕ) *
        Nat.ofDigits L ((lineOptions l).map optionMask) := by
  let zero : Fin L := ⟨0, by omega⟩
  change encodeWord L (l r) = encodeWord L (l zero) + _
  let opts : List (Option (Fin L)) :=
    List.ofFn (fun j : Fin (Fintype.card ι) =>
      l.idxFun ((Fintype.equivFin ι).symm j))
  have hrList :
      List.ofFn (fun j : Fin (Fintype.card ι) =>
        ((l r) ((Fintype.equivFin ι).symm j) : ℕ)) =
        opts.map (fun o : Option (Fin L) => (o.getD r : ℕ)) := by
    rw [List.map_ofFn, List.ofFn_inj]
    funext j
    simp only [Function.comp_apply, Line.coe_apply]
  have hzList :
      List.ofFn (fun j : Fin (Fintype.card ι) =>
        ((l zero) ((Fintype.equivFin ι).symm j) : ℕ)) =
        opts.map optionBase := by
    rw [List.map_ofFn, List.ofFn_inj]
    funext j
    simp only [Function.comp_apply, Line.coe_apply]
    cases l.idxFun ((Fintype.equivFin ι).symm j) <;>
      simp [optionBase, zero]
  unfold encodeWord lineOptions
  rw [hrList, hzList]
  exact ofDigits_option_line r opts

/-- A finite van der Waerden theorem obtained from Hales--Jewett: for every
number of colors and every requested length at least two, one finite initial
interval already forces a monochromatic arithmetic progression of that
length. -/
theorem finite_van_der_waerden (K L : ℕ) (hL : 1 < L) :
    ∃ N : ℕ, 0 < N ∧ ∀ color : ℕ → Fin K,
      ∃ b d : ℕ, 0 < d ∧ b + (L - 1) * d < N ∧
        ∀ r : Fin L, color (b + (r : ℕ) * d) = color b := by
  rcases Line.exists_mono_in_high_dimension (Fin L) (Fin K) with
    ⟨ι, inst, hmono⟩
  letI : Fintype ι := inst
  let N := L ^ Fintype.card ι
  have hN : 0 < N := by
    unfold N
    positivity
  refine ⟨N, hN, ?_⟩
  intro color
  let C : (ι → Fin L) → Fin K := fun x => color (encodeWord L x)
  rcases hmono C with ⟨l, k, hk⟩
  let zero : Fin L := ⟨0, by omega⟩
  let last : Fin L := ⟨L - 1, by omega⟩
  let b := encodeWord L (l zero)
  let d := Nat.ofDigits L ((lineOptions l).map optionMask)
  have hd : 0 < d := line_step_pos hL l
  have hlast : b + (L - 1) * d < N := by
    have hcode := encodeWord_lt hL (l last)
    have hval : (last : ℕ) = L - 1 := rfl
    rw [encode_line_affine hL l last, hval] at hcode
    exact hcode
  refine ⟨b, d, hd, hlast, ?_⟩
  intro r
  dsimp [b, d]
  rw [← encode_line_affine hL l r]
  change C (l r) = C (l zero)
  exact (hk r).trans (hk zero).symm

/-- Evaluation of a three-dimensional exponent vector. -/
def eval3 (a b c i j k : ℕ) : ℕ := a ^ i * b ^ j * c ^ k

/-- For pairwise-coprime bases greater than one, divisibility of monomials is
exactly coordinatewise comparison of their exponent vectors. -/
theorem eval3_dvd_iff {a b c i j k i' j' k' : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    eval3 a b c i j k ∣ eval3 a b c i' j' k' ↔
      i ≤ i' ∧ j ≤ j' ∧ k ≤ k' := by
  constructor
  · intro hdiv
    have haiDivLhs : a ^ i ∣ eval3 a b c i j k := by
      exact ⟨b ^ j * c ^ k, by simp [eval3, mul_assoc]⟩
    have haiDivRhs : a ^ i ∣ eval3 a b c i' j' k' := haiDivLhs.trans hdiv
    have haiCoprime : Nat.Coprime (a ^ i) (b ^ j' * c ^ k') :=
      ((hab.pow_left i).pow_right j').mul_right ((hac.pow_left i).pow_right k')
    have haiDiv : a ^ i ∣ a ^ i' := by
      apply haiCoprime.dvd_of_dvd_mul_right
      simpa only [eval3, mul_assoc] using haiDivRhs
    have hbjDivLhs : b ^ j ∣ eval3 a b c i j k := by
      exact ⟨a ^ i * c ^ k, by simp [eval3, mul_assoc, mul_left_comm]⟩
    have hbjDivRhs : b ^ j ∣ eval3 a b c i' j' k' := hbjDivLhs.trans hdiv
    have hbjCoprime : Nat.Coprime (b ^ j) (a ^ i' * c ^ k') :=
      ((hab.symm.pow_left j).pow_right i').mul_right ((hbc.pow_left j).pow_right k')
    have hbjDiv : b ^ j ∣ b ^ j' := by
      apply hbjCoprime.dvd_of_dvd_mul_right
      simpa only [eval3, mul_assoc, mul_comm, mul_left_comm] using hbjDivRhs
    have hckDivLhs : c ^ k ∣ eval3 a b c i j k := by
      exact ⟨a ^ i * b ^ j, by simp [eval3, mul_assoc, mul_comm]⟩
    have hckDivRhs : c ^ k ∣ eval3 a b c i' j' k' := hckDivLhs.trans hdiv
    have hckCoprime : Nat.Coprime (c ^ k) (a ^ i' * b ^ j') :=
      ((hac.symm.pow_left k).pow_right i').mul_right ((hbc.symm.pow_left k).pow_right j')
    have hckDiv : c ^ k ∣ c ^ k' := by
      apply hckCoprime.dvd_of_dvd_mul_right
      simpa only [eval3, mul_assoc, mul_comm, mul_left_comm] using hckDivRhs
    exact ⟨(Nat.pow_dvd_pow_iff_le_right ha).mp haiDiv,
      (Nat.pow_dvd_pow_iff_le_right hb).mp hbjDiv,
      (Nat.pow_dvd_pow_iff_le_right hc).mp hckDiv⟩
  · rintro ⟨hi, hj, hk⟩
    exact Nat.mul_dvd_mul
      (Nat.mul_dvd_mul (pow_dvd_pow a hi) (pow_dvd_pow b hj))
      (pow_dvd_pow c hk)

/-- Divisibility between two monomials of the same total exponent degree forces
the exponent triples to be identical. -/
theorem exponents_eq_of_eval3_dvd_of_degree_eq
    {a b c i j k i' j' k' : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hdiv : eval3 a b c i j k ∣ eval3 a b c i' j' k')
    (hdegree : i + j + k = i' + j' + k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have hcoord := (eval3_dvd_iff ha hb hc hab hac hbc).mp hdiv
  omega

/-- Distinct exponent triples on one homogeneous level evaluate to a
pairwise-nondividing family, hence every subset of a level is a valid primitive
family of summands. -/
theorem not_eval3_dvd_of_same_degree
    {a b c i j k i' j' k' : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hdegree : i + j + k = i' + j' + k')
    (hne : ¬(i = i' ∧ j = j' ∧ k = k')) :
    ¬eval3 a b c i j k ∣ eval3 a b c i' j' k' := by
  intro hdiv
  exact hne (exponents_eq_of_eval3_dvd_of_degree_eq
    ha hb hc hab hac hbc hdiv hdegree)

/-- The `t`-th term in a residue correction gadget of length `r`. -/
def correctionTerm (a b c r t : ℕ) : ℕ :=
  b ^ (a.totient * t) * c ^ (a.totient * (r - 1 - t))

/-- The correction gadget as a genuine set of distinct integer summands. -/
def correctionSet (a b c r : ℕ) : Finset ℕ :=
  (Finset.range r).image (correctionTerm a b c r)

/-- Every correction term is congruent to one modulo `a`. -/
theorem correctionTerm_modEq_one {a b c r t : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) :
    correctionTerm a b c r t ≡ 1 [MOD a] := by
  have hb : b ^ a.totient ≡ 1 [MOD a] := Nat.ModEq.pow_totient hab.symm
  have hc : c ^ a.totient ≡ 1 [MOD a] := Nat.ModEq.pow_totient hac.symm
  have hbt := hb.pow t
  have hct := hc.pow (r - 1 - t)
  simpa [correctionTerm, pow_mul] using hbt.mul hct

/-- Different indices in a gadget give monomials which do not divide one
another. -/
theorem correctionTerm_not_dvd {a b c r t u : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (ht : t < r) (hu : u < r) (htu : t ≠ u) :
    ¬correctionTerm a b c r t ∣ correctionTerm a b c r u := by
  have htot : 0 < a.totient := Nat.totient_pos.mpr (by omega)
  have ht' : t ≤ r - 1 := by omega
  have hu' : u ≤ r - 1 := by omega
  have htSum : t + (r - 1 - t) = r - 1 := by omega
  have huSum : u + (r - 1 - u) = r - 1 := by omega
  have hdegree :
      a.totient * t + a.totient * (r - 1 - t) + 0 =
      a.totient * u + a.totient * (r - 1 - u) + 0 := by
    simp only [add_zero, ← Nat.mul_add, htSum, huSum]
  have hne : ¬(a.totient * t = a.totient * u ∧
      a.totient * (r - 1 - t) = a.totient * (r - 1 - u) ∧ (0 : ℕ) = 0) := by
    intro h
    exact htu (Nat.eq_of_mul_eq_mul_left htot h.1)
  have h := not_eval3_dvd_of_same_degree hb hc ha hbc hab.symm hac.symm hdegree hne
  simpa [eval3, correctionTerm, mul_assoc] using h

/-- The index-to-value map is injective on the gadget range. -/
theorem correctionTerm_injOn {a b c r : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    Set.InjOn (correctionTerm a b c r) (Finset.range r : Set ℕ) := by
  intro t ht u hu heq
  by_contra htu
  have hnot := correctionTerm_not_dvd ha hb hc hab hac hbc
    (Finset.mem_range.mp ht) (Finset.mem_range.mp hu) htu
  apply hnot
  rw [heq]

/-- The correction set is a divisibility antichain. -/
theorem correctionSet_isPrimitive {a b c r : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    IsPrimitive (correctionSet a b c r) := by
  intro x hx y hy hxy
  rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
  apply correctionTerm_not_dvd ha hb hc hab hac hbc
    (Finset.mem_range.mp ht) (Finset.mem_range.mp hu)
  intro htu
  subst u
  exact hxy rfl

/-- A length-`r` correction gadget has sum congruent to `r` modulo `a`. -/
theorem correctionSet_sum_modEq {a b c r : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    (correctionSet a b c r).sum id ≡ r [MOD a] := by
  have hinj := correctionTerm_injOn (r := r) ha hb hc hab hac hbc
  rw [correctionSet, Finset.sum_image hinj]
  have hsum :
      (Finset.range r).sum (correctionTerm a b c r) ≡
      (Finset.range r).sum (fun _t => 1) [MOD a] :=
    Nat.ModEq.sum (fun t ht => correctionTerm_modEq_one hab hac)
  have hones : (Finset.range r).sum (fun _t => (1 : ℕ)) = r := by simp
  rw [hones] at hsum
  simpa only [id_eq] using hsum

/-- Recursive bounded-coefficient sums with homogeneous two-base weights.
At stage `M`, this is exactly the set of sums
`Σ_{i=0}^M s_i A^(M-i) B^i` with `s_i<L`. -/
def HomogeneousRadixRep (A B L : ℕ) : ℕ → ℕ → Prop
  | 0, n => n < L
  | M + 1, n => ∃ x s : ℕ,
      HomogeneousRadixRep A B L M x ∧ s < L ∧
        n = A * x + B ^ (M + 1) * s

private theorem exists_interval_shift_decomposition
    {U V P K y : ℕ} (hP : 0 < P) (hK : 0 < K)
    (hUV : U ≤ V) (hwidth : P - 1 ≤ V - U)
    (hyLo : U ≤ y) (hyHi : y ≤ V + P * (K - 1)) :
    ∃ x q : ℕ, U ≤ x ∧ x ≤ V ∧ q < K ∧ y = x + P * q := by
  by_cases hq : (y - U) / P < K
  · let q := (y - U) / P
    let x := U + (y - U) % P
    refine ⟨x, q, by dsimp [x]; omega, ?_, hq, ?_⟩
    · have hmod : (y - U) % P ≤ P - 1 := by
        have := Nat.mod_lt (y - U) hP
        omega
      have hVU : U + (P - 1) ≤ V := by
        have hh := (Nat.le_sub_iff_add_le hUV).mp hwidth
        simpa [Nat.add_comm] using hh
      dsimp [x]
      exact (Nat.add_le_add_left hmod U).trans hVU
    · have hdecomp := Nat.mod_add_div (y - U) P
      have hy : U + (y - U) = y := Nat.add_sub_of_le hyLo
      dsimp [x, q]
      omega
  · have hqge : K ≤ (y - U) / P := by omega
    have hKP : K * P ≤ y - U :=
      (Nat.le_div_iff_mul_le hP).mp hqge
    have hPK : P * K ≤ y - U := by simpa [Nat.mul_comm] using hKP
    let q := K - 1
    have hqK : q < K := by dsimp [q]; omega
    have hPqPK : P * q < P * K := Nat.mul_lt_mul_of_pos_left hqK hP
    have hPq : P * q ≤ y :=
      hPqPK.le.trans (hPK.trans (Nat.sub_le y U))
    have hUPq : U + P * q ≤ y := by
      have hh : P * q ≤ y - U := hPqPK.le.trans hPK
      have hh' := (Nat.le_sub_iff_add_le hyLo).mp hh
      simpa [Nat.add_comm] using hh'
    let x := y - P * q
    refine ⟨x, q, ?_, ?_, hqK, ?_⟩
    · dsimp [x]
      exact Nat.le_sub_of_add_le hUPq
    · dsimp [x]
      exact Nat.sub_le_iff_le_add.mpr (by simpa [q, Nat.add_comm] using hyHi)
    · dsimp [x]
      exact (Nat.sub_add_cancel hPq).symm

private theorem bounded_residue_power {A B e : ℕ}
    (hA : 0 < A) (hcop : Nat.Coprime A B) (n : ℕ) :
    ∃ r : ℕ, r < A ∧ (B ^ e * r) % A = n % A := by
  let f : Fin A → Fin A := fun r =>
    ⟨(B ^ e * (r : ℕ)) % A, Nat.mod_lt _ hA⟩
  have hf : Function.Injective f := by
    intro r s hrs
    have hmod : B ^ e * (r : ℕ) ≡ B ^ e * (s : ℕ) [MOD A] :=
      congrArg Fin.val hrs
    have hpowCop : Nat.Coprime A (B ^ e) := hcop.pow_right e
    have hrsMod : (r : ℕ) ≡ (s : ℕ) [MOD A] :=
      Nat.ModEq.cancel_left_of_coprime hpowCop (by
        simpa [Nat.mul_comm] using hmod)
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hrsMod r.isLt s.isLt)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp⟩
  let target : Fin A := ⟨n % A, Nat.mod_lt _ hA⟩
  rcases hbij.2 target with ⟨r, hr⟩
  exact ⟨r, r.isLt, congrArg Fin.val hr⟩

/-- One interval-amplification step for homogeneous bounded radix sums. -/
theorem homogeneousRadixRep_interval_step
    {A B L M U V K : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hcop : Nat.Coprime A B)
    (hK : 0 < K) (hL : L = A * K)
    (hUV : U ≤ V)
    (hwidth : B ^ (M + 1) - 1 ≤ V - U)
    (hrep : ∀ n, U ≤ n → n ≤ V → HomogeneousRadixRep A B L M n) :
    ∀ n,
      A * U + B ^ (M + 1) * (A - 1) ≤ n →
      n ≤ A * (V + B ^ (M + 1) * (K - 1)) →
      HomogeneousRadixRep A B L (M + 1) n := by
  intro n hnLo hnHi
  let P := B ^ (M + 1)
  have hP : 0 < P := pow_pos hB _
  rcases bounded_residue_power (e := M + 1) hA hcop n with ⟨r, hrA, hrmod⟩
  let z := P * r
  have hzle : z ≤ P * (A - 1) := by
    dsimp [z]
    exact Nat.mul_le_mul_left P (by omega)
  have hzn : z ≤ n := by
    have hbase : P * (A - 1) ≤ n := by
      dsimp [P] at ⊢
      omega
    exact hzle.trans hbase
  have hmod : (n - z) % A = 0 := by
    have hnmod : n ≡ n % A [MOD A] := by simp [Nat.ModEq]
    have hzmod : z ≡ n % A [MOD A] := by
      change z % A = (n % A) % A
      simp [z, P, hrmod, Nat.mod_eq_of_lt (Nat.mod_lt n hA)]
    have hh := Nat.ModEq.sub hzn (le_refl (n % A)) hnmod hzmod
    simpa [Nat.ModEq] using hh
  have hdiv : A ∣ n - z := Nat.dvd_iff_mod_eq_zero.mpr hmod
  let y := (n - z) / A
  have hAy : A * y = n - z := Nat.mul_div_cancel' hdiv
  have hyLo : U ≤ y := by
    apply (Nat.le_div_iff_mul_le hA).2
    have hAUz : A * U + z ≤ n := by
      have hzbound : z ≤ P * (A - 1) := hzle
      dsimp [P] at hzbound
      omega
    have hAU : A * U ≤ n - z := Nat.le_sub_of_add_le hAUz
    simpa [Nat.mul_comm] using hAU
  have hyHi : y ≤ V + P * (K - 1) := by
    apply Nat.le_of_mul_le_mul_left (c := A) _ hA
    rw [hAy]
    dsimp [z, P] at hnHi ⊢
    omega
  rcases exists_interval_shift_decomposition hP hK hUV
      (by simpa [P] using hwidth) hyLo hyHi with
    ⟨x, q, hxLo, hxHi, hqK, hy⟩
  let s := A * q + r
  have hsL : s < L := by
    rw [hL]
    dsimp [s]
    nlinarith
  refine ⟨x, s, hrep x hxLo hxHi, hsL, ?_⟩
  have hnEq : n = A * y + z := by rw [hAy]; omega
  rw [hnEq, hy]
  dsimp [s, z, P]
  ring

/-- Choosing `L=4AB` gives a robust interval whose width grows at least like
`B^(M+1)` at every homogeneous-radix stage. -/
theorem homogeneousRadixRep_large_interval
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hcop : Nat.Coprime A B) :
    let L := 4 * A * B
    ∀ M : ℕ, ∃ U V : ℕ,
      U ≤ V ∧ 2 * A * B ^ (M + 1) ≤ V - U ∧
      ∀ n, U ≤ n → n ≤ V → HomogeneousRadixRep A B L M n := by
  dsimp only
  let L := 4 * A * B
  intro M
  induction M with
  | zero =>
      refine ⟨0, L - 1, Nat.zero_le _, ?_, ?_⟩
      · dsimp [L]
        have hAB : 1 ≤ A * B := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
          (Nat.ne_of_gt hA) (Nat.ne_of_gt hB))
        rw [pow_one]
        have hh : 2 * (A * B) ≤ 4 * (A * B) - 1 := by omega
        simpa [Nat.mul_assoc] using hh
      · intro n _hn0 hn
        simp only [HomogeneousRadixRep]
        dsimp [L] at hn ⊢
        have hLpos : 0 < 4 * A * B := by positivity
        omega
  | succ M ih =>
      rcases ih with ⟨U, V, hUV, hwidth, hrep⟩
      let K := 4 * B
      let U' := A * U + B ^ (M + 1) * (A - 1)
      let V' := A * (V + B ^ (M + 1) * (K - 1))
      have hstep := homogeneousRadixRep_interval_step hA hB hcop
        (K := K) (by dsimp [K]; positivity) (by dsimp [L, K]; ring)
        hUV (by
          have hcoef : 0 < 2 * A := by positivity
          have hle : B ^ (M + 1) ≤ (2 * A) * B ^ (M + 1) :=
            Nat.le_mul_of_pos_left _ hcoef
          exact (Nat.sub_le _ _).trans (hle.trans hwidth)) hrep
      refine ⟨U', V', ?_, ?_, ?_⟩
      · dsimp [U', V', K]
        rw [Nat.mul_add]
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left A hUV
        · have hB1 : 1 ≤ B := hB
          have hKcoef : A - 1 ≤ A * (4 * B - 1) := by
            calc
              A - 1 ≤ A := Nat.sub_le _ _
              _ ≤ A * (4 * B - 1) :=
                Nat.le_mul_of_pos_right A (by omega)
          have hh := Nat.mul_le_mul_left (B ^ (M + 1)) hKcoef
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
      · apply Nat.le_sub_of_add_le
        dsimp [U', V', K]
        rw [Nat.mul_add]
        have hB1 : 1 ≤ B := hB
        have hcoef : (A - 1) + 2 * A * B ≤ A * (4 * B - 1) := by
          calc
            (A - 1) + 2 * A * B ≤ A + 2 * A * B :=
              Nat.add_le_add_right (Nat.sub_le A 1) _
            _ = A * (2 * B + 1) := by ring
            _ ≤ A * (4 * B - 1) := by
              exact Nat.mul_le_mul_left A (by omega)
        have hcoefP := Nat.mul_le_mul_left (B ^ (M + 1)) hcoef
        have hpow : B ^ (M + 2) = B ^ (M + 1) * B := by
          rw [show M + 2 = (M + 1) + 1 by omega, pow_succ]
        rw [hpow]
        calc
          2 * A * (B ^ (M + 1) * B) +
              (A * U + B ^ (M + 1) * (A - 1)) =
            A * U + B ^ (M + 1) * ((A - 1) + 2 * A * B) := by ring
          _ ≤ A * U + B ^ (M + 1) * (A * (4 * B - 1)) :=
            Nat.add_le_add_left hcoefP _
          _ ≤ A * V + B ^ (M + 1) * (A * (4 * B - 1)) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left A hUV) _
          _ = A * V + A * (B ^ (M + 1) * (4 * B - 1)) := by ring
      · intro n hnLo hnHi
        exact hstep n hnLo hnHi

private theorem exists_eventual_pow_period (x d : ℕ) (hd : 0 < d) :
    ∃ P T : ℕ, 0 < T ∧ ∀ k : ℕ,
      x ^ (P + k + T) ≡ x ^ (P + k) [MOD d] := by
  let f : Fin (d + 1) → Fin d := fun i => ⟨x ^ (i : ℕ) % d, Nat.mod_lt _ hd⟩
  obtain ⟨u, v, huv, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  wlog huvlt : (u : ℕ) < (v : ℕ) generalizing u v
  · have hvult : (v : ℕ) < (u : ℕ) := by
      exact lt_of_le_of_ne (Nat.le_of_not_gt huvlt) (by
        intro h
        apply huv
        exact Fin.ext h.symm)
    exact this v u huv.symm heq.symm hvult
  let P := (u : ℕ)
  let T := (v : ℕ) - (u : ℕ)
  have hT : 0 < T := by dsimp [T]; omega
  refine ⟨P, T, hT, ?_⟩
  intro k
  have hbase : x ^ (u : ℕ) ≡ x ^ (v : ℕ) [MOD d] := by
    exact congrArg Fin.val heq
  have hmul := hbase.mul_right (x ^ k)
  have hv : (v : ℕ) = P + T := by dsimp [P, T]; omega
  simpa [P, hv, pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul.symm

private theorem pow_period_multiple {x d P T : ℕ} (_hT : 0 < T)
    (h : ∀ k : ℕ, x ^ (P + k + T) ≡ x ^ (P + k) [MOD d])
    (m k : ℕ) : x ^ (P + k + m * T) ≡ x ^ (P + k) [MOD d] := by
  induction m with
  | zero => simpa using (Nat.ModEq.refl (n := d) (x ^ (P + k)))
  | succ m ih =>
      have hstep := h (k + m * T)
      have hstep' : x ^ (P + k + (m + 1) * T) ≡
          x ^ (P + k + m * T) [MOD d] := by
        simpa [Nat.succ_mul, add_assoc] using hstep
      exact hstep'.trans ih

private theorem pow_period_shift {x d P T P' : ℕ} (hPP : P ≤ P') (hT : 0 < T)
    (h : ∀ k : ℕ, x ^ (P + k + T) ≡ x ^ (P + k) [MOD d])
    (m k : ℕ) : x ^ (P' + k + m * T) ≡ x ^ (P' + k) [MOD d] := by
  have hs := pow_period_multiple hT h m (P' - P + k)
  have hcancel : P + (P' - P + k) = P' + k := by omega
  simpa [hcancel] using hs

/-- Three arbitrary bases have a common positive eventual exponent period
modulo every positive modulus. No coprimality with the modulus is needed. -/
theorem exists_common_pow_period (a b c d : ℕ) (hd : 0 < d) :
    ∃ P T : ℕ, 0 < P ∧ 0 < T ∧
      (∀ k, a ^ (P + k + T) ≡ a ^ (P + k) [MOD d]) ∧
      (∀ k, b ^ (P + k + T) ≡ b ^ (P + k) [MOD d]) ∧
      (∀ k, c ^ (P + k + T) ≡ c ^ (P + k) [MOD d]) := by
  obtain ⟨Pa, Ta, hTa, ha⟩ := exists_eventual_pow_period a d hd
  obtain ⟨Pb, Tb, hTb, hb⟩ := exists_eventual_pow_period b d hd
  obtain ⟨Pc, Tc, hTc, hc⟩ := exists_eventual_pow_period c d hd
  let P := Pa + Pb + Pc + 1
  let T := Ta * Tb * Tc
  have hP : 0 < P := by dsimp [P]; omega
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨P, T, hP, hT, ?_, ?_, ?_⟩
  · intro k
    have h := pow_period_shift (P' := P) (by dsimp [P]; omega) hTa ha (Tb * Tc) k
    simpa [T, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  · intro k
    have h := pow_period_shift (P' := P) (by dsimp [P]; omega) hTb hb (Ta * Tc) k
    simpa [T, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  · intro k
    have h := pow_period_shift (P' := P) (by dsimp [P]; omega) hTc hc (Ta * Tb) k
    simpa [T, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- An integer Bezout combination gives bounded nonnegative coefficients
realizing every residue modulo a positive modulus. -/
theorem bounded_residue_combo_of_int_bezout {g₁ g₂ g₃ d : ℕ} (hd : 0 < d)
    {u v w : ℤ}
    (hbez : u * (g₁ : ℤ) + v * (g₂ : ℤ) + w * (g₃ : ℤ) = 1)
    (r : ℕ) :
    ∃ i j k : ℕ, i < d ∧ j < d ∧ k < d ∧
      i * g₁ + j * g₂ + k * g₃ ≡ r [MOD d] := by
  letI : NeZero d := ⟨by omega⟩
  let R : ZMod d := r
  let I : ZMod d := R * u
  let J : ZMod d := R * v
  let K : ZMod d := R * w
  refine ⟨I.val, J.val, K.val, ZMod.val_lt I, ZMod.val_lt J, ZMod.val_lt K, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  change I * g₁ + J * g₂ + K * g₃ = R
  dsimp [I, J, K, R]
  have hbezZ : (u : ZMod d) * g₁ + (v : ZMod d) * g₂ +
      (w : ZMod d) * g₃ = 1 := by
    have hz := congrArg (Int.castRingHom (ZMod d)) hbez
    simpa using hz
  calc
    (r : ZMod d) * u * g₁ + (r : ZMod d) * v * g₂ +
        (r : ZMod d) * w * g₃ =
      (r : ZMod d) * (u * g₁ + v * g₂ + w * g₃) := by ring
    _ = r := by rw [hbezZ]; simp

private theorem period_multiple_from {x d P T : ℕ}
    (h : ∀ k, x ^ (P + k + T) ≡ x ^ (P + k) [MOD d])
    (m k : ℕ) : x ^ (P + k + m * T) ≡ x ^ (P + k) [MOD d] := by
  induction m with
  | zero => simpa using (Nat.ModEq.refl (n := d) (x ^ (P + k)))
  | succ m ih =>
      have hs := h (k + m * T)
      have hs' : x ^ (P + k + (m + 1) * T) ≡
          x ^ (P + k + m * T) [MOD d] := by
        simpa [Nat.succ_mul, add_assoc] using hs
      exact hs'.trans ih

private theorem periodic_split_modEq {x y d P T R D t count : ℕ}
    (_hT : 0 < T) (hPR : P ≤ R)
    (hmargin : P + count * T ≤ D - R)
    (hx : ∀ k, x ^ (P + k + T) ≡ x ^ (P + k) [MOD d])
    (hy : ∀ k, y ^ (P + k + T) ≡ y ^ (P + k) [MOD d])
    (ht : t < count) :
    x ^ (R + t * T) * y ^ (D - R - t * T) ≡
      x ^ R * y ^ (D - R) [MOD d] := by
  have hx0 := period_multiple_from hx t (R - P)
  have hRP : P + (R - P) = R := by omega
  have hxEq : x ^ (R + t * T) ≡ x ^ R [MOD d] := by
    simpa [hRP] using hx0
  have htT : t * T ≤ D - R - P := by
    have hm : count * T ≤ D - R - P := by omega
    exact (Nat.mul_le_mul_right T (Nat.le_of_lt ht)).trans hm
  have hlowP : P ≤ D - R - t * T := by omega
  have hyLow := period_multiple_from hy t (D - R - t * T - P)
  have hstart : P + (D - R - t * T - P) = D - R - t * T := by omega
  have hend : D - R - t * T + t * T = D - R := by omega
  have hyEq : y ^ (D - R - t * T) ≡ y ^ (D - R) [MOD d] := by
    simpa [hstart, hend] using hyLow.symm
  exact hxEq.mul hyEq

/-- Asymmetric opposite-face products still have gcd one, with an explicit
integer Bezout identity. -/
theorem asymmetric_face_products_int_bezout {a b c R S : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    ∃ u v w : ℤ,
      u * ((b ^ R * c ^ S : ℕ) : ℤ) +
        v * ((a ^ R * c ^ S : ℕ) : ℤ) +
        w * ((a ^ S * b ^ R : ℕ) : ℤ) = 1 := by
  have hbaPow : Nat.Coprime (b ^ R) (a ^ R) := hab.symm.pow R R
  have hc_ab : Nat.Coprime c (a * b) := hac.symm.mul_right hbc.symm
  have hcPow : Nat.Coprime (c ^ S) (a ^ S * b ^ R) :=
    (hac.symm.pow S S).mul_right (hbc.symm.pow S R)
  let u0 : ℤ := (b ^ R).gcdA (a ^ R)
  let v0 : ℤ := (b ^ R).gcdB (a ^ R)
  let x0 : ℤ := (c ^ S).gcdA (a ^ S * b ^ R)
  let w0 : ℤ := (c ^ S).gcdB (a ^ S * b ^ R)
  have huv : (b ^ R : ℤ) * u0 + (a ^ R : ℤ) * v0 = 1 := by
    have h := Nat.gcd_eq_gcd_ab (b ^ R) (a ^ R)
    rw [hbaPow] at h
    simpa [u0, v0] using h.symm
  have hxw : (c ^ S : ℤ) * x0 + ((a ^ S * b ^ R : ℕ) : ℤ) * w0 = 1 := by
    have h := Nat.gcd_eq_gcd_ab (c ^ S) (a ^ S * b ^ R)
    rw [hcPow] at h
    simpa [x0, w0] using h.symm
  refine ⟨x0 * u0, x0 * v0, w0, ?_⟩
  push_cast
  calc
    x0 * u0 * (b ^ R * c ^ S) + x0 * v0 * (a ^ R * c ^ S) +
        w0 * (a ^ S * b ^ R) =
      x0 * c ^ S * (b ^ R * u0 + a ^ R * v0) +
        (a ^ S * b ^ R) * w0 := by ring
    _ = x0 * c ^ S + (a ^ S * b ^ R) * w0 := by rw [huv]; ring
    _ = (c ^ S : ℤ) * x0 + (a ^ S * b ^ R) * w0 := by ring
    _ = 1 := hxw

/-- On every sufficiently high exact homogeneous degree, every residue has a
primitive face-supported correction. For ordered bases `a≤c<b`, all correction
sums are bounded by one constant times `c^D`. -/
theorem exact_degree_bounded_face_corrections {a b c d : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hacOrder : a ≤ c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hd : 0 < d) :
    ∃ C D₀ : ℕ, 0 < C ∧ ∀ D : ℕ, D₀ ≤ D → ∀ r : ℕ,
      ∃ s : Finset ℕ,
        (∀ z ∈ s, z ∈ Smooth3 a b c) ∧
        (∀ z ∈ s, ∃ i j k : ℕ,
          i + j + k = D ∧ z = eval3 a b c i j k ∧
          (i = 0 ∨ j = 0 ∨ k = 0)) ∧
        IsPrimitive s ∧ s.sum id ≡ r [MOD d] ∧ s.sum id ≤ C * c ^ D := by
  obtain ⟨P, T, hP, hT, hpa, hpb, hpc⟩ := exists_common_pow_period a b c d hd
  let R := P + d * T
  let E := R + d * T
  let C := 3 * d * b ^ E
  let D₀ := R + (P + d * T)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, D₀, hC, ?_⟩
  intro D hD r
  have hmargin : P + d * T ≤ D - R := by
    dsimp [D₀] at hD
    omega
  let S := D - R
  obtain ⟨u, v, w, hbez⟩ := asymmetric_face_products_int_bezout
    (R := R) (S := S) hab hac hbc
  obtain ⟨ni, nj, nk, hni, hnj, hnk, hcombo⟩ :=
    bounded_residue_combo_of_int_bezout hd hbez r
  let I := Fin ni ⊕ (Fin nj ⊕ Fin nk)
  let expo : I → ℕ × ℕ × ℕ := fun z => match z with
    | Sum.inl t => (0, R + (t : ℕ) * T, D - R - (t : ℕ) * T)
    | Sum.inr (Sum.inl t) => (R + (t : ℕ) * T, 0, D - R - (t : ℕ) * T)
    | Sum.inr (Sum.inr t) => (D - R - (t : ℕ) * T, R + (t : ℕ) * T, 0)
  let term : I → ℕ := fun z =>
    eval3 a b c (expo z).1 (expo z).2.1 (expo z).2.2
  let tagBase : I → ℕ := fun z => match z with
    | Sum.inl _ => b ^ R * c ^ S
    | Sum.inr (Sum.inl _) => a ^ R * c ^ S
    | Sum.inr (Sum.inr _) => a ^ S * b ^ R
  have hindex_lt : ∀ z : I, match z with
      | Sum.inl t => (t : ℕ) < d
      | Sum.inr (Sum.inl t) => (t : ℕ) < d
      | Sum.inr (Sum.inr t) => (t : ℕ) < d := by
    intro z
    cases z with
    | inl t => exact t.isLt.trans hni
    | inr z => cases z with
      | inl t => exact t.isLt.trans hnj
      | inr t => exact t.isLt.trans hnk
  have hlow_pos (t : ℕ) (ht : t < d) : 0 < D - R - t * T := by
    have hm : P + d * T ≤ D - R := hmargin
    have htT := Nat.mul_le_mul_right T (Nat.le_of_lt ht)
    omega
  have hexpo_degree (z : I) :
      (expo z).1 + (expo z).2.1 + (expo z).2.2 = D := by
    have hz := hindex_lt z
    cases z with
    | inl t =>
      simp only [expo]
      have ht := Nat.mul_le_mul_right T (Nat.le_of_lt hz)
      omega
    | inr z => cases z with
      | inl t =>
        simp only [expo]
        have ht := Nat.mul_le_mul_right T (Nat.le_of_lt hz)
        omega
      | inr t =>
        simp only [expo]
        have ht := Nat.mul_le_mul_right T (Nat.le_of_lt hz)
        omega
  have heval_inj : Function.Injective (fun p : ℕ × ℕ × ℕ =>
      eval3 a b c p.1 p.2.1 p.2.2) := by
    intro p q hpq
    change eval3 a b c p.1 p.2.1 p.2.2 =
      eval3 a b c q.1 q.2.1 q.2.2 at hpq
    have h1 : eval3 a b c p.1 p.2.1 p.2.2 ∣
        eval3 a b c q.1 q.2.1 q.2.2 := by rw [hpq]
    have h2 : eval3 a b c q.1 q.2.1 q.2.2 ∣
        eval3 a b c p.1 p.2.1 p.2.2 := by rw [hpq]
    have hle := (eval3_dvd_iff ha hb hc hab hac hbc).mp h1
    have hge := (eval3_dvd_iff ha hb hc hab hac hbc).mp h2
    apply Prod.ext
    · omega
    · apply Prod.ext <;> omega
  have hexpo_inj : Function.Injective expo := by
    intro z z' hzz'
    have hz := hindex_lt z
    have hz' := hindex_lt z'
    cases z with
    | inl t => cases z' with
      | inl t' =>
        simp only [expo, Prod.mk.injEq] at hzz'
        have hm : (t : ℕ) * T = (t' : ℕ) * T := by omega
        have htt : t = t' := Fin.ext (Nat.eq_of_mul_eq_mul_right hT hm)
        exact congrArg (fun q : Fin ni => (Sum.inl q : I)) htt
      | inr z' => cases z' with
        | inl t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hlow_pos (t' : ℕ) hz'
          omega
        | inr t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hlow_pos (t' : ℕ) hz'
          omega
    | inr z => cases z with
      | inl t => cases z' with
        | inl t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hlow_pos (t : ℕ) hz
          omega
        | inr z' => cases z' with
          | inl t' =>
            simp only [expo, Prod.mk.injEq] at hzz'
            have hm : (t : ℕ) * T = (t' : ℕ) * T := by omega
            have htt : t = t' := Fin.ext (Nat.eq_of_mul_eq_mul_right hT hm)
            exact congrArg (fun q : Fin nj => (Sum.inr (Sum.inl q) : I)) htt
          | inr t' =>
            exfalso
            simp only [expo, Prod.mk.injEq] at hzz'
            have hp := hlow_pos (t' : ℕ) hz'
            omega
      | inr t => cases z' with
        | inl t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hlow_pos (t : ℕ) hz
          omega
        | inr z' => cases z' with
          | inl t' =>
            exfalso
            simp only [expo, Prod.mk.injEq] at hzz'
            have hp := hlow_pos (t : ℕ) hz
            omega
          | inr t' =>
            simp only [expo, Prod.mk.injEq] at hzz'
            have hm : (t : ℕ) * T = (t' : ℕ) * T := by omega
            have htt : t = t' := Fin.ext (Nat.eq_of_mul_eq_mul_right hT hm)
            exact congrArg (fun q : Fin nk => (Sum.inr (Sum.inr q) : I)) htt
  have hterm_inj : Function.Injective term := fun _ _ h => hexpo_inj (heval_inj h)
  let s : Finset ℕ := Finset.univ.image term
  refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨idx, _hidx, rfl⟩
    exact ⟨(expo idx).1, (expo idx).2.1, (expo idx).2.2, rfl⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨idx, _hidx, rfl⟩
    refine ⟨(expo idx).1, (expo idx).2.1, (expo idx).2.2,
      hexpo_degree idx, rfl, ?_⟩
    cases idx with
    | inl t => exact Or.inl rfl
    | inr idx => cases idx with
      | inl t => exact Or.inr (Or.inl rfl)
      | inr t => exact Or.inr (Or.inr rfl)
  · intro x hx y hy hxy hdvd
    rcases Finset.mem_image.mp hx with ⟨ix, _hix, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨iy, _hiy, rfl⟩
    apply hxy
    have he := exponents_eq_of_eval3_dvd_of_degree_eq ha hb hc hab hac hbc hdvd
      ((hexpo_degree ix).trans (hexpo_degree iy).symm)
    unfold term
    rw [he.1, he.2.1, he.2.2]
  · have htermMod : ∀ idx : I, term idx ≡ tagBase idx [MOD d] := by
      intro idx
      have hi := hindex_lt idx
      cases idx with
      | inl t =>
        dsimp [term, expo, tagBase, S, eval3]
        simp only [one_mul]
        exact periodic_split_modEq hT (by dsimp [R]; omega) hmargin hpb hpc hi
      | inr idx => cases idx with
        | inl t =>
          dsimp [term, expo, tagBase, S, eval3]
          simp only [mul_one]
          exact periodic_split_modEq hT (by dsimp [R]; omega) hmargin hpa hpc hi
        | inr t =>
          dsimp [term, expo, tagBase, S, eval3]
          simp only [mul_one]
          simpa [Nat.mul_comm] using
            (periodic_split_modEq hT (by dsimp [R]; omega) hmargin hpb hpa hi)
    have hsumImage : s.sum id = ∑ idx : I, term idx := by
      change (Finset.univ.image term).sum id = ∑ idx : I, term idx
      rw [Finset.sum_image]
      · rfl
      · intro x _hx y _hy hxy
        exact hterm_inj hxy
    rw [hsumImage]
    have hsum : (∑ idx : I, term idx) ≡ (∑ idx : I, tagBase idx) [MOD d] :=
      Nat.ModEq.sum (s := Finset.univ) (fun idx _ => htermMod idx)
    have htag : (∑ idx : I, tagBase idx) =
        ni * (b ^ R * c ^ S) + nj * (a ^ R * c ^ S) +
          nk * (a ^ S * b ^ R) := by
      change (∑ idx : Fin ni ⊕ (Fin nj ⊕ Fin nk),
        match idx with
        | Sum.inl _ => b ^ R * c ^ S
        | Sum.inr (Sum.inl _) => a ^ R * c ^ S
        | Sum.inr (Sum.inr _) => a ^ S * b ^ R) = _
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Fin.sum_const, nsmul_eq_mul]
      ac_rfl
    rw [htag] at hsum
    exact hsum.trans hcombo
  · have hcard : s.card ≤ 3 * d := by
      calc
        s.card ≤ Fintype.card I := by
          dsimp [s]
          exact (Finset.card_image_le.trans_eq (Finset.card_univ))
        _ = ni + nj + nk := by simp [I, Nat.add_assoc]
        _ ≤ 3 * d := by omega
    have htermBound : ∀ z ∈ s, z ≤ b ^ E * c ^ D := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨idx, _hidx, rfl⟩
      have hi := hindex_lt idx
      cases idx with
      | inl t =>
        have hhigh : R + (t : ℕ) * T ≤ E := by
          dsimp [E]
          have hm := Nat.mul_le_mul_right T (Nat.le_of_lt hi)
          omega
        dsimp [term, expo, eval3]
        simp only [one_mul]
        have hbpow := Nat.pow_le_pow_right (by omega : 0 < b) hhigh
        have hcpow : c ^ (D - R - (t : ℕ) * T) ≤ c ^ D :=
          Nat.pow_le_pow_right (by omega) (by omega)
        exact Nat.mul_le_mul hbpow hcpow
      | inr idx => cases idx with
        | inl t =>
          have hhigh : R + (t : ℕ) * T ≤ E := by
            dsimp [E]
            have hm := Nat.mul_le_mul_right T (Nat.le_of_lt hi)
            omega
          dsimp [term, expo, eval3]
          simp only [mul_one]
          have hapow : a ^ (R + (t : ℕ) * T) ≤ c ^ (R + (t : ℕ) * T) :=
            Nat.pow_le_pow_left hacOrder _
          have hprod : a ^ (R + (t : ℕ) * T) *
              c ^ (D - R - (t : ℕ) * T) ≤ c ^ D := by
            calc
              _ ≤ c ^ (R + (t : ℕ) * T) *
                  c ^ (D - R - (t : ℕ) * T) :=
                Nat.mul_le_mul_right _ hapow
              _ = c ^ D := by rw [← pow_add]; congr 1; omega
          exact hprod.trans (Nat.le_mul_of_pos_left _ (pow_pos (by omega) E))
        | inr t =>
          have hhigh : R + (t : ℕ) * T ≤ E := by
            dsimp [E]
            have hm := Nat.mul_le_mul_right T (Nat.le_of_lt hi)
            omega
          dsimp [term, expo, eval3]
          simp only [mul_one]
          have hapow : a ^ (D - R - (t : ℕ) * T) ≤
              c ^ (D - R - (t : ℕ) * T) := Nat.pow_le_pow_left hacOrder _
          have hbpow := Nat.pow_le_pow_right (by omega : 0 < b) hhigh
          calc
            a ^ (D - R - (t : ℕ) * T) * b ^ (R + (t : ℕ) * T) ≤
                c ^ D * b ^ E := Nat.mul_le_mul
                  (hapow.trans (Nat.pow_le_pow_right (by omega) (by omega))) hbpow
            _ = b ^ E * c ^ D := by ac_rfl
    have hsumBound := Finset.sum_le_card_nsmul s id (b ^ E * c ^ D)
      (by simpa only [id_eq] using htermBound)
    calc
      s.sum id ≤ s.card * (b ^ E * c ^ D) := by simpa using hsumBound
      _ ≤ (3 * d) * (b ^ E * c ^ D) :=
        Nat.mul_le_mul_right _ hcard
      _ = C * c ^ D := by dsimp [C]; ring

/-- Multiply every member of a finite set by a common factor. -/
def scaleFinset (a : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.image (fun x => a * x)

private theorem scaleFinset_injOn {a : ℕ} (ha : 0 < a) (s : Finset ℕ) :
    Set.InjOn (fun x : ℕ => a * x) (s : Set ℕ) := by
  intro x _hx y _hy hxy
  exact Nat.eq_of_mul_eq_mul_left ha hxy

/-- Core gluing lemma for the Erdős--Lewin induction. A primitive old
representation may be scaled by `a` and joined to a primitive correction set,
provided every old term is smaller than every correction term and correction
terms are coprime to `a`. -/
theorem isPrimitive_scaleFinset_union {a : ℕ} {s t : Finset ℕ}
    (ha : 1 < a)
    (hsPos : ∀ x ∈ s, 0 < x)
    (hsPrimitive : IsPrimitive s)
    (htPrimitive : IsPrimitive t)
    (htCoprime : ∀ y ∈ t, Nat.Coprime a y)
    (hsep : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    IsPrimitive (scaleFinset a s ∪ t) := by
  intro z hz w hw hzw hdvd
  rcases Finset.mem_union.mp hz with hzs | hzt
  · rcases Finset.mem_image.mp hzs with ⟨x, hx, rfl⟩
    rcases Finset.mem_union.mp hw with hws | hwt
    · rcases Finset.mem_image.mp hws with ⟨y, hy, rfl⟩
      apply hsPrimitive hx hy
      · intro hxy
        subst y
        exact hzw rfl
      · exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < a)).mp hdvd
    · have haDiv : a ∣ w := (dvd_mul_right a x).trans hdvd
      have haOne := (htCoprime w hwt).eq_one_of_dvd haDiv
      omega
  · rcases Finset.mem_union.mp hw with hws | hwt
    · rcases Finset.mem_image.mp hws with ⟨y, hy, rfl⟩
      have hzDivY : z ∣ y := (htCoprime z hzt).symm.dvd_of_dvd_mul_left hdvd
      have hzLeY : z ≤ y := Nat.le_of_dvd (hsPos y hy) hzDivY
      exact (Nat.not_lt_of_ge hzLeY) (hsep y hy z hzt)
    · exact htPrimitive hzt hwt hzw hdvd

/-- The scaled old set and a coprime correction set are disjoint. -/
theorem disjoint_scaleFinset_correction {a : ℕ} {s t : Finset ℕ}
    (ha : 1 < a) (htCoprime : ∀ y ∈ t, Nat.Coprime a y) :
    Disjoint (scaleFinset a s) t := by
  rw [Finset.disjoint_left]
  intro y hyScale hyT
  rcases Finset.mem_image.mp hyScale with ⟨x, _hx, rfl⟩
  have haDiv : a ∣ a * x := dvd_mul_right a x
  have haOne := (htCoprime (a * x) hyT).eq_one_of_dvd haDiv
  omega

/-- Exact sum formula for adjoining a correction set after scaling. -/
theorem sum_scaleFinset_union {a : ℕ} {s t : Finset ℕ}
    (ha : 1 < a) (htCoprime : ∀ y ∈ t, Nat.Coprime a y) :
    (scaleFinset a s ∪ t).sum id = a * s.sum id + t.sum id := by
  rw [Finset.sum_union (disjoint_scaleFinset_correction ha htCoprime)]
  congr 1
  unfold scaleFinset
  rw [Finset.sum_image (scaleFinset_injOn (by omega) s)]
  simpa only [id_eq] using (Finset.mul_sum s id a).symm

/-- A geometric grid between `q*a^R` and `q*c^R` has a point immediately
below any target in that interval.  The second inequality is the useful
multiplicative lower bound on that point. -/
theorem exists_geometric_grid_point {a c q R T : ℕ}
    (_ha : 0 < a) (hac : a < c) (_hq : 0 < q)
    (hlo : q * a ^ R ≤ T) (hhi : T ≤ q * c ^ R) :
    ∃ k : ℕ, k ≤ R ∧
      q * a ^ (R - k) * c ^ k ≤ T ∧
      a * T ≤ c * (q * a ^ (R - k) * c ^ k) := by
  let good : Finset ℕ := (Finset.range (R + 1)).filter
    (fun k => q * a ^ (R - k) * c ^ k ≤ T)
  have hgood : good.Nonempty := by
    refine ⟨0, ?_⟩
    simp [good, hlo]
  let k := good.max' hgood
  have hkmem : k ∈ good := Finset.max'_mem good hgood
  have hkR : k ≤ R := by
    have := (Finset.mem_filter.mp hkmem).1
    simp only [Finset.mem_range] at this
    omega
  have hklo : q * a ^ (R - k) * c ^ k ≤ T :=
    (Finset.mem_filter.mp hkmem).2
  refine ⟨k, hkR, hklo, ?_⟩
  by_cases hk : k = R
  · have hklo' : q * c ^ R ≤ T := by rw [hk] at hklo; simpa using hklo
    have hEq : T = q * c ^ R := by omega
    rw [hEq, hk]
    simp only [Nat.sub_self, pow_zero, mul_one]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt hac)
  · have hklt : k < R := by omega
    have hnextRange : k + 1 ∈ Finset.range (R + 1) := by simp; omega
    have hnextNot : ¬q * a ^ (R - (k + 1)) * c ^ (k + 1) ≤ T := by
      intro hle
      have hnextGood : k + 1 ∈ good := Finset.mem_filter.mpr ⟨hnextRange, hle⟩
      have hmax := Finset.le_max' good (k + 1) hnextGood
      omega
    have hnext : T < q * a ^ (R - (k + 1)) * c ^ (k + 1) := by omega
    have hsub : R - k = (R - (k + 1)) + 1 := by omega
    calc
      a * T ≤ a * (q * a ^ (R - (k + 1)) * c ^ (k + 1)) :=
        Nat.mul_le_mul_left a hnext.le
      _ = c * (q * a ^ (R - k) * c ^ k) := by
        rw [hsub, pow_succ, pow_succ]
        ring

/-- A long explicit strip of one homogeneous exponent level lies in a fixed
multiplicative window around the interior ray `(b^u c^v)^M`.  The strip is
placed beyond a prescribed `b`-exponent cutoff `H` and all its terms are strict
interior terms after one common `abc` shift. -/
theorem exists_long_interior_shell {a b c u v δ M H : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hacLt : a < c) (hcb : c < b)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (_hu : 0 < u) (hv : 0 < v)
    (hHM : H + 2 ≤ M)
    (hdom : a ^ δ * (b * a ^ v) ^ M ≤ (c ^ v) ^ M) :
    let G := u + v
    let B := b ^ u * c ^ v
    let X := a * b * c * B ^ M
    ∃ p : Finset ℕ,
      M - (H + 2) + 1 ≤ p.card ∧
      (∀ z ∈ p, ∃ i j k : ℕ,
        0 < i ∧ 0 < j ∧ 0 < k ∧
        i + j + k = δ + G * M + 3 ∧
        u * M + H + 2 < j ∧
        z = eval3 a b c i j k) ∧
      (∀ z ∈ p, z ∈ Smooth3 a b c) ∧
      IsPrimitive p ∧
      (∀ z ∈ p, z ≤ X ∧ a * X ≤ c * z) := by
  dsimp only
  let G := u + v
  let B := b ^ u * c ^ v
  let X := a * b * c * B ^ M
  let J : Finset ℕ := Finset.Icc (H + 2) M
  have hR (s : ℕ) (hs : s ∈ J) : s ≤ v * M + δ := by
    have hsM : s ≤ M := (Finset.mem_Icc.mp hs).2
    have hvM : M ≤ v * M := by
      simpa only [one_mul] using Nat.mul_le_mul_right M (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hv))
    omega
  have hlow (s : ℕ) (hs : s ∈ J) :
      b ^ s * a ^ (v * M + δ - s) ≤ c ^ (v * M) := by
    have hsM : s ≤ M := (Finset.mem_Icc.mp hs).2
    have hbpow : b ^ s ≤ b ^ M := Nat.pow_le_pow_right (by omega) hsM
    have hapow : a ^ (v * M + δ - s) ≤ a ^ (v * M + δ) :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    calc
      b ^ s * a ^ (v * M + δ - s) ≤ b ^ M * a ^ (v * M + δ) :=
        Nat.mul_le_mul hbpow hapow
      _ = a ^ δ * (b * a ^ v) ^ M := by
        simp only [mul_pow, pow_mul, pow_add]
        ring
      _ ≤ (c ^ v) ^ M := hdom
      _ = c ^ (v * M) := by rw [pow_mul]
  have hhigh (s : ℕ) (hs : s ∈ J) :
      c ^ (v * M) ≤ b ^ s * c ^ (v * M + δ - s) := by
    have hsR := hR s hs
    have hcs : c ^ s ≤ b ^ s := Nat.pow_le_pow_left hcb.le _
    have hsplit : s + (v * M + δ - s) = v * M + δ := by omega
    calc
      c ^ (v * M) ≤ c ^ (v * M + δ) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ = c ^ s * c ^ (v * M + δ - s) := by rw [← pow_add, hsplit]
      _ ≤ b ^ s * c ^ (v * M + δ - s) :=
        Nat.mul_le_mul_right _ hcs
  let JS := {s : ℕ // s ∈ J}
  have hex (s : JS) : ∃ k : ℕ,
      k ≤ v * M + δ - s.1 ∧
      b ^ s.1 * a ^ (v * M + δ - s.1 - k) * c ^ k ≤ c ^ (v * M) ∧
      a * c ^ (v * M) ≤
        c * (b ^ s.1 * a ^ (v * M + δ - s.1 - k) * c ^ k) := by
    exact exists_geometric_grid_point (a := a) (c := c) (q := b ^ s.1)
      (R := v * M + δ - s.1) (T := c ^ (v * M))
      (by omega) hacLt (pow_pos (by omega) _) (hlow s.1 s.2) (hhigh s.1 s.2)
  let kval (s : JS) : ℕ := Classical.choose (hex s)
  have hkval (s : JS) := Classical.choose_spec (hex s)
  let term (s : JS) : ℕ :=
    eval3 a b c
      (v * M + δ - s.1 - kval s + 1)
      (u * M + s.1 + 1)
      (kval s + 1)
  let p : Finset ℕ := J.attach.image term
  have hterm_inj : Function.Injective term := by
    intro s t hst
    have hdvd : term s ∣ term t := by rw [hst]
    have hcoord := (eval3_dvd_iff ha hb hc hab hac hbc).mp hdvd
    have hdvd' : term t ∣ term s := by rw [hst]
    have hcoord' := (eval3_dvd_iff ha hb hc hab hac hbc).mp hdvd'
    apply Subtype.ext
    omega
  have hdegree (s : JS) :
      (v * M + δ - s.1 - kval s + 1) + (u * M + s.1 + 1) +
        (kval s + 1) = δ + G * M + 3 := by
    have hk := (hkval s).1
    have hsR := hR s.1 s.2
    have hsub1 : (v * M + δ - s.1 - kval s) + kval s =
        v * M + δ - s.1 := Nat.sub_add_cancel hk
    have hsub2 : (v * M + δ - s.1) + s.1 = v * M + δ :=
      Nat.sub_add_cancel hsR
    have hGM : G * M = u * M + v * M := by
      dsimp [G]
      rw [Nat.add_mul]
    rw [hGM]
    omega
  have hterm_value (s : JS) : term s =
      (a * b * c * b ^ (u * M)) *
        (b ^ s.1 * a ^ (v * M + δ - s.1 - kval s) * c ^ (kval s)) := by
    dsimp [term, eval3]
    rw [pow_succ, pow_succ, pow_succ, pow_add]
    ring
  have hX_value : X =
      (a * b * c * b ^ (u * M)) * c ^ (v * M) := by
    dsimp [X, B]
    simp only [mul_pow, pow_mul]
    ring
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · have hcard : p.card = J.card := by
      dsimp [p]
      rw [Finset.card_image_iff.mpr]
      · exact Finset.card_attach
      · intro s _hs t _ht hst
        exact hterm_inj hst
    rw [hcard]
    simp [J]
    omega
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, _hs, rfl⟩
    have hslo : H + 2 ≤ s.1 := (Finset.mem_Icc.mp s.2).1
    refine ⟨v * M + δ - s.1 - kval s + 1,
      u * M + s.1 + 1, kval s + 1,
      by omega, by omega, by omega, hdegree s, by omega, rfl⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, _hs, rfl⟩
    exact ⟨v * M + δ - s.1 - kval s + 1,
      u * M + s.1 + 1, kval s + 1, rfl⟩
  · intro x hx y hy hxy hdvd
    rcases Finset.mem_image.mp hx with ⟨s, _hs, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨t, _ht, rfl⟩
    apply hxy
    have he := exponents_eq_of_eval3_dvd_of_degree_eq ha hb hc hab hac hbc hdvd
      ((hdegree s).trans (hdegree t).symm)
    simp only [term]
    rw [he.1, he.2.1, he.2.2]
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, _hs, rfl⟩
    have hks := hkval s
    constructor
    · change term s ≤ X
      rw [hterm_value, hX_value]
      exact Nat.mul_le_mul_left _ hks.2.1
    · change a * X ≤ c * term s
      rw [hterm_value, hX_value]
      have hmul := Nat.mul_le_mul_left (a * b * c * b ^ (u * M)) hks.2.2
      convert hmul using 1 <;> ring

/-- Positive powers of coprime nontrivial natural numbers cannot coincide. -/
theorem coprime_pow_ne_pow {b c p q : ℕ}
    (hb : 1 < b) (hbc : Nat.Coprime b c) (hp : 0 < p) (_hq : 0 < q) :
    b ^ p ≠ c ^ q := by
  intro heq
  have hbDiv : b ∣ c ^ q := by
    rw [← heq]
    exact dvd_pow_self b (by omega)
  have hbOne := (hbc.pow_right q).eq_one_of_dvd hbDiv
  omega

/-- The logarithms of coprime nontrivial integers have irrational ratio. -/
theorem irrational_log_ratio {b c : ℕ}
    (hb : 1 < b) (hc : 1 < c) (hbc : Nat.Coprime b c) :
    Irrational (Real.log (b : ℝ) / Real.log (c : ℝ)) := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hlogc : 0 < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast hc)
  have hrPosReal : (0 : ℝ) < (r : ℝ) := by
    rw [hr]
    positivity
  have hrPos : (0 : ℚ) < r := Rat.cast_pos.mp hrPosReal
  have hnumPos : 0 < r.num := Rat.num_pos.mpr hrPos
  let p : ℕ := r.num.toNat
  let q : ℕ := r.den
  have hpPos : 0 < p := by
    dsimp [p]
    omega
  have hqPos : 0 < q := by
    exact r.den_pos
  have hpCast : ((p : ℕ) : ℝ) = (r.num : ℝ) := by
    have hnumNonneg : 0 ≤ r.num := by omega
    have hpInt : (p : ℤ) = r.num := by
      exact Int.toNat_of_nonneg hnumNonneg
    exact_mod_cast hpInt
  have hratio : Real.log (b : ℝ) / Real.log (c : ℝ) =
      (p : ℝ) / (q : ℝ) := by
    rw [← hr]
    rw [Rat.cast_def]
    simp only [q, hpCast]
  have hlogs : (q : ℝ) * Real.log (b : ℝ) =
      (p : ℝ) * Real.log (c : ℝ) := by
    field_simp [ne_of_gt hlogc, ne_of_gt (show (0 : ℝ) < q by exact_mod_cast hqPos)] at hratio
    nlinarith
  have hlogPowers : Real.log ((b : ℝ) ^ q) = Real.log ((c : ℝ) ^ p) := by
    rw [Real.log_pow, Real.log_pow]
    exact hlogs
  have hpowersReal : (b : ℝ) ^ q = (c : ℝ) ^ p := by
    apply Real.log_injOn_pos
    · exact pow_pos (show (0 : ℝ) < (b : ℝ) by exact_mod_cast (show 0 < b by omega)) q
    · exact pow_pos (show (0 : ℝ) < (c : ℝ) by exact_mod_cast (show 0 < c by omega)) p
    · exact hlogPowers
  have hpowersNat : b ^ q = c ^ p := by exact_mod_cast hpowersReal
  exact coprime_pow_ne_pow hb hbc hqPos hpPos hpowersNat

/-- Integer linear combinations of the two logarithms occur in every positive
neighborhood of zero. -/
theorem exists_small_positive_log_combination {b c : ℕ}
    (hb : 1 < b) (hc : 1 < c) (hbc : Nat.Coprime b c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m n : ℤ, 0 < m • Real.log (b : ℝ) + n • Real.log (c : ℝ) ∧
      m • Real.log (b : ℝ) + n • Real.log (c : ℝ) < ε := by
  have hirr := irrational_log_ratio hb hc hbc
  have hdense : Dense (AddSubgroup.closure
      ({Real.log (b : ℝ), Real.log (c : ℝ)} : Set ℝ) : Set ℝ) :=
    (dense_addSubgroupClosure_pair_iff).mpr hirr
  rcases hdense.exists_between hε with ⟨z, hz, hz0, hzε⟩
  rcases AddSubgroup.mem_closure_pair.mp hz with ⟨m, n, rfl⟩
  exact ⟨m, n, hz0, hzε⟩

/-- There are positive powers of `b` and `c` whose logarithms differ, in
one orientation or the other, by any prescribed positive amount. -/
theorem exists_close_power_logs {b c : ℕ}
    (hb : 1 < b) (hc : 1 < c) (hbc : Nat.Coprime b c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      ((0 < (p : ℝ) * Real.log (b : ℝ) - (q : ℝ) * Real.log (c : ℝ) ∧
          (p : ℝ) * Real.log (b : ℝ) - (q : ℝ) * Real.log (c : ℝ) < ε) ∨
       (0 < (q : ℝ) * Real.log (c : ℝ) - (p : ℝ) * Real.log (b : ℝ) ∧
          (q : ℝ) * Real.log (c : ℝ) - (p : ℝ) * Real.log (b : ℝ) < ε)) := by
  have hlb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hlc : 0 < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast hc)
  let δ : ℝ := min ε (min (Real.log (b : ℝ)) (Real.log (c : ℝ)))
  have hδ : 0 < δ := by simp [δ, hε, hlb, hlc]
  have hδε : δ ≤ ε := min_le_left _ _
  have hδb : δ ≤ Real.log (b : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ ≤ Real.log (c : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
  rcases exists_small_positive_log_combination hb hc hbc hδ with
    ⟨m, n, hz0, hzδ⟩
  simp only [zsmul_eq_mul] at hz0 hzδ
  have hzε : (m : ℝ) * Real.log (b : ℝ) + (n : ℝ) * Real.log (c : ℝ) < ε :=
    hzδ.trans_le hδε
  rcases lt_trichotomy m 0 with hmneg | rfl | hmpos
  · rcases lt_trichotomy n 0 with hnneg | rfl | hnpos
    · have hmle : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ (-1 : ℤ) by omega)
      have hnle : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ (-1 : ℤ) by omega)
      nlinarith
    · simp only [Int.cast_zero, zero_mul, add_zero] at hz0
      have hmle : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ (-1 : ℤ) by omega)
      nlinarith
    · let p : ℕ := (-m).toNat
      let q : ℕ := n.toNat
      have hpInt : (p : ℤ) = -m := by
        exact Int.toNat_of_nonneg (by omega)
      have hqInt : (q : ℤ) = n := by
        exact Int.toNat_of_nonneg (by omega)
      have hpReal : (p : ℝ) = -(m : ℝ) := by exact_mod_cast hpInt
      have hqReal : (q : ℝ) = (n : ℝ) := by exact_mod_cast hqInt
      refine ⟨p, q, ?_, ?_, Or.inr ?_⟩
      · dsimp [p]
        omega
      · dsimp [q]
        omega
      · rw [hpReal, hqReal]
        constructor <;> nlinarith
  · rcases lt_trichotomy n 0 with hnneg | rfl | hnpos
    · simp only [Int.cast_zero, zero_mul, zero_add] at hz0
      have hnle : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ (-1 : ℤ) by omega)
      nlinarith
    · norm_num at hz0
    · simp only [Int.cast_zero, zero_mul, zero_add] at hzδ
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
      nlinarith
  · rcases lt_trichotomy n 0 with hnneg | rfl | hnpos
    · let p : ℕ := m.toNat
      let q : ℕ := (-n).toNat
      have hpInt : (p : ℤ) = m := by
        exact Int.toNat_of_nonneg (by omega)
      have hqInt : (q : ℤ) = -n := by
        exact Int.toNat_of_nonneg (by omega)
      have hpReal : (p : ℝ) = (m : ℝ) := by exact_mod_cast hpInt
      have hqReal : (q : ℝ) = -(n : ℝ) := by exact_mod_cast hqInt
      refine ⟨p, q, ?_, ?_, Or.inl ?_⟩
      · dsimp [p]
        omega
      · dsimp [q]
        omega
      · rw [hpReal, hqReal]
        constructor <;> nlinarith
    · simp only [Int.cast_zero, zero_mul, add_zero] at hzδ
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
      nlinarith
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
      nlinarith

/-- The multiplicative semigroup generated by two coprime nontrivial integers
is asymptotically dense on every fixed multiplicative scale: every sufficiently
large `x` has a semigroup point in `(x/ρ,x]`. -/
theorem smooth2_eventually_multiplicatively_leftDense
    {b c : ℕ} (hb : 1 < b) (hc : 1 < c) (hbc : Nat.Coprime b c)
    {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ Y : ℝ, ∀ x : ℝ, Y ≤ x →
      ∃ u v : ℕ, x / ρ < (b : ℝ) ^ u * (c : ℝ) ^ v ∧
        (b : ℝ) ^ u * (c : ℝ) ^ v ≤ x := by
  have hlb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hlc : 0 < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast hc)
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (show 0 < c by omega)
  have hρpos : 0 < ρ := by linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  rcases exists_close_power_logs hb hc hbc hlogρ with
    ⟨p, q, hp, hq, hdir | hdir⟩
  · let d : ℝ := (p : ℝ) * Real.log (b : ℝ) - (q : ℝ) * Real.log (c : ℝ)
    have hd : d = (p : ℝ) * Real.log (b : ℝ) - (q : ℝ) * Real.log (c : ℝ) := rfl
    rcases additiveSemigroup_eventually_leftDense hlb hlc hp hq hd hdir.1 hdir.2 with
      ⟨X, hX⟩
    refine ⟨Real.exp X, ?_⟩
    intro x hx
    have hxpos : 0 < x := (Real.exp_pos X).trans_le hx
    have hXlog : X ≤ Real.log x := by
      apply Real.exp_le_exp.mp
      simpa [Real.exp_log hxpos] using hx
    rcases hX (Real.log x) hXlog with ⟨u, v, huvLower, huvUpper⟩
    refine ⟨u, v, ?_, ?_⟩
    · have he := Real.exp_lt_exp.mpr huvLower
      simpa [Real.exp_sub, Real.exp_log hxpos, Real.exp_log hρpos,
        Real.exp_add, Real.exp_nat_mul, Real.exp_log hbpos,
        Real.exp_log hcpos] using he
    · have he := Real.exp_le_exp.mpr huvUpper
      simpa [Real.exp_add, Real.exp_nat_mul, Real.exp_log hbpos,
        Real.exp_log hcpos, Real.exp_log hxpos] using he
  · let d : ℝ := (q : ℝ) * Real.log (c : ℝ) - (p : ℝ) * Real.log (b : ℝ)
    have hd : d = (q : ℝ) * Real.log (c : ℝ) - (p : ℝ) * Real.log (b : ℝ) := rfl
    rcases additiveSemigroup_eventually_leftDense hlc hlb hq hp hd hdir.1 hdir.2 with
      ⟨X, hX⟩
    refine ⟨Real.exp X, ?_⟩
    intro x hx
    have hxpos : 0 < x := (Real.exp_pos X).trans_le hx
    have hXlog : X ≤ Real.log x := by
      apply Real.exp_le_exp.mp
      simpa [Real.exp_log hxpos] using hx
    rcases hX (Real.log x) hXlog with ⟨v, u, huvLower, huvUpper⟩
    refine ⟨u, v, ?_, ?_⟩
    · have he := Real.exp_lt_exp.mpr huvLower
      simpa [Real.exp_sub, Real.exp_log hxpos, Real.exp_log hρpos,
        Real.exp_add, Real.exp_nat_mul, Real.exp_log hbpos,
        Real.exp_log hcpos, add_comm] using he
    · have he := Real.exp_le_exp.mpr huvUpper
      simpa [Real.exp_add, Real.exp_nat_mul, Real.exp_log hbpos,
        Real.exp_log hcpos, Real.exp_log hxpos, add_comm] using he

/-- A power of a larger natural base eventually dominates any fixed multiple
of the corresponding power of a smaller base. -/
theorem eventually_const_mul_pow_le_pow {x y C : ℕ} (hxy : x < y) :
    ∃ N : ℕ, ∀ n, N ≤ n → C * x ^ n ≤ y ^ n := by
  have hreal : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hlt : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  have ho := isLittleO_pow_pow_of_lt_left hreal hlt
  have hcpos : (0 : ℝ) < ((C + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hev := ho.bound hcpos
  rw [eventually_atTop] at hev
  rcases hev with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hh := hN n hn
  simp only [Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ x),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ y)] at hh
  have hmult : (((C + 1 : ℕ) : ℝ) * (x : ℝ) ^ n) ≤ (y : ℝ) ^ n := by
    have hcp : (0 : ℝ) < ((C + 1 : ℕ) : ℝ) := by positivity
    calc
      (((C + 1 : ℕ) : ℝ) * (x : ℝ) ^ n)
          ≤ ((C + 1 : ℕ) : ℝ) *
              (((C + 1 : ℕ) : ℝ)⁻¹ * (y : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left hh hcp.le
      _ = (y : ℝ) ^ n := by field_simp
  have hC : (((C : ℕ) : ℝ) * (x : ℝ) ^ n) ≤ (y : ℝ) ^ n := by
    apply le_trans _ hmult
    gcongr
    norm_num
  exact_mod_cast hC

/-- If `a<c`, one can choose a positive exponent for which the `c` power
beats an arbitrarily prescribed multiple of the `a` power. -/
theorem exists_positive_pow_multiple_le {a c K : ℕ} (hac : a < c) :
    ∃ v : ℕ, 0 < v ∧ K * a ^ v ≤ c ^ v := by
  rcases eventually_const_mul_pow_le_pow (C := K) hac with ⟨N, hN⟩
  let v := max N 1
  exact ⟨v, by dsimp [v]; omega, hN v (by dsimp [v]; omega)⟩

/-- Evaluation of a position-dependent digit code in ordinary radix `q`.
The actual digit selected at position `i` may be much larger than `q`; only its
residue will matter below. -/
def radixEval {q n : ℕ} (digit : Fin n → Fin q → ℕ)
    (word : Fin n → Fin q) : ℕ :=
  ∑ i : Fin n, q ^ (i : ℕ) * digit i (word i)

private theorem radixEval_succ {q n : ℕ}
    (digit : Fin (n + 1) → Fin q → ℕ)
    (word : Fin (n + 1) → Fin q) :
    radixEval digit word = digit 0 (word 0) +
      q * radixEval (fun i => digit i.succ) (fun i => word i.succ) := by
  rw [radixEval, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul]
  congr 1
  rw [radixEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Fin.val_succ, pow_succ]
  ac_rfl

/-- If each position's actual digits have pairwise distinct residues modulo
`q`, then radix evaluation is injective modulo `q^n`. This remains true even
when the actual digits are large and position-dependent. -/
theorem radixEval_mod_injective {q n : ℕ} (hq : 1 < q)
    (digit : Fin n → Fin q → ℕ)
    (hdigit : ∀ i, Function.Injective (fun r => digit i r % q)) :
    Function.Injective (fun word : Fin n → Fin q => radixEval digit word % q ^ n) := by
  induction n with
  | zero =>
      intro x y _h
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro x y hxy
      have hmod : radixEval digit x ≡ radixEval digit y [MOD q ^ (n + 1)] := hxy
      have hmodq : radixEval digit x ≡ radixEval digit y [MOD q] :=
        hmod.of_dvd (by exact dvd_pow_self q (by omega : n + 1 ≠ 0))
      rw [radixEval_succ, radixEval_succ] at hmodq
      have hheadResidue : digit 0 (x 0) % q = digit 0 (y 0) % q := by
        simpa [Nat.ModEq] using hmodq
      have hhead : x 0 = y 0 := hdigit 0 hheadResidue
      have htailMod :
          radixEval (fun (i : Fin n) => digit i.succ)
              (fun (i : Fin n) => x i.succ) ≡
            radixEval (fun (i : Fin n) => digit i.succ)
              (fun (i : Fin n) => y i.succ) [MOD q ^ n] := by
        rw [radixEval_succ, radixEval_succ, hhead] at hmod
        have hcancelAdd :
            q * radixEval (fun (i : Fin n) => digit i.succ)
                (fun (i : Fin n) => x i.succ) ≡
              q * radixEval (fun (i : Fin n) => digit i.succ)
                (fun (i : Fin n) => y i.succ) [MOD q ^ (n + 1)] :=
          Nat.ModEq.add_left_cancel
            (Nat.ModEq.refl (digit 0 (y 0))) hmod
        have hpow : q ^ (n + 1) = q * q ^ n := by simp [pow_succ, Nat.mul_comm]
        rw [hpow] at hcancelAdd
        exact Nat.ModEq.mul_left_cancel' (by omega : q ≠ 0) hcancelAdd
      have htailEq : (fun (i : Fin n) => x i.succ) =
          (fun (i : Fin n) => y i.succ) := by
        apply ih (fun (i : Fin n) => digit i.succ)
          (fun (i : Fin n) => hdigit i.succ)
        exact htailMod
      funext i
      refine Fin.cases hhead ?_ i
      intro j
      exact congrFun htailEq j

/-- Number of edge degrees reserved for a block of `c-1` equal-residue terms. -/
def edgeDigitDepth (c : ℕ) : ℕ := c.totient * (c - 2)

/-- The `t`-th reserved term on the `a,b` edge of homogeneous degree `E`.
For `E ≥ edgeDigitDepth c` and `t<c-1`, its two exponents sum to `E`. -/
def edgeDigitTerm (a b c E t : ℕ) : ℕ :=
  a ^ (E - edgeDigitDepth c) * correctionTerm c a b (c - 1) t

/-- Nested subset digit: choose the first `r` terms of the reserved edge block. -/
def edgeDigit (a b c E r : ℕ) : ℕ :=
  (Finset.range r).sum (edgeDigitTerm a b c E)

/-- Every reserved edge term has the same unit residue modulo `c`. -/
theorem edgeDigitTerm_modEq {a b c E t : ℕ}
    (hca : Nat.Coprime c a) (hcb : Nat.Coprime c b) :
    edgeDigitTerm a b c E t ≡ a ^ (E - edgeDigitDepth c) [MOD c] := by
  have h := correctionTerm_modEq_one (r := c - 1) (t := t) hca hcb
  simpa [edgeDigitTerm] using h.mul_left (a ^ (E - edgeDigitDepth c))

/-- A nested digit of length `r` is congruent to `r` times the common edge
unit. -/
theorem edgeDigit_modEq {a b c E r : ℕ}
    (hca : Nat.Coprime c a) (hcb : Nat.Coprime c b) :
    edgeDigit a b c E r ≡ r * a ^ (E - edgeDigitDepth c) [MOD c] := by
  have hsum :
      (Finset.range r).sum (edgeDigitTerm a b c E) ≡
        (Finset.range r).sum
          (fun _t => a ^ (E - edgeDigitDepth c)) [MOD c] :=
    Nat.ModEq.sum (fun t _ht => edgeDigitTerm_modEq hca hcb)
  simpa [edgeDigit] using hsum

/-- The `c` nested edge digits have pairwise distinct residues modulo `c`.
Thus they can serve as one position of the radix code in F-018. -/
theorem edgeDigit_residue_injective {a b c E : ℕ} (_hc : 1 < c)
    (hca : Nat.Coprime c a) (hcb : Nat.Coprime c b) :
    Function.Injective (fun r : Fin c => edgeDigit a b c E r % c) := by
  intro r s hrs
  have hrsMod : edgeDigit a b c E r ≡ edgeDigit a b c E s [MOD c] := hrs
  have hr := edgeDigit_modEq (E := E) (r := (r : ℕ)) hca hcb
  have hs := edgeDigit_modEq (E := E) (r := (s : ℕ)) hca hcb
  have hmul :
      a ^ (E - edgeDigitDepth c) * (r : ℕ) ≡
        a ^ (E - edgeDigitDepth c) * (s : ℕ) [MOD c] := by
    simpa [Nat.mul_comm] using hr.symm.trans (hrsMod.trans hs)
  have hcop : Nat.Coprime c (a ^ (E - edgeDigitDepth c)) :=
    hca.pow_right _
  have hrs' : (r : ℕ) ≡ (s : ℕ) [MOD c] :=
    Nat.ModEq.cancel_left_of_coprime hcop hmul
  apply Fin.ext
  exact Nat.ModEq.eq_of_lt_of_lt hrs' r.isLt s.isLt

/-- The reserved edge term really lies on homogeneous degree `E`. -/
theorem edgeDigitTerm_exponent_sum {c E t : ℕ}
    (hE : edgeDigitDepth c ≤ E) (ht : t < c - 1) :
    (E - edgeDigitDepth c + c.totient * t) +
        c.totient * (c - 1 - 1 - t) = E := by
  have ht' : t ≤ c - 2 := by omega
  have hsplit : t + (c - 2 - t) = c - 2 := by omega
  have hmul : c.totient * t + c.totient * (c - 2 - t) =
      c.totient * (c - 2) := by
    rw [← Nat.mul_add, hsplit]
  have hcsub : c - 1 - 1 - t = c - 2 - t := by omega
  simp only [edgeDigitDepth] at hE ⊢
  rw [hcsub, add_assoc, hmul]
  exact Nat.sub_add_cancel hE

/-- Degree of the `a,b` edge paired with c-adic position `i`. -/
def edgeCodeDegree (c n : ℕ) (i : Fin n) : ℕ :=
  edgeDigitDepth c + (n - 1 - (i : ℕ))

/-- Numeric evaluation of the nested edge choices in `n` consecutive c-adic
layers of one homogeneous level. -/
def edgeCodeEval (a b c n : ℕ) (word : Fin n → Fin c) : ℕ :=
  radixEval (fun i r =>
    edgeDigit a b c (edgeCodeDegree c n i) (r : ℕ)) word

/-- The `c^n` edge-choice words give pairwise distinct residues modulo `c^n`.
This is the promised complete-residue subsystem inside consecutive layers of a
homogeneous level. -/
theorem edgeCodeEval_mod_injective {a b c n : ℕ} (hc : 1 < c)
    (hca : Nat.Coprime c a) (hcb : Nat.Coprime c b) :
    Function.Injective
      (fun word : Fin n → Fin c => edgeCodeEval a b c n word % c ^ n) := by
  unfold edgeCodeEval
  apply radixEval_mod_injective hc
  intro i
  exact edgeDigit_residue_injective hc hca hcb

/-- Every term used at c-adic position `i` has total three-variable exponent
`edgeDigitDepth c + n - 1`, independent of `i` and of the nested-digit index. -/
theorem edgeCodeTerm_total_degree {c n : ℕ} (i : Fin n) {t : ℕ}
    (ht : t < c - 1) :
    ((edgeCodeDegree c n i - edgeDigitDepth c + c.totient * t) +
      c.totient * (c - 1 - 1 - t)) + (i : ℕ) =
      edgeDigitDepth c + n - 1 := by
  have hi : (i : ℕ) ≤ n - 1 := by omega
  have hE : edgeDigitDepth c ≤ edgeCodeDegree c n i := by
    simp [edgeCodeDegree]
  rw [edgeDigitTerm_exponent_sum hE ht]
  simp only [edgeCodeDegree]
  omega

/-- Total value of the fixed `c-1`-term edge block before translating it to a
larger homogeneous degree. -/
def edgeDigitMass (a b c : ℕ) : ℕ :=
  (Finset.range (c - 1)).sum (correctionTerm c a b (c - 1))

/-- Every nested digit is bounded by the translated mass of the full reserved
edge block. -/
theorem edgeDigit_le_mass {a b c E r : ℕ} (hr : r ≤ c - 1) :
    edgeDigit a b c E r ≤
      a ^ (E - edgeDigitDepth c) * edgeDigitMass a b c := by
  have hsub : Finset.range r ⊆ Finset.range (c - 1) := by
    intro t ht
    simp only [Finset.mem_range] at ht ⊢
    omega
  have hsum := Finset.sum_le_sum_of_subset (f := correctionTerm c a b (c - 1)) hsub
  rw [edgeDigit, edgeDigitMass]
  simp only [edgeDigitTerm, ← Finset.mul_sum]
  exact Nat.mul_le_mul_left _ hsum

private theorem geom_edge_sum_le_pow {a c n : ℕ} (hac : a < c) :
    (Finset.range n).sum (fun i => c ^ i * a ^ (n - 1 - i)) ≤ c ^ n := by
  let S := (Finset.range n).sum (fun i => c ^ i * a ^ (n - 1 - i))
  have hgeom : S * (c - a) = c ^ n - a ^ n := by
    dsimp [S]
    exact geom_sum₂_mul_of_ge (Nat.le_of_lt hac) n
  have hfactor : 1 ≤ c - a := by omega
  have hSleMul : S ≤ S * (c - a) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left S hfactor
  rw [hgeom] at hSleMul
  exact hSleMul.trans (Nat.sub_le _ _)

/-- Uniform carry bound for the homogeneous edge radix code. Although it has
`c^n` different residue words, every evaluation is at most a fixed block mass
times `c^n`. -/
theorem edgeCodeEval_le_mass_mul_pow {a b c n : ℕ} (hac : a < c)
    (word : Fin n → Fin c) :
    edgeCodeEval a b c n word ≤ edgeDigitMass a b c * c ^ n := by
  rw [edgeCodeEval, radixEval]
  calc
    (∑ i : Fin n, c ^ (i : ℕ) *
        edgeDigit a b c (edgeCodeDegree c n i) (word i : ℕ))
        ≤ ∑ i : Fin n, c ^ (i : ℕ) *
          (a ^ (n - 1 - (i : ℕ)) * edgeDigitMass a b c) := by
            apply Finset.sum_le_sum
            intro i _hi
            apply Nat.mul_le_mul_left
            have hr : (word i : ℕ) ≤ c - 1 := by omega
            have h := edgeDigit_le_mass
              (a := a) (b := b) (c := c) (E := edgeCodeDegree c n i) hr
            have hdeg : edgeCodeDegree c n i - edgeDigitDepth c =
                n - 1 - (i : ℕ) := by
              simp [edgeCodeDegree]
            simpa [hdeg] using h
    _ = edgeDigitMass a b c *
        (∑ i : Fin n, c ^ (i : ℕ) * a ^ (n - 1 - (i : ℕ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          ac_rfl
    _ = edgeDigitMass a b c *
        (Finset.range n).sum (fun i => c ^ i * a ^ (n - 1 - i)) := by
          congr 1
          exact Fin.sum_univ_eq_sum_range
            (fun i : ℕ => c ^ i * a ^ (n - 1 - i)) n
    _ ≤ edgeDigitMass a b c * c ^ n :=
      Nat.mul_le_mul_left _ (geom_edge_sum_le_pow hac)
abbrev EdgeCodeIndex (_c n : ℕ) := Fin n × ℕ

/-- Exponent evaluation attached to one reserved code position. -/
def edgeCodeValue (a b c n : ℕ) (p : EdgeCodeIndex c n) : ℕ :=
  eval3 a b c
    (edgeCodeDegree c n p.1 - edgeDigitDepth c + c.totient * p.2)
    (c.totient * (c - 1 - 1 - p.2)) (p.1 : ℕ)

/-- Positions selected by a nested-digit word. -/
def edgeCodeIndexSet {c n : ℕ} (word : Fin n → Fin c) :
    Finset (EdgeCodeIndex c n) :=
  ((Finset.univ : Finset (Fin n)).product (Finset.range (c - 1))).filter
    (fun p => p.2 < (word p.1 : ℕ))

/-- The actual finite set of smooth integer terms selected by a code word. -/
def edgeCodeFinset (a b c n : ℕ) (word : Fin n → Fin c) : Finset ℕ :=
  (edgeCodeIndexSet word).image (edgeCodeValue a b c n)

private theorem edgeCodeValue_eq {a b c n : ℕ} (p : EdgeCodeIndex c n) :
    edgeCodeValue a b c n p =
      c ^ (p.1 : ℕ) * edgeDigitTerm a b c (edgeCodeDegree c n p.1) p.2 := by
  unfold edgeCodeValue eval3 edgeDigitTerm correctionTerm
  rw [pow_add]
  have hcsub : c - 1 - 1 - p.2 = c - 2 - p.2 := by omega
  rw [hcsub]
  ac_rfl

private theorem edgeCodeValue_degree {c n : ℕ} (p : EdgeCodeIndex c n)
    (hp : p.2 < c - 1) :
    (edgeCodeDegree c n p.1 - edgeDigitDepth c + c.totient * p.2) +
      c.totient * (c - 1 - 1 - p.2) + (p.1 : ℕ) =
        edgeDigitDepth c + n - 1 := by
  exact edgeCodeTerm_total_degree p.1 hp

private theorem edgeCodeValue_injective {a b c n : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    {p q : EdgeCodeIndex c n} (hp : p.2 < c - 1) (hq : q.2 < c - 1)
    (hpq : edgeCodeValue a b c n p = edgeCodeValue a b c n q) : p = q := by
  have hdiv : edgeCodeValue a b c n p ∣ edgeCodeValue a b c n q := by
    rw [hpq]
  have hexp := exponents_eq_of_eval3_dvd_of_degree_eq ha hb hc hab hac hbc hdiv
    (edgeCodeValue_degree p hp |>.trans (edgeCodeValue_degree q hq).symm)
  have hp1 : p.1 = q.1 := Fin.ext hexp.2.2
  have hmul : c.totient * p.2 = c.totient * q.2 := by
    have hdegree : edgeCodeDegree c n p.1 = edgeCodeDegree c n q.1 := by
      rw [hp1]
    omega
  have htot : 0 < c.totient := Nat.totient_pos.mpr (by omega)
  have hp2 : p.2 = q.2 := Nat.eq_of_mul_eq_mul_left htot hmul
  exact Prod.ext hp1 hp2

private theorem sum_range_if_lt {C r : ℕ} (hr : r ≤ C) (f : ℕ → ℕ) :
    (∑ t ∈ Finset.range C, if t < r then f t else 0) =
      ∑ t ∈ Finset.range r, f t := by
  calc
    (∑ t ∈ Finset.range C, if t < r then f t else 0) =
      ∑ t ∈ Finset.range r, if t < r then f t else 0 := by
        symm
        apply Finset.sum_subset
        · intro t ht
          simp only [Finset.mem_range] at ht ⊢
          omega
        · intro t htC htr
          simp only [Finset.mem_range] at htC htr
          simp [show ¬t < r by omega]
    _ = ∑ t ∈ Finset.range r, f t := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.mem_range] at ht
      simp [ht]

/-- Summing the actual finite set gives exactly the arithmetic radix evaluation
used in F-019. -/
theorem edgeCodeFinset_sum {a b c n : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (word : Fin n → Fin c) :
    (edgeCodeFinset a b c n word).sum id = edgeCodeEval a b c n word := by
  rw [edgeCodeFinset, Finset.sum_image]
  · rw [edgeCodeIndexSet, Finset.sum_filter]
    change (∑ p ∈ (Finset.univ : Finset (Fin n)).product (Finset.range (c - 1)),
      if p.2 < (word p.1 : ℕ) then edgeCodeValue a b c n p else 0) = _
    rw [show
      (∑ p ∈ (Finset.univ : Finset (Fin n)).product (Finset.range (c - 1)),
        if p.2 < (word p.1 : ℕ) then edgeCodeValue a b c n p else 0) =
      ∑ i : Fin n, ∑ t ∈ Finset.range (c - 1),
        if t < (word i : ℕ) then edgeCodeValue a b c n (i, t) else 0 by
          simpa using Finset.sum_product (Finset.univ : Finset (Fin n))
            (Finset.range (c - 1))
            (fun p => if p.2 < (word p.1 : ℕ) then
              edgeCodeValue a b c n p else 0)]
    rw [edgeCodeEval, radixEval]
    apply Finset.sum_congr rfl
    intro i _hi
    have hr : (word i : ℕ) ≤ c - 1 := by omega
    rw [sum_range_if_lt hr (fun t => edgeCodeValue a b c n (i, t))]
    rw [edgeDigit]
    calc
      (∑ t ∈ Finset.range (word i : ℕ), edgeCodeValue a b c n (i, t)) =
          ∑ t ∈ Finset.range (word i : ℕ),
            c ^ (i : ℕ) * edgeDigitTerm a b c (edgeCodeDegree c n i) t := by
              apply Finset.sum_congr rfl
              intro t _ht
              rw [edgeCodeValue_eq (p := (i, t))]
      _ = c ^ (i : ℕ) * (Finset.range (word i : ℕ)).sum
          (edgeDigitTerm a b c (edgeCodeDegree c n i)) := by
            rw [Finset.mul_sum]
  · intro p hp q hq hpq
    have hp' : p.2 < c - 1 := by
      exact Finset.mem_range.mp
        ((Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2)
    have hq' : q.2 < c - 1 := by
      exact Finset.mem_range.mp
        ((Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2)
    exact edgeCodeValue_injective ha hb hc hab hac hbc hp' hq' hpq

/-- The complete-residue edge code contains arithmetic progressions of every
prescribed finite length.  The progression occurs among actual evaluations,
not merely among their residues. -/
theorem edgeCodeEval_arbitrarily_long_progressions {a b c : ℕ}
    (_ha : 1 < a) (_hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (_hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (L : ℕ) (hL : 1 < L) :
    ∃ n B d : ℕ, 0 < d ∧
      ∃ words : Fin L → (Fin n → Fin c),
        ∀ r : Fin L,
          edgeCodeEval a b c n (words r) = B + (r : ℕ) * d := by
  let A := edgeDigitMass a b c
  rcases finite_van_der_waerden (A + 1) L hL with ⟨N, hN, hvdw⟩
  rcases pow_unbounded_of_one_lt N hc with ⟨n, hnStrict⟩
  have hn : N ≤ c ^ n := hnStrict.le
  let Q := c ^ n
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  let residueMap : (Fin n → Fin c) → Fin Q := fun w =>
    ⟨edgeCodeEval a b c n w % Q, Nat.mod_lt _ hQ⟩
  have hresInj : Function.Injective residueMap := by
    intro u v huv
    apply edgeCodeEval_mod_injective hc hac.symm hbc.symm
    exact congrArg Fin.val huv
  have hcard : Fintype.card (Fin n → Fin c) = Fintype.card (Fin Q) := by
    simp [Q]
  have hresBij : Function.Bijective residueMap :=
    (Fintype.bijective_iff_injective_and_card residueMap).2 ⟨hresInj, hcard⟩
  let wordFor : Fin Q → (Fin n → Fin c) := fun r => Classical.choose (hresBij.2 r)
  have hwordFor (r : Fin Q) : residueMap (wordFor r) = r := by
    exact Classical.choose_spec (hresBij.2 r)
  have hcarry (r : Fin Q) :
      edgeCodeEval a b c n (wordFor r) / Q ≤ A := by
    apply Nat.div_le_of_le_mul
    have hbound := edgeCodeEval_le_mass_mul_pow (a := a) (b := b) (c := c)
      hacLt (wordFor r)
    simpa [A, Q, Nat.mul_comm] using hbound
  let color : ℕ → Fin (A + 1) := fun x =>
    ⟨edgeCodeEval a b c n (wordFor ⟨x % Q, Nat.mod_lt _ hQ⟩) / Q,
      by have := hcarry ⟨x % Q, Nat.mod_lt _ hQ⟩; omega⟩
  rcases hvdw color with ⟨b0, d, hd, hlast, hmono⟩
  have hquery (r : Fin L) : b0 + (r : ℕ) * d < Q := by
    have hrle : (r : ℕ) ≤ L - 1 := by omega
    have hle : b0 + (r : ℕ) * d ≤ b0 + (L - 1) * d :=
      Nat.add_le_add_left (Nat.mul_le_mul_right d hrle) b0
    exact hle.trans_lt (hlast.trans_le hn)
  let words : Fin L → (Fin n → Fin c) := fun r =>
    wordFor ⟨b0 + (r : ℕ) * d, hquery r⟩
  let zero : Fin L := ⟨0, by omega⟩
  have hcarryEq (r : Fin L) :
      edgeCodeEval a b c n (words r) / Q =
        edgeCodeEval a b c n (words zero) / Q := by
    have hcEq : color (b0 + (r : ℕ) * d) = color b0 := hmono r
    have hbQ : b0 < Q := by
      have hz := hquery zero
      simpa [zero] using hz
    simpa [color, words, zero, Nat.mod_eq_of_lt (hquery r),
      Nat.mod_eq_of_lt hbQ] using congrArg Fin.val hcEq
  have hresidue (r : Fin L) :
      edgeCodeEval a b c n (words r) % Q = b0 + (r : ℕ) * d := by
    have hw := congrArg Fin.val (hwordFor ⟨b0 + (r : ℕ) * d, hquery r⟩)
    exact hw
  let B := edgeCodeEval a b c n (words zero)
  refine ⟨n, B, d, hd, words, ?_⟩
  intro r
  have hdecomp := Nat.mod_add_div (edgeCodeEval a b c n (words r)) Q
  have hdecomp0 := Nat.mod_add_div (edgeCodeEval a b c n (words zero)) Q
  rw [hresidue r, hcarryEq r] at hdecomp
  have hzero : (zero : ℕ) = 0 := rfl
  rw [hresidue zero, hzero, Nat.zero_mul, Nat.add_zero] at hdecomp0
  dsimp [B]
  omega

/-- A common `b,c`-smooth scale which remains one modulo `a`. -/
def correctionMultiplier (a b c u v : ℕ) : ℕ :=
  b ^ (a.totient * u) * c ^ (a.totient * v)

/-- A residue gadget shifted to a desired multiplicative scale. -/
def shiftedCorrectionSet (a b c r u v : ℕ) : Finset ℕ :=
  scaleFinset (correctionMultiplier a b c u v) (correctionSet a b c r)

theorem correctionMultiplier_modEq_one {a b c u v : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) :
    correctionMultiplier a b c u v ≡ 1 [MOD a] := by
  have hb : b ^ a.totient ≡ 1 [MOD a] := Nat.ModEq.pow_totient hab.symm
  have hc : c ^ a.totient ≡ 1 [MOD a] := Nat.ModEq.pow_totient hac.symm
  simpa [correctionMultiplier, pow_mul] using (hb.pow u).mul (hc.pow v)

theorem correctionMultiplier_pos {a b c u v : ℕ} (hb : 1 < b) (hc : 1 < c) :
    0 < correctionMultiplier a b c u v := by
  simp [correctionMultiplier, pow_pos (by omega : 0 < b), pow_pos (by omega : 0 < c)]

private theorem correctionTerm_pos {a b c r t : ℕ} (hb : 1 < b) (hc : 1 < c) :
    0 < correctionTerm a b c r t := by
  simp [correctionTerm, pow_pos (by omega : 0 < b), pow_pos (by omega : 0 < c)]

/-- Every shifted correction term is at least its common multiplier. -/
theorem correctionMultiplier_le_of_mem_shifted {a b c r u v y : ℕ}
    (hb : 1 < b) (hc : 1 < c)
    (hy : y ∈ shiftedCorrectionSet a b c r u v) :
    correctionMultiplier a b c u v ≤ y := by
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
  exact Nat.le_mul_of_pos_right _ (correctionTerm_pos hb hc)

/-- Common scaling preserves the gadget antichain. -/
theorem shiftedCorrectionSet_isPrimitive {a b c r u v : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    IsPrimitive (shiftedCorrectionSet a b c r u v) := by
  intro x hx y hy hxy
  rcases Finset.mem_image.mp hx with ⟨x₀, hx₀, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨y₀, hy₀, rfl⟩
  intro hdvd
  apply (correctionSet_isPrimitive ha hb hc hab hac hbc) hx₀ hy₀
  · intro heq
    subst y₀
    exact hxy rfl
  · exact (Nat.mul_dvd_mul_iff_left (correctionMultiplier_pos hb hc)).mp hdvd

/-- Exact shifted-gadget sum. -/
theorem shiftedCorrectionSet_sum {a b c r u v : ℕ}
    (_ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    (shiftedCorrectionSet a b c r u v).sum id =
      correctionMultiplier a b c u v * (correctionSet a b c r).sum id := by
  unfold shiftedCorrectionSet scaleFinset
  have hinj : Set.InjOn (fun x : ℕ => correctionMultiplier a b c u v * x)
      (correctionSet a b c r : Set ℕ) := by
    intro x _hx y _hy hxy
    exact Nat.eq_of_mul_eq_mul_left (correctionMultiplier_pos hb hc) hxy
  rw [Finset.sum_image hinj]
  simpa only [id_eq] using
    (Finset.mul_sum (correctionSet a b c r) id (correctionMultiplier a b c u v)).symm

/-- Every shifted correction term is coprime to `a`. -/
theorem shiftedCorrectionSet_coprime {a b c r u v y : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c)
    (hy : y ∈ shiftedCorrectionSet a b c r u v) :
    Nat.Coprime a y := by
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
  unfold correctionMultiplier correctionTerm
  exact (((hab.pow_right _).mul_right (hac.pow_right _)).mul_right
    ((hab.pow_right _).mul_right (hac.pow_right _)))

/-- The shifted correction sum retains residue `r` modulo `a`. -/
theorem shiftedCorrectionSet_sum_modEq {a b c r u v : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    (shiftedCorrectionSet a b c r u v).sum id ≡ r [MOD a] := by
  rw [shiftedCorrectionSet_sum ha hb hc]
  simpa using (correctionMultiplier_modEq_one (u := u) (v := v) hab hac).mul
    (correctionSet_sum_modEq (r := r) ha hb hc hab hac hbc)

/-- Every shifted correction term belongs to the original three-base smooth set. -/
theorem shiftedCorrectionSet_subset_smooth3 {a b c r u v : ℕ}
    {y : ℕ} (hy : y ∈ shiftedCorrectionSet a b c r u v) :
    y ∈ Smooth3 a b c := by
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
  refine ⟨0, a.totient * u + a.totient * t,
    a.totient * v + a.totient * (r - 1 - t), ?_⟩
  simp [correctionMultiplier, correctionTerm, pow_add, mul_assoc, mul_comm, mul_left_comm]

private theorem smooth3_pos {a b c x : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hx : x ∈ Smooth3 a b c) :
    0 < x := by
  rcases hx with ⟨i, j, k, rfl⟩
  positivity

private theorem correctionSet_sum_pos {a b c r : ℕ}
    (_hb : 1 < b) (hc : 1 < c) (hr : 0 < r) :
    0 < (correctionSet a b c r).sum id := by
  have hmem : correctionTerm a b c r 0 ∈ correctionSet a b c r := by
    apply Finset.mem_image.mpr
    exact ⟨0, Finset.mem_range.mpr hr, rfl⟩
  have hterm : 0 < correctionTerm a b c r 0 := by
    unfold correctionTerm
    positivity
  exact hterm.trans_le (by
    simpa only [id_eq] using Finset.single_le_sum (fun z _hz => Nat.zero_le z) hmem)

/-- For each fixed nonzero residue modulo `a`, every sufficiently large target
in that residue reduces to a smaller target by an F-010 correction. The smaller
target loses at most the explicit factor `a*(S+1)`, where `S` is the unshifted
correction-gadget sum. -/
theorem eventually_reduce_nonzero_residue
    {a b c r : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hr : 0 < r) :
    let S := (correctionSet a b c r).sum id
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n ≡ r [MOD a] →
      ∃ m : ℕ, m < n ∧ n ≤ a * (S + 1) * m ∧
        (IsRepresentable (Smooth3 a b c) m → IsRepresentable (Smooth3 a b c) n) := by
  dsimp only
  let S : ℕ := (correctionSet a b c r).sum id
  have hS : 0 < S := correctionSet_sum_pos hb hc hr
  have hφ : 0 < a.totient := Nat.totient_pos.mpr (by omega)
  let B₀ : ℕ := b ^ a.totient
  let C₀ : ℕ := c ^ a.totient
  have hB₀ : 1 < B₀ := Nat.one_lt_pow (by omega) hb
  have hC₀ : 1 < C₀ := Nat.one_lt_pow (by omega) hc
  have hBC : Nat.Coprime B₀ C₀ := hbc.pow _ _
  let ρ : ℝ := ((S + a : ℕ) : ℝ) / ((S + 1 : ℕ) : ℝ)
  have hρ : 1 < ρ := by
    dsimp [ρ]
    rw [one_lt_div (by positivity : (0 : ℝ) < (S + 1 : ℕ))]
    exact_mod_cast (show S + 1 < S + a by omega)
  rcases smooth2_eventually_multiplicatively_leftDense hB₀ hC₀ hBC hρ with
    ⟨Y, hY⟩
  rcases exists_nat_ge (Y * (S + 1 : ℕ)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hnmod
  have hnCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxY : Y ≤ (n : ℝ) / (S + 1 : ℕ) := by
    have hden : (0 : ℝ) < (S + 1 : ℕ) := by positivity
    apply (le_div_iff₀ hden).mpr
    exact hN.trans hnCast
  rcases hY ((n : ℝ) / (S + 1 : ℕ)) hxY with ⟨u, v, hwLower, hwUpper⟩
  let w : ℕ := correctionMultiplier a b c u v
  have hwCast : (w : ℝ) = (B₀ : ℝ) ^ u * (C₀ : ℝ) ^ v := by
    simp [w, B₀, C₀, correctionMultiplier, pow_mul]
  have hfrac : ((n : ℝ) / (S + 1 : ℕ)) / ρ = (n : ℝ) / (S + a : ℕ) := by
    dsimp [ρ]
    field_simp
  rw [← hwCast, hfrac] at hwLower
  rw [← hwCast] at hwUpper
  have hCritReal : (n : ℝ) < (w : ℝ) * (S + a : ℕ) :=
    (div_lt_iff₀ (by positivity : (0 : ℝ) < (S + a : ℕ))).mp hwLower
  have hUpperReal : (w : ℝ) * (S + 1 : ℕ) ≤ (n : ℝ) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < (S + 1 : ℕ))).mp hwUpper
  have hCrit : n < w * (S + a) := by exact_mod_cast hCritReal
  have hUpper : w * (S + 1) ≤ n := by exact_mod_cast hUpperReal
  let t : Finset ℕ := shiftedCorrectionSet a b c r u v
  let B : ℕ := t.sum id
  have hB : B = w * S := by
    dsimp [B, t, w, S]
    exact shiftedCorrectionSet_sum ha hb hc
  have hBLe : B ≤ n := by
    rw [hB]
    nlinarith
  have hBmod : B ≡ r [MOD a] := by
    dsimp [B, t]
    exact shiftedCorrectionSet_sum_modEq ha hb hc hab hac hbc
  have hsubmod : n - B ≡ 0 [MOD a] := by
    simpa using hnmod.sub hBLe (le_refl r) hBmod
  have hdiv : a ∣ n - B := Nat.modEq_zero_iff_dvd.mp hsubmod
  let m : ℕ := (n - B) / a
  have ham : a * m = n - B := Nat.mul_div_cancel' hdiv
  have hnEq : n = a * m + B := by
    rw [ham]
    omega
  have hmLtW : m < w := by
    have h' : a * m + w * S < w * (S + a) := by simpa [hnEq, hB] using hCrit
    have h'' : w * S + a * m < w * S + a * w := by
      simpa [mul_add, mul_comm, mul_left_comm, add_comm, add_left_comm] using h'
    have hamlt : a * m < a * w := (Nat.add_lt_add_iff_left).mp h''
    exact (Nat.mul_lt_mul_left (by omega : 0 < a)).mp hamlt
  have hwLeAm : w ≤ a * m := by
    have h' : w * (S + 1) ≤ a * m + w * S := by simpa [hnEq, hB] using hUpper
    have h'' : w * S + w ≤ w * S + a * m := by
      simpa [mul_add, add_comm, add_left_comm] using h'
    exact (Nat.add_le_add_iff_left).mp h''
  have hnBound : n ≤ a * (S + 1) * m := by
    rw [hnEq, hB]
    calc
      a * m + w * S ≤ a * m + (a * m) * S := Nat.add_le_add_left (Nat.mul_le_mul_right S hwLeAm) _
      _ = a * (S + 1) * m := by ring
  have hwPos : 0 < w := correctionMultiplier_pos hb hc
  have hnPos : 0 < n := (Nat.mul_pos hwPos (by omega)).trans_le hUpper
  have hmPos : 0 < m := by
    by_contra hm0
    have hmEq : m = 0 := Nat.eq_zero_of_not_pos hm0
    rw [hmEq] at hnBound
    simp only [mul_zero] at hnBound
    omega
  have hmLtN : m < n := by
    have hmLtAm : m < a * m := by
      simpa using Nat.mul_lt_mul_of_pos_right ha hmPos
    have hamLe : a * m ≤ n := by
      rw [hnEq]
      exact Nat.le_add_right _ _
    exact hmLtAm.trans_le hamLe
  refine ⟨m, hmLtN, hnBound, ?_⟩
  rintro ⟨s, hsA, hsPrimitive, hsSum⟩
  have hsPos : ∀ x ∈ s, 0 < x := fun x hx => smooth3_pos ha hb hc (hsA x hx)
  have htPrimitive : IsPrimitive t := by
    dsimp [t]
    exact shiftedCorrectionSet_isPrimitive ha hb hc hab hac hbc
  have htCoprime : ∀ y ∈ t, Nat.Coprime a y := by
    intro y hy
    exact shiftedCorrectionSet_coprime hab hac hy
  have hsep : ∀ x ∈ s, ∀ y ∈ t, x < y := by
    intro x hx y hy
    have hxLe : x ≤ m := by
      rw [← hsSum]
      simpa only [id_eq] using Finset.single_le_sum (fun z _hz => Nat.zero_le z) hx
    have hwLe : w ≤ y := correctionMultiplier_le_of_mem_shifted hb hc hy
    exact hxLe.trans_lt (hmLtW.trans_le hwLe)
  refine ⟨scaleFinset a s ∪ t, ?_,
    isPrimitive_scaleFinset_union ha hsPos hsPrimitive htPrimitive htCoprime hsep, ?_⟩
  · intro y hy
    rcases Finset.mem_union.mp hy with hyOld | hyCorr
    · rcases Finset.mem_image.mp hyOld with ⟨x, hx, rfl⟩
      rcases hsA x hx with ⟨i, j, k, rfl⟩
      refine ⟨i + 1, j, k, ?_⟩
      simp [pow_succ, mul_assoc, mul_comm]
    · exact shiftedCorrectionSet_subset_smooth3 hyCorr
  · rw [sum_scaleFinset_union ha htCoprime, hsSum]
    change a * m + B = n
    exact hnEq.symm

private theorem representable_scale_base {a b c m : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hrep : IsRepresentable (Smooth3 a b c) m) :
    IsRepresentable (Smooth3 a b c) (a * m) := by
  rcases hrep with ⟨s, hsA, hsPrimitive, hsSum⟩
  have hsPos : ∀ x ∈ s, 0 < x := by
    intro x hx
    rcases hsA x hx with ⟨i, j, k, rfl⟩
    positivity
  have htPrimitive : IsPrimitive (∅ : Finset ℕ) := by simp [IsPrimitive]
  have htCoprime : ∀ y ∈ (∅ : Finset ℕ), Nat.Coprime a y := by simp
  have hsep : ∀ x ∈ s, ∀ y ∈ (∅ : Finset ℕ), x < y := by simp
  refine ⟨scaleFinset a s, ?_, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases hsA x hx with ⟨i, j, k, rfl⟩
    refine ⟨i + 1, j, k, ?_⟩
    simp [pow_succ, mul_assoc, mul_comm]
  · simpa using isPrimitive_scaleFinset_union ha hsPos hsPrimitive
      htPrimitive htCoprime hsep
  · have hsum := sum_scaleFinset_union (s := s) (t := ∅) ha htCoprime
    simp only [Finset.union_empty, Finset.sum_empty, add_zero] at hsum
    rw [hsum, hsSum]

/-- Flexible form of the finite seed gate: once the reduction constants are
fixed, a represented block may start at any larger threshold, not only at the
particular threshold used to define the constants. -/
theorem flexible_finite_seed_gate
    {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    ∃ N₀ C : ℕ, 0 < N₀ ∧ 1 < C ∧
      ∀ N : ℕ, N₀ ≤ N →
        ((∀ n : ℕ, N ≤ n → n ≤ C * N →
            IsRepresentable (Smooth3 a b c) n) →
          IsDComplete (Smooth3 a b c)) := by
  classical
  have hall : ∀ r : ℕ, ∃ Nr : ℕ, 0 < r →
      ∀ n : ℕ, Nr ≤ n → n ≡ r [MOD a] →
        ∃ m : ℕ, m < n ∧
          n ≤ a * ((correctionSet a b c r).sum id + 1) * m ∧
          (IsRepresentable (Smooth3 a b c) m →
            IsRepresentable (Smooth3 a b c) n) := by
    intro r
    by_cases hr : 0 < r
    · rcases eventually_reduce_nonzero_residue ha hb hc hab hac hbc hr with ⟨N, hN⟩
      exact ⟨N, fun _hr => hN⟩
    · exact ⟨0, fun h => False.elim (hr h)⟩
  choose Nr hNr using hall
  let N₀ : ℕ := 1 + ∑ r ∈ Finset.range a, Nr r
  let Cr : ℕ → ℕ := fun r => a * ((correctionSet a b c r).sum id + 1)
  let C : ℕ := a + ∑ r ∈ Finset.range a, Cr r
  have hN₀pos : 0 < N₀ := by simp [N₀]
  have hCgeA : a ≤ C := by simp [C]
  have hCpos : 0 < C := (by omega : 0 < a).trans_le hCgeA
  have hCone : 1 < C := ha.trans_le hCgeA
  have hNrLe : ∀ r < a, Nr r ≤ N₀ := by
    intro r hr
    have hle : Nr r ≤ ∑ z ∈ Finset.range a, Nr z := by
      exact Finset.single_le_sum (fun z _hz => Nat.zero_le (Nr z))
        (Finset.mem_range.mpr hr)
    dsimp [N₀]
    omega
  have hCrLe : ∀ r < a, Cr r ≤ C := by
    intro r hr
    have hle : Cr r ≤ ∑ z ∈ Finset.range a, Cr z := by
      exact Finset.single_le_sum (fun z _hz => Nat.zero_le (Cr z))
        (Finset.mem_range.mpr hr)
    dsimp [C]
    omega
  refine ⟨N₀, C, hN₀pos, hCone, ?_⟩
  intro N hN₀N hseed
  have hreduce : ∀ n : ℕ, C * N < n →
      ∃ m : ℕ, N ≤ m ∧ m < n ∧
        (IsRepresentable (Smooth3 a b c) m →
          IsRepresentable (Smooth3 a b c) n) := by
    intro n hnLarge
    let r : ℕ := n % a
    have hrlt : r < a := Nat.mod_lt n (by omega)
    by_cases hr0 : r = 0
    · have hdiv : a ∣ n := by
        apply Nat.dvd_of_mod_eq_zero
        exact hr0
      let m : ℕ := n / a
      have ham : a * m = n := Nat.mul_div_cancel' hdiv
      have hNm : N ≤ m := by
        apply (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr
        have haNle : a * N ≤ C * N := Nat.mul_le_mul_right N hCgeA
        simpa [mul_comm] using haNle.trans (Nat.le_of_lt hnLarge)
      have hNpos : 0 < N := hN₀pos.trans_le hN₀N
      have hmPos : 0 < m := hNpos.trans_le hNm
      have hmLt : m < n := by
        rw [← ham]
        simpa using Nat.mul_lt_mul_of_pos_right ha hmPos
      refine ⟨m, hNm, hmLt, ?_⟩
      intro hmRep
      rw [← ham]
      exact representable_scale_base ha hb hc hmRep
    · have hrpos : 0 < r := by omega
      have hNn : N ≤ n :=
        (Nat.le_mul_of_pos_left N hCpos).trans (Nat.le_of_lt hnLarge)
      have hnNr : Nr r ≤ n := (hNrLe r hrlt).trans (hN₀N.trans hNn)
      have hnmod : n ≡ r [MOD a] := (Nat.mod_modEq n a).symm
      rcases hNr r hrpos n hnNr hnmod with ⟨m, hmLt, hnm, hlift⟩
      have hnmC : n ≤ C * m := by
        exact hnm.trans (Nat.mul_le_mul_right m (hCrLe r hrlt))
      have hNm : N ≤ m := by
        have hmul : C * N < C * m := hnLarge.trans_le hnmC
        exact (Nat.mul_lt_mul_left hCpos).mp hmul |>.le
      exact ⟨m, hNm, hmLt, hlift⟩
  refine ⟨N, ?_⟩
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnSeed : n ≤ C * N
      · exact hseed n hn hnSeed
      · rcases hreduce n (lt_of_not_ge hnSeed) with ⟨m, hmN, hmn, hlift⟩
        exact hlift (ih m hmn hmN)

/-- Exponent information for every actual term selected by an edge-code word. -/
theorem edgeCodeFinset_exponent_region {a b c n : ℕ}
    (word : Fin n → Fin c) {x : ℕ} (hx : x ∈ edgeCodeFinset a b c n word) :
    ∃ i j k : ℕ, x = eval3 a b c i j k ∧
      i + j + k = edgeDigitDepth c + n - 1 ∧ j ≤ edgeDigitDepth c := by
  rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
  have hpRange : p.2 < c - 1 := by
    exact Finset.mem_range.mp
      ((Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2)
  refine ⟨edgeCodeDegree c n p.1 - edgeDigitDepth c + c.totient * p.2,
    c.totient * (c - 1 - 1 - p.2), (p.1 : ℕ), rfl,
    edgeCodeTerm_total_degree p.1 hpRange, ?_⟩
  simp only [edgeDigitDepth]
  have hsub : c - 1 - 1 - p.2 ≤ c - 2 := by omega
  exact Nat.mul_le_mul_left c.totient hsub

/-- Exact sum after scaling a finite set by a positive scalar. -/
theorem scaleFinset_sum {q : ℕ} (hq : 0 < q) (s : Finset ℕ) :
    (scaleFinset q s).sum id = q * s.sum id := by
  unfold scaleFinset
  rw [Finset.sum_image]
  · simpa only [id_eq] using (Finset.mul_sum s id q).symm
  · intro x _hx y _hy hxy
    exact Nat.eq_of_mul_eq_mul_left hq hxy

/-- All members of a finset are strict-interior monomials on one exact level,
with a common upper bound on their `b` exponent. -/
def IsInteriorLevelBand (a b c D J : ℕ) (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∃ i j k : ℕ,
    0 < i ∧ 0 < j ∧ 0 < k ∧ i + j + k = D ∧ j ≤ J ∧
      x = eval3 a b c i j k

/-- Any finite set whose members have one exact exponent degree is primitive. -/
theorem isPrimitive_of_exact_level {a b c D : ℕ} {s : Finset ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hs : ∀ x ∈ s, ∃ i j k : ℕ,
      i + j + k = D ∧ x = eval3 a b c i j k) : IsPrimitive s := by
  intro x hx y hy hxy hdvd
  rcases hs x hx with ⟨ix, jx, kx, hxdeg, rfl⟩
  rcases hs y hy with ⟨iy, jy, ky, hydeg, rfl⟩
  apply not_eval3_dvd_of_same_degree ha hb hc hab hac hbc
    (hxdeg.trans hydeg.symm) _ hdvd
  intro he
  apply hxy
  rcases he with ⟨rfl, rfl, rfl⟩
  rfl

/-- The sum of the homogeneous weights through stage `M`. -/
def homogeneousWeightMass (A B : ℕ) : ℕ → ℕ
  | 0 => 1
  | M + 1 => A * homogeneousWeightMass A B M + B ^ (M + 1)

/-- The homogeneous weight mass is bounded by one further power of the larger
base. -/
theorem homogeneousWeightMass_le_pow {A B M : ℕ}
    (hA : 0 < A) (hAB : A < B) :
    homogeneousWeightMass A B M ≤ B ^ (M + 1) := by
  induction M with
  | zero =>
      simp [homogeneousWeightMass]
      omega
  | succ M ih =>
      rw [homogeneousWeightMass]
      have hmul := Nat.mul_le_mul_left A ih
      have hApow : A * B ^ (M + 1) ≤ (B - 1) * B ^ (M + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      calc
        A * homogeneousWeightMass A B M + B ^ (M + 1) ≤
            A * B ^ (M + 1) + B ^ (M + 1) := Nat.add_le_add_right hmul _
        _ ≤ (B - 1) * B ^ (M + 1) + B ^ (M + 1) :=
          Nat.add_le_add_right hApow _
        _ = B ^ (M + 2) := by
          have hB : 0 < B := hA.trans hAB
          have hB1 : 1 ≤ B := by omega
          calc
            (B - 1) * B ^ (M + 1) + B ^ (M + 1) =
                ((B - 1) + 1) * B ^ (M + 1) := by ring
            _ = B * B ^ (M + 1) := by rw [Nat.sub_add_cancel hB1]
            _ = B ^ (M + 2) := by
              rw [show M + 2 = (M + 1) + 1 by omega, pow_succ]
              ring

/-- Every bounded homogeneous-radix value is at most `L` times the homogeneous
weight mass. -/
theorem HomogeneousRadixRep.le_mass {A B L M n : ℕ}
    (hrep : HomogeneousRadixRep A B L M n) :
    n ≤ L * homogeneousWeightMass A B M := by
  induction M generalizing n with
  | zero =>
      simp only [HomogeneousRadixRep] at hrep
      simp [homogeneousWeightMass]
      omega
  | succ M ih =>
      rcases hrep with ⟨x, s, hx, hs, rfl⟩
      have hxle := ih hx
      rw [homogeneousWeightMass]
      calc
        A * x + B ^ (M + 1) * s ≤
            A * (L * homogeneousWeightMass A B M) + B ^ (M + 1) * L :=
          Nat.add_le_add (Nat.mul_le_mul_left A hxle)
            (Nat.mul_le_mul_left _ hs.le)
        _ = L * (A * homogeneousWeightMass A B M + B ^ (M + 1)) := by ring

/-- Scaling an interior band in the `a` direction preserves its interior
geometry and raises its exact degree. -/
theorem scaleInteriorBandA {a b c D J G : ℕ} {s : Finset ℕ}
    (_ha : 0 < a) (hs : IsInteriorLevelBand a b c D J s) :
    IsInteriorLevelBand a b c (D + G) J (scaleFinset (a ^ G) s) := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  rcases hs y hy with ⟨i, j, k, hi, hj, hk, hdeg, hjJ, rfl⟩
  refine ⟨i + G, j, k, by omega, hj, hk, by omega, hjJ, ?_⟩
  dsimp [eval3]
  rw [pow_add]
  ring

/-- A raw edge block translated by `abc*(b^u c^v)^e` is a strict-interior
exact-level block in the corresponding `b`-exponent band. -/
theorem translatedEdgeCode_interiorBand {a b c n u v e : ℕ}
    (word : Fin n → Fin c) :
    let H := edgeDigitDepth c
    let δ := H + n - 1
    let q := a * b * c * (b ^ u * c ^ v) ^ e
    IsInteriorLevelBand a b c (δ + (u + v) * e + 3)
      (u * e + H + 1) (scaleFinset q (edgeCodeFinset a b c n word)) := by
  dsimp only
  let H := edgeDigitDepth c
  let δ := H + n - 1
  let q := a * b * c * (b ^ u * c ^ v) ^ e
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  rcases edgeCodeFinset_exponent_region word hy with
    ⟨i, j, k, rfl, hdegree, hjH⟩
  refine ⟨i + 1, j + u * e + 1, k + v * e + 1,
    by omega, by omega, by omega, ?_, by omega, ?_⟩
  · rw [Nat.add_mul]
    omega
  · dsimp [q, eval3]
    simp only [mul_pow]
    rw [pow_add, pow_add, pow_add]
    ring

/-- A bounded homogeneous-radix coefficient word can be realized by a union
of translated copies of one primitive AP digit family.  All actual terms are
strict-interior monomials on one exact degree, and the digit copies occupy
separated `b`-exponent bands. -/
theorem homogeneousRadixRep_realized_by_edge_AP
    {a b c n L B₀ d u v M value : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (_hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (huBand : edgeDigitDepth c + 1 < u)
    (words : Fin L → (Fin n → Fin c))
    (hwords : ∀ r : Fin L,
      edgeCodeEval a b c n (words r) = B₀ + (r : ℕ) * d)
    (hrep : HomogeneousRadixRep (a ^ (u + v)) (b ^ u * c ^ v) L M value) :
    let H := edgeDigitDepth c
    let δ := H + n - 1
    let A := a ^ (u + v)
    let B := b ^ u * c ^ v
    let q := a * b * c
    ∃ s : Finset ℕ,
      IsInteriorLevelBand a b c (δ + (u + v) * M + 3)
        (u * M + H + 1) s ∧
      s.sum id = q * (B₀ * homogeneousWeightMass A B M + d * value) := by
  dsimp only
  let H := edgeDigitDepth c
  let δ := H + n - 1
  let A := a ^ (u + v)
  let B := b ^ u * c ^ v
  let q := a * b * c
  induction M generalizing value with
  | zero =>
      simp only [HomogeneousRadixRep] at hrep
      let r : Fin L := ⟨value, hrep⟩
      let s := scaleFinset q (edgeCodeFinset a b c n (words r))
      refine ⟨s, ?_, ?_⟩
      · have hbnd := translatedEdgeCode_interiorBand (a := a) (b := b) (c := c)
          (u := u) (v := v) (e := 0) (words r)
        simpa [s, H, δ, q] using hbnd
      · dsimp [s]
        rw [scaleFinset_sum (by dsimp [q]; positivity)]
        rw [edgeCodeFinset_sum ha hb hc hab hac hbc, hwords r]
        simp [homogeneousWeightMass, r]
        ring
  | succ M ih =>
      rcases hrep with ⟨oldValue, digit, hold, hdigit, rfl⟩
      rcases ih hold with ⟨oldSet, holdBand, holdSum⟩
      let r : Fin L := ⟨digit, hdigit⟩
      let oldScaled := scaleFinset A oldSet
      let newSet := scaleFinset (q * B ^ (M + 1))
        (edgeCodeFinset a b c n (words r))
      let s := oldScaled ∪ newSet
      have holdScaled : IsInteriorLevelBand a b c
          (δ + (u + v) * M + 3 + (u + v))
          (u * M + H + 1) oldScaled := by
        exact scaleInteriorBandA (by omega : 0 < a) holdBand
      have hnewBand : IsInteriorLevelBand a b c
          (δ + (u + v) * (M + 1) + 3)
          (u * (M + 1) + H + 1) newSet := by
        have hbnd := translatedEdgeCode_interiorBand (a := a) (b := b) (c := c)
          (u := u) (v := v) (e := M + 1) (words r)
        simpa [newSet, q, B, H, δ, mul_assoc] using hbnd
      have hdegreeEq : δ + (u + v) * M + 3 + (u + v) =
          δ + (u + v) * (M + 1) + 3 := by ring
      have hdis : Disjoint oldScaled newSet := by
        rw [Finset.disjoint_left]
        intro x hxold hxnew
        rcases holdScaled x hxold with
          ⟨io, jo, ko, _hio, _hjo, _hko, _hdo, hjoBand, hxo⟩
        rcases hnewBand x hxnew with
          ⟨inw, jnw, knw, _hinw, _hjnw, _hknw, _hdn, _hjnwBand, hxn⟩
        have heq : eval3 a b c io jo ko = eval3 a b c inw jnw knw := by
          rw [← hxo, ← hxn]
        have hdvd : eval3 a b c io jo ko ∣ eval3 a b c inw jnw knw := by rw [heq]
        have hcoord := (eval3_dvd_iff ha hb hc hab hac hbc).mp hdvd
        have hdvdRev : eval3 a b c inw jnw knw ∣ eval3 a b c io jo ko := by
          rw [heq]
        have hcoordRev := (eval3_dvd_iff ha hb hc hab hac hbc).mp hdvdRev
        have hjnewLo : u * (M + 1) + 1 ≤ jnw := by
          rcases Finset.mem_image.mp hxnew with ⟨y, hy, hyv⟩
          rcases edgeCodeFinset_exponent_region (words r) hy with
            ⟨ii, jj, kk, hyval, _hdeg, _hjj⟩
          have hscaledVal : q * B ^ (M + 1) * y =
              eval3 a b c (ii + 1) (jj + u * (M + 1) + 1)
                (kk + v * (M + 1) + 1) := by
            rw [hyval]
            dsimp [q, B, eval3]
            simp only [mul_pow]
            rw [pow_add, pow_add, pow_add]
            ring
          have heqNew : eval3 a b c inw jnw knw =
              eval3 a b c (ii + 1) (jj + u * (M + 1) + 1)
                (kk + v * (M + 1) + 1) := by
            rw [← hxn, ← hyv, hscaledVal]
          have hd1 : eval3 a b c inw jnw knw ∣
              eval3 a b c (ii + 1) (jj + u * (M + 1) + 1)
                (kk + v * (M + 1) + 1) := by rw [heqNew]
          have hd2 : eval3 a b c (ii + 1) (jj + u * (M + 1) + 1)
                (kk + v * (M + 1) + 1) ∣ eval3 a b c inw jnw knw := by
            rw [heqNew]
          have _hc1 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd1
          have hc2 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd2
          exact (by
            calc
              u * (M + 1) + 1 ≤ jj + u * (M + 1) + 1 := by omega
              _ ≤ jnw := hc2.2.1)
        have : jo < jnw := by
          calc
            jo ≤ u * M + H + 1 := hjoBand
            _ < u * M + u + 1 := by omega
            _ = u * (M + 1) + 1 := by rw [Nat.mul_succ]
            _ ≤ jnw := hjnewLo
        exact (Nat.not_le_of_gt this) hcoordRev.2.1
      refine ⟨s, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hxold | hxnew
        · rcases holdScaled x hxold with
            ⟨i, j, k, hi, hj, hk, hdeg, hjBand, hval⟩
          have hjBound : j ≤ u * (M + 1) + H + 1 := by
            calc
              j ≤ u * M + H + 1 := hjBand
              _ ≤ u * (M + 1) + H + 1 := by
                exact Nat.add_le_add_right
                  (Nat.mul_le_mul_left u (by omega : M ≤ M + 1)) (H + 1)
          exact ⟨i, j, k, hi, hj, hk, hdeg.trans hdegreeEq, hjBound, hval⟩
        · exact hnewBand x hxnew
      · dsimp [s]
        rw [Finset.sum_union hdis]
        change oldScaled.sum id + newSet.sum id = _
        dsimp [oldScaled, newSet]
        rw [scaleFinset_sum (pow_pos (by omega) _), holdSum]
        rw [scaleFinset_sum (by dsimp [q, B]; positivity)]
        rw [edgeCodeFinset_sum ha hb hc hab hac hbc, hwords r]
        dsimp [A, B, q]
        rw [homogeneousWeightMass]
        ring

/-- If every optional summand is no larger than an existing interval width plus
one, adjoining arbitrary subsets of those summands extends the interval all
the way by their total sum. -/
theorem interval_decompose_with_optional {p : Finset ℕ} {L U n : ℕ}
    (hLU : L ≤ U)
    (hp : ∀ x ∈ p, x ≤ U - L + 1)
    (hnL : L ≤ n) (hnU : n ≤ U + p.sum id) :
    ∃ q : Finset ℕ, q ⊆ p ∧ ∃ m : ℕ,
      L ≤ m ∧ m ≤ U ∧ n = m + q.sum id := by
  induction p using Finset.induction generalizing n with
  | empty =>
      refine ⟨∅, by simp, n, hnL, ?_, by simp⟩
      simpa using hnU
  | @insert x p hxp ih =>
      rw [Finset.sum_insert hxp] at hnU
      simp only [id_eq] at hnU
      by_cases hsmall : n ≤ U + p.sum id
      · rcases ih (fun y hy => hp y (Finset.mem_insert_of_mem hy)) hnL hsmall with
          ⟨q, hqp, m, hmL, hmU, hnm⟩
        exact ⟨q, hqp.trans (Finset.subset_insert x p), m, hmL, hmU, hnm⟩
      · have hxBound := hp x (by simp)
        have hxn : x ≤ n := by omega
        have hXL : x + L ≤ U + 1 := by
          calc
            x + L ≤ (U - L + 1) + L := Nat.add_le_add_right hxBound L
            _ = U + 1 := by
              rw [show U - L + 1 + L = (U - L + L) + 1 by omega,
                Nat.sub_add_cancel hLU]
        have hxLn : x + L ≤ n := hXL.trans (by omega)
        have hnSubL : L ≤ n - x := by
          apply Nat.le_sub_of_add_le
          simpa [Nat.add_comm] using hxLn
        have hnSubU : n - x ≤ U + p.sum id := by
          apply Nat.sub_le_iff_le_add.mpr
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnU
        rcases ih (fun y hy => hp y (Finset.mem_insert_of_mem hy))
            hnSubL hnSubU with ⟨q, hqp, m, hmL, hmU, hnm⟩
        have hxq : x ∉ q := fun hxq => hxp (hqp hxq)
        refine ⟨insert x q, ?_, m, hmL, hmU, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyq
          · simp
          · exact Finset.mem_insert_of_mem (hqp hyq)
        · rw [Finset.sum_insert hxq]
          simp only [id_eq]
          calc
            n = (n - x) + x := (Nat.sub_add_cancel hxn).symm
            _ = (m + q.sum id) + x := by rw [hnm]
            _ = m + (x + q.sum id) := by omega

/-- An exact-level represented interval can be extended by a disjoint optional
finset whose terms fit below its width.  Exact degree guarantees primitive
unions automatically. -/
theorem representable_interval_extend_by_level_finset
    {a b c D L U : ℕ} {p : Finset ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hLU : L ≤ U)
    (hpBound : ∀ x ∈ p, x ≤ U - L + 1)
    (hpSmooth : ∀ x ∈ p, x ∈ Smooth3 a b c)
    (hpDegree : ∀ x ∈ p, ∃ i j k : ℕ,
      i + j + k = D ∧ x = eval3 a b c i j k)
    (hbase : ∀ n : ℕ, L ≤ n → n ≤ U →
      ∃ s : Finset ℕ,
        (∀ x ∈ s, x ∈ Smooth3 a b c) ∧
        (∀ x ∈ s, ∃ i j k : ℕ,
          i + j + k = D ∧ x = eval3 a b c i j k) ∧
        Disjoint s p ∧ s.sum id = n) :
    ∀ n : ℕ, L ≤ n → n ≤ U + p.sum id →
      IsRepresentable (Smooth3 a b c) n := by
  intro n hnL hnU
  rcases interval_decompose_with_optional hLU hpBound hnL hnU with
    ⟨q, hqp, m, hmL, hmU, hnm⟩
  rcases hbase m hmL hmU with ⟨s, hsSmooth, hsDegree, hsp, hsSum⟩
  have hsq : Disjoint s q := hsp.mono_right hqp
  let t := s ∪ q
  refine ⟨t, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hxs | hxq
    · exact hsSmooth x hxs
    · exact hpSmooth x (hqp hxq)
  · refine isPrimitive_of_exact_level (D := D) ha hb hc hab hac hbc ?_
    intro x hx
    rcases Finset.mem_union.mp hx with hxs | hxq
    · exact hsDegree x hxs
    · exact hpDegree x (hqp hxq)
  · dsimp [t]
    rw [Finset.sum_union hsq, hsSum, hnm]

/-- A member of a seed construction is either on a coordinate face, or is a
strict-interior term in the bounded `b`-exponent part of one exact level. -/
def IsSeedLevelSet (a b c D J : ℕ) (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∃ i j k : ℕ,
    i + j + k = D ∧ x = eval3 a b c i j k ∧
      ((i = 0 ∨ j = 0 ∨ k = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < k ∧ j ≤ J))

/-- A seed-level set consists of smooth terms. -/
theorem seedLevelSet_subset_smooth3 {a b c D J : ℕ} {s : Finset ℕ}
    (hs : IsSeedLevelSet a b c D J s) :
    ∀ x ∈ s, x ∈ Smooth3 a b c := by
  intro x hx
  rcases hs x hx with ⟨i, j, k, _hdeg, rfl, _hshape⟩
  exact ⟨i, j, k, rfl⟩

/-- A seed-level set is disjoint from a strict-interior shell lying beyond its
`b`-exponent cutoff. -/
theorem seedLevelSet_disjoint_high_shell
    {a b c D J : ℕ} {s p : Finset ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hs : IsSeedLevelSet a b c D J s)
    (hp : ∀ x ∈ p, ∃ i j k : ℕ,
      0 < i ∧ 0 < j ∧ 0 < k ∧ i + j + k = D ∧ J < j ∧
        x = eval3 a b c i j k) :
    Disjoint s p := by
  rw [Finset.disjoint_left]
  intro x hxs hxp
  rcases hs x hxs with ⟨i, j, k, _hdeg, hxval, hshape⟩
  rcases hp x hxp with ⟨i', j', k', hi', hj', hk', _hdeg', hjHigh, hxval'⟩
  have heq : eval3 a b c i j k = eval3 a b c i' j' k' := by
    rw [← hxval, ← hxval']
  have hd1 : eval3 a b c i j k ∣ eval3 a b c i' j' k' := by rw [heq]
  have hd2 : eval3 a b c i' j' k' ∣ eval3 a b c i j k := by rw [heq]
  have hc1 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd1
  have hc2 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd2
  rcases hshape with hface | hinterior
  · rcases hface with rfl | rfl | rfl <;> omega
  · omega

private abbrev orderedSeedDegree (c n u v M : ℕ) : ℕ :=
  edgeDigitDepth c + n - 1 + (u + v) * M + 3

private abbrev orderedSeedA (a u v : ℕ) : ℕ :=
  a ^ (u + v)

private abbrev orderedSeedB (b c u v : ℕ) : ℕ :=
  b ^ u * c ^ v

private abbrev orderedSeedStep (a b c d : ℕ) : ℕ :=
  (a * b * c) * d

private abbrev orderedSeedOffset (a b c B₀ u v M : ℕ) : ℕ :=
  (a * b * c) *
    (B₀ * homogeneousWeightMass (orderedSeedA a u v) (orderedSeedB b c u v) M)

private abbrev orderedSeedLo (a b c n B₀ d u v M Ccorr U : ℕ) : ℕ :=
  orderedSeedOffset a b c B₀ u v M +
    orderedSeedStep a b c d * U +
      Ccorr * c ^ orderedSeedDegree c n u v M

private abbrev orderedSeedHi (a b c B₀ d u v M V : ℕ) : ℕ :=
  orderedSeedOffset a b c B₀ u v M + orderedSeedStep a b c d * V

/-- The base represented interval inside the ordered seed construction. -/
private theorem ordered_seed_base_interval
    {a b c n L B₀ d u v M Ccorr D₀ U V : ℕ}
    {words : Fin L → (Fin n → Fin c)} {p : Finset ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (huBand : edgeDigitDepth c + 1 < u)
    (hqd : 0 < orderedSeedStep a b c d)
    (hMDegree : D₀ ≤ orderedSeedDegree c n u v M)
    (hwords : ∀ r : Fin L, edgeCodeEval a b c n (words r) = B₀ + (r : ℕ) * d)
    (hcorr : ∀ D : ℕ, D₀ ≤ D → ∀ r : ℕ,
      ∃ s : Finset ℕ,
        (∀ z ∈ s, z ∈ Smooth3 a b c) ∧
        (∀ z ∈ s, ∃ i j k : ℕ,
          i + j + k = D ∧ z = eval3 a b c i j k ∧
          (i = 0 ∨ j = 0 ∨ k = 0)) ∧
        IsPrimitive s ∧
          s.sum id ≡ r [MOD orderedSeedStep a b c d] ∧
          s.sum id ≤ Ccorr * c ^ D)
    (hradix : ∀ value : ℕ, U ≤ value → value ≤ V →
      HomogeneousRadixRep (orderedSeedA a u v) (orderedSeedB b c u v) L M value)
    (hpHigh : ∀ x ∈ p, ∃ i j k : ℕ,
      0 < i ∧ 0 < j ∧ 0 < k ∧
        i + j + k = orderedSeedDegree c n u v M ∧
        u * M + edgeDigitDepth c + 1 < j ∧ x = eval3 a b c i j k) :
    ∀ target : ℕ,
      orderedSeedLo a b c n B₀ d u v M Ccorr U ≤ target →
      target ≤ orderedSeedHi a b c B₀ d u v M V →
        ∃ s : Finset ℕ,
          (∀ x ∈ s, x ∈ Smooth3 a b c) ∧
          (∀ x ∈ s, ∃ i j k : ℕ,
            i + j + k = orderedSeedDegree c n u v M ∧
              x = eval3 a b c i j k) ∧
          Disjoint s p ∧ s.sum id = target := by
  intro target htLo htHi
  let G := u + v
  let A := a ^ G
  let B := b ^ u * c ^ v
  let q := a * b * c
  let Step := q * d
  let Mass := homogeneousWeightMass A B M
  let Offset := q * (B₀ * Mass)
  let D := orderedSeedDegree c n u v M
  let Z := Ccorr * c ^ D
  let Lo := Offset + Step * U + Z
  let Hi := Offset + Step * V
  have htLo' : Lo ≤ target := by
    simpa [Lo, Offset, Step, q, Mass, A, B, G, Z, D,
      orderedSeedLo, orderedSeedOffset, orderedSeedStep, orderedSeedA,
      orderedSeedB] using htLo
  have htHi' : target ≤ Hi := by
    simpa [Hi, Offset, Step, q, Mass, A, B, G, orderedSeedHi,
      orderedSeedOffset, orderedSeedStep, orderedSeedA, orderedSeedB] using htHi
  have hOffT : Offset ≤ target := by dsimp [Lo] at htLo'; omega
  let Y := target - Offset
  have hYeq : Offset + Y = target := Nat.add_sub_of_le hOffT
  let r := Y % Step
  have hMDegree' : D₀ ≤ D := by simpa [D] using hMDegree
  rcases hcorr D hMDegree' r with
    ⟨corr, hcorrSmooth, hcorrShape, _hcorrPrim, hcorrMod, hcorrBound⟩
  have hcorrZ : corr.sum id ≤ Z := by simpa [Z] using hcorrBound
  have hZY : Z ≤ Y := by
    dsimp [Lo] at htLo'
    dsimp [Y]
    omega
  have hcorrY : corr.sum id ≤ Y := hcorrZ.trans hZY
  have hYmod : Y ≡ r [MOD Step] := (Nat.mod_modEq Y Step).symm
  have hmodEq : Y ≡ corr.sum id [MOD Step] := hYmod.trans hcorrMod.symm
  have hsubMod := hmodEq.sub hcorrY (le_refl (corr.sum id))
    (Nat.ModEq.refl (n := Step) (corr.sum id))
  have hdvd : Step ∣ Y - corr.sum id := by
    apply Nat.dvd_of_mod_eq_zero
    simpa [Nat.ModEq] using hsubMod
  let coeff := (Y - corr.sum id) / Step
  have hStepCoeff : Step * coeff = Y - corr.sum id :=
    Nat.mul_div_cancel' hdvd
  have hcoeffU : U ≤ coeff := by
    apply (Nat.le_div_iff_mul_le hqd).2
    dsimp [Lo] at htLo'
    have : Step * U + corr.sum id ≤ Y := by omega
    have hmul : Step * U ≤ Y - corr.sum id := Nat.le_sub_of_add_le this
    change U * Step ≤ Y - corr.sum id
    simpa [Nat.mul_comm] using hmul
  have hcoeffV : coeff ≤ V := by
    apply Nat.le_of_mul_le_mul_left (c := Step) _ hqd
    rw [hStepCoeff]
    dsimp [Hi] at htHi'
    have hYV : Y ≤ Step * V := by
      dsimp [Y]
      omega
    exact (Nat.sub_le _ _).trans hYV
  have hcoeffRep := hradix coeff hcoeffU hcoeffV
  rcases homogeneousRadixRep_realized_by_edge_AP ha hb hc hacLt hab hac hbc
      huBand words hwords hcoeffRep with ⟨ap, hapBand, hapSum⟩
  have hapSeed : IsSeedLevelSet a b c D (u * M + edgeDigitDepth c + 1) ap := by
    intro x hx
    rcases hapBand x hx with ⟨i, j, k, hi, hj, hk, hdeg, hjBound, hval⟩
    exact ⟨i, j, k, by simpa [D] using hdeg, hval,
      Or.inr ⟨hi, hj, hk, hjBound⟩⟩
  have hcorrSeed : IsSeedLevelSet a b c D (u * M + edgeDigitDepth c + 1) corr := by
    intro x hx
    rcases hcorrShape x hx with ⟨i, j, k, hdeg, hval, hface⟩
    exact ⟨i, j, k, hdeg, hval, Or.inl hface⟩
  have hdisAPCorr : Disjoint ap corr := by
    rw [Finset.disjoint_left]
    intro x hxap hxcorr
    rcases hapBand x hxap with ⟨i, j, k, _hi, _hj, _hk, _hdeg, _hjB, hval⟩
    rcases hcorrShape x hxcorr with ⟨i', j', k', _hdeg', hval', hface⟩
    have heq : eval3 a b c i j k = eval3 a b c i' j' k' := by
      rw [← hval, ← hval']
    have hd1 : eval3 a b c i j k ∣ eval3 a b c i' j' k' := by rw [heq]
    have hd2 : eval3 a b c i' j' k' ∣ eval3 a b c i j k := by rw [heq]
    have hc1 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd1
    have hc2 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd2
    rcases hface with rfl | rfl | rfl <;> omega
  let s := ap ∪ corr
  have hsSeed : IsSeedLevelSet a b c D (u * M + edgeDigitDepth c + 1) s := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxa | hxc
    · exact hapSeed x hxa
    · exact hcorrSeed x hxc
  refine ⟨s, seedLevelSet_subset_smooth3 hsSeed, ?_,
    seedLevelSet_disjoint_high_shell ha hb hc hab hac hbc hsSeed hpHigh, ?_⟩
  · intro x hx
    rcases hsSeed x hx with ⟨i, j, k, hdeg, hval, _hshape⟩
    exact ⟨i, j, k, hdeg, hval⟩
  · dsimp [s]
    rw [Finset.sum_union hdisAPCorr]
    have hsumEq : Step * coeff + corr.sum id = Y := by
      rw [hStepCoeff]
      exact Nat.sub_add_cancel hcorrY
    calc
      ap.sum id + corr.sum id =
          q * (B₀ * homogeneousWeightMass A B M + d * coeff) + corr.sum id :=
        by rw [hapSum]
      _ = Offset + (Step * coeff + corr.sum id) := by
        dsimp [Offset, Step, Mass]
        ring
      _ = Offset + Y := by rw [hsumEq]
      _ = target := hYeq

/-- The optional interior shell is large enough to extend the base interval up to
the requested multiplicative width. -/
private theorem ordered_seed_room
    {q A B Step U V Z M : ℕ}
    (hZ : Z ≤ B ^ M)
    (hcoef : q + 1 ≤ Step * (2 * A * B))
    (hStepWidth : Step * (2 * A * B ^ (M + 1)) ≤ Step * (V - U)) :
    Z + q * B ^ M ≤ Step * (V - U) := by
  calc
    Z + q * B ^ M ≤ B ^ M + q * B ^ M :=
      Nat.add_le_add_right hZ (q * B ^ M)
    _ = (q + 1) * B ^ M := by ring
    _ ≤ (Step * (2 * A * B)) * B ^ M :=
      Nat.mul_le_mul_right _ hcoef
    _ = Step * (2 * A * B ^ (M + 1)) := by rw [pow_succ]; ring
    _ ≤ Step * (V - U) := hStepWidth

private theorem ordered_seed_lo_le_hi
    {Offset Step U V Z q B M : ℕ}
    (hUV : U ≤ V)
    (hroom : Z + q * B ^ M ≤ Step * (V - U)) :
    Offset + Step * U + Z ≤ Offset + Step * V := by
  have hUVadd : U + (V - U) = V := Nat.add_sub_of_le hUV
  have hZroom : Z ≤ Step * (V - U) :=
    (Nat.le_add_right Z (q * B ^ M)).trans hroom
  calc
    Offset + Step * U + Z = Offset + (Step * U + Z) := by omega
    _ ≤ Offset + (Step * U + Step * (V - U)) :=
      Nat.add_le_add_left (Nat.add_le_add_left hZroom _) _
    _ = Offset + Step * V := by rw [← Nat.mul_add, hUVadd]

private theorem ordered_seed_width
    {Offset Step U V Z q B M : ℕ}
    (hUV : U ≤ V)
    (hroom : Z + q * B ^ M ≤ Step * (V - U)) :
    q * B ^ M ≤ (Offset + Step * V) - (Offset + Step * U + Z) := by
  apply Nat.le_sub_of_add_le
  have hUVadd : U + (V - U) = V := Nat.add_sub_of_le hUV
  calc
    q * B ^ M + (Offset + Step * U + Z) =
        Offset + (Step * U + (Z + q * B ^ M)) := by omega
    _ ≤ Offset + (Step * U + Step * (V - U)) :=
      Nat.add_le_add_left (Nat.add_le_add_left hroom _) _
    _ = Offset + Step * V := by rw [← Nat.mul_add, hUVadd]

private theorem ordered_seed_lo_bound
    {q B₀ Step L Mass B M U Z : ℕ}
    (hMass : Mass ≤ B ^ (M + 1))
    (hUbound : U ≤ L * Mass)
    (hZbound : Z ≤ B ^ (M + 1)) :
    q * (B₀ * Mass) + Step * U + Z ≤
      (q * B₀ + Step * L + 1) * B ^ (M + 1) := by
  have hOff : q * (B₀ * Mass) ≤ (q * B₀) * B ^ (M + 1) := by
    convert Nat.mul_le_mul_left (q * B₀) hMass using 1
    ring
  have hSU : Step * U ≤ (Step * L) * B ^ (M + 1) := by
    calc
      Step * U ≤ Step * (L * Mass) := Nat.mul_le_mul_left Step hUbound
      _ ≤ Step * (L * B ^ (M + 1)) :=
        Nat.mul_le_mul_left Step (Nat.mul_le_mul_left L hMass)
      _ = (Step * L) * B ^ (M + 1) := by ring
  calc
    q * (B₀ * Mass) + Step * U + Z ≤
        (q * B₀) * B ^ (M + 1) + (Step * L) * B ^ (M + 1) +
          B ^ (M + 1) :=
      Nat.add_le_add (Nat.add_le_add hOff hSU) hZbound
    _ = (q * B₀ + Step * L + 1) * B ^ (M + 1) := by ring

private theorem ordered_seed_optional_sum_enough
    {a c q B K M R T Lo : ℕ} {p : Finset ℕ}
    (hc : 1 < c) (hR : 1 < R)
    (hLoBound : Lo ≤ K * B ^ (M + 1))
    (hsumLower : p.card * (a * (q * B ^ M)) ≤ c * p.sum id)
    (haq : 1 ≤ a * q)
    (hpCardT : T ≤ p.card)
    (hTdef : T = c * R * K * B) :
    (R - 1) * Lo ≤ p.sum id := by
  have hscaledLo : c * ((R - 1) * Lo) ≤ c * p.sum id := by
    calc
      c * ((R - 1) * Lo) ≤
          c * ((R - 1) * (K * B ^ (M + 1))) :=
        Nat.mul_le_mul_left c (Nat.mul_le_mul_left (R - 1) hLoBound)
      _ ≤ p.card * (a * (q * B ^ M)) := by
        have hpow : B ^ (M + 1) = B * B ^ M := by rw [pow_succ]; ring
        rw [hpow]
        have hcoefT : c * (R - 1) * K * B ≤ p.card := by
          calc
            c * (R - 1) * K * B ≤ c * R * K * B := by
              gcongr
              omega
            _ = T := hTdef.symm
            _ ≤ p.card := hpCardT
        calc
          c * ((R - 1) * (K * (B * B ^ M))) =
              (c * (R - 1) * K * B) * B ^ M := by ring
          _ ≤ p.card * B ^ M := Nat.mul_le_mul_right _ hcoefT
          _ ≤ p.card * (a * q * B ^ M) := by
            have hh : B ^ M ≤ a * q * B ^ M := by
              simpa only [one_mul] using Nat.mul_le_mul_right (B ^ M) haq
            exact Nat.mul_le_mul_left p.card hh
          _ = p.card * (a * (q * B ^ M)) := by ring
      _ ≤ c * p.sum id := hsumLower
  exact Nat.le_of_mul_le_mul_left hscaledLo (by omega : 0 < c)

/-- Ordered bases `a<c<b` have primitive represented intervals of arbitrarily
large multiplicative width.  The construction combines a homogeneous AP-radix
interval, exact-degree face corrections, and a long optional interior shell. -/
theorem ordered_arbitrarily_wide_primitive_seed
    {a b c R Nmin : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hacLt : a < c) (hcb : c < b)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hR : 1 < R) :
    ∃ N : ℕ, Nmin ≤ N ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n → n ≤ R * N →
      IsRepresentable (Smooth3 a b c) n := by
  let H := edgeDigitDepth c
  let u := H + 2
  have hu : 0 < u := by dsimp [u]; omega
  have huBand : edgeDigitDepth c + 1 < u := by dsimp [u, H]; omega
  rcases exists_positive_pow_multiple_le (a := a) (c := c) (K := 2 * b) hacLt with
    ⟨v, hv, hvDom⟩
  let G := u + v
  let A := a ^ G
  let B := b ^ u * c ^ v
  let q := a * b * c
  let L := 4 * A * B
  have hG : 0 < G := by dsimp [G]; omega
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hAB : A < B := by
    have hacPow : a ^ G < c ^ G := Nat.pow_lt_pow_left hacLt (Nat.ne_of_gt hG)
    have hcbPow : c ^ u < b ^ u := Nat.pow_lt_pow_left hcb (Nat.ne_of_gt hu)
    calc
      A = a ^ G := rfl
      _ < c ^ G := hacPow
      _ = c ^ u * c ^ v := by dsimp [G]; rw [pow_add]
      _ ≤ b ^ u * c ^ v := Nat.mul_le_mul_right (c ^ v) hcbPow.le
      _ = B := rfl
  have hcopAB : Nat.Coprime A B := by
    have ha_bc : Nat.Coprime a (b * c) := hab.mul_right hac
    have ha_bu : Nat.Coprime (a ^ G) (b ^ u) := hab.pow G u
    have ha_cv : Nat.Coprime (a ^ G) (c ^ v) := hac.pow G v
    exact ha_bu.mul_right ha_cv
  have hL : 1 < L := by
    change 1 < 4 * A * B
    have hA1 : 1 ≤ A := hA
    have hB1 : 1 ≤ B := hB
    nlinarith
  rcases edgeCodeEval_arbitrarily_long_progressions ha hb hc hacLt hab hac hbc L hL with
    ⟨n₀, B₀, d, hd, words, hwords⟩
  let δ := H + n₀ - 1
  have hqd : 0 < q * d := by dsimp [q]; positivity
  rcases exact_degree_bounded_face_corrections ha hb hc hacLt.le hab hac hbc hqd with
    ⟨Ccorr, D₀, hCcorr, hcorr⟩
  have hsmallShellBase : b * a ^ v < c ^ v := by
    have hpos : 0 < b * a ^ v := by positivity
    nlinarith [hvDom]
  rcases eventually_const_mul_pow_le_pow (C := a ^ δ) hsmallShellBase with
    ⟨Nshell, hNshell⟩
  have hsmallCorrBase : c ^ G < B := by
    dsimp [G, B]
    rw [pow_add]
    have hpow := Nat.pow_lt_pow_left hcb (Nat.ne_of_gt hu)
    exact Nat.mul_lt_mul_of_pos_right hpow (pow_pos (by omega) v)
  rcases eventually_const_mul_pow_le_pow
      (C := Ccorr * c ^ (δ + 3)) hsmallCorrBase with
    ⟨Ncorr, hNcorr⟩
  let Step := q * d
  let K := q * B₀ + Step * L + 1
  let T := c * R * K * B
  let M := Nshell + Ncorr + D₀ + T + Nmin + H + 3
  have hMNshell : Nshell ≤ M := by dsimp [M]; omega
  have hMNcorr : Ncorr ≤ M := by dsimp [M]; omega
  have hMDegree : D₀ ≤ δ + G * M + 3 := by
    have hD0M : D₀ ≤ M := by dsimp [M]; omega
    have hGM : M ≤ G * M := by
      simpa only [one_mul] using Nat.mul_le_mul_right M (by omega : 1 ≤ G)
    exact hD0M.trans (hGM.trans (by omega))
  have hHM : H + 2 ≤ M := by dsimp [M]; omega
  have hcardTarget : T ≤ M - (H + 2) + 1 := by dsimp [M]; omega
  have hshellDom : a ^ δ * (b * a ^ v) ^ M ≤ (c ^ v) ^ M :=
    hNshell M hMNshell
  have hcorrDom0 :
      (Ccorr * c ^ (δ + 3)) * (c ^ G) ^ M ≤ B ^ M :=
    hNcorr M hMNcorr
  let D := δ + G * M + 3
  have hcorrDom : Ccorr * c ^ D ≤ B ^ M := by
    dsimp [D]
    rw [show δ + G * M + 3 = (δ + 3) + G * M by omega, pow_add,
      show c ^ (G * M) = (c ^ G) ^ M by rw [pow_mul]]
    simpa [mul_assoc] using hcorrDom0
  rcases homogeneousRadixRep_large_interval hA hB hcopAB M with
    ⟨U, V, hUV, hwidth, hradix⟩
  let Mass := homogeneousWeightMass A B M
  let Offset := q * (B₀ * Mass)
  let Z := Ccorr * c ^ D
  let Lo := Offset + Step * U + Z
  let Hi := Offset + Step * V
  have hMass : Mass ≤ B ^ (M + 1) :=
    homogeneousWeightMass_le_pow hA hAB
  have hUbound : U ≤ L * Mass :=
    (HomogeneousRadixRep.le_mass (hradix U (le_refl U) hUV))
  have hZ : Z ≤ B ^ M := by exact hcorrDom
  have hBpowStep : B ^ M ≤ B ^ (M + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hStepWidth : Step * (2 * A * B ^ (M + 1)) ≤ Step * (V - U) :=
    Nat.mul_le_mul_left Step hwidth
  have hcoef : q + 1 ≤ Step * (2 * A * B) := by
    have hq : 0 < q := by dsimp [q]; positivity
    have hfactor : 1 ≤ d * A * B :=
      (Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (Nat.ne_of_gt hd) (Nat.ne_of_gt hA))
          (Nat.ne_of_gt hB)))
    calc
      q + 1 ≤ 2 * q := by omega
      _ ≤ (2 * q) * (d * A * B) := Nat.le_mul_of_pos_right _ hfactor
      _ = Step * (2 * A * B) := by dsimp [Step]; ring
  have hroom : Z + q * B ^ M ≤ Step * (V - U) :=
    ordered_seed_room hZ hcoef hStepWidth
  have hLoHi : Lo ≤ Hi := by
    simpa [Lo, Hi] using
      ordered_seed_lo_le_hi (Offset := Offset) (Step := Step) (U := U) (V := V)
        (Z := Z) (q := q) (B := B) (M := M) hUV hroom
  have hWidthX : q * B ^ M ≤ Hi - Lo := by
    simpa [Lo, Hi] using
      ordered_seed_width (Offset := Offset) (Step := Step) (U := U) (V := V)
        (Z := Z) (q := q) (B := B) (M := M) hUV hroom
  have hLoBound : Lo ≤ K * B ^ (M + 1) := by
    simpa [Lo, K, Offset] using
      ordered_seed_lo_bound (q := q) (B₀ := B₀) (Step := Step) (L := L)
        (Mass := Mass) (B := B) (M := M) (U := U) (Z := Z)
        hMass hUbound (hZ.trans hBpowStep)
  have hLoPos : 0 < Lo := by
    have hZpos : 0 < Z := by dsimp [Z]; positivity
    dsimp [Lo]
    omega
  have hsucc_le_cpow : ∀ t : ℕ, t + 1 ≤ c ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        rw [pow_succ]
        have hc2 : 2 ≤ c := by omega
        calc
          t + 1 + 1 ≤ 2 * (t + 1) := by omega
          _ ≤ c * c ^ t := Nat.mul_le_mul hc2 ih
          _ = c ^ t * c := by ring
  have hNminLo : Nmin ≤ Lo := by
    have hNminM : Nmin ≤ M := by dsimp [M]; omega
    have hMD : M ≤ D := by
      have hGM : M ≤ G * M := by
        simpa only [one_mul] using Nat.mul_le_mul_right M (by omega : 1 ≤ G)
      dsimp [D]
      omega
    have hcD : D + 1 ≤ c ^ D := hsucc_le_cpow D
    have hcZ : c ^ D ≤ Z := by
      dsimp [Z]
      exact Nat.le_mul_of_pos_left _ hCcorr
    have hDleZ : D ≤ Z := (Nat.le_add_right D 1).trans (hcD.trans hcZ)
    have hZleLo : Z ≤ Lo := by dsimp [Lo]; omega
    exact hNminM.trans (hMD.trans (hDleZ.trans hZleLo))
  rcases exists_long_interior_shell ha hb hc hacLt hcb hab hac hbc hu hv hHM
      hshellDom (H := H) with ⟨p, hpCard, hpShape, hpSmooth, hpPrim, hpBounds⟩
  have hpDegree : ∀ x ∈ p, ∃ i j k : ℕ,
      i + j + k = D ∧ x = eval3 a b c i j k := by
    intro x hx
    rcases hpShape x hx with ⟨i, j, k, _hi, _hj, _hk, hdeg, _hhigh, hval⟩
    exact ⟨i, j, k, by simpa [D] using hdeg, hval⟩
  have hpHigh : ∀ x ∈ p, ∃ i j k : ℕ,
      0 < i ∧ 0 < j ∧ 0 < k ∧ i + j + k = D ∧
        u * M + H + 1 < j ∧ x = eval3 a b c i j k := by
    intro x hx
    rcases hpShape x hx with ⟨i, j, k, hi, hj, hk, hdeg, hhigh, hval⟩
    exact ⟨i, j, k, hi, hj, hk, by simpa [D] using hdeg, by omega, hval⟩
  have hpFit : ∀ x ∈ p, x ≤ Hi - Lo + 1 := by
    intro x hx
    have hxX : x ≤ q * B ^ M := by
      simpa [q, B] using (hpBounds x hx).1
    exact hxX.trans (hWidthX.trans (Nat.le_add_right _ 1))
  have hbase : ∀ target : ℕ, Lo ≤ target → target ≤ Hi →
      ∃ s : Finset ℕ,
        (∀ x ∈ s, x ∈ Smooth3 a b c) ∧
        (∀ x ∈ s, ∃ i j k : ℕ,
          i + j + k = D ∧ x = eval3 a b c i j k) ∧
        Disjoint s p ∧ s.sum id = target := by
    have hbase' := ordered_seed_base_interval
      (a := a) (b := b) (c := c) (n := n₀) (L := L) (B₀ := B₀) (d := d)
      (u := u) (v := v) (M := M) (Ccorr := Ccorr) (D₀ := D₀)
      (U := U) (V := V) (words := words) (p := p)
      ha hb hc hacLt hab hac hbc huBand
      (by simpa [orderedSeedStep, q] using hqd)
      (by simpa [orderedSeedDegree, D, δ, G, H] using hMDegree)
      hwords
      (by
        intro D' hD' r
        simpa [orderedSeedStep, q] using hcorr D' hD' r)
      (by
        intro value hU hV
        simpa [orderedSeedA, orderedSeedB, A, B, G] using hradix value hU hV)
      (by
        intro x hx
        rcases hpHigh x hx with ⟨i, j, k, hi, hj, hk, hdeg, hjHigh, hval⟩
        exact ⟨i, j, k, hi, hj, hk,
          by simpa [orderedSeedDegree, D, δ, G, H] using hdeg,
          by simpa [H] using hjHigh, hval⟩)
    simpa [orderedSeedLo, orderedSeedHi, orderedSeedOffset, orderedSeedStep,
      orderedSeedA, orderedSeedB, orderedSeedDegree, Lo, Hi, Offset, Step, q,
      Mass, A, B, G, D, δ, H] using hbase'
  have hsumLower : p.card * (a * (q * B ^ M)) ≤ c * p.sum id := by
    have hsum := Finset.sum_le_sum (s := p) (fun x hx => (hpBounds x hx).2)
    calc
      p.card * (a * (q * B ^ M)) =
          ∑ _x ∈ p, a * (a * b * c * (b ^ u * c ^ v) ^ M) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        dsimp [q, B]
      _ ≤ ∑ x ∈ p, c * x := hsum
      _ = c * p.sum id := by
        rw [Finset.mul_sum]
        simp only [id_eq]
  have hpCardT : T ≤ p.card := hcardTarget.trans hpCard
  have hoptionalEnough : (R - 1) * Lo ≤ p.sum id :=
    ordered_seed_optional_sum_enough hc hR hLoBound hsumLower
      (by
        have hqpos : 0 < q := by dsimp [q]; positivity
        have hapq : 0 < a * q := Nat.mul_pos (by omega : 0 < a) hqpos
        omega) hpCardT rfl
  have hRLo : R * Lo ≤ Hi + p.sum id := by
    have hbaseWidth : Lo ≤ Hi := hLoHi
    have hRdecomp : R - 1 + 1 = R := Nat.sub_add_cancel (by omega : 1 ≤ R)
    calc
      R * Lo = (R - 1 + 1) * Lo := by rw [hRdecomp]
      _ = Lo + (R - 1) * Lo := by ring
      _ ≤ Hi + p.sum id := Nat.add_le_add hbaseWidth hoptionalEnough
  refine ⟨Lo, hNminLo, hLoPos, ?_⟩
  intro target htLo htR
  apply representable_interval_extend_by_level_finset ha hb hc hab hac hbc
    hLoHi hpFit hpSmooth hpDegree hbase target htLo
  exact htR.trans hRLo

/-- The arbitrarily wide seed discharges the flexible finite-seed gate for
strictly ordered bases `a<c<b`. -/
theorem ordered_three_base_is_dComplete
    {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hacLt : a < c) (hcb : c < b)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    IsDComplete (Smooth3 a b c) := by
  rcases flexible_finite_seed_gate ha hb hc hab hac hbc with
    ⟨N₀, C, hN₀, hC, hgate⟩
  rcases ordered_arbitrarily_wide_primitive_seed ha hb hc hacLt hcb hab hac hbc hC
      (Nmin := N₀) with ⟨N, hN₀N, _hNpos, hseed⟩
  exact hgate N hN₀N hseed

/-- Swapping the first two bases does not change the smooth set. -/
theorem smooth3_swap12 (a b c : ℕ) : Smooth3 a b c = Smooth3 b a c := by
  ext x
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨j, i, k, by ac_rfl⟩
  · rintro ⟨j, i, k, rfl⟩
    exact ⟨i, j, k, by ac_rfl⟩

/-- Swapping the last two bases does not change the smooth set. -/
theorem smooth3_swap23 (a b c : ℕ) : Smooth3 a b c = Smooth3 a c b := by
  ext x
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨i, k, j, by ac_rfl⟩
  · rintro ⟨i, k, j, rfl⟩
    exact ⟨i, j, k, by ac_rfl⟩

/-- A cyclic permutation does not change the smooth set. -/
theorem smooth3_cycle (a b c : ℕ) : Smooth3 a b c = Smooth3 b c a := by
  ext x
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨j, k, i, by ac_rfl⟩
  · rintro ⟨j, k, i, rfl⟩
    exact ⟨i, j, k, by ac_rfl⟩

/-- Every pairwise-coprime triple of bases greater than one is d-complete. -/
theorem intended_erdos_123 : IntendedStatement := by
  intro a b c ha hb hc hpw
  rcases hpw with ⟨hab, hac, hbc⟩
  have habne : a ≠ b := by
    intro heq
    subst b
    rw [Nat.coprime_self] at hab
    omega
  have hacne : a ≠ c := by
    intro heq
    subst c
    rw [Nat.coprime_self] at hac
    omega
  have hbcne : b ≠ c := by
    intro heq
    subst c
    rw [Nat.coprime_self] at hbc
    omega
  have horders :
      (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨
      (b < a ∧ a < c) ∨ (b < c ∧ c < a) ∨
      (c < a ∧ a < b) ∨ (c < b ∧ b < a) := by
    omega
  rcases horders with habc | hacb | hbac | hbca | hcab | hcba
  · have h := ordered_three_base_is_dComplete ha hc hb
      habc.1 (habc.2) hac hab hbc.symm
    rw [smooth3_swap23] at h
    exact h
  · exact ordered_three_base_is_dComplete ha hb hc hacb.1 hacb.2 hab hac hbc
  · have h := ordered_three_base_is_dComplete hb hc ha
      hbac.1 hbac.2 hbc hab.symm hac.symm
    rw [show Smooth3 b c a = Smooth3 a b c by
      exact (smooth3_cycle a b c).symm] at h
    exact h
  · have h := ordered_three_base_is_dComplete hb ha hc
      hbca.1 hbca.2 hab.symm hbc hac
    rw [smooth3_swap12] at h
    exact h
  · have h := ordered_three_base_is_dComplete hc hb ha
      hcab.1 hcab.2 hbc.symm hac.symm hab.symm
    rw [show Smooth3 c b a = Smooth3 a b c by
      calc
        Smooth3 c b a = Smooth3 b a c := smooth3_cycle c b a
        _ = Smooth3 a b c := smooth3_swap12 b a c] at h
    exact h
  · have h := ordered_three_base_is_dComplete hc ha hb
      hcba.1 hcba.2 hac.symm hbc.symm hab
    rw [show Smooth3 c a b = Smooth3 a b c by exact smooth3_cycle c a b] at h
    exact h

/-- Erdős Problem 123 for the intended nondegenerate hypothesis `a,b,c>1`. -/
theorem erdos_123 : IntendedStatement := intended_erdos_123
end
end Erdos123

#print axioms Erdos123.erdos_123
-- 'Erdos123.erdos_123' depends on axioms: [propext, Classical.choice, Quot.sound]

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.PSeries
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Primorial

/-!
# Prime-chain combinatorics for Erdős 48

The analytic Ford--Konyagin--Luca estimate counts the finite target set
defined here.  This file records the order and closure facts independently
of that estimate.
-/

namespace Erdos48

open scoped BigOperators

/-! ## A finite-state contraction lemma

The Ford--Konyagin--Luca proof encodes links in a prime chain by a
nonnegative matrix indexed by reduced residue classes.  The source uses the
maximum row sum rather than Perron--Frobenius theory.  The following generic
recursion is that argument, separated from the arithmetic evaluation of the
row sum. -/

section FiniteStateContraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight of all length-`k` directed paths from `a` to `b`, with the
matrix convention that rows are destinations and columns are sources. -/
noncomputable def pathWeight (w : ι → ι → ℝ) : ℕ → ι → ι → ℝ
  | 0, b, a => if b = a then 1 else 0
  | k + 1, b, a => ∑ c : ι, w b c * pathWeight w k c a

@[simp] lemma pathWeight_zero (w : ι → ι → ℝ) (b a : ι) :
    pathWeight w 0 b a = if b = a then 1 else 0 := rfl

@[simp] lemma pathWeight_succ (w : ι → ι → ℝ) (k : ℕ) (b a : ι) :
    pathWeight w (k + 1) b a =
      ∑ c : ι, w b c * pathWeight w k c a := rfl

lemma pathWeight_nonneg {w : ι → ι → ℝ}
    (hw : ∀ b a, 0 ≤ w b a) (k : ℕ) (b a : ι) :
    0 ≤ pathWeight w k b a := by
  induction k generalizing b a with
  | zero => simp only [pathWeight]; split <;> positivity
  | succ k ih =>
      rw [pathWeight_succ]
      exact Finset.sum_nonneg fun c _ ↦ mul_nonneg (hw b c) (ih c a)

/-- If every row of a nonnegative transition matrix has mass at most `R`,
then every entry of its `k`-fold path matrix is at most `R^k`. -/
lemma pathWeight_le_pow {w : ι → ι → ℝ} {R : ℝ}
    (hw : ∀ b a, 0 ≤ w b a) (hR : 0 ≤ R)
    (hrow : ∀ b, (∑ a : ι, w b a) ≤ R)
    (k : ℕ) (b a : ι) :
    pathWeight w k b a ≤ R ^ k := by
  induction k generalizing b a with
  | zero => simp only [pathWeight, pow_zero]; split <;> norm_num
  | succ k ih =>
      rw [pathWeight_succ, pow_succ]
      calc
        (∑ c : ι, w b c * pathWeight w k c a)
            ≤ ∑ c : ι, w b c * R ^ k := by
              apply Finset.sum_le_sum
              intro c _
              exact mul_le_mul_of_nonneg_left (ih c a) (hw b c)
        _ = (∑ c : ι, w b c) * R ^ k := by rw [Finset.sum_mul]
        _ ≤ R * R ^ k :=
          mul_le_mul_of_nonneg_right (hrow b) (pow_nonneg hR k)
        _ = R ^ k * R := mul_comm _ _

/-- Consequently, a column sum is bounded by the number of states times
`R^k`.  This is the crude column estimate used in the FKL paper. -/
lemma sum_pathWeight_le_card_mul_pow {w : ι → ι → ℝ} {R : ℝ}
    (hw : ∀ b a, 0 ≤ w b a) (hR : 0 ≤ R)
    (hrow : ∀ b, (∑ a : ι, w b a) ≤ R)
    (k : ℕ) (a : ι) :
    (∑ b : ι, pathWeight w k b a) ≤ Fintype.card ι * R ^ k := by
  calc
    (∑ b : ι, pathWeight w k b a) ≤ ∑ _b : ι, R ^ k :=
      Finset.sum_le_sum fun b _ ↦ pathWeight_le_pow hw hR hrow k b a
    _ = Fintype.card ι * R ^ k := by simp

/-- Summing over every path length up to a finite cutoff costs the geometric
factor `(1-R)⁻¹`. -/
lemma sum_range_sum_pathWeight_le {w : ι → ι → ℝ} {R : ℝ}
    (hw : ∀ b a, 0 ≤ w b a) (hR : 0 ≤ R) (hRone : R < 1)
    (hrow : ∀ b, (∑ a : ι, w b a) ≤ R)
    (L : ℕ) (a : ι) :
    (∑ k ∈ Finset.range (L + 1), ∑ b : ι, pathWeight w k b a) ≤
      Fintype.card ι / (1 - R) := by
  calc
    (∑ k ∈ Finset.range (L + 1), ∑ b : ι, pathWeight w k b a)
        ≤ ∑ k ∈ Finset.range (L + 1), Fintype.card ι * R ^ k := by
          exact Finset.sum_le_sum fun k _ ↦
            sum_pathWeight_le_card_mul_pow hw hR hrow k a
    _ = Fintype.card ι * (∑ k ∈ Finset.range (L + 1), R ^ k) := by
      rw [Finset.mul_sum]
    _ ≤ Fintype.card ι * (1 / (1 - R)) := by
      apply mul_le_mul_of_nonneg_left
      · have hgeom :=
          geom_sum_Ico_le_of_lt_one (m := 0) (n := L + 1) hR hRone
        convert hgeom using 1 <;> simp
      · positivity
    _ = Fintype.card ι / (1 - R) := by ring

end FiniteStateContraction

/-- Every fiber of a surjective homomorphism of finite groups has the same
cardinality; multiplying it by the codomain cardinality recovers the domain
cardinality.  This finite form avoids quotient-cardinality bookkeeping in
the reduced-residue calculation below. -/
lemma card_fiber_mul_card_eq_of_surjective
    {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq H]
    (f : G →* H) (hf : Function.Surjective f) (y : H) :
    ((Finset.univ.filter fun x : G ↦ f x = y).card) * Fintype.card H =
      Fintype.card G := by
  classical
  have hpartition :
      Fintype.card G =
        ∑ z : H, (Finset.univ.filter fun x : G ↦ f x = z).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset G)) (t := (Finset.univ : Finset H))
        (f := f) (fun _ _ ↦ Finset.mem_univ _))
  have hequal (z : H) :
      (Finset.univ.filter fun x : G ↦ f x = z).card =
        (Finset.univ.filter fun x : G ↦ f x = y).card := by
    exact MonoidHom.card_fiber_eq_of_mem_range f (hf z) (hf y)
  calc
    (Finset.univ.filter fun x : G ↦ f x = y).card * Fintype.card H =
        ∑ _z : H, (Finset.univ.filter fun x : G ↦ f x = y).card := by
          simp [mul_comm]
    _ = ∑ z : H, (Finset.univ.filter fun x : G ↦ f x = z).card := by
      exact Finset.sum_congr rfl fun z _ ↦ (hequal z).symm
    _ = Fintype.card G := hpartition.symm

/-! ## The sifted link matrix -/

/-- Reduced residue classes modulo `r`, represented as units of `ZMod r`.
This representation makes reduction to a divisor modulus a genuine group
homomorphism, which is the clean way to count the fibers occurring in an
FKL row. -/
abbrev ReducedResidue (r : ℕ) := (ZMod r)ˣ

noncomputable instance (r : ℕ) [NeZero r] : Fintype (ReducedResidue r) :=
  Fintype.ofFinite (ReducedResidue r)
noncomputable instance (r : ℕ) [NeZero r] : DecidableEq (ReducedResidue r) :=
  Classical.decEq (ReducedResidue r)

/-- The standard representative of a reduced residue class. -/
def ReducedResidue.val {r : ℕ} (a : ReducedResidue r) : ℕ :=
  a.1.val

/-- One summand in the FKL link series from residue `a` to residue `b`.
The zero multiplier is excluded explicitly. -/
noncomputable def linkTerm (r : ℕ) (s : ℝ)
    (b a : ReducedResidue r) (m : ℕ) : ℝ :=
  if 0 < m ∧ (a.val * m + 1) % r = b.val then (m : ℝ) ^ (-s) else 0

/-- The weighted series of all possible multipliers taking residue `a` to
residue `b`. -/
noncomputable def linkWeight (r : ℕ) (s : ℝ)
    (b a : ReducedResidue r) : ℝ :=
  ∑' m : ℕ, linkTerm r s b a m

lemma summable_linkTerm {r : ℕ} {s : ℝ} (hs : 1 < s)
    (b a : ReducedResidue r) :
    Summable (linkTerm r s b a) := by
  have hbase : Summable (fun m : ℕ ↦ (m : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  let A : Set ℕ := {m | 0 < m ∧ (a.val * m + 1) % r = b.val}
  have hind : Summable (A.indicator fun m : ℕ ↦ (m : ℝ) ^ (-s)) :=
    hbase.indicator A
  exact hind.congr fun m ↦ by
    by_cases hm : 0 < m ∧ (a.val * m + 1) % r = b.val
    · simp [A, Set.indicator, linkTerm, hm]
    · simp [A, Set.indicator, linkTerm, hm]

lemma linkTerm_nonneg (r : ℕ) (s : ℝ)
    (b a : ReducedResidue r) (m : ℕ) :
    0 ≤ linkTerm r s b a m := by
  dsimp [linkTerm]
  split <;> positivity

lemma linkWeight_nonneg (r : ℕ) (s : ℝ)
    (b a : ReducedResidue r) :
    0 ≤ linkWeight r s b a := by
  exact tsum_nonneg fun m ↦ linkTerm_nonneg r s b a m

/-- A finite row sum can be moved inside the absolutely convergent link
series.  This is the first reduction in the arithmetic evaluation of an FKL
row. -/
lemma sum_linkWeight_eq_tsum_sum {r : ℕ} [NeZero r] {s : ℝ} (hs : 1 < s)
    (b : ReducedResidue r) :
    (∑ a : ReducedResidue r, linkWeight r s b a) =
      ∑' m : ℕ, ∑ a : ReducedResidue r, linkTerm r s b a m := by
  rw [Summable.tsum_finsetSum]
  · rfl
  · intro a _
    exact summable_linkTerm hs b a

/-- The reduced residue classes which solve one link congruence for a fixed
multiplier. -/
noncomputable def linkSources (r : ℕ) [NeZero r]
    (b : ReducedResidue r) (m : ℕ) :
    Finset (ReducedResidue r) :=
  Finset.univ.filter fun a ↦ (a.val * m + 1) % r = b.val

@[simp] lemma mem_linkSources {r : ℕ} [NeZero r]
    {b : ReducedResidue r} {m : ℕ}
    {a : ReducedResidue r} :
    a ∈ linkSources r b m ↔ (a.val * m + 1) % r = b.val := by
  simp [linkSources]

/-- For a positive multiplier, one horizontal slice of the link series is
its common analytic weight times the number of congruence solutions. -/
lemma sum_linkTerm_eq_card_mul {r m : ℕ} [NeZero r] {s : ℝ}
    (b : ReducedResidue r) (hm : 0 < m) :
    (∑ a : ReducedResidue r, linkTerm r s b a m) =
      (linkSources r b m).card * (m : ℝ) ^ (-s) := by
  classical
  simp only [linkTerm, hm, true_and]
  rw [← Finset.sum_filter]
  simp [linkSources]

/-- For squarefree `r`, one multiplier has at most `φ(gcd(m,r))`
possible source classes in any row.  If the congruence is soluble this is an
equality: after cancelling `gcd(m,r)`, its solutions are one fiber of the
surjective reduction map `(ZMod r)ˣ → (ZMod (r/gcd(m,r)))ˣ`. -/
lemma card_linkSources_le_totient_gcd {r m : ℕ} [NeZero r]
    (hr : Squarefree r) (b : ReducedResidue r) :
    (linkSources r b m).card ≤ (m.gcd r).totient := by
  classical
  let d := m.gcd r
  let R := r / d
  have hrpos : 0 < r := NeZero.pos r
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_right m hrpos
  have hdr : d ∣ r := by
    dsimp [d]
    exact Nat.gcd_dvd_right m r
  have hdm : d ∣ m := by
    dsimp [d]
    exact Nat.gcd_dvd_left m r
  have hRpos : 0 < R := by
    dsimp [R]
    exact Nat.div_pos (Nat.gcd_le_right m hrpos) hdpos
  let _ : NeZero R := ⟨hRpos.ne'⟩
  have hRr : R ∣ r := by
    dsimp [R]
    exact Nat.div_dvd_of_dvd hdr
  let f : ReducedResidue r →* ReducedResidue R := ZMod.unitsMap hRr
  by_cases hsource : linkSources r b m = ∅
  · simp [hsource]
  obtain ⟨a₀, ha₀⟩ := Finset.nonempty_iff_ne_empty.mpr hsource
  have hfiber :
      linkSources r b m = Finset.univ.filter fun a : ReducedResidue r ↦
        f a = f a₀ := by
    ext a
    simp only [mem_linkSources, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      have hmod : a.val * m + 1 ≡ a₀.val * m + 1 [MOD r] := by
        show (a.val * m + 1) % r = (a₀.val * m + 1) % r
        rw [ha, mem_linkSources.mp ha₀]
      have hmul : a.val * m ≡ a₀.val * m [MOD r] :=
        Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) hmod
      have hcancel : a.val ≡ a₀.val [MOD R] := by
        simpa only [R, d, Nat.gcd_comm] using
          hmul.cancel_right_div_gcd hrpos
      apply Units.ext
      change ((a : ZMod r).cast : ZMod R) = (a₀ : ZMod r).cast
      rw [← ZMod.natCast_zmod_val (a : ZMod r),
        ← ZMod.natCast_zmod_val (a₀ : ZMod r),
        ZMod.cast_natCast hRr, ZMod.cast_natCast hRr]
      exact (ZMod.natCast_eq_natCast_iff a.val a₀.val R).2 hcancel
    · intro ha
      have hcast : ((a : ZMod r).cast : ZMod R) = (a₀ : ZMod r).cast := by
        exact congrArg Units.val ha
      have hnat : (a.val : ZMod R) = (a₀.val : ZMod R) := by
        rw [← ZMod.natCast_zmod_val (a : ZMod r),
          ← ZMod.natCast_zmod_val (a₀ : ZMod r),
          ZMod.cast_natCast hRr, ZMod.cast_natCast hRr] at hcast
        exact hcast
      have hmodR : a.val ≡ a₀.val [MOD R] :=
        (ZMod.natCast_eq_natCast_iff a.val a₀.val R).1 hnat
      have hprod : a.val * m ≡ a₀.val * m [MOD r] := by
        have hscaled := (hmodR.mul_right (m / d)).mul_right' d
        simpa only [R, Nat.div_mul_cancel hdr, Nat.div_mul_cancel hdm,
          mul_assoc] using hscaled
      have hadd := hprod.add_right 1
      show (a.val * m + 1) % r = b.val
      have hbval : b.val < r := ZMod.val_lt b.1
      have ha₀mod : a₀.val * m + 1 ≡ b.val [MOD r] := by
        show (a₀.val * m + 1) % r = b.val % r
        simpa only [Nat.mod_eq_of_lt hbval] using mem_linkSources.mp ha₀
      have hfinal := hadd.trans ha₀mod
      change (a.val * m + 1) % r = b.val % r at hfinal
      rw [Nat.mod_eq_of_lt hbval] at hfinal
      exact hfinal
  have hcard := card_fiber_mul_card_eq_of_surjective f
    (ZMod.unitsMap_surjective hRr) (f a₀)
  have hcardR : Fintype.card (ReducedResidue R) = R.totient :=
    ZMod.card_units_eq_totient R
  have hcardr : Fintype.card (ReducedResidue r) = r.totient :=
    ZMod.card_units_eq_totient r
  rw [← hfiber, hcardR, hcardr] at hcard
  have hcop : R.Coprime d := by
    have hgd : r.gcd d = d := Nat.gcd_eq_right_iff_dvd.mpr hdr
    have hc := Nat.coprime_div_gcd_of_squarefree hr hdpos.ne'
    simpa only [R, hgd] using hc
  have htot : r.totient = R.totient * d.totient := by
    rw [← Nat.div_mul_cancel hdr, Nat.totient_mul hcop]
  have hcancel : R.totient * (linkSources r b m).card =
      R.totient * d.totient := by
    simpa only [htot, mul_comm] using hcard
  have heq : (linkSources r b m).card = d.totient :=
    Nat.mul_left_cancel (Nat.totient_pos.mpr hRpos) hcancel
  simpa only [d] using heq.le

/-- Solubility of the link congruence fixes the gcd class of its multiplier:
it is the gcd of `b-1` with the modulus. -/
lemma gcd_eq_gcd_pred_of_mem_linkSources {r m : ℕ} [NeZero r]
    (hr : 2 ≤ r) (b : ReducedResidue r) {a : ReducedResidue r}
    (ha : a ∈ linkSources r b m) :
    m.gcd r = (b.val - 1).gcd r := by
  have hbCoprime : b.val.Coprime r := ZMod.val_coe_unit_coprime b
  have hbpos : 0 < b.val := by
    by_contra hb
    have hbzero : b.val = 0 := Nat.eq_zero_of_not_pos hb
    rw [hbzero, Nat.coprime_zero_left] at hbCoprime
    omega
  have hbval : b.val < r := ZMod.val_lt b.1
  have hmodAdd : a.val * m + 1 ≡ b.val [MOD r] := by
    show (a.val * m + 1) % r = b.val % r
    simpa only [Nat.mod_eq_of_lt hbval] using mem_linkSources.mp ha
  have hmod : a.val * m ≡ b.val - 1 [MOD r] := by
    have hbRewrite : b.val = (b.val - 1) + 1 :=
      (Nat.sub_add_cancel hbpos).symm
    rw [hbRewrite] at hmodAdd
    exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) hmodAdd
  calc
    m.gcd r = (a.val * m).gcd r :=
      (ZMod.val_coe_unit_coprime a).gcd_mul_left_cancel m |>.symm
    _ = (b.val - 1).gcd r := hmod.gcd_eq

/-- The nonnegative Dirichlet-series term belonging to one gcd class. -/
noncomputable def gcdClassTerm (r d : ℕ) (s : ℝ) (m : ℕ) : ℝ :=
  if 0 < m ∧ m.gcd r = d then (m : ℝ) ^ (-s) else 0

lemma gcdClassTerm_nonneg (r d : ℕ) (s : ℝ) (m : ℕ) :
    0 ≤ gcdClassTerm r d s m := by
  simp only [gcdClassTerm]
  split <;> positivity

lemma summable_gcdClassTerm {r d : ℕ} {s : ℝ} (hs : 1 < s) :
    Summable (gcdClassTerm r d s) := by
  have hbase : Summable (fun m : ℕ ↦ (m : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  let A : Set ℕ := {m | 0 < m ∧ m.gcd r = d}
  exact (hbase.indicator A).congr fun m ↦ by
    by_cases hm : 0 < m ∧ m.gcd r = d
    · simp [A, Set.indicator, gcdClassTerm, hm]
    · simp [A, Set.indicator, gcdClassTerm, hm]

/-- Arithmetic row reduction for the FKL matrix.  Every nonzero slice lies
in the gcd class determined by `b-1`, and the preceding fiber count bounds
its multiplicity by the totient of that class. -/
lemma sum_linkWeight_le_gcdClassSeries {r : ℕ} [NeZero r]
    (hrSquarefree : Squarefree r) (hr : 2 ≤ r) {s : ℝ} (hs : 1 < s)
    (b : ReducedResidue r) :
    (∑ a : ReducedResidue r, linkWeight r s b a) ≤
      ∑' m : ℕ, ((b.val - 1).gcd r).totient *
        gcdClassTerm r ((b.val - 1).gcd r) s m := by
  rw [sum_linkWeight_eq_tsum_sum hs]
  apply Summable.tsum_le_tsum
  · intro m
    by_cases hm : 0 < m
    · rw [sum_linkTerm_eq_card_mul b hm]
      by_cases hsource : linkSources r b m = ∅
      · rw [hsource]
        simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
        exact mul_nonneg (by positivity)
          (gcdClassTerm_nonneg r ((b.val - 1).gcd r) s m)
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hsource
        have hgcd := gcd_eq_gcd_pred_of_mem_linkSources hr b ha
        have hcard := card_linkSources_le_totient_gcd (m := m) hrSquarefree b
        rw [hgcd] at hcard
        simp only [gcdClassTerm, hm, hgcd, and_self, if_true]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    · have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      simp [linkTerm, gcdClassTerm]
  · have hfinite (S : Finset (ReducedResidue r)) :
        Summable (fun m : ℕ ↦ ∑ a ∈ S, linkTerm r s b a m) := by
      induction S using Finset.induction with
      | empty => simp
      | @insert a S ha ih =>
          simp only [Finset.sum_insert ha]
          exact (summable_linkTerm hs b a).add ih
    simpa only [Finset.sum_const_zero, Finset.sum_attach] using
      hfinite Finset.univ
  · have hsum := summable_gcdClassTerm
      (r := r) (d := (b.val - 1).gcd r) hs
    simpa only [smul_eq_mul] using
      (Summable.const_smul (((b.val - 1).gcd r).totient : ℝ) hsum)

/-! ## Splitting a p-series into small-prime and rough parts -/

/-- The factor of `n` supported on the primes in `S`. -/
def supportedPart (S : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (· ∈ S)).prod

/-- The complementary factor of `n`, supported away from `S`. -/
def unsupportedPart (S : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (· ∉ S)).prod

lemma supportedPart_mul_unsupportedPart {S : Finset ℕ} {n : ℕ} (hn : n ≠ 0) :
    supportedPart S n * unsupportedPart S n = n := by
  have hperm := List.filter_append_perm (fun p : ℕ ↦ decide (p ∈ S)) n.primeFactorsList
  have hprod := hperm.prod_eq
  rw [List.prod_append] at hprod
  have hfilter :
      n.primeFactorsList.filter (fun p : ℕ ↦ !(decide (p ∈ S))) =
        n.primeFactorsList.filter (· ∉ S) := by
    apply List.filter_congr
    intro p hp
    simp
  rw [hfilter] at hprod
  exact hprod.trans (Nat.prod_primeFactorsList hn)

lemma supportedPart_mem_factoredNumbers (S : Finset ℕ) (n : ℕ) :
    supportedPart S n ∈ Nat.factoredNumbers S := by
  exact Nat.prod_mem_factoredNumbers S n

lemma supportedPart_pos (S : Finset ℕ) (n : ℕ) : 0 < supportedPart S n := by
  unfold supportedPart
  apply List.prod_pos
  intro p hp
  have hpList := List.mem_of_mem_filter hp
  exact (Nat.prime_of_mem_primeFactorsList hpList).pos

lemma unsupportedPart_pos (S : Finset ℕ) (n : ℕ) : 0 < unsupportedPart S n := by
  unfold unsupportedPart
  apply List.prod_pos
  intro p hp
  have hpList := List.mem_of_mem_filter hp
  exact (Nat.prime_of_mem_primeFactorsList hpList).pos

/-- If `d ∣ r` and `n` is coprime to `r/d`, the part of `n` supported away
from the primes of `d` is coprime to all of `r`. -/
lemma unsupportedPart_coprime_of_coprime_div {r d n : ℕ}
    (hr : 0 < r) (hd : d ∣ r) (hn : n ≠ 0)
    (hcop : n.Coprime (r / d)) :
    (unsupportedPart d.primeFactors n).Coprime r := by
  have hdne : d ≠ 0 := by
    intro hd0
    subst d
    simp at hd
    omega
  by_contra hnot
  obtain ⟨p, hpPrime, hpPart, hpr⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hnot
  obtain ⟨q, hqFilter, hpq⟩ := hpPrime.prime.dvd_prod_iff.mp hpPart
  have hqList : q ∈ n.primeFactorsList := List.mem_of_mem_filter hqFilter
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactorsList hqList
  have hpqEq : p = q := (Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp hpq
  subst q
  have hpNotD : p ∉ d.primeFactors :=
    of_decide_eq_true (List.mem_filter.mp hqFilter).2
  have hpn : p ∣ n := (Nat.mem_primeFactorsList hn).mp hqList |>.2
  have hrFactor : r = d * (r / d) := (Nat.mul_div_cancel' hd).symm
  rw [hrFactor] at hpr
  obtain hpd | hpR := hpPrime.dvd_mul.mp hpr
  · exact hpNotD ((Nat.mem_primeFactors).2 ⟨hpPrime, hpd, hdne⟩)
  · exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hpPrime, hpn, hpR⟩) hcop

/-- Positive integers coprime to `r`, used as the index type for the rough
part of the p-series. -/
def PositiveCoprime (r : ℕ) := {n : ℕ // 0 < n ∧ n.Coprime r}

/-- The p-series restricted to positive integers coprime to `r`. -/
noncomputable def positiveCoprimeSeries (r : ℕ) (s : ℝ) : ℝ :=
  ∑' n : PositiveCoprime r, (n.1 : ℝ) ^ (-s)

/-- The p-series over integers supported on a prescribed finite prime set. -/
noncomputable def factoredSeries (S : Finset ℕ) (s : ℝ) : ℝ :=
  ∑' n : Nat.factoredNumbers S, (n.1 : ℝ) ^ (-s)

lemma summable_positiveCoprimeSeries {r : ℕ} {s : ℝ} (hs : 1 < s) :
    Summable (fun n : PositiveCoprime r ↦ (n.1 : ℝ) ^ (-s)) := by
  exact (Real.summable_nat_rpow.mpr (by linarith)).subtype _

lemma summable_factoredSeries {S : Finset ℕ} {s : ℝ} (hs : 1 < s) :
    Summable (fun n : Nat.factoredNumbers S ↦ (n.1 : ℝ) ^ (-s)) := by
  exact (Real.summable_nat_rpow.mpr (by linarith)).subtype _

/-- Removing the prime factors belonging to `d` injects the integers
coprime to `r/d` into a product of a `d`-factored integer and an integer
coprime to all of `r`.  Summing the completely multiplicative p-series along
that injection gives the required small/rough factorization inequality. -/
lemma positiveCoprimeSeries_div_le_factored_mul {r d : ℕ}
    (hr : 0 < r) (hd : d ∣ r) {s : ℝ} (hs : 1 < s) :
    positiveCoprimeSeries (r / d) s ≤
      factoredSeries d.primeFactors s * positiveCoprimeSeries r s := by
  let encode : PositiveCoprime (r / d) →
      Nat.factoredNumbers d.primeFactors × PositiveCoprime r := fun n ↦
    (⟨supportedPart d.primeFactors n.1,
        supportedPart_mem_factoredNumbers d.primeFactors n.1⟩,
      ⟨unsupportedPart d.primeFactors n.1,
        unsupportedPart_pos d.primeFactors n.1,
        unsupportedPart_coprime_of_coprime_div hr hd n.2.1.ne' n.2.2⟩)
  have hencode : Function.Injective encode := by
    intro n k hnk
    apply Subtype.ext
    have hsupp : supportedPart d.primeFactors n.1 =
        supportedPart d.primeFactors k.1 :=
      congrArg (fun z ↦ z.1.1) hnk
    have hunsupp : unsupportedPart d.primeFactors n.1 =
        unsupportedPart d.primeFactors k.1 :=
      congrArg (fun z ↦ z.2.1) hnk
    calc
      n.1 = supportedPart d.primeFactors n.1 *
          unsupportedPart d.primeFactors n.1 :=
        (supportedPart_mul_unsupportedPart n.2.1.ne').symm
      _ = supportedPart d.primeFactors k.1 *
          unsupportedPart d.primeFactors k.1 := by rw [hsupp, hunsupp]
      _ = k.1 := supportedPart_mul_unsupportedPart k.2.1.ne'
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hleft : Summable
      (fun n : PositiveCoprime (r / d) ↦ (n.1 : ℝ) ^ (-s)) :=
    hbase.subtype _
  have hsmall : Summable
      (fun n : Nat.factoredNumbers d.primeFactors ↦ (n.1 : ℝ) ^ (-s)) :=
    hbase.subtype _
  have hrough : Summable
      (fun n : PositiveCoprime r ↦ (n.1 : ℝ) ^ (-s)) :=
    hbase.subtype _
  have hprod : Summable (fun z : Nat.factoredNumbers d.primeFactors ×
      PositiveCoprime r ↦ (z.1.1 : ℝ) ^ (-s) * (z.2.1 : ℝ) ^ (-s)) :=
    Summable.mul_of_nonneg hsmall hrough (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  have hweight (n : PositiveCoprime (r / d)) :
      (n.1 : ℝ) ^ (-s) =
        ((encode n).1.1 : ℝ) ^ (-s) * ((encode n).2.1 : ℝ) ^ (-s) := by
    have hsplit := supportedPart_mul_unsupportedPart (S := d.primeFactors) n.2.1.ne'
    rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ (encode n).1.1)
      (by positivity : (0 : ℝ) ≤ (encode n).2.1)]
    congr 1
    exact_mod_cast hsplit.symm
  calc
    positiveCoprimeSeries (r / d) s =
        ∑' n : PositiveCoprime (r / d), (n.1 : ℝ) ^ (-s) := rfl
    _ ≤ ∑' z : Nat.factoredNumbers d.primeFactors × PositiveCoprime r,
        (z.1.1 : ℝ) ^ (-s) * (z.2.1 : ℝ) ^ (-s) := by
      exact Summable.tsum_le_tsum_of_inj encode hencode
        (fun _ _ ↦ mul_nonneg (by positivity) (by positivity))
        (fun n ↦ (hweight n).le) hleft hprod
    _ = factoredSeries d.primeFactors s * positiveCoprimeSeries r s := by
      symm
      exact hsmall.tsum_mul_tsum hrough hprod

/-- The gcd-class series is obtained by extracting its mandatory factor
`d`; the residual integer is coprime to `r/d`. -/
lemma gcdClassSeries_le_rpow_mul_positiveCoprime {r d : ℕ}
    (hr : 0 < r) (hdpos : 0 < d) (hd : d ∣ r)
    (hcop : d.Coprime (r / d)) {s : ℝ} (hs : 1 < s) :
    (∑' m : ℕ, gcdClassTerm r d s m) ≤
      (d : ℝ) ^ (-s) * positiveCoprimeSeries (r / d) s := by
  let A : Set ℕ := {m | 0 < m ∧ m.gcd r = d}
  let divide : A → PositiveCoprime (r / d) := fun m ↦ by
    have hdm : d ∣ m.1 := by
      rw [← m.2.2]
      exact Nat.gcd_dvd_left m.1 r
    have hdle : d ≤ m.1 := Nat.le_of_dvd m.2.1 hdm
    refine ⟨m.1 / d, Nat.div_pos hdle hdpos, ?_⟩
    rw [Nat.coprime_iff_gcd_eq_one]
    have hrFactor : r = d * (r / d) := (Nat.mul_div_cancel' hd).symm
    have hmFactor : m.1 = d * (m.1 / d) := (Nat.mul_div_cancel' hdm).symm
    have hgcd : d * ((m.1 / d).gcd (r / d)) = d * 1 := by
      rw [← Nat.gcd_mul_left, ← hmFactor, ← hrFactor, m.2.2, mul_one]
    exact Nat.mul_left_cancel hdpos hgcd
  have hdivide : Function.Injective divide := by
    intro m n hmn
    apply Subtype.ext
    have hdiv : m.1 / d = n.1 / d := congrArg Subtype.val hmn
    have hdm : d ∣ m.1 := by
      rw [← m.2.2]
      exact Nat.gcd_dvd_left m.1 r
    have hdn : d ∣ n.1 := by
      rw [← n.2.2]
      exact Nat.gcd_dvd_left n.1 r
    calc
      m.1 = d * (m.1 / d) := (Nat.mul_div_cancel' hdm).symm
      _ = d * (n.1 / d) := by rw [hdiv]
      _ = n.1 := Nat.mul_div_cancel' hdn
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hA : Summable (fun m : A ↦ (m.1 : ℝ) ^ (-s)) := hbase.subtype _
  have hrough := summable_positiveCoprimeSeries (r := r / d) hs
  have htarget : Summable (fun n : PositiveCoprime (r / d) ↦
      (d : ℝ) ^ (-s) * (n.1 : ℝ) ^ (-s)) :=
    Summable.mul_left _ hrough
  have hweight (m : A) :
      (m.1 : ℝ) ^ (-s) =
        (d : ℝ) ^ (-s) * ((divide m).1 : ℝ) ^ (-s) := by
    have hdm : d ∣ m.1 := by
      rw [← m.2.2]
      exact Nat.gcd_dvd_left m.1 r
    rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ d)
      (by positivity : (0 : ℝ) ≤ (divide m).1)]
    congr 1
    exact_mod_cast (Nat.mul_div_cancel' hdm).symm
  calc
    (∑' m : ℕ, gcdClassTerm r d s m) =
        ∑' m : ℕ, A.indicator (fun m : ℕ ↦ (m : ℝ) ^ (-s)) m := by
      apply tsum_congr
      intro m
      by_cases hm : 0 < m ∧ m.gcd r = d
      · simp [A, Set.indicator, gcdClassTerm, hm]
      · simp [A, Set.indicator, gcdClassTerm, hm]
    _ = ∑' m : A, (m.1 : ℝ) ^ (-s) :=
      (tsum_subtype A (fun m : ℕ ↦ (m : ℝ) ^ (-s))).symm
    _ ≤ ∑' n : PositiveCoprime (r / d),
        (d : ℝ) ^ (-s) * (n.1 : ℝ) ^ (-s) := by
      exact Summable.tsum_le_tsum_of_inj divide hdivide
        (fun _ _ ↦ mul_nonneg (by positivity) (by positivity))
        (fun m ↦ (hweight m).le) hA htarget
    _ = (d : ℝ) ^ (-s) * positiveCoprimeSeries (r / d) s := by
      exact hrough.tsum_mul_left _

/-- The completely multiplicative real p-series weight. -/
noncomputable def natRpowHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]

@[simp] lemma natRpowHom_apply (s : ℝ) (n : ℕ) :
    natRpowHom s n = (n : ℝ) ^ (-s) := rfl

lemma summable_natRpowHom {s : ℝ} (hs : 1 < s) :
    Summable (natRpowHom s) := by
  exact Real.summable_nat_rpow.mpr (by linarith)

/-- One local factor after the mandatory occurrence of a prime has been
combined with its arbitrary further powers. -/
noncomputable def mandatoryPrimeFactor (p : ℕ) (s : ℝ) : ℝ :=
  ((p - 1 : ℕ) : ℝ) * (p : ℝ) ^ (-s) *
    (1 - (p : ℝ) ^ (-s))⁻¹

lemma mandatoryPrimeFactor_nonneg {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 1 < s) : 0 ≤ mandatoryPrimeFactor p s := by
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hxpos : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by positivity) _
  have hxlt : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpOne (by linarith)
  unfold mandatoryPrimeFactor
  positivity

lemma mandatoryPrimeFactor_lt_one {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 1 < s) : mandatoryPrimeFactor p s < 1 := by
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpPos : (0 : ℝ) < p := hpOne.trans' zero_lt_one
  let x : ℝ := (p : ℝ) ^ (-s)
  have hxpos : 0 < x := Real.rpow_pos_of_pos hpPos _
  have hxlt : x < (p : ℝ) ^ (-1 : ℝ) := by
    dsimp [x]
    exact (Real.rpow_lt_rpow_left_iff hpOne).2 (by linarith)
  have hpx : (p : ℝ) * x < 1 := by
    calc
      (p : ℝ) * x < (p : ℝ) * (p : ℝ) ^ (-1 : ℝ) :=
        mul_lt_mul_of_pos_left hxlt hpPos
      _ = 1 := by rw [Real.rpow_neg_one, mul_inv_cancel₀ hpPos.ne']
  have hxone : x < 1 := by
    have hgap : 0 < ((p : ℝ) - 1) * x :=
      mul_pos (sub_pos.mpr hpOne) hxpos
    nlinarith
  unfold mandatoryPrimeFactor
  change (((p - 1 : ℕ) : ℝ) * x) * (1 - x)⁻¹ < 1
  rw [← div_eq_mul_inv, div_lt_one (by linarith : 0 < 1 - x)]
  have hpCast : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le]
    norm_num
  rw [hpCast]
  nlinarith

lemma mandatoryPrimeFactor_le_one {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 1 < s) : mandatoryPrimeFactor p s ≤ 1 :=
  (mandatoryPrimeFactor_lt_one hp hs).le

lemma factoredSeries_eq_primeProduct (S : Finset ℕ) {s : ℝ} (hs : 1 < s) :
    factoredSeries S s =
      ∏ p ∈ S with p.Prime, (1 - (p : ℝ) ^ (-s))⁻¹ := by
  have h := EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers
    (f := natRpowHom s) (summable_natRpowHom hs) S
  simpa only [factoredSeries, natRpowHom_apply] using h.symm

lemma factoredSeries_primeFactors_eq (d : ℕ) {s : ℝ} (hs : 1 < s) :
    factoredSeries d.primeFactors s =
      ∏ p ∈ d.primeFactors, (1 - (p : ℝ) ^ (-s))⁻¹ := by
  rw [factoredSeries_eq_primeProduct d.primeFactors hs]
  apply Finset.prod_subset
  · exact Finset.filter_subset _ _
  · intro p hp hnot
    exact (hnot (Finset.mem_filter.mpr
      ⟨hp, Nat.prime_of_mem_primeFactors hp⟩)).elim

lemma totient_eq_prod_pred_of_squarefree {d : ℕ}
    (hd : Squarefree d) (hdpos : 0 < d) :
    d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul,
    Nat.prod_primeFactors_of_squarefree hd, Nat.div_self hdpos]
  simp

/-- The mandatory-factor coefficient is exactly the product of its local
prime factors. -/
lemma totient_rpow_factoredSeries_eq_prod {d : ℕ}
    (hd : Squarefree d) (hdpos : 0 < d) {s : ℝ} (hs : 1 < s) :
    (d.totient : ℝ) * (d : ℝ) ^ (-s) *
        factoredSeries d.primeFactors s =
      ∏ p ∈ d.primeFactors, mandatoryPrimeFactor p s := by
  have hphi : (d.totient : ℝ) =
      ∏ p ∈ d.primeFactors, ((p - 1 : ℕ) : ℝ) := by
    rw [totient_eq_prod_pred_of_squarefree hd hdpos]
    norm_cast
  have hpow : (d : ℝ) ^ (-s) =
      ∏ p ∈ d.primeFactors, (p : ℝ) ^ (-s) := by
    rw [Real.finsetProd_rpow]
    · rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
    · intro p hp
      positivity
  rw [hphi, hpow, factoredSeries_primeFactors_eq d hs]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rfl

/-- If `d` is squarefree and even, the product of all mandatory local
factors is no larger than its factor at `2`. -/
lemma totient_rpow_factoredSeries_le_twoFactor {d : ℕ}
    (hd : Squarefree d) (hdpos : 0 < d) (heven : 2 ∣ d)
    {s : ℝ} (hs : 1 < s) :
    (d.totient : ℝ) * (d : ℝ) ^ (-s) *
        factoredSeries d.primeFactors s ≤ mandatoryPrimeFactor 2 s := by
  rw [totient_rpow_factoredSeries_eq_prod hd hdpos hs]
  have htwo : 2 ∈ d.primeFactors :=
    (Nat.mem_primeFactors).2 ⟨Nat.prime_two, heven, hdpos.ne'⟩
  have hrest :
      (∏ p ∈ d.primeFactors.erase 2, mandatoryPrimeFactor p s) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      exact mandatoryPrimeFactor_nonneg
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) hs
    · intro p hp
      exact mandatoryPrimeFactor_le_one
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) hs
  calc
    (∏ p ∈ d.primeFactors, mandatoryPrimeFactor p s) =
        (∏ p ∈ d.primeFactors.erase 2, mandatoryPrimeFactor p s) *
          mandatoryPrimeFactor 2 s :=
      (Finset.prod_erase_mul d.primeFactors (fun p ↦ mandatoryPrimeFactor p s) htwo).symm
    _ ≤ 1 * mandatoryPrimeFactor 2 s :=
      mul_le_mul_of_nonneg_right hrest
        (mandatoryPrimeFactor_nonneg Nat.prime_two hs)
    _ = mandatoryPrimeFactor 2 s := one_mul _

/-- In particular, the mandatory-factor coefficient is strictly below one. -/
lemma totient_rpow_factoredSeries_lt_one {d : ℕ}
    (hd : Squarefree d) (hdpos : 0 < d) (heven : 2 ∣ d)
    {s : ℝ} (hs : 1 < s) :
    (d.totient : ℝ) * (d : ℝ) ^ (-s) *
        factoredSeries d.primeFactors s < 1 :=
  (totient_rpow_factoredSeries_le_twoFactor hd hdpos heven hs).trans_lt
    (mandatoryPrimeFactor_lt_one Nat.prime_two hs)

/-- The distinguished integer `1` in every positive-coprime index type. -/
def onePositiveCoprime (r : ℕ) : PositiveCoprime r :=
  ⟨1, by simp⟩

/-- A summable p-series has an arbitrarily small tail, stated in the exact
subtype form used for rough integers. -/
lemma exists_pSeriesTail_lt {s ε : ℝ} (hs : 1 < s) (hε : 0 < ε) :
    ∃ Y : ℕ, 3 ≤ Y ∧
      (∑' n : {n : ℕ // Y ≤ n}, (n.1 : ℝ) ^ (-s)) < ε := by
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  obtain ⟨N, hN⟩ := (summable_iff_nat_tsum_vanishing.mp hbase)
    (Metric.ball (0 : ℝ) ε) (Metric.ball_mem_nhds 0 hε)
  refine ⟨N + 3, by omega, ?_⟩
  have htail := hN {n : ℕ | N + 3 ≤ n} (by
    intro n hn
    change N ≤ n
    change N + 3 ≤ n at hn
    omega)
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at htail
  exact lt_of_le_of_lt (le_abs_self _) htail

/-- If `r` contains every prime below `Y`, every positive integer coprime to
`r`, other than `1`, lies in the p-series tail beginning at `Y`. -/
lemma positiveCoprimeSeries_le_one_add_tail {r Y : ℕ} {s : ℝ}
    (hdiv : ∀ p : ℕ, p.Prime → p < Y → p ∣ r)
    (hs : 1 < s) :
    positiveCoprimeSeries r s ≤
      1 + ∑' n : {n : ℕ // Y ≤ n}, (n.1 : ℝ) ^ (-s) := by
  classical
  let one : PositiveCoprime r := onePositiveCoprime r
  let B : Set (PositiveCoprime r) := {n | n ≠ one}
  let tail : Set ℕ := {n | Y ≤ n}
  let encode : B → tail := fun n ↦ by
    refine ⟨n.1.1, ?_⟩
    by_contra hlt
    have hnlt : n.1.1 < Y := Nat.lt_of_not_ge hlt
    have hnOne : n.1.1 ≠ 1 := by
      intro hn
      apply n.2
      apply Subtype.ext
      exact hn
    have hnPos : 0 < n.1.1 := n.1.2.1
    have hnTwo : 2 ≤ n.1.1 := by omega
    let p := n.1.1.minFac
    have hpPrime : p.Prime := Nat.minFac_prime (by omega)
    have hpN : p ∣ n.1.1 := Nat.minFac_dvd n.1.1
    have hpLe : p ≤ n.1.1 := Nat.le_of_dvd n.1.2.1 hpN
    have hpR : p ∣ r := hdiv p hpPrime (hpLe.trans_lt hnlt)
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hpPrime, hpN, hpR⟩) n.1.2.2
  have hencode : Function.Injective encode := by
    intro n k hnk
    apply Subtype.ext
    apply Subtype.ext
    change (encode n).1 = (encode k).1
    exact congrArg Subtype.val hnk
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hB : Summable (fun n : B ↦ (n.1.1 : ℝ) ^ (-s)) :=
    (hbase.subtype _).subtype _
  have htail : Summable (fun n : tail ↦ (n.1 : ℝ) ^ (-s)) :=
    hbase.subtype _
  have hsubtype :
      (∑' n : PositiveCoprime r,
          if n = one then 0 else (n.1 : ℝ) ^ (-s)) =
        ∑' n : B, (n.1.1 : ℝ) ^ (-s) := by
    calc
      (∑' n : PositiveCoprime r,
          if n = one then 0 else (n.1 : ℝ) ^ (-s)) =
          ∑' n : PositiveCoprime r,
            B.indicator (fun n : PositiveCoprime r ↦ (n.1 : ℝ) ^ (-s)) n := by
        apply tsum_congr
        intro n
        by_cases hn : n = one
        · simp [B, Set.indicator, hn]
        · simp [B, Set.indicator, hn]
      _ = ∑' n : B, (n.1.1 : ℝ) ^ (-s) :=
        (tsum_subtype B
          (fun n : PositiveCoprime r ↦ (n.1 : ℝ) ^ (-s))).symm
  have hBtail : (∑' n : B, (n.1.1 : ℝ) ^ (-s)) ≤
      ∑' n : tail, (n.1 : ℝ) ^ (-s) := by
    exact Summable.tsum_le_tsum_of_inj encode hencode
      (fun _ _ ↦ by positivity) (fun _ ↦ le_rfl) hB htail
  change (∑' n : B, (n.1.1 : ℝ) ^ (-s)) ≤
      ∑' n : {n : ℕ // Y ≤ n}, (n.1 : ℝ) ^ (-s) at hBtail
  have hsplit := (summable_positiveCoprimeSeries (r := r) hs).tsum_eq_add_tsum_ite one
  change positiveCoprimeSeries r s =
      (one.1 : ℝ) ^ (-s) +
        ∑' n : PositiveCoprime r,
          (if n = one then 0 else (n.1 : ℝ) ^ (-s)) at hsplit
  rw [hsubtype] at hsplit
  rw [hsplit]
  simpa [one, onePositiveCoprime] using add_le_add_left hBtail 1

/-! ## Uniform contraction of the sifted link matrix -/

/-- Once the modulus is squarefree and even, every gcd class occurring in
an FKL row contains the mandatory prime `2`.  All remaining local factors
are at most one, and the primes not dividing the modulus contribute only
the rough p-series. -/
lemma sum_linkWeight_le_twoFactor_mul_positiveCoprime
    {r : ℕ} [NeZero r] (hrSquarefree : Squarefree r) (heven : 2 ∣ r)
    {s : ℝ} (hs : 1 < s) (b : ReducedResidue r) :
    (∑ a : ReducedResidue r, linkWeight r s b a) ≤
      mandatoryPrimeFactor 2 s * positiveCoprimeSeries r s := by
  let d := (b.val - 1).gcd r
  have hrpos : 0 < r := NeZero.pos r
  have hrTwo : 2 ≤ r := Nat.le_of_dvd hrpos heven
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_right (b.val - 1) hrpos
  have hdr : d ∣ r := by
    dsimp [d]
    exact Nat.gcd_dvd_right _ _
  have hdSquarefree : Squarefree d :=
    hrSquarefree.squarefree_of_dvd hdr
  have hbCoprime : b.val.Coprime r := ZMod.val_coe_unit_coprime b
  have hbOdd : Odd b.val :=
    (hbCoprime.of_dvd_right heven).odd_of_right
  have hdEven : 2 ∣ d := by
    apply Nat.dvd_gcd
    · exact (Nat.Odd.sub_odd hbOdd (by simp)).two_dvd
    · exact heven
  have hclass := sum_linkWeight_le_gcdClassSeries hrSquarefree hrTwo hs b
  have hclassExtract := gcdClassSeries_le_rpow_mul_positiveCoprime
    hrpos hdpos hdr (by
      have hgd : r.gcd d = d := Nat.gcd_eq_right_iff_dvd.mpr hdr
      have hc := Nat.coprime_div_gcd_of_squarefree hrSquarefree hdpos.ne'
      simpa only [hgd] using hc.symm) hs
  have hsplit := positiveCoprimeSeries_div_le_factored_mul hrpos hdr hs
  have hphi : 0 ≤ (d.totient : ℝ) := by positivity
  have hdpow : 0 ≤ (d : ℝ) ^ (-s) := by positivity
  have hrough : 0 ≤ positiveCoprimeSeries r s :=
    tsum_nonneg fun _ ↦ by positivity
  calc
    (∑ a : ReducedResidue r, linkWeight r s b a) ≤
        ∑' m : ℕ, (d.totient : ℝ) * gcdClassTerm r d s m := by
      simpa only [d] using hclass
    _ = (d.totient : ℝ) * (∑' m : ℕ, gcdClassTerm r d s m) := by
      exact (summable_gcdClassTerm (r := r) (d := d) hs).tsum_mul_left _
    _ ≤ (d.totient : ℝ) *
        ((d : ℝ) ^ (-s) * positiveCoprimeSeries (r / d) s) :=
      mul_le_mul_of_nonneg_left hclassExtract hphi
    _ ≤ (d.totient : ℝ) * ((d : ℝ) ^ (-s) *
        (factoredSeries d.primeFactors s * positiveCoprimeSeries r s)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsplit hdpow) hphi
    _ = ((d.totient : ℝ) * (d : ℝ) ^ (-s) *
        factoredSeries d.primeFactors s) * positiveCoprimeSeries r s := by
      ring
    _ ≤ mandatoryPrimeFactor 2 s * positiveCoprimeSeries r s :=
      mul_le_mul_of_nonneg_right
        (totient_rpow_factoredSeries_le_twoFactor
          hdSquarefree hdpos hdEven hs) hrough

/-- For every exponent `s > 1`, a primorial modulus makes the maximum row
sum of the FKL link matrix strictly smaller than one.  This is the complete
finite-state contraction step in the Ford--Konyagin--Luca prime-chain
argument. -/
theorem exists_linkWeight_row_contraction {s : ℝ} (hs : 1 < s) :
    ∃ r : ℕ, ∃ R : ℝ, 0 < r ∧ Squarefree r ∧ 2 ∣ r ∧
      0 ≤ R ∧ R < 1 ∧
      ∀ (_hr : NeZero r) (b : ReducedResidue r),
        (∑ a : ReducedResidue r, linkWeight r s b a) ≤ R := by
  let c := mandatoryPrimeFactor 2 s
  let ε := (1 - c) / 2
  have hcNonneg : 0 ≤ c := mandatoryPrimeFactor_nonneg Nat.prime_two hs
  have hcOne : c < 1 := mandatoryPrimeFactor_lt_one Nat.prime_two hs
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨Y, hY, htail⟩ := exists_pSeriesTail_lt hs hε
  let r := primorial Y
  let R := c * (1 + ε)
  have hrpos : 0 < r := primorial_pos Y
  have hrSquarefree : Squarefree r := squarefree_primorial Y
  have hrEven : 2 ∣ r := Nat.prime_two.dvd_primorial_iff.mpr (by omega)
  have hrough : positiveCoprimeSeries r s ≤ 1 + ε := by
    calc
      positiveCoprimeSeries r s ≤
          1 + ∑' n : {n : ℕ // Y ≤ n}, (n.1 : ℝ) ^ (-s) := by
        apply positiveCoprimeSeries_le_one_add_tail
        intro p hpPrime hpY
        exact hpPrime.dvd_primorial_iff.mpr hpY.le
        exact hs
      _ ≤ 1 + ε := by
        simpa [add_comm] using add_le_add_left htail.le 1
  have hROne : R < 1 := by
    dsimp [R, ε]
    nlinarith
  refine ⟨r, R, hrpos, hrSquarefree, hrEven, ?_, hROne, ?_⟩
  · dsimp [R]
    positivity
  · intro hr b
    let _ : NeZero r := hr
    calc
      (∑ a : ReducedResidue r, linkWeight r s b a) ≤
          c * positiveCoprimeSeries r s := by
        simpa only [c] using
          sum_linkWeight_le_twoFactor_mul_positiveCoprime
            hrSquarefree hrEven hs b
      _ ≤ c * (1 + ε) := mul_le_mul_of_nonneg_left hrough hcNonneg
      _ = R := rfl

/-! ## Expanding matrix powers into labelled multiplier paths -/

/-- A length-`k` path in the link matrix, retaining the positive integer
multiplier attached to every edge.  The equality proof in the zero-length
case records that its endpoints agree. -/
def LinkPath (r : ℕ) : ℕ → ReducedResidue r → ReducedResidue r → Type
  | 0, b, a => PLift (b = a)
  | k + 1, _b, a => Σ c : ReducedResidue r, ℕ × LinkPath r k c a

/-- The product of the individual link-series terms along a labelled path. -/
noncomputable def linkPathWeight (r : ℕ) (s : ℝ) :
    ∀ {k : ℕ} {b a : ReducedResidue r}, LinkPath r k b a → ℝ
  | 0, _b, _a, _p => 1
  | _k + 1, b, _a, ⟨c, m, p⟩ =>
      linkTerm r s b c m * linkPathWeight r s p

lemma linkPathWeight_nonneg (r : ℕ) (s : ℝ) :
    ∀ {k : ℕ} {b a : ReducedResidue r} (p : LinkPath r k b a),
      0 ≤ linkPathWeight r s p := by
  intro k
  induction k with
  | zero => intro b a p; simp [linkPathWeight]
  | succ k ih =>
      rintro b a ⟨c, m, p⟩
      exact mul_nonneg (linkTerm_nonneg r s b c m) (ih p)

/-- The labelled-path series is summable whenever `s > 1`. -/
lemma summable_linkPathWeight {r : ℕ} [NeZero r] {s : ℝ} (hs : 1 < s) :
    ∀ (k : ℕ) (b a : ReducedResidue r),
      Summable (fun p : LinkPath r k b a ↦ linkPathWeight r s p) := by
  intro k
  induction k with
  | zero =>
      intro b a
      let toUnit : LinkPath r 0 b a → PUnit := fun _ ↦ PUnit.unit
      have hpathEq (p q : LinkPath r 0 b a) : p = q := by
        rcases p with ⟨hp⟩
        rcases q with ⟨hq⟩
        congr
      have htoUnit : Function.Injective toUnit := fun p q _ ↦ hpathEq p q
      let : Finite (LinkPath r 0 b a) := Finite.of_injective toUnit htoUnit
      exact Summable.of_finite
  | succ k ih =>
      intro b a
      apply (summable_sigma_of_nonneg
        (fun p : Σ c : ReducedResidue r, ℕ × LinkPath r k c a ↦ by
          rcases p with ⟨c, m, p⟩
          exact mul_nonneg (linkTerm_nonneg r s b c m)
            (linkPathWeight_nonneg r s p))).2
      constructor
      · intro c
        exact Summable.mul_of_nonneg (summable_linkTerm hs b c) (ih c a)
          (fun _ ↦ linkTerm_nonneg r s b c _)
          (fun _ ↦ linkPathWeight_nonneg r s _)
      · exact Summable.of_finite

/-- Expanding the recursive matrix product gives exactly the sum over all
labelled multiplier paths. -/
lemma tsum_linkPathWeight_eq_pathWeight {r : ℕ} [NeZero r]
    {s : ℝ} (hs : 1 < s) :
    ∀ (k : ℕ) (b a : ReducedResidue r),
      (∑' p : LinkPath r k b a, linkPathWeight r s p) =
        pathWeight (linkWeight r s) k b a := by
  intro k
  induction k with
  | zero =>
      intro b a
      by_cases hba : b = a
      · subst b
        let p0 : LinkPath r 0 a a := ⟨rfl⟩
        rw [pathWeight_zero, if_pos rfl, tsum_eq_single p0]
        · rfl
        · intro p hp
          have hpp0 : p = p0 := by
            rcases p with ⟨hp'⟩
            congr
          exact (hp hpp0).elim
      · have : IsEmpty (PLift (b = a)) :=
          ⟨fun p ↦ hba p.down⟩
        rw [pathWeight_zero, if_neg hba]
        have hfun :
            (fun p : LinkPath r 0 b a ↦ linkPathWeight r s p) = 0 := by
          funext p
          exact (hba p.down).elim
        rw [hfun]
        exact tsum_zero
  | succ k ih =>
      intro b a
      have hsum := summable_linkPathWeight hs (k + 1) b a
      rw [pathWeight_succ]
      calc
        (∑' p : LinkPath r (k + 1) b a, linkPathWeight r s p) =
            ∑' c : ReducedResidue r,
              ∑' z : ℕ × LinkPath r k c a,
                linkTerm r s b c z.1 * linkPathWeight r s z.2 := by
          exact hsum.tsum_sigma
        _ = ∑ c : ReducedResidue r,
              linkWeight r s b c *
                (∑' p : LinkPath r k c a, linkPathWeight r s p) := by
          rw [tsum_fintype]
          apply Finset.sum_congr rfl
          intro c _
          symm
          exact (summable_linkTerm hs b c).tsum_mul_tsum
            (summable_linkPathWeight hs k c a)
            (Summable.mul_of_nonneg (summable_linkTerm hs b c)
              (summable_linkPathWeight hs k c a)
              (fun _ ↦ linkTerm_nonneg r s b c _)
              (fun _ ↦ linkPathWeight_nonneg r s _))
        _ = ∑ c : ReducedResidue r,
              linkWeight r s b c * pathWeight (linkWeight r s) k c a := by
          apply Finset.sum_congr rfl
          intro c _
          rw [ih c a]

/-- One edge in a Pratt prime chain: `q` and `t` are prime and
`t ≡ 1 (mod q)`. -/
def PrimeChainStep (q t : ℕ) : Prop :=
  q.Prime ∧ t.Prime ∧ q ∣ t - 1

/-- A prime chain with its length exposed. -/
inductive PrimeChainPath : ℕ → ℕ → ℕ → Prop
  | refl {q : ℕ} (hq : q.Prime) : PrimeChainPath 0 q q
  | tail {k q u t : ℕ} (hqu : PrimeChainPath k q u)
      (hut : PrimeChainStep u t) : PrimeChainPath (k + 1) q t

lemma PrimeChainPath.start_prime {k q t : ℕ}
    (h : PrimeChainPath k q t) : q.Prime := by
  induction h with
  | refl hq => exact hq
  | tail _ _ ih => exact ih

lemma PrimeChainPath.end_prime {k q t : ℕ}
    (h : PrimeChainPath k q t) : t.Prime := by
  cases h with
  | refl hq => exact hq
  | tail _ hut => exact hut.2.1

lemma PrimeChainPath.start_le_end {k q t : ℕ}
    (h : PrimeChainPath k q t) : q ≤ t := by
  induction h with
  | refl _ => exact le_rfl
  | @tail k q u t hqu hut ih =>
      have htPos : 0 < t - 1 := by
        have := hut.2.1.two_le
        omega
      have hutLe : u ≤ t - 1 := Nat.le_of_dvd htPos hut.2.2
      omega

/-- The unit residue represented by an integer coprime to the modulus. -/
def reducedResidueOfCoprime {r : ℕ} (n : ℕ) (h : n.Coprime r) :
    ReducedResidue r := ZMod.unitOfCoprime n h

@[simp] lemma reducedResidueOfCoprime_val {r n : ℕ} (h : n.Coprime r) :
    (reducedResidueOfCoprime n h).val = n % r := by
  change (ZMod.unitOfCoprime n h : ZMod r).val = n % r
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]

/-- Reconstruct the terminal integer from a starting integer and the edge
multipliers retained by a labelled link path. -/
def linkPathEval (q : ℕ) :
    ∀ {r k : ℕ} {b a : ReducedResidue r}, LinkPath r k b a → ℕ
  | _r, 0, _b, _a, _p => q
  | _r, _k + 1, _b, _a, ⟨_c, m, p⟩ => linkPathEval q p * m + 1

/-- Product of all edge multipliers of a labelled link path. -/
def linkPathMultiplierProduct :
    ∀ {r k : ℕ} {b a : ReducedResidue r}, LinkPath r k b a → ℕ
  | _r, 0, _b, _a, _p => 1
  | _r, _k + 1, _b, _a, ⟨_c, m, p⟩ =>
      m * linkPathMultiplierProduct p

/-- A genuine prime chain gives a positive labelled path in the link
matrix.  Besides reconstructing the endpoint, the lemma records both the
exact analytic weight and the elementary lower comparison between the
product of its multipliers and the endpoint. -/
lemma PrimeChainPath.exists_linkPath {r k q t : ℕ} [NeZero r]
    (h : PrimeChainPath k q t)
    (hcop : ∀ n : ℕ, n.Prime → q ≤ n → n.Coprime r)
    (s : ℝ) :
    ∃ p : LinkPath r k
        (reducedResidueOfCoprime t
          (hcop t h.end_prime h.start_le_end))
        (reducedResidueOfCoprime q
          (hcop q h.start_prime le_rfl)),
      linkPathEval q p = t ∧
      0 < linkPathMultiplierProduct p ∧
      linkPathWeight r s p =
        (linkPathMultiplierProduct p : ℝ) ^ (-s) ∧
      q * linkPathMultiplierProduct p ≤ t := by
  induction h with
  | refl hq =>
      refine ⟨⟨rfl⟩, rfl, by simp [linkPathMultiplierProduct], ?_, ?_⟩
      · simp [linkPathWeight, linkPathMultiplierProduct]
      · simp [linkPathMultiplierProduct]
  | @tail k q u t hqu hut ih =>
      obtain ⟨p, hpEval, hpPos, hpWeight, hpLe⟩ := ih hcop
      let m := (t - 1) / u
      have huPrime : u.Prime := hqu.end_prime
      have huPos : 0 < u := huPrime.pos
      have htPrime : t.Prime := hut.2.1
      have htPos : 0 < t - 1 := by
        have := htPrime.two_le
        omega
      have huLe : u ≤ t - 1 := Nat.le_of_dvd htPos hut.2.2
      have hutLe : u ≤ t := huLe.trans (Nat.sub_le t 1)
      have hmPos : 0 < m := Nat.div_pos huLe huPos
      have hutEq : u * m + 1 = t := by
        dsimp [m]
        rw [Nat.mul_div_cancel' hut.2.2]
        omega
      let c := reducedResidueOfCoprime u
        (hcop u huPrime hqu.start_le_end)
      let b := reducedResidueOfCoprime t
        (hcop t htPrime (hqu.start_le_end.trans hutLe))
      have hcong : (c.val * m + 1) % r = b.val := by
        rw [reducedResidueOfCoprime_val, reducedResidueOfCoprime_val]
        have hmod : u % r * m + 1 ≡ t [MOD r] := by
          have heqmod : u * m + 1 ≡ t [MOD r] := by rw [hutEq]
          exact (((Nat.mod_modEq u r).mul_right m).add_right 1).trans heqmod
        exact hmod
      let p' : LinkPath r (k + 1) b
          (reducedResidueOfCoprime q
            (hcop q hqu.start_prime le_rfl)) := ⟨c, m, p⟩
      refine ⟨p', ?_, ?_, ?_, ?_⟩
      · dsimp [p', linkPathEval]
        rw [hpEval, hutEq]
      · dsimp [p', linkPathMultiplierProduct]
        positivity
      · dsimp [p', linkPathWeight, linkPathMultiplierProduct]
        rw [show linkTerm r s b c m = (m : ℝ) ^ (-s) by
          simp only [linkTerm, hmPos, hcong, and_self, if_true], hpWeight]
        rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ m)
          (by positivity : (0 : ℝ) ≤ linkPathMultiplierProduct p)]
        congr 1
        norm_num
      · dsimp [p', linkPathMultiplierProduct]
        calc
          q * (m * linkPathMultiplierProduct p) =
              (q * linkPathMultiplierProduct p) * m := by ring
          _ ≤ u * m := Nat.mul_le_mul_right m hpLe
          _ ≤ t := by omega

/-- Targets at a specified prime-chain length. -/
noncomputable def primeChainTargetsAtLength (y q k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (y + 1)).filter fun t ↦ PrimeChainPath k q t

@[simp] lemma mem_primeChainTargetsAtLength {y q k t : ℕ} :
    t ∈ primeChainTargetsAtLength y q k ↔
      t ≤ y ∧ PrimeChainPath k q t := by
  classical
  simp [primeChainTargetsAtLength]

/-- Each bounded length-`k` prime-chain target injects into a distinct
positive labelled matrix path.  Summing their common minimum weight gives
the bridge from arithmetic chain counts to a matrix column sum. -/
lemma card_primeChainTargetsAtLength_mul_rpow_le
    {r q y k : ℕ} [NeZero r] {s : ℝ} (hs : 1 < s)
    (hq : q.Prime)
    (hcop : ∀ n : ℕ, n.Prime → q ≤ n → n.Coprime r) :
    ((primeChainTargetsAtLength y q k).card : ℝ) *
        ((y : ℝ) / (q : ℝ)) ^ (-s) ≤
      ∑ b : ReducedResidue r,
        pathWeight (linkWeight r s) k b
          (reducedResidueOfCoprime q (hcop q hq le_rfl)) := by
  classical
  let S := primeChainTargetsAtLength y q k
  let a := reducedResidueOfCoprime q (hcop q hq le_rfl)
  let chain (t : {t // t ∈ S}) : PrimeChainPath k q t.1 :=
    (mem_primeChainTargetsAtLength.mp t.2).2
  let terminalCoprime (t : {t // t ∈ S}) : t.1.Coprime r :=
    hcop t.1 (chain t).end_prime (chain t).start_le_end
  let chosen (t : {t // t ∈ S}) :=
    Classical.choose ((chain t).exists_linkPath hcop s)
  have chosen_spec (t : {t // t ∈ S}) :
      linkPathEval q (chosen t) = t.1 ∧
      0 < linkPathMultiplierProduct (chosen t) ∧
      linkPathWeight r s (chosen t) =
        (linkPathMultiplierProduct (chosen t) : ℝ) ^ (-s) ∧
      q * linkPathMultiplierProduct (chosen t) ≤ t.1 :=
    Classical.choose_spec ((chain t).exists_linkPath hcop s)
  let encode (t : {t // t ∈ S}) :
      Σ b : ReducedResidue r, LinkPath r k b a :=
    ⟨reducedResidueOfCoprime t.1 (terminalCoprime t), chosen t⟩
  have hencode : Function.Injective encode := by
    intro t u htu
    apply Subtype.ext
    have heval := congrArg
      (fun z : Σ b : ReducedResidue r, LinkPath r k b a ↦
        linkPathEval q z.2) htu
    change linkPathEval q (chosen t) = linkPathEval q (chosen u) at heval
    rw [(chosen_spec t).1, (chosen_spec u).1] at heval
    exact heval
  have htarget : Summable
      (fun z : Σ b : ReducedResidue r, LinkPath r k b a ↦
        linkPathWeight r s z.2) := by
    rw [summable_sigma_of_nonneg
      (β := fun b : ReducedResidue r ↦ LinkPath r k b a)
      (fun z ↦ linkPathWeight_nonneg r s z.2)]
    constructor
    · intro b
      exact summable_linkPathWeight hs k b a
    · exact Summable.of_finite
  have hqposReal : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hsource : Summable
      (fun _t : {t // t ∈ S} ↦ ((y : ℝ) / (q : ℝ)) ^ (-s)) :=
    Summable.of_finite
  have hinjSum :
      (∑' _t : {t // t ∈ S}, ((y : ℝ) / (q : ℝ)) ^ (-s)) ≤
        ∑' z : Σ b : ReducedResidue r, LinkPath r k b a,
          linkPathWeight r s z.2 := by
    exact Summable.tsum_le_tsum_of_inj encode hencode
      (fun z _ ↦ linkPathWeight_nonneg r s z.2)
      (fun t ↦ by
        rw [(chosen_spec t).2.2.1]
        apply Real.rpow_le_rpow_of_nonpos
        · exact_mod_cast (chosen_spec t).2.1
        · apply (le_div_iff₀ hqposReal).2
          have hnat := (chosen_spec t).2.2.2.trans
            (mem_primeChainTargetsAtLength.mp t.2).1
          exact_mod_cast (by simpa [mul_comm] using hnat)
        · linarith)
      hsource htarget
  calc
    ((primeChainTargetsAtLength y q k).card : ℝ) *
          ((y : ℝ) / (q : ℝ)) ^ (-s) =
        ∑' _t : {t // t ∈ S}, ((y : ℝ) / (q : ℝ)) ^ (-s) := by
      rw [tsum_fintype]
      simp [S]
    _ ≤ ∑' z : Σ b : ReducedResidue r, LinkPath r k b a,
        linkPathWeight r s z.2 := hinjSum
    _ = ∑' b : ReducedResidue r,
        ∑' p : LinkPath r k b a, linkPathWeight r s p :=
      htarget.tsum_sigma
    _ = ∑ b : ReducedResidue r,
        pathWeight (linkWeight r s) k b a := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro b _
      exact tsum_linkPathWeight_eq_pathWeight hs k b a
    _ = ∑ b : ReducedResidue r,
        pathWeight (linkWeight r s) k b
          (reducedResidueOfCoprime q (hcop q hq le_rfl)) := rfl

/-- Weighted form of the path injection.  The edge multipliers satisfy
`q * ∏ mᵢ ≤ t`, so a target contributes at most `q⁻ˢ` times the weight of
its chosen labelled path.  This is the source of the reciprocal
prime-chain estimate used in the FLP good branch. -/
lemma sum_primeChainTargetsAtLength_rpow_neg_le
    {r q y k : ℕ} [NeZero r] {s : ℝ} (hs : 1 < s)
    (hq : q.Prime)
    (hcop : ∀ n : ℕ, n.Prime → q ≤ n → n.Coprime r) :
    (∑ t ∈ primeChainTargetsAtLength y q k, (t : ℝ) ^ (-s)) ≤
      (q : ℝ) ^ (-s) *
        ∑ b : ReducedResidue r,
          pathWeight (linkWeight r s) k b
            (reducedResidueOfCoprime q (hcop q hq le_rfl)) := by
  classical
  let S := primeChainTargetsAtLength y q k
  let a := reducedResidueOfCoprime q (hcop q hq le_rfl)
  let chain (t : {t // t ∈ S}) : PrimeChainPath k q t.1 :=
    (mem_primeChainTargetsAtLength.mp t.2).2
  let terminalCoprime (t : {t // t ∈ S}) : t.1.Coprime r :=
    hcop t.1 (chain t).end_prime (chain t).start_le_end
  let chosen (t : {t // t ∈ S}) :=
    Classical.choose ((chain t).exists_linkPath hcop s)
  have chosen_spec (t : {t // t ∈ S}) :
      linkPathEval q (chosen t) = t.1 ∧
      0 < linkPathMultiplierProduct (chosen t) ∧
      linkPathWeight r s (chosen t) =
        (linkPathMultiplierProduct (chosen t) : ℝ) ^ (-s) ∧
      q * linkPathMultiplierProduct (chosen t) ≤ t.1 :=
    Classical.choose_spec ((chain t).exists_linkPath hcop s)
  let encode (t : {t // t ∈ S}) :
      Σ b : ReducedResidue r, LinkPath r k b a :=
    ⟨reducedResidueOfCoprime t.1 (terminalCoprime t), chosen t⟩
  have hencode : Function.Injective encode := by
    intro t u htu
    apply Subtype.ext
    have heval := congrArg
      (fun z : Σ b : ReducedResidue r, LinkPath r k b a ↦
        linkPathEval q z.2) htu
    change linkPathEval q (chosen t) = linkPathEval q (chosen u) at heval
    rw [(chosen_spec t).1, (chosen_spec u).1] at heval
    exact heval
  have htarget0 : Summable
      (fun z : Σ b : ReducedResidue r, LinkPath r k b a ↦
        linkPathWeight r s z.2) := by
    rw [summable_sigma_of_nonneg
      (β := fun b : ReducedResidue r ↦ LinkPath r k b a)
      (fun z ↦ linkPathWeight_nonneg r s z.2)]
    constructor
    · intro b
      exact summable_linkPathWeight hs k b a
    · exact Summable.of_finite
  have htarget : Summable
      (fun z : Σ b : ReducedResidue r, LinkPath r k b a ↦
        (q : ℝ) ^ (-s) * linkPathWeight r s z.2) :=
    htarget0.mul_left _
  have hsource : Summable
      (fun t : {t // t ∈ S} ↦ (t.1 : ℝ) ^ (-s)) :=
    Summable.of_finite
  have hinjSum :
      (∑' t : {t // t ∈ S}, (t.1 : ℝ) ^ (-s)) ≤
        ∑' z : Σ b : ReducedResidue r, LinkPath r k b a,
          (q : ℝ) ^ (-s) * linkPathWeight r s z.2 := by
    exact Summable.tsum_le_tsum_of_inj encode hencode
      (fun z _ ↦ mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (linkPathWeight_nonneg r s z.2))
      (fun t ↦ by
        rw [(chosen_spec t).2.2.1]
        have hprodPos : (0 : ℝ) <
            q * linkPathMultiplierProduct (chosen t) := by
          exact_mod_cast Nat.mul_pos hq.pos (chosen_spec t).2.1
        calc
          (t.1 : ℝ) ^ (-s) ≤
              ((q * linkPathMultiplierProduct (chosen t) : ℕ) : ℝ) ^ (-s) := by
            rw [Nat.cast_mul]
            apply Real.rpow_le_rpow_of_nonpos hprodPos
            · exact_mod_cast (chosen_spec t).2.2.2
            · linarith
          _ = (q : ℝ) ^ (-s) *
              (linkPathMultiplierProduct (chosen t) : ℝ) ^ (-s) := by
            rw [Nat.cast_mul, Real.mul_rpow]
            · positivity
            · positivity)
      hsource htarget
  calc
    (∑ t ∈ primeChainTargetsAtLength y q k, (t : ℝ) ^ (-s)) =
        ∑' t : {t // t ∈ S}, (t.1 : ℝ) ^ (-s) := by
      rw [tsum_fintype]
      exact (Finset.sum_attach S (fun t ↦ (t : ℝ) ^ (-s))).symm
    _ ≤ ∑' z : Σ b : ReducedResidue r, LinkPath r k b a,
        (q : ℝ) ^ (-s) * linkPathWeight r s z.2 := hinjSum
    _ = ∑' b : ReducedResidue r,
        ∑' p : LinkPath r k b a,
          (q : ℝ) ^ (-s) * linkPathWeight r s p :=
      htarget.tsum_sigma
    _ = ∑ b : ReducedResidue r,
        (q : ℝ) ^ (-s) * pathWeight (linkWeight r s) k b a := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro b _
      rw [tsum_mul_left]
      congr 1
      exact tsum_linkPathWeight_eq_pathWeight hs k b a
    _ = (q : ℝ) ^ (-s) *
        ∑ b : ReducedResidue r, pathWeight (linkWeight r s) k b a := by
      rw [Finset.mul_sum]
    _ = (q : ℝ) ^ (-s) *
        ∑ b : ReducedResidue r,
          pathWeight (linkWeight r s) k b
            (reducedResidueOfCoprime q (hcop q hq le_rfl)) := rfl

/-- The row contraction turns the weighted injection into an explicit bound
for targets at one fixed chain length. -/
lemma card_primeChainTargetsAtLength_le
    {r q y k : ℕ} [NeZero r] {s R : ℝ} (hs : 1 < s)
    (hw : ∀ b : ReducedResidue r,
      (∑ a : ReducedResidue r, linkWeight r s b a) ≤ R)
    (hR : 0 ≤ R) (hq : q.Prime) (hqy : q ≤ y)
    (hcop : ∀ n : ℕ, n.Prime → q ≤ n → n.Coprime r) :
    ((primeChainTargetsAtLength y q k).card : ℝ) ≤
      Fintype.card (ReducedResidue r) * R ^ k *
        ((y : ℝ) / (q : ℝ)) ^ s := by
  let x : ℝ := (y : ℝ) / (q : ℝ)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hxpos : 0 < x := div_pos (by exact_mod_cast hqy.trans' hq.pos) hqpos
  have hweighted := card_primeChainTargetsAtLength_mul_rpow_le
    (y := y) (k := k) hs hq hcop
  have hcolumn := sum_pathWeight_le_card_mul_pow
    (w := linkWeight r s) (R := R) (fun b a ↦ linkWeight_nonneg r s b a)
    hR hw k (reducedResidueOfCoprime q (hcop q hq le_rfl))
  have hbound :
      ((primeChainTargetsAtLength y q k).card : ℝ) * x ^ (-s) ≤
        Fintype.card (ReducedResidue r) * R ^ k := by
    have hweighted' :
        ((primeChainTargetsAtLength y q k).card : ℝ) * x ^ (-s) ≤
          ∑ b : ReducedResidue r,
            pathWeight (linkWeight r s) k b
              (reducedResidueOfCoprime q (hcop q hq le_rfl)) := by
      simpa only [x] using hweighted
    exact hweighted'.trans hcolumn
  have hcancel : x ^ (-s) * x ^ s = 1 := by
    rw [← Real.rpow_add hxpos]
    simp
  calc
    ((primeChainTargetsAtLength y q k).card : ℝ) =
        (((primeChainTargetsAtLength y q k).card : ℝ) * x ^ (-s)) * x ^ s := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ (Fintype.card (ReducedResidue r) * R ^ k) * x ^ s :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hxpos.le s)
    _ = Fintype.card (ReducedResidue r) * R ^ k *
        ((y : ℝ) / (q : ℝ)) ^ s := rfl

/-- Reflexive-transitive prime-chain reachability. -/
def PrimeChainReachable (q t : ℕ) : Prop :=
  Relation.ReflTransGen PrimeChainStep q t

lemma PrimeChainPath.reachable {k q t : ℕ}
    (h : PrimeChainPath k q t) : PrimeChainReachable q t := by
  induction h with
  | refl _ => exact Relation.ReflTransGen.refl
  | tail _ hut ih => exact ih.tail hut

lemma PrimeChainPath.length_le_end {k q t : ℕ}
    (h : PrimeChainPath k q t) : k ≤ t := by
  induction h with
  | refl _ => exact Nat.zero_le _
  | @tail k q u t hqu hut ih =>
      have htPos : 0 < t - 1 := by
        have := hut.2.1.two_le
        omega
      have hutLe : u ≤ t - 1 := Nat.le_of_dvd htPos hut.2.2
      omega

lemma PrimeChainReachable.exists_path {q t : ℕ}
    (h : PrimeChainReachable q t) (ht : t.Prime) :
    ∃ k : ℕ, PrimeChainPath k q t := by
  induction h with
  | refl => exact ⟨0, PrimeChainPath.refl ht⟩
  | @tail b c hbc hct ih =>
      obtain ⟨k, hk⟩ := ih hct.1
      exact ⟨k + 1, hk.tail hct⟩

lemma primeChainReachable_refl (q : ℕ) : PrimeChainReachable q q :=
  Relation.ReflTransGen.refl

lemma primeChainReachable_trans {q r t : ℕ}
    (hqr : PrimeChainReachable q r) (hrt : PrimeChainReachable r t) :
    PrimeChainReachable q t :=
  hqr.trans hrt

lemma primeChainReachable_tail {q r t : ℕ}
    (hqr : PrimeChainReachable q r) (hrt : PrimeChainStep r t) :
    PrimeChainReachable q t :=
  hqr.tail hrt

lemma primeChainStep_lt {q t : ℕ} (h : PrimeChainStep q t) : q < t := by
  have htTwo := h.2.1.two_le
  have htPos : 0 < t - 1 := by omega
  have hle : q ≤ t - 1 := Nat.le_of_dvd htPos h.2.2
  omega

/-- Reachability never decreases the prime. -/
lemma primeChainReachable_le {q t : ℕ} (h : PrimeChainReachable q t) : q ≤ t := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact le_rfl
  | single hstep => exact (primeChainStep_lt hstep).le
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The primes at most `y` reachable by a chain beginning at `q`. -/
noncomputable def primeChainTargets (y q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (y + 1)).filter fun t ↦
    t.Prime ∧ PrimeChainReachable q t

@[simp] lemma mem_primeChainTargets {y q t : ℕ} :
    t ∈ primeChainTargets y q ↔
      t ≤ y ∧ t.Prime ∧ PrimeChainReachable q t := by
  classical
  simp only [primeChainTargets, Finset.mem_filter, Finset.mem_range]
  simp only [Nat.lt_succ_iff]

lemma primeChainTargets_eq_empty_of_lt {y q : ℕ} (hyq : y < q) :
    primeChainTargets y q = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hmem := mem_primeChainTargets.mp ht
  exact (not_le_of_gt hyq) ((primeChainReachable_le hmem.2.2).trans hmem.1)

lemma card_primeChainTargets_le (y q : ℕ) :
    (primeChainTargets y q).card ≤ y + 1 := by
  classical
  rw [primeChainTargets]
  simpa using Finset.card_le_card
    (Finset.filter_subset (p := fun t : ℕ ↦
      t.Prime ∧ PrimeChainReachable q t) (Finset.range (y + 1)))

/-- Every bounded reachable target occurs at some length no larger than the
target itself. -/
lemma primeChainTargets_subset_biUnion_atLength (y q : ℕ) :
    primeChainTargets y q ⊆
      (Finset.range (y + 1)).biUnion (primeChainTargetsAtLength y q) := by
  classical
  intro t ht
  obtain ⟨hty, htPrime, htReach⟩ := mem_primeChainTargets.mp ht
  obtain ⟨k, hk⟩ := htReach.exists_path htPrime
  apply Finset.mem_biUnion.mpr
  exact ⟨k, Finset.mem_range.mpr (hk.length_le_end.trans_lt (Nat.lt_succ_of_le hty)),
    mem_primeChainTargetsAtLength.mpr ⟨hty, hk⟩⟩

/-- A nonnegative sum over a finite union is at most the sum over all of its
pieces, with repetitions retained on the right. -/
lemma sum_biUnion_le_sum_sum {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s.biUnion t, f x) ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      let U := s.biUnion t
      have hleft : t a ⊆ t a ∪ U := Finset.subset_union_left
      have hdiff : (t a ∪ U) \ t a ⊆ U := by
        intro x hx
        have hxData := Finset.mem_sdiff.mp hx
        exact (Finset.mem_union.mp hxData.1).resolve_left hxData.2
      have hrem :
          (∑ x ∈ (t a ∪ U) \ t a, f x) ≤ ∑ x ∈ U, f x :=
        Finset.sum_le_sum_of_subset_of_nonneg hdiff
          (fun x _ _ ↦ hf x)
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      calc
        (∑ x ∈ t a ∪ U, f x) =
            (∑ x ∈ (t a ∪ U) \ t a, f x) + ∑ x ∈ t a, f x :=
          (Finset.sum_sdiff hleft).symm
        _ ≤ (∑ x ∈ U, f x) + ∑ x ∈ t a, f x :=
          add_le_add hrem le_rfl
        _ = (∑ x ∈ t a, f x) + ∑ x ∈ U, f x := by ring
        _ ≤ (∑ x ∈ t a, f x) + ∑ i ∈ s, ∑ x ∈ t i, f x :=
          add_le_add le_rfl ih

lemma card_primeChainTargets_le_sum_atLength (y q : ℕ) :
    (primeChainTargets y q).card ≤
      ∑ k ∈ Finset.range (y + 1),
        (primeChainTargetsAtLength y q k).card := by
  classical
  exact (Finset.card_le_card
    (primeChainTargets_subset_biUnion_atLength y q)).trans
      Finset.card_biUnion_le

/-- Sum the weighted fixed-length path bounds over every possible chain
length.  This is the reciprocal-strength FKL estimate before the row
contraction is specialized. -/
lemma sum_primeChainTargets_rpow_neg_le_of_row
    {r q y : ℕ} [NeZero r] {s R : ℝ} (hs : 1 < s)
    (hw : ∀ b : ReducedResidue r,
      (∑ a : ReducedResidue r, linkWeight r s b a) ≤ R)
    (hR : 0 ≤ R) (hRone : R < 1) (hq : q.Prime)
    (hcop : ∀ n : ℕ, n.Prime → q ≤ n → n.Coprime r) :
    (∑ t ∈ primeChainTargets y q, (t : ℝ) ^ (-s)) ≤
      (Fintype.card (ReducedResidue r) : ℝ) / (1 - R) *
        (q : ℝ) ^ (-s) := by
  classical
  have hnonneg (t : ℕ) : 0 ≤ (t : ℝ) ^ (-s) :=
    Real.rpow_nonneg (by positivity) _
  have hsubset := primeChainTargets_subset_biUnion_atLength y q
  have hunion :
      (∑ t ∈ (Finset.range (y + 1)).biUnion
          (primeChainTargetsAtLength y q), (t : ℝ) ^ (-s)) ≤
        ∑ k ∈ Finset.range (y + 1),
          ∑ t ∈ primeChainTargetsAtLength y q k, (t : ℝ) ^ (-s) :=
    sum_biUnion_le_sum_sum _ _ _ hnonneg
  have hqpow : 0 ≤ (q : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
  have hgeom :
      (∑ k ∈ Finset.range (y + 1), R ^ k) ≤ 1 / (1 - R) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := y + 1) hR hRone
    simpa using h
  calc
    (∑ t ∈ primeChainTargets y q, (t : ℝ) ^ (-s)) ≤
        ∑ t ∈ (Finset.range (y + 1)).biUnion
          (primeChainTargetsAtLength y q), (t : ℝ) ^ (-s) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun t _ _ ↦ hnonneg t)
    _ ≤ ∑ k ∈ Finset.range (y + 1),
        ∑ t ∈ primeChainTargetsAtLength y q k, (t : ℝ) ^ (-s) := hunion
    _ ≤ ∑ k ∈ Finset.range (y + 1),
        (q : ℝ) ^ (-s) *
          ((Fintype.card (ReducedResidue r) : ℝ) * R ^ k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (sum_primeChainTargetsAtLength_rpow_neg_le hs hq hcop).trans
        (mul_le_mul_of_nonneg_left
          (sum_pathWeight_le_card_mul_pow
            (w := linkWeight r s) (R := R)
            (fun b a ↦ linkWeight_nonneg r s b a) hR hw k
            (reducedResidueOfCoprime q (hcop q hq le_rfl))) hqpow)
    _ = ((q : ℝ) ^ (-s) *
          (Fintype.card (ReducedResidue r) : ℝ)) *
        (∑ k ∈ Finset.range (y + 1), R ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ((q : ℝ) ^ (-s) *
          (Fintype.card (ReducedResidue r) : ℝ)) *
        (1 / (1 - R)) := by
      apply mul_le_mul_of_nonneg_left hgeom
      positivity
    _ = (Fintype.card (ReducedResidue r) : ℝ) / (1 - R) *
        (q : ℝ) ^ (-s) := by ring

/-- Summing the fixed-length estimates and the geometric contraction gives
the FKL bound for the full bounded prime-chain closure. -/
lemma card_primeChainTargets_le_of_row
    {r q y : ℕ} [NeZero r] {s R : ℝ} (hs : 1 < s)
    (hw : ∀ b : ReducedResidue r,
      (∑ a : ReducedResidue r, linkWeight r s b a) ≤ R)
    (hR : 0 ≤ R) (hRone : R < 1) (hq : q.Prime) (hqy : q ≤ y)
    (hcop : ∀ n : ℕ, n.Prime → q ≤ n → n.Coprime r) :
    ((primeChainTargets y q).card : ℝ) ≤
      (Fintype.card (ReducedResidue r) : ℝ) / (1 - R) *
        ((y : ℝ) / (q : ℝ)) ^ s := by
  let x : ℝ := (y : ℝ) / (q : ℝ)
  have hcardNat := card_primeChainTargets_le_sum_atLength y q
  have hcardReal : ((primeChainTargets y q).card : ℝ) ≤
      ∑ k ∈ Finset.range (y + 1),
        ((primeChainTargetsAtLength y q k).card : ℝ) := by
    exact_mod_cast hcardNat
  have hxpow : 0 ≤ x ^ s := Real.rpow_nonneg (by positivity) s
  have hgeom : (∑ k ∈ Finset.range (y + 1), R ^ k) ≤ 1 / (1 - R) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := y + 1) hR hRone
    simpa using h
  calc
    ((primeChainTargets y q).card : ℝ) ≤
        ∑ k ∈ Finset.range (y + 1),
          ((primeChainTargetsAtLength y q k).card : ℝ) := hcardReal
    _ ≤ ∑ k ∈ Finset.range (y + 1),
        (Fintype.card (ReducedResidue r) : ℝ) * R ^ k * x ^ s := by
      exact Finset.sum_le_sum fun k _ ↦
        card_primeChainTargetsAtLength_le hs hw hR hq hqy hcop
    _ = ((Fintype.card (ReducedResidue r) : ℝ) * x ^ s) *
        (∑ k ∈ Finset.range (y + 1), R ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ((Fintype.card (ReducedResidue r) : ℝ) * x ^ s) *
        (1 / (1 - R)) :=
      mul_le_mul_of_nonneg_left hgeom (mul_nonneg (by positivity) hxpow)
    _ = (Fintype.card (ReducedResidue r) : ℝ) / (1 - R) *
        ((y : ℝ) / (q : ℝ)) ^ s := by
      dsimp [x]
      ring

/-- Ford--Konyagin--Luca prime-chain estimate in the uniform form needed by
FLP: after a fixed cutoff depending only on `ε`, the number of prime-chain
targets up to `y` is at most `C (y/q)^(1+ε)`. -/
theorem exists_primeChainTargets_card_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ q y : ℕ, q.Prime → Q < q → q ≤ y →
        ((primeChainTargets y q).card : ℝ) ≤
          C * ((y : ℝ) / (q : ℝ)) ^ (1 + ε) := by
  have hs : 1 < (1 + ε : ℝ) := by linarith
  obtain ⟨r, R, hrpos, _hrSquarefree, _hrEven, hR, hRone, hrow⟩ :=
    exists_linkWeight_row_contraction hs
  let hr : NeZero r := ⟨hrpos.ne'⟩
  let _ : NeZero r := hr
  let C : ℝ := (Fintype.card (ReducedResidue r) : ℝ) / (1 - R)
  have hcardPos : 0 < Fintype.card (ReducedResidue r) := Fintype.card_pos
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨r, C, hC, ?_⟩
  intro q y hq hrq hqy
  have hcop : ∀ n : ℕ, n.Prime → q ≤ n → n.Coprime r := by
    intro n hn hqn
    apply hn.coprime_iff_not_dvd.mpr
    intro hnr
    have hnrLe : n ≤ r := Nat.le_of_dvd hrpos hnr
    omega
  have hrow' : ∀ b : ReducedResidue r,
      (∑ a : ReducedResidue r, linkWeight r (1 + ε) b a) ≤ R :=
    hrow hr
  simpa only [C] using
    card_primeChainTargets_le_of_row hs hrow' hR hRone hq hqy hcop

/-- Uniform weighted FKL estimate.  Unlike the cardinal version, its bound
is independent of the terminal cutoff `y`. -/
theorem exists_primeChainTargets_rpow_sum_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ q y : ℕ, q.Prime → Q < q → q ≤ y →
        (∑ t ∈ primeChainTargets y q,
          (t : ℝ) ^ (-(1 + ε))) ≤
            C * (q : ℝ) ^ (-(1 + ε)) := by
  have hs : 1 < (1 + ε : ℝ) := by linarith
  obtain ⟨r, R, hrpos, _hrSquarefree, _hrEven, hR, hRone, hrow⟩ :=
    exists_linkWeight_row_contraction hs
  let hr : NeZero r := ⟨hrpos.ne'⟩
  let _ : NeZero r := hr
  let C : ℝ := (Fintype.card (ReducedResidue r) : ℝ) / (1 - R)
  have hcardPos : 0 < Fintype.card (ReducedResidue r) := Fintype.card_pos
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨r, C, hC, ?_⟩
  intro q y hq hrq hqy
  have hcop : ∀ n : ℕ, n.Prime → q ≤ n → n.Coprime r := by
    intro n hn hqn
    apply hn.coprime_iff_not_dvd.mpr
    intro hnr
    have hnrLe : n ≤ r := Nat.le_of_dvd hrpos hnr
    omega
  have hrow' : ∀ b : ReducedResidue r,
      (∑ a : ReducedResidue r, linkWeight r (1 + ε) b a) ≤ R :=
    hrow hr
  simpa only [C] using
    sum_primeChainTargets_rpow_neg_le_of_row hs hrow' hR hRone hq hcop

/-- Reciprocal version of the FKL estimate.  The elementary inequality
`t⁻¹ ≤ y^ε t⁻¹⁻ε` converts the weighted path estimate into exactly the
harmonic-mass bound used to remove the bad prime-chain closure. -/
theorem exists_primeChainTargets_harmonic_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ q y : ℕ, q.Prime → Q < q → q ≤ y →
        (∑ t ∈ primeChainTargets y q, (t : ℝ)⁻¹) ≤
          C * (y : ℝ) ^ ε * (q : ℝ) ^ (-(1 + ε)) := by
  obtain ⟨Q, C, hC, hweighted⟩ :=
    exists_primeChainTargets_rpow_sum_bound hε
  refine ⟨Q, C, hC, ?_⟩
  intro q y hq hQq hqy
  have hyPos : (0 : ℝ) < y := by
    exact_mod_cast hq.pos.trans_le hqy
  have hpoint (t : ℕ) (ht : t ∈ primeChainTargets y q) :
      (t : ℝ)⁻¹ ≤ (y : ℝ) ^ ε * (t : ℝ) ^ (-(1 + ε)) := by
    have htData := mem_primeChainTargets.mp ht
    have htPos : (0 : ℝ) < t := by exact_mod_cast htData.2.1.pos
    have hty : (t : ℝ) ≤ y := by exact_mod_cast htData.1
    have hpow : (t : ℝ) ^ ε ≤ (y : ℝ) ^ ε :=
      Real.rpow_le_rpow htPos.le hty hε.le
    calc
      (t : ℝ)⁻¹ = (t : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
      _ = (t : ℝ) ^ ε * (t : ℝ) ^ (-(1 + ε)) := by
        rw [← Real.rpow_add htPos]
        congr 1
        ring
      _ ≤ (y : ℝ) ^ ε * (t : ℝ) ^ (-(1 + ε)) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg htPos.le _)
  calc
    (∑ t ∈ primeChainTargets y q, (t : ℝ)⁻¹) ≤
        ∑ t ∈ primeChainTargets y q,
          (y : ℝ) ^ ε * (t : ℝ) ^ (-(1 + ε)) := by
      exact Finset.sum_le_sum fun t ht ↦ hpoint t ht
    _ = (y : ℝ) ^ ε *
        (∑ t ∈ primeChainTargets y q,
          (t : ℝ) ^ (-(1 + ε))) := by
      rw [Finset.mul_sum]
    _ ≤ (y : ℝ) ^ ε *
        (C * (q : ℝ) ^ (-(1 + ε))) :=
      mul_le_mul_of_nonneg_left (hweighted q y hq hQq hqy)
        (Real.rpow_nonneg hyPos.le _)
    _ = C * (y : ℝ) ^ ε * (q : ℝ) ^ (-(1 + ε)) := by ring

/-- The finite bounded prime-chain closure of a finite set of roots. -/
noncomputable def primeChainClosureTargets (y : ℕ) (E : Finset ℕ) : Finset ℕ :=
  E.biUnion (primeChainTargets y)

@[simp] lemma mem_primeChainClosureTargets {y : ℕ} {E : Finset ℕ} {t : ℕ} :
    t ∈ primeChainClosureTargets y E ↔
      ∃ q ∈ E, t ≤ y ∧ t.Prime ∧ PrimeChainReachable q t := by
  classical
  simp [primeChainClosureTargets]

/-- Summing the reciprocal FKL estimate over finitely many bad roots.  The
right side deliberately retains the weighted root mass, which is the sharp
quantity available from the few-bad-moduli estimate. -/
theorem exists_primeChainClosureTargets_harmonic_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (E : Finset ℕ) (y : ℕ),
        (∀ q ∈ E, q.Prime ∧ Q < q ∧ q ≤ y) →
        (∑ t ∈ primeChainClosureTargets y E, (t : ℝ)⁻¹) ≤
          C * (y : ℝ) ^ ε *
            ∑ q ∈ E, (q : ℝ) ^ (-(1 + ε)) := by
  obtain ⟨Q, C, hC, htarget⟩ :=
    exists_primeChainTargets_harmonic_bound hε
  refine ⟨Q, C, hC, ?_⟩
  intro E y hE
  have hunion := sum_biUnion_le_sum_sum E (primeChainTargets y)
    (fun t : ℕ ↦ (t : ℝ)⁻¹) (fun t ↦ by positivity)
  calc
    (∑ t ∈ primeChainClosureTargets y E, (t : ℝ)⁻¹) ≤
        ∑ q ∈ E, ∑ t ∈ primeChainTargets y q, (t : ℝ)⁻¹ := by
      simpa only [primeChainClosureTargets] using hunion
    _ ≤ ∑ q ∈ E,
        C * (y : ℝ) ^ ε * (q : ℝ) ^ (-(1 + ε)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact htarget q y (hE q hq).1 (hE q hq).2.1 (hE q hq).2.2
    _ = C * (y : ℝ) ^ ε *
        ∑ q ∈ E, (q : ℝ) ^ (-(1 + ε)) := by
      rw [Finset.mul_sum]

/-- The upward prime-chain closure of a set of bad root primes. -/
def primeChainClosure (E : Set ℕ) : Set ℕ :=
  {t | t.Prime ∧ ∃ q ∈ E, PrimeChainReachable q t}

lemma mem_primeChainClosure_of_mem {E : Set ℕ} {q : ℕ}
    (hqPrime : q.Prime) (hqE : q ∈ E) : q ∈ primeChainClosure E := by
  exact ⟨hqPrime, q, hqE, primeChainReachable_refl q⟩

lemma primeChainClosure_mono {E F : Set ℕ} (hEF : E ⊆ F) :
    primeChainClosure E ⊆ primeChainClosure F := by
  rintro t ⟨ht, q, hqE, hqt⟩
  exact ⟨ht, q, hEF hqE, hqt⟩

/-- The chain closure is closed under adding one congruence edge. -/
lemma mem_primeChainClosure_of_step {E : Set ℕ} {q t : ℕ}
    (hq : q ∈ primeChainClosure E) (hqt : PrimeChainStep q t) :
    t ∈ primeChainClosure E := by
  obtain ⟨_, r, hrE, hrq⟩ := hq
  exact ⟨hqt.2.1, r, hrE, primeChainReachable_tail hrq hqt⟩

/-- Contrapositive closure form used in the good-branch valuation argument. -/
lemma not_mem_primeChainClosure_of_dvd_pred {E : Set ℕ} {q t : ℕ}
    (hqPrime : q.Prime) (htPrime : t.Prime) (hqt : q ∣ t - 1)
    (ht : t ∉ primeChainClosure E) : q ∉ primeChainClosure E := by
  intro hq
  exact ht (mem_primeChainClosure_of_step hq ⟨hqPrime, htPrime, hqt⟩)

end Erdos48

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file develops verified supporting lemmas toward a Lean formalization of
the resolution of Erdős Problem 402, also known as Graham's gcd conjecture.

Informal authors:
- R. Balasubramanian
- K. Soundararajan

Reference:
- R. Balasubramanian and K. Soundararajan, "On a conjecture of R. L. Graham",
  Acta Arithmetica 75 (1996), 1--38.

Progress log:
- verified: normalization, reciprocal/lcm reductions, prime-cardinality and
  Boyle lemmas, collision structure, the closed range through cardinality 7000,
  Lemmas 2.1--2.5, the Section 4 exceptional-prime reduction, and exact finite
  lower/upper endgame interfaces;
- verified most recently: a complete first-moment/PNT separation proving the
  conjecture for every sufficiently large cardinality, and the square-root
  prime-pair reduction used by the published medium-range computation;
- remaining: an axiom-free explicit prime certificate bridging cardinalities
  `7001` through the non-effective threshold inherited from `MediumPNT`.
-/

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.MaricaSchoenheim
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import PrimeNumberTheoremAnd.MediumPNT

namespace Erdos402

open scoped Pointwise
open Filter Asymptotics

/-- The integral form of the bound in Graham's gcd conjecture. -/
def GrahamBound (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, A.card * a.gcd b ≤ a

/-- Executable witness search for `GrahamBound`.  This is used only to
kernel-check closed finite certificates. -/
private def hasGrahamBound (A : Finset ℕ) : Bool :=
  (A.sort (· ≤ ·)).any fun a ↦
    (A.sort (· ≤ ·)).any fun b ↦ decide (A.card * a.gcd b ≤ a)

private lemma hasGrahamBound_eq_true (A : Finset ℕ) :
    hasGrahamBound A = true ↔ GrahamBound A := by
  simp only [hasGrahamBound, List.any_eq_true, decide_eq_true_eq, Finset.mem_sort,
    GrahamBound]

/-- The `n`-element subsets of `D` for which executable witness search
finds no Graham pair. -/
private def badSubsets (D : Finset ℕ) (n : ℕ) : Finset (Finset ℕ) :=
  (D.powersetCard n).filter fun A ↦ hasGrahamBound A = false

private lemma grahamBound_of_badSubsets_eq_empty {D A : Finset ℕ} {n : ℕ}
    (hcert : badSubsets D n = ∅) (hsub : A ⊆ D) (hcard : A.card = n) :
    GrahamBound A := by
  by_contra hbad
  have hbool : hasGrahamBound A = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hbad ((hasGrahamBound_eq_true A).mp htrue)
  have hmem : A ∈ badSubsets D n := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, hbool⟩
  rw [hcert] at hmem
  exact Finset.notMem_empty A hmem

/-- Clearing the positive denominator in the rational statement produces the
integral form used in the number-theoretic argument. -/
lemma gcd_cast_le_div_iff {a b n : ℕ} (hn : 0 < n) :
    (a.gcd b : ℚ) ≤ (a / n : ℚ) ↔ n * a.gcd b ≤ a := by
  rw [le_div_iff₀]
  · norm_cast
    simp only [mul_comm]
  · exact_mod_cast hn

/-- Final cast-and-witness conversion from the integral Graham bound to the
exact Formal Conjectures statement. -/
lemma erdos_402_of_grahamBound (A : Finset ℕ) (hA : A.Nonempty)
    (h : GrahamBound A) :
    ∃ᵉ (a ∈ A) (b ∈ A), a.gcd b ≤ (a / A.card : ℚ) := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  refine ⟨a, ha, b, hb, ?_⟩
  exact (gcd_cast_le_div_iff (Finset.card_pos.mpr hA)).2 hab

/-- Increasing enumeration of a finset, extended by zero outside its range. -/
private def enumerate (A : Finset ℕ) (k : ℕ) : ℕ :=
  if hk : k < A.card then A.orderEmbOfFin rfl ⟨k, hk⟩ else 0

@[simp] private lemma enumerate_of_lt (A : Finset ℕ) {k : ℕ} (hk : k < A.card) :
    enumerate A k = A.orderEmbOfFin rfl ⟨k, hk⟩ := by
  simp [enumerate, hk]

private lemma enumerate_strictMonoOn (A : Finset ℕ) :
    StrictMonoOn (enumerate A) (Set.Iio A.card) := by
  intro i hi j hj hij
  rw [enumerate_of_lt A hi, enumerate_of_lt A hj]
  exact (A.orderEmbOfFin rfl).strictMono hij

/-- The finset formulation is exactly Mathlib's sequence formulation of
Graham's conjecture, after enumerating the finset in increasing order. -/
lemma grahamBound_of_grahamConjecture (A : Finset ℕ) (hA : A.Nonempty)
    (h : Nat.GrahamConjecture A.card (enumerate A)) : GrahamBound A := by
  have hn : A.card ≠ 0 := Finset.card_ne_zero.mpr hA
  obtain ⟨i, hi, j, hj, hij⟩ := h hn (enumerate_strictMonoOn A)
  refine ⟨A.orderEmbOfFin rfl ⟨i, hi⟩, A.orderEmbOfFin_mem rfl ⟨i, hi⟩,
    A.orderEmbOfFin rfl ⟨j, hj⟩, A.orderEmbOfFin_mem rfl ⟨j, hj⟩, ?_⟩
  simpa [enumerate_of_lt A hi, enumerate_of_lt A hj, mul_comm] using hij

/-- Mathlib's Marica--Schönheim argument settles the squarefree special case. -/
lemma grahamBound_of_squarefree (A : Finset ℕ) (hA : A.Nonempty)
    (hsq : ∀ a ∈ A, Squarefree a) : GrahamBound A := by
  apply grahamBound_of_grahamConjecture A hA
  apply Nat.grahamConjecture_of_squarefree
  intro k hk
  rw [enumerate_of_lt A hk]
  exact hsq _ (A.orderEmbOfFin_mem rfl ⟨k, hk⟩)

/-! ## The prime-cardinality case -/

/-- If two positive integers have both directed gcd quotients below the
prime `p`, their `p`-free parts have the same nonzero residue modulo `p`
only when the integers themselves are equal. -/
private lemma primeFree_inj {p a b : ℕ} (hp : p.Prime) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : a / a.gcd b < p) (hb : b / a.gcd b < p)
    (hc : ((ordCompl[p] a : ℕ) : ZMod p) = ((ordCompl[p] b : ℕ) : ZMod p)) : a = b := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := a.gcd b
  let x := a / g
  let y := b / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hxpos : 0 < x := Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
  have hypos : 0 < y := Nat.div_pos (Nat.gcd_le_right a (Nat.pos_of_ne_zero hb0)) hgpos
  have hxlt : x < p := ha
  have hylt : y < p := hb
  have hpx : ¬p ∣ x := by
    intro h
    exact (not_lt_of_ge (Nat.le_of_dvd hxpos h)) hxlt
  have hpy : ¬p ∣ y := by
    intro h
    exact (not_lt_of_ge (Nat.le_of_dvd hypos h)) hylt
  have hox : ordCompl[p] x = x :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd x hp).mpr (Or.inr hpx)
  have hoy : ordCompl[p] y = y :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd y hp).mpr (Or.inr hpy)
  have hga : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hcg0 : ((ordCompl[p] g : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_ordCompl hp hgpos.ne'
      ((ZMod.natCast_eq_zero_iff (ordCompl[p] g : ℕ) p).mp hz)
  have hc' : ((ordCompl[p] g : ℕ) : ZMod p) * x =
      ((ordCompl[p] g : ℕ) : ZMod p) * y := by
    simpa only [← hga, ← hgb, Nat.ordCompl_mul, hox, hoy, Nat.cast_mul] using hc
  have hxyZ : (x : ZMod p) = y := mul_left_cancel₀ hcg0 hc'
  have hxy : x = y := by
    have hv := congrArg ZMod.val hxyZ
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hv
  rw [← hga, ← hgb, hxy]

/-- Graham's bound for sets of prime cardinality.  Under a counterexample
hypothesis, `p`-free reduction modulo `p` would inject `p` elements into
the `p - 1` nonzero residue classes. -/
lemma grahamBound_of_prime_card (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hp : A.card.Prime) : GrahamBound A := by
  by_contra hbad
  let p := A.card
  letI : Fact p.Prime := ⟨hp⟩
  have hquot : ∀ a ∈ A, ∀ b ∈ A, a / a.gcd b < p := by
    intro a ha b hb
    have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ ha)
    have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    rw [Nat.div_lt_iff_lt_mul hgpos]
    by_contra h
    apply hbad
    exact ⟨a, ha, b, hb, by simpa [p, mul_comm] using h⟩
  letI := Fintype.ofFinite {z : ZMod p // z ≠ 0}
  let color : {a // a ∈ A} → {z : ZMod p // z ≠ 0} := fun a ↦
    ⟨((ordCompl[p] a.1 : ℕ) : ZMod p), by
      intro hz
      have ha0 : a.1 ≠ 0 := fun h ↦ h₀ (h ▸ a.2)
      exact Nat.not_dvd_ordCompl hp ha0
        ((ZMod.natCast_eq_zero_iff (ordCompl[p] a.1 : ℕ) p).mp hz)⟩
  have hcolor : Function.Injective color := by
    intro a b hab
    apply Subtype.ext
    apply primeFree_inj hp
    · exact fun h ↦ h₀ (h ▸ a.2)
    · exact fun h ↦ h₀ (h ▸ b.2)
    · exact hquot a.1 a.2 b.1 b.2
    · simpa [Nat.gcd_comm] using hquot b.1 b.2 a.1 a.2
    · exact congrArg Subtype.val hab
  have hle := Fintype.card_le_of_injective color hcolor
  have hcod : Fintype.card {z : ZMod p // z ≠ 0} = p - 1 := by
    rw [Fintype.card_subtype_compl (fun z : ZMod p ↦ z = 0)]
    simp
  rw [Fintype.card_coe, hcod] at hle
  exact (not_le_of_gt (Nat.sub_lt hp.pos Nat.zero_lt_one)) (by simpa [p] using hle)

/-- Ordinary residues modulo `p` are injective on a family whose two
directed gcd quotients are below `p`, provided `p` divides neither
integer. -/
private lemma residue_inj_of_div_gcd_lt {p a b : ℕ} (hp : p.Prime)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hpa : ¬p ∣ a)
    (ha : a / a.gcd b < p) (hb : b / a.gcd b < p)
    (hc : (a : ZMod p) = (b : ZMod p)) : a = b := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := a.gcd b
  let x := a / g
  let y := b / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hxlt : x < p := ha
  have hylt : y < p := hb
  have hga : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hpg : ¬p ∣ g := fun h ↦ hpa (h.trans (Nat.gcd_dvd_left a b))
  have hcg0 : (g : ZMod p) ≠ 0 := by
    intro hz
    exact hpg ((ZMod.natCast_eq_zero_iff g p).mp hz)
  have hc' : (g : ZMod p) * x = (g : ZMod p) * y := by
    calc
      (g : ZMod p) * x = ((g * x : ℕ) : ZMod p) := (Nat.cast_mul g x).symm
      _ = (a : ZMod p) := congrArg (fun n : ℕ ↦ (n : ZMod p)) hga
      _ = (b : ZMod p) := hc
      _ = ((g * y : ℕ) : ZMod p) := congrArg (fun n : ℕ ↦ (n : ZMod p)) hgb.symm
      _ = (g : ZMod p) * y := Nat.cast_mul g y
  have hxyZ : (x : ZMod p) = y := mul_left_cancel₀ hcg0 hc'
  have hxy : x = y := by
    have hv := congrArg ZMod.val hxyZ
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hv
  rw [← hga, ← hgb, hxy]

/-- Canonical representative of the unordered pair of nonzero residues
`{r, -r}`. -/
private def foldedResidue (p a : ℕ) : ℕ :=
  min (a % p) (p - a % p)

private lemma foldedResidue_pos {p a : ℕ} (hp : 0 < p) (hpa : ¬p ∣ a) :
    0 < foldedResidue p a := by
  have hrlt : a % p < p := Nat.mod_lt a hp
  have hr0 : a % p ≠ 0 := by
    intro h
    exact hpa (Nat.dvd_of_mod_eq_zero h)
  unfold foldedResidue
  omega

private lemma foldedResidue_le_div_two {p a : ℕ} (hp : 0 < p) :
    foldedResidue p a ≤ p / 2 := by
  have hrlt : a % p < p := Nat.mod_lt a hp
  unfold foldedResidue
  omega

private lemma foldedResidue_eq_iff {p a b : ℕ} (hp : 0 < p)
    (hpa : ¬p ∣ a) (hpb : ¬p ∣ b)
    (h : foldedResidue p a = foldedResidue p b) :
    a % p = b % p ∨ a % p + b % p = p := by
  have halt : a % p < p := Nat.mod_lt a hp
  have hblt : b % p < p := Nat.mod_lt b hp
  have ha0 : a % p ≠ 0 := fun hz ↦ hpa (Nat.dvd_of_mod_eq_zero hz)
  have hb0 : b % p ≠ 0 := fun hz ↦ hpb (Nat.dvd_of_mod_eq_zero hz)
  unfold foldedResidue at h
  simp only [min_def] at h
  split at h <;> split at h <;> omega

/-- The least member of `A` having the same folded residue as `a`; it is
used to choose one canonical representative from each residue class modulo
sign.  The default value is irrelevant when `a ∉ A`. -/
private noncomputable def foldedMin (A : Finset ℕ) (p a : ℕ) : ℕ := by
  classical
  exact if ha : a ∈ A then
    (A.filter fun b ↦ foldedResidue p b = foldedResidue p a).min'
      ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  else 0

private lemma foldedMin_mem {A : Finset ℕ} {p a : ℕ} (ha : a ∈ A) :
    foldedMin A p a ∈ A := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

private lemma foldedMin_color {A : Finset ℕ} {p a : ℕ} (ha : a ∈ A) :
    foldedResidue p (foldedMin A p a) = foldedResidue p a := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  let S := A.filter fun b ↦ foldedResidue p b = foldedResidue p a
  have hS : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  exact (Finset.mem_filter.mp (S.min'_mem hS)).2

private lemma foldedMin_le {A : Finset ℕ} {p a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hcolor : foldedResidue p b = foldedResidue p a) : foldedMin A p a ≤ b := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨hb, hcolor⟩

private lemma foldedMin_eq_of_color {A : Finset ℕ} {p a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A)
    (hcolor : foldedResidue p a = foldedResidue p b) :
    foldedMin A p a = foldedMin A p b := by
  apply Nat.le_antisymm
  · apply foldedMin_le ha (foldedMin_mem hb)
    exact (foldedMin_color hb).trans hcolor.symm
  · apply foldedMin_le hb (foldedMin_mem ha)
    exact (foldedMin_color ha).trans hcolor

/-- Positive common multipliers represented by the pair `α, β` in `A`.
The image by division merely supplies a finite ambient set; the filter is
the mathematical definition. -/
private def representedMultipliers (A : Finset ℕ) (α β : ℕ) : Finset ℕ :=
  (A.image fun a ↦ a / α).filter fun d ↦ 0 < d ∧ α * d ∈ A ∧ β * d ∈ A

private lemma mem_representedMultipliers {A : Finset ℕ} {α β d : ℕ} (hα : 0 < α) :
    d ∈ representedMultipliers A α β ↔ 0 < d ∧ α * d ∈ A ∧ β * d ∈ A := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨α * d, h.2.1, ?_⟩, h⟩
    exact Nat.mul_div_cancel_left d hα

private lemma representedMultipliers_nonzero {A : Finset ℕ} {α β : ℕ} (hα : 0 < α) :
    0 ∉ representedMultipliers A α β := by
  rw [mem_representedMultipliers hα]
  simp

/-- The paper's multiplicity `rₚ(α)`. -/
private def representationCount (A : Finset ℕ) (p α : ℕ) : ℕ :=
  (representedMultipliers A α (p - α)).card

/-- The finite dependent set counted by `∑_{α∈Jₚ} rₚ(α)`. -/
private def representationPairs (A : Finset ℕ) (p : ℕ) :
    Finset ((α : ℕ) × ℕ) :=
  (Finset.Icc ((p + 1) / 2) A.card).sigma fun α ↦
    representedMultipliers A α (p - α)

/-- For any finite family of natural multiplicities, total mass at least the
number of indices forces the total excess above one to dominate the number
of zero fibers. -/
private lemma zero_card_le_excess {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (h : S.card ≤ S.sum f) :
    (S.filter fun x ↦ f x = 0).card ≤
      (S.filter fun x ↦ 2 ≤ f x).sum fun x ↦ f x - 1 := by
  let Z := S.filter fun x ↦ f x = 0
  let M := S.filter fun x ↦ 2 ≤ f x
  have hZ : Z.card = ∑ x ∈ S, if f x = 0 then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_filter (fun x ↦ f x = 0) (fun _ ↦ 1)
  have hM : M.sum (fun x ↦ f x - 1) =
      ∑ x ∈ S, if 2 ≤ f x then f x - 1 else 0 := by
    exact Finset.sum_filter (fun x ↦ 2 ≤ f x) (fun x ↦ f x - 1)
  have hid : S.sum f + Z.card = S.card + M.sum (fun x ↦ f x - 1) := by
    rw [hZ, hM, Finset.card_eq_sum_ones]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> omega
  change Z.card ≤ M.sum fun x ↦ f x - 1
  omega

/-! ## Normalization and the finite-divisor reduction -/

/-- Divide every member of `A` by the common gcd. -/
private def normalize (A : Finset ℕ) : Finset ℕ :=
  A.image fun a ↦ a / A.gcd id

private lemma gcd_pos (A : Finset ℕ) (h₀ : 0 ∉ A) (hA : A.Nonempty) :
    0 < A.gcd id := by
  apply Nat.pos_of_ne_zero
  intro hg
  obtain ⟨a, ha⟩ := hA
  have := Finset.gcd_eq_zero_iff.mp hg a ha
  exact h₀ (this ▸ ha)

private lemma normalize_card (A : Finset ℕ) : (normalize A).card = A.card := by
  classical
  rw [normalize, Finset.card_image_of_injOn]
  intro a ha b hb hab
  have hda : A.gcd id ∣ a := by
    obtain ⟨c, hc⟩ := Finset.gcd_dvd (f := id) ha
    exact ⟨c, hc⟩
  have hdb : A.gcd id ∣ b := by
    obtain ⟨c, hc⟩ := Finset.gcd_dvd (f := id) hb
    exact ⟨c, hc⟩
  exact (Nat.div_left_inj hda hdb).mp hab

private lemma normalize_mem (A : Finset ℕ) {a : ℕ} (ha : a ∈ A) :
    a / A.gcd id ∈ normalize A := by
  classical
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

private lemma normalize_nonzero (A : Finset ℕ) (h₀ : 0 ∉ A) : 0 ∉ normalize A := by
  classical
  intro h
  obtain ⟨a, ha, hadiv⟩ := Finset.mem_image.mp h
  have hgda : A.gcd id ∣ a := Finset.gcd_dvd ha
  have ha0 : a ≠ 0 := fun hzero ↦ h₀ (hzero ▸ ha)
  have hdiv0 : a / A.gcd id ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hgda)
      (gcd_pos A h₀ ⟨a, ha⟩)
  exact hdiv0 hadiv

private lemma normalize_gcd (A : Finset ℕ) (h₀ : 0 ∉ A) (hA : A.Nonempty) :
    (normalize A).gcd id = 1 := by
  classical
  unfold normalize
  rw [← Finset.gcd_eq_gcd_image]
  obtain ⟨a, ha⟩ := hA
  exact Finset.gcd_div_id_eq_one ha (fun h ↦ h₀ (h ▸ ha))

/-- In a strict counterexample every directed gcd quotient is strictly
smaller than the cardinality. -/
private lemma div_gcd_lt_card_of_not_grahamBound (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (ha0 : a ≠ 0) : a / a.gcd b < A.card := by
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  rw [Nat.div_lt_iff_lt_mul hgpos]
  exact Nat.lt_of_not_ge fun h ↦ hbad ⟨a, ha, b, hb, by simpa [mul_comm] using h⟩

/-- After gcd-normalization, a prime at least as large as the cardinality
cannot divide any member of a strict counterexample. -/
private lemma prime_not_dvd_of_card_le (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hcard : A.card ≤ p) {a : ℕ} (ha : a ∈ A) : ¬p ∣ a := by
  intro hpa
  have hex : ∃ b ∈ A, ¬p ∣ b := by
    by_contra h
    push Not at h
    have hpgcd : p ∣ A.gcd id := Finset.dvd_gcd fun b hb ↦ h b hb
    rw [hgcd] at hpgcd
    exact hp.not_dvd_one hpgcd
  obtain ⟨b, hb, hpb⟩ := hex
  have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ ha)
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hpg : ¬p ∣ a.gcd b := fun h ↦ hpb (h.trans (Nat.gcd_dvd_right a b))
  have hpquot : p ∣ a / a.gcd b := by
    have hprod : (a / a.gcd b) * a.gcd b = a :=
      Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
    have hp_prod : p ∣ (a / a.gcd b) * a.gcd b := by
      rw [hprod]
      exact hpa
    exact (hp.dvd_mul.mp hp_prod).resolve_right hpg
  have hqpos : 0 < a / a.gcd b :=
    Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
  have hple : p ≤ a / a.gcd b := Nat.le_of_dvd hqpos hpquot
  have hlt := div_gcd_lt_card_of_not_grahamBound A hbad ha hb ha0
  omega

/-- Boyle's large-prime-divisor lemma.  In a normalized strict
counterexample no prime `q` with `|A| ≤ 2q` can divide a member.

The proof splits `A` into the `q`-divisible part `qU` and the `q`-free
part `V`.  Every cross quotient from `qU` to `V` is a positive multiple
of `q` below `|A|`, hence equals `q`; consequently every `u ∈ U` divides
every `v ∈ V`.  Ordering `U` and `V` gives `|U| + |V| - 1 = |A| - 1`
distinct ratios `v/u`.  They all belong to `{1, ..., |A|-1} \ {q}`,
which has only `|A|-2` elements. -/
private lemma prime_not_dvd_of_card_le_two_mul (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {q : ℕ} (hq : q.Prime)
    (hlarge : A.card ≤ 2 * q) {a : ℕ} (ha : a ∈ A) : ¬q ∣ a := by
  classical
  by_cases hcard : A.card ≤ q
  · exact prime_not_dvd_of_card_le A h₀ hgcd hbad hq hcard ha
  have hqn : q < A.card := Nat.lt_of_not_ge hcard
  intro hqa
  let C := A.filter fun x ↦ q ∣ x
  let V := A.filter fun x ↦ ¬q ∣ x
  let U := C.image fun x ↦ x / q
  have hCne : C.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hqa⟩⟩
  have hVne : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hall : ∀ x ∈ A, q ∣ x := by
      intro x hx
      by_contra hqx
      have : x ∈ V := Finset.mem_filter.mpr ⟨hx, hqx⟩
      simpa [h] using this
    have hqgcd : q ∣ A.gcd id := Finset.dvd_gcd hall
    rw [hgcd] at hqgcd
    exact hq.not_dvd_one hqgcd
  have hUne : U.Nonempty := hCne.image _
  have hUcard : U.card = C.card := by
    dsimp only [U]
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    have hqx : q ∣ x := (Finset.mem_filter.mp hx).2
    have hqy : q ∣ y := (Finset.mem_filter.mp hy).2
    exact (Nat.div_left_inj hqx hqy).mp hxy
  have hpartition : C.card + V.card = A.card := by
    simpa only [C, V] using
      (Finset.card_filter_add_card_filter_not (s := A) (p := fun x ↦ q ∣ x))
  have hcross : ∀ c ∈ C, ∀ v ∈ V, c / q ∣ v := by
    intro c hc v hv
    have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
    have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
    have hvA : v ∈ A := (Finset.mem_filter.mp hv).1
    have hqv : ¬q ∣ v := (Finset.mem_filter.mp hv).2
    have hc0 : c ≠ 0 := fun hz ↦ h₀ (hz ▸ hcA)
    have hgpos : 0 < c.gcd v := Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hc0)
    have hqg : ¬q ∣ c.gcd v := fun h ↦ hqv (h.trans (Nat.gcd_dvd_right c v))
    have hqquot : q ∣ c / c.gcd v := by
      have hprod : (c / c.gcd v) * c.gcd v = c :=
        Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
      have : q ∣ (c / c.gcd v) * c.gcd v := by simpa [hprod] using hqc
      exact (hq.dvd_mul.mp this).resolve_right hqg
    have hquotpos : 0 < c / c.gcd v :=
      Nat.div_pos (Nat.gcd_le_left v (Nat.pos_of_ne_zero hc0)) hgpos
    have hquotlt : c / c.gcd v < A.card :=
      div_gcd_lt_card_of_not_grahamBound A hbad hcA hvA hc0
    have hquoteq : c / c.gcd v = q := by
      obtain ⟨k, hk⟩ := hqquot
      have hkpos : 0 < k := by
        exact Nat.pos_of_mul_pos_left (hk ▸ hquotpos)
      have hkle : k = 1 := by
        by_contra hk1
        have hk2 : 2 ≤ k := by omega
        have htwo : 2 * q ≤ c / c.gcd v := by
          calc
            2 * q = q * 2 := Nat.mul_comm 2 q
            _ ≤ q * k := Nat.mul_le_mul_left q hk2
            _ = c / c.gcd v := hk.symm
        omega
      simpa [hkle] using hk
    have hcprod : q * (c / q) = c := by
      simpa [mul_comm] using Nat.mul_div_cancel' hqc
    have hgprod : q * c.gcd v = c := by
      calc
        q * c.gcd v = (c / c.gcd v) * c.gcd v := by rw [hquoteq]
        _ = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
    have hg : c.gcd v = c / q := Nat.mul_left_cancel hq.pos (hgprod.trans hcprod.symm)
    rw [← hg]
    exact Nat.gcd_dvd_right c v
  have hcrossU : ∀ u ∈ U, ∀ v ∈ V, u ∣ v := by
    intro u hu v hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hu
    exact hcross c hc v hv
  let u₀ := U.min' hUne
  let v₀ := V.min' hVne
  have hu₀ : u₀ ∈ U := U.min'_mem hUne
  have hv₀ : v₀ ∈ V := V.min'_mem hVne
  have hu₀pos : 0 < u₀ := by
    obtain ⟨c, hc, hcu⟩ := Finset.mem_image.mp hu₀
    have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
    have hc0 : c ≠ 0 := fun h ↦ h₀ (h ▸ hcA)
    have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
    rw [← hcu]
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) hqc) hq.pos
  have hv₀pos : 0 < v₀ := by
    exact Nat.pos_of_ne_zero fun h ↦ h₀ (h ▸ (Finset.mem_filter.mp hv₀).1)
  let S₁ := U.image fun u ↦ v₀ / u
  let S₂ := (V.erase v₀).image fun v ↦ v / u₀
  have hS₁card : S₁.card = U.card := by
    dsimp only [S₁]
    rw [Finset.card_image_of_injOn]
    intro u hu w hw huw
    have huv : u ∣ v₀ := hcrossU u hu v₀ hv₀
    have hwv : w ∣ v₀ := hcrossU w hw v₀ hv₀
    have hu0 : 0 < u := by
      exact Nat.pos_of_dvd_of_pos huv hv₀pos
    have hquotpos : 0 < v₀ / u := Nat.div_pos (Nat.le_of_dvd hv₀pos huv) hu0
    change v₀ / u = v₀ / w at huw
    apply Nat.mul_left_cancel hquotpos
    calc
      (v₀ / u) * u = v₀ := Nat.div_mul_cancel huv
      _ = (v₀ / w) * w := (Nat.div_mul_cancel hwv).symm
      _ = (v₀ / u) * w := congrArg (fun z ↦ z * w) huw.symm
  have hS₂card : S₂.card = V.card - 1 := by
    dsimp only [S₂]
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_erase_of_mem hv₀]
    · intro v hv w hw hvw
      have hvV : v ∈ V := Finset.mem_of_mem_erase hv
      have hwV : w ∈ V := Finset.mem_of_mem_erase hw
      have huv : u₀ ∣ v := hcrossU u₀ hu₀ v hvV
      have huw : u₀ ∣ w := hcrossU u₀ hu₀ w hwV
      change v / u₀ = w / u₀ at hvw
      calc
        v = (v / u₀) * u₀ := (Nat.div_mul_cancel huv).symm
        _ = (w / u₀) * u₀ := congrArg (fun z ↦ z * u₀) hvw
        _ = w := Nat.div_mul_cancel huw
  have hSdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨v, hv, huvEq⟩ := Finset.mem_image.mp hx₂
    have hvV : v ∈ V := Finset.mem_of_mem_erase hv
    have hvne : v ≠ v₀ := (Finset.mem_erase.mp hv).1
    have hv₀lt : v₀ < v := (V.min'_le v hvV).lt_of_ne (Ne.symm hvne)
    have hu₀le : u₀ ≤ u := U.min'_le u hu
    have huv₀ : u ∣ v₀ := hcrossU u hu v₀ hv₀
    have hu₀v : u₀ ∣ v := hcrossU u₀ hu₀ v hvV
    have hvle : v ≤ v₀ := by
      calc
        v = (v / u₀) * u₀ := (Nat.div_mul_cancel hu₀v).symm
        _ = (v₀ / u) * u₀ := by rw [huvEq]
        _ ≤ (v₀ / u) * u := Nat.mul_le_mul_left (v₀ / u) hu₀le
        _ = v₀ := Nat.div_mul_cancel huv₀
    exact (not_le_of_gt hv₀lt) hvle
  let R := S₁ ∪ S₂
  have hRcard : R.card = A.card - 1 := by
    dsimp only [R]
    rw [Finset.card_union_of_disjoint hSdisj, hS₁card, hS₂card, hUcard]
    have hVpos : 0 < V.card := Finset.card_pos.mpr hVne
    omega
  let T := (Finset.Ico 1 A.card).erase q
  have hratio_mem_T : ∀ u ∈ U, ∀ v ∈ V, v / u ∈ T := by
    intro u hu v hv
    have huv : u ∣ v := hcrossU u hu v hv
    have hvA : v ∈ A := (Finset.mem_filter.mp hv).1
    have hv0 : v ≠ 0 := fun h ↦ h₀ (h ▸ hvA)
    have hu0 : 0 < u := Nat.pos_of_dvd_of_pos huv (Nat.pos_of_ne_zero hv0)
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · intro heq
      have hqratio : q ∣ v / u := heq ▸ dvd_refl q
      have hqv : q ∣ v := by
        rw [← Nat.div_mul_cancel huv]
        exact dvd_mul_of_dvd_left hqratio u
      exact (Finset.mem_filter.mp hv).2 hqv
    · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) huv) hu0
    · obtain ⟨c, hc, hcu⟩ := Finset.mem_image.mp hu
      have hcA : c ∈ A := (Finset.mem_filter.mp hc).1
      have hc0 : c ≠ 0 := fun h ↦ h₀ (h ▸ hcA)
      have hqc : q ∣ c := (Finset.mem_filter.mp hc).2
      have hg : c.gcd v = u := by
        have hgprod : q * c.gcd v = c := by
          have hgpos : 0 < c.gcd v := Nat.gcd_pos_of_pos_left v (Nat.pos_of_ne_zero hc0)
          have hqv : ¬q ∣ v := (Finset.mem_filter.mp hv).2
          have hqg : ¬q ∣ c.gcd v := fun h ↦ hqv (h.trans (Nat.gcd_dvd_right c v))
          have hqquot : q ∣ c / c.gcd v := by
            have hp : q ∣ (c / c.gcd v) * c.gcd v := by
              rw [Nat.div_mul_cancel (Nat.gcd_dvd_left c v)]
              exact hqc
            exact (hq.dvd_mul.mp hp).resolve_right hqg
          have hquotpos : 0 < c / c.gcd v :=
            Nat.div_pos (Nat.gcd_le_left v (Nat.pos_of_ne_zero hc0)) hgpos
          have hquotlt := div_gcd_lt_card_of_not_grahamBound A hbad hcA hvA hc0
          obtain ⟨k, hk⟩ := hqquot
          have hkpos : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ hquotpos)
          have hkone : k = 1 := by
            by_contra hk1
            have hk2 : 2 ≤ k := by omega
            have htwo : 2 * q ≤ c / c.gcd v := by
              calc
                2 * q = q * 2 := Nat.mul_comm 2 q
                _ ≤ q * k := Nat.mul_le_mul_left q hk2
                _ = c / c.gcd v := hk.symm
            omega
          have hquoteq : c / c.gcd v = q := by simpa [hkone] using hk
          calc
            q * c.gcd v = (c / c.gcd v) * c.gcd v := by rw [hquoteq]
            _ = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
        have hcprod : q * (c / q) = c := by
          simpa [mul_comm] using Nat.mul_div_cancel' hqc
        have hgg : c.gcd v = c / q :=
          Nat.mul_left_cancel hq.pos (hgprod.trans hcprod.symm)
        simpa [hcu] using hgg
      have hlt := div_gcd_lt_card_of_not_grahamBound A hbad hvA hcA hv0
      rw [Nat.gcd_comm v c, hg] at hlt
      exact hlt
  have hRsub : R ⊆ T := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact hratio_mem_T u hu v₀ hv₀
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact hratio_mem_T u₀ hu₀ v (Finset.mem_of_mem_erase hv)
  have hqT : q ∈ Finset.Ico 1 A.card := Finset.mem_Ico.mpr ⟨hq.one_le, hqn⟩
  have hTcard : T.card = A.card - 2 := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem hqT, Nat.card_Ico]
    omega
  have hRupper : R.card ≤ A.card - 2 :=
    (Finset.card_le_card hRsub).trans_eq hTcard
  omega

/-! ## The two-representation factorization -/

/-- If the two pairs `a * c, b * d` have coprime first coordinates and
coprime second coordinates, their cross gcd is the product of the two
cross gcds.  This is the prime-exponent identity used in
Balasubramanian--Soundararajan, Lemma 2.3. -/
private lemma gcd_mul_cross_of_coprime {a b c d : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (hab : a.Coprime b) (hcd : c.Coprime d) :
    (a * c).gcd (b * d) = a.gcd d * b.gcd c := by
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_pos_of_pos_left _
      (Nat.mul_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hc))).ne'
    (Nat.mul_ne_zero (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hb))
  intro q
  have habf : min (a.factorization q) (b.factorization q) = 0 := by
    have h := congrArg (fun f ↦ f q) (Nat.factorization_gcd ha hb)
    rw [hab.gcd_eq_one, Nat.factorization_one] at h
    change 0 = min (a.factorization q) (b.factorization q) at h
    exact h.symm
  have hcdf : min (c.factorization q) (d.factorization q) = 0 := by
    have h := congrArg (fun f ↦ f q) (Nat.factorization_gcd hc hd)
    rw [hcd.gcd_eq_one, Nat.factorization_one] at h
    change 0 = min (c.factorization q) (d.factorization q) at h
    exact h.symm
  rw [Nat.factorization_gcd (Nat.mul_ne_zero ha hc) (Nat.mul_ne_zero hb hd),
    Nat.factorization_mul ha hc, Nat.factorization_mul hb hd,
    Nat.factorization_mul (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hb),
    Nat.factorization_gcd ha hd, Nat.factorization_gcd hb hc]
  change min (a.factorization q + c.factorization q)
      (b.factorization q + d.factorization q) =
    min (a.factorization q) (d.factorization q) +
      min (b.factorization q) (c.factorization q)
  omega

/-- Multiplying both entries by the same positive scale does not change a
directed gcd quotient. -/
private lemma div_gcd_mul_right (x y c : ℕ) (hc : 0 < c) :
    (x * c) / (x * c).gcd (y * c) = x / x.gcd y := by
  rw [Nat.gcd_mul_right, Nat.mul_div_mul_right _ _ hc]

/-- The two positive summands of a prime are coprime. -/
private lemma coprime_prime_sub {p α : ℕ} (hp : p.Prime) (hα : 0 < α)
    (hαp : α < p) : α.Coprime (p - α) := by
  rw [Nat.coprime_sub_self_right hαp.le]
  exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hα hαp)).symm

/-- Pure arithmetic form of the factorization-and-closeness part of
Balasubramanian--Soundararajan, Lemma 2.3.  Put
`Xᵢ = gcd dᵢ α` and `Yᵢ = gcd dᵢ β`.  When `α` and `β` are coprime,
`d₁` and `d₂` are coprime, the four directed quotients are below `N`,
and `N² < 2α²`, the residual factors in `dᵢ = XᵢYᵢZᵢ` must both be one.
The four cross-multiplied closeness inequalities are returned as well. -/
private lemma factor_closeness {N α β d₁ d₂ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hαβ : α.Coprime β) (hd : d₁.Coprime d₂)
    (hsq : N * N < 2 * (α * α))
    (hα₁₂ : (α * d₁) / (α * d₁).gcd (β * d₂) < N)
    (hα₂₁ : (α * d₂) / (α * d₂).gcd (β * d₁) < N)
    (hβ₁₂ : (β * d₁) / (β * d₁).gcd (α * d₂) < N)
    (hβ₂₁ : (β * d₂) / (β * d₂).gcd (α * d₁) < N) :
    d₁ = d₁.gcd α * d₁.gcd β ∧
    d₂ = d₂.gcd α * d₂.gcd β ∧
    α * d₁.gcd α < N * d₂.gcd α ∧
    α * d₂.gcd α < N * d₁.gcd α ∧
    β * d₁.gcd β < N * d₂.gcd β ∧
    β * d₂.gcd β < N * d₁.gcd β := by
  let X₁ := d₁.gcd α
  let Y₁ := d₁.gcd β
  let X₂ := d₂.gcd α
  let Y₂ := d₂.gcd β
  have hX₁ : 0 < X₁ := Nat.gcd_pos_of_pos_left α hd₁
  have hY₁ : 0 < Y₁ := Nat.gcd_pos_of_pos_left β hd₁
  have hX₂ : 0 < X₂ := Nat.gcd_pos_of_pos_left α hd₂
  have hY₂ : 0 < Y₂ := Nat.gcd_pos_of_pos_left β hd₂
  have hXY₁ : X₁ * Y₁ ∣ d₁ := by
    apply (hαβ.gcd_both d₁ d₁).mul_dvd_of_dvd_of_dvd
    · exact Nat.gcd_dvd_left d₁ α
    · exact Nat.gcd_dvd_left d₁ β
  have hXY₂ : X₂ * Y₂ ∣ d₂ := by
    apply (hαβ.gcd_both d₂ d₂).mul_dvd_of_dvd_of_dvd
    · exact Nat.gcd_dvd_left d₂ α
    · exact Nat.gcd_dvd_left d₂ β
  let Z₁ := d₁ / (X₁ * Y₁)
  let Z₂ := d₂ / (X₂ * Y₂)
  have hZ₁ : 0 < Z₁ := Nat.div_pos (Nat.le_of_dvd hd₁ hXY₁)
    (Nat.mul_pos hX₁ hY₁)
  have hZ₂ : 0 < Z₂ := Nat.div_pos (Nat.le_of_dvd hd₂ hXY₂)
    (Nat.mul_pos hX₂ hY₂)
  have hd₁eq : d₁ = X₁ * Y₁ * Z₁ := by
    simpa [Z₁, mul_comm] using (Nat.div_mul_cancel hXY₁).symm
  have hd₂eq : d₂ = X₂ * Y₂ * Z₂ := by
    simpa [Z₂, mul_comm] using (Nat.div_mul_cancel hXY₂).symm
  have hgα₁₂ : (α * d₁).gcd (β * d₂) = X₂ * Y₁ := by
    rw [gcd_mul_cross_of_coprime hα.ne' hβ.ne' hd₁.ne' hd₂.ne' hαβ hd]
    simp only [X₂, Y₁, Nat.gcd_comm]
  have hgα₂₁ : (α * d₂).gcd (β * d₁) = X₁ * Y₂ := by
    rw [gcd_mul_cross_of_coprime hα.ne' hβ.ne' hd₂.ne' hd₁.ne' hαβ hd.symm]
    simp only [X₁, Y₂, Nat.gcd_comm]
  have hgβ₁₂ : (β * d₁).gcd (α * d₂) = Y₂ * X₁ := by
    rw [gcd_mul_cross_of_coprime hβ.ne' hα.ne' hd₁.ne' hd₂.ne' hαβ.symm hd]
    simp only [Y₂, X₁, Nat.gcd_comm]
  have hgβ₂₁ : (β * d₂).gcd (α * d₁) = Y₁ * X₂ := by
    rw [gcd_mul_cross_of_coprime hβ.ne' hα.ne' hd₂.ne' hd₁.ne' hαβ.symm hd.symm]
    simp only [Y₁, X₂, Nat.gcd_comm]
  have hiα₁₂ : α * X₁ * Z₁ < N * X₂ := by
    rw [hgα₁₂, Nat.div_lt_iff_lt_mul (Nat.mul_pos hX₂ hY₁)] at hα₁₂
    rw [hd₁eq] at hα₁₂
    apply (Nat.mul_lt_mul_right hY₁).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hα₁₂
  have hiα₂₁ : α * X₂ * Z₂ < N * X₁ := by
    rw [hgα₂₁, Nat.div_lt_iff_lt_mul (Nat.mul_pos hX₁ hY₂)] at hα₂₁
    rw [hd₂eq] at hα₂₁
    apply (Nat.mul_lt_mul_right hY₂).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hα₂₁
  have hprod : α * α * (Z₁ * Z₂) < N * N := by
    have hm := mul_lt_mul hiα₁₂ hiα₂₁.le
      (Nat.mul_pos (Nat.mul_pos hα hX₂) hZ₂) (Nat.zero_le (N * X₂))
    have hm' : (α * α * (Z₁ * Z₂)) * (X₁ * X₂) <
        (N * N) * (X₁ * X₂) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    exact (Nat.mul_lt_mul_right (Nat.mul_pos hX₁ hX₂)).mp hm'
  have hZone : Z₁ * Z₂ = 1 := by
    have hlt : α * α * (Z₁ * Z₂) < α * α * 2 := by
      exact hprod.trans (by simpa only [mul_comm] using hsq)
    have hlt' : Z₁ * Z₂ < 2 :=
      (Nat.mul_lt_mul_left (Nat.mul_pos hα hα)).mp hlt
    have hpos : 0 < Z₁ * Z₂ := Nat.mul_pos hZ₁ hZ₂
    omega
  have hz₁one : Z₁ = 1 := Nat.dvd_one.mp ⟨Z₂, hZone.symm⟩
  have hz₂one : Z₂ = 1 :=
    Nat.dvd_one.mp ⟨Z₁, by simpa [mul_comm] using hZone.symm⟩
  have hd₁fac : d₁ = X₁ * Y₁ := by simpa [hz₁one] using hd₁eq
  have hd₂fac : d₂ = X₂ * Y₂ := by simpa [hz₂one] using hd₂eq
  have hiβ₁₂ : β * Y₁ < N * Y₂ := by
    rw [hgβ₁₂, Nat.div_lt_iff_lt_mul (Nat.mul_pos hY₂ hX₁)] at hβ₁₂
    rw [hd₁fac] at hβ₁₂
    apply (Nat.mul_lt_mul_right hX₁).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hβ₁₂
  have hiβ₂₁ : β * Y₂ < N * Y₁ := by
    rw [hgβ₂₁, Nat.div_lt_iff_lt_mul (Nat.mul_pos hY₁ hX₂)] at hβ₂₁
    rw [hd₂fac] at hβ₂₁
    apply (Nat.mul_lt_mul_right hX₂).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hβ₂₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [X₁, Y₁] using hd₁fac
  · simpa only [X₂, Y₂] using hd₂fac
  · simpa only [X₁, X₂] using (by simpa [hz₁one] using hiα₁₂)
  · simpa only [X₁, X₂] using (by simpa [hz₂one] using hiα₂₁)
  · simpa only [Y₁, Y₂] using hiβ₁₂
  · simpa only [Y₁, Y₂] using hiβ₂₁

/-- Set-theoretic adapter for `factor_closeness`.  Four represented members
of a strict counterexample may have a common scale `c`; cancelling it from
their gcd quotients supplies exactly the four hypotheses of the pure
arithmetic lemma. -/
private lemma factor_closeness_of_counterexample (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β d₁ d₂ c : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hc : 0 < c)
    (hαβ : α.Coprime β) (hd : d₁.Coprime d₂)
    (hsq : A.card * A.card < 2 * (α * α))
    (hαd₁ : α * d₁ * c ∈ A) (hβd₁ : β * d₁ * c ∈ A)
    (hαd₂ : α * d₂ * c ∈ A) (hβd₂ : β * d₂ * c ∈ A) :
    d₁ = d₁.gcd α * d₁.gcd β ∧
    d₂ = d₂.gcd α * d₂.gcd β ∧
    α * d₁.gcd α < A.card * d₂.gcd α ∧
    α * d₂.gcd α < A.card * d₁.gcd α ∧
    β * d₁.gcd β < A.card * d₂.gcd β ∧
    β * d₂.gcd β < A.card * d₁.gcd β := by
  apply factor_closeness hα hβ hd₁ hd₂ hαβ hd hsq
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hαd₁ hβd₂
      (Nat.mul_ne_zero (Nat.mul_ne_zero hα.ne' hd₁.ne') hc.ne')
    simpa only [div_gcd_mul_right (α * d₁) (β * d₂) c hc] using h
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hαd₂ hβd₁
      (Nat.mul_ne_zero (Nat.mul_ne_zero hα.ne' hd₂.ne') hc.ne')
    simpa only [div_gcd_mul_right (α * d₂) (β * d₁) c hc] using h
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hβd₁ hαd₂
      (Nat.mul_ne_zero (Nat.mul_ne_zero hβ.ne' hd₁.ne') hc.ne')
    simpa only [div_gcd_mul_right (β * d₁) (α * d₂) c hc] using h
  · have h := div_gcd_lt_card_of_not_grahamBound A hbad hβd₂ hαd₁
      (Nat.mul_ne_zero (Nat.mul_ne_zero hβ.ne' hd₂.ne') hc.ne')
    simpa only [div_gcd_mul_right (β * d₂) (α * d₁) c hc] using h

/-- Distinct members of a strict counterexample with equal folded residues
produce an exact prime-sum relation after division by their gcd.  This is
the pointwise form of the collision counted in Lemma 2.1 of the paper. -/
private lemma gcd_quotients_sum_prime_of_folded_eq (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p a b : ℕ} (hp : p.Prime) (hlower : A.card < p)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hfold : foldedResidue p a = foldedResidue p b) :
    a / a.gcd b + b / a.gcd b = p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpfree {x : ℕ} (hx : x ∈ A) : ¬p ∣ x :=
    prime_not_dvd_of_card_le A h₀ hgcd hbad hp (Nat.le_of_lt hlower) hx
  have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ ha)
  have hb0 : b ≠ 0 := fun hz ↦ h₀ (hz ▸ hb)
  have hqa : a / a.gcd b < p :=
    (div_gcd_lt_card_of_not_grahamBound A hbad ha hb ha0).trans hlower
  have hqbRaw : b / b.gcd a < p :=
    (div_gcd_lt_card_of_not_grahamBound A hbad hb ha hb0).trans hlower
  have hqb : b / a.gcd b < p := by simpa [Nat.gcd_comm] using hqbRaw
  rcases foldedResidue_eq_iff hp.pos (hpfree ha) (hpfree hb) hfold with hsame | hsum
  · have hcast : (a : ZMod p) = (b : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff' a b p).mpr hsame
    exact (hab (residue_inj_of_div_gcd_lt hp ha0 hb0 (hpfree ha)
      hqa hqb hcast)).elim
  · let g := a.gcd b
    let x := a / g
    let y := b / g
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    have hga : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
    have hgb : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
    have hpg : ¬p ∣ g := fun h ↦ (hpfree ha) (h.trans (Nat.gcd_dvd_left a b))
    have hcg0 : (g : ZMod p) ≠ 0 := by
      intro hz
      exact hpg ((ZMod.natCast_eq_zero_iff g p).mp hz)
    have hpab : p ∣ a + b := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod, hsum, Nat.mod_self]
    have hcastsum : (a : ZMod p) + (b : ZMod p) = 0 := by
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      exact hpab
    have hfactor : (g : ZMod p) * ((x : ZMod p) + (y : ZMod p)) = 0 := by
      rw [mul_add]
      calc
        (g : ZMod p) * x + (g : ZMod p) * y =
            ((g * x : ℕ) : ZMod p) + ((g * y : ℕ) : ZMod p) := by
              rw [Nat.cast_mul, Nat.cast_mul]
        _ = (a : ZMod p) + (b : ZMod p) := by rw [hga, hgb]
        _ = 0 := hcastsum
    have hxycast : (x : ZMod p) + (y : ZMod p) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hcg0
    have hpxy : p ∣ x + y := by
      apply (ZMod.natCast_eq_zero_iff (x + y) p).mp
      simpa only [Nat.cast_add] using hxycast
    have hxpos : 0 < x :=
      Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
    have hypos : 0 < y :=
      Nat.div_pos (Nat.gcd_le_right a (Nat.pos_of_ne_zero hb0)) hgpos
    have hxlt : x < p := by simpa only [x, g] using hqa
    have hylt : y < p := by simpa only [y, g] using hqb
    have hxy : x + y = p :=
      Nat.eq_of_dvd_of_lt_two_mul (by omega) hpxy (by omega)
    simpa only [g, x, y] using hxy

/-- Let `A` be a normalized strict counterexample.  If a prime `p` lies
strictly between `|A|` and `2|A|`, folding the nonzero residue classes
modulo sign forces two distinct members whose reduced coprime factors
add up to `p`.  This is the elementary pigeonhole step used in the
Balasubramanian--Soundararajan argument. -/
private lemma exists_gcd_quotients_sum_prime (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hlower : A.card < p) (hupper : p < 2 * A.card) :
    ∃ a ∈ A, ∃ b ∈ A,
      a ≠ b ∧ a / a.gcd b + b / a.gcd b = p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hpfree {a : ℕ} (ha : a ∈ A) : ¬p ∣ a :=
    prime_not_dvd_of_card_le A h₀ hgcd hbad hp (Nat.le_of_lt hlower) ha
  let color : {a // a ∈ A} → Fin (p / 2) := fun a ↦
    ⟨foldedResidue p a.1 - 1, by
      have hpos := foldedResidue_pos hp.pos (hpfree a.2)
      have hle := foldedResidue_le_div_two (a := a.1) hp.pos
      omega⟩
  have hninj : ¬ Function.Injective color := by
    intro hinj
    have hle := Fintype.card_le_of_injective color hinj
    have hhalf : p / 2 < A.card := by omega
    have hle' : A.card ≤ p / 2 := by simpa using hle
    exact (not_le_of_gt hhalf) hle'
  rw [Function.Injective] at hninj
  push Not at hninj
  obtain ⟨a, b, habColor, hab⟩ := hninj
  have ha0 : a.1 ≠ 0 := fun hz ↦ h₀ (hz ▸ a.2)
  have hb0 : b.1 ≠ 0 := fun hz ↦ h₀ (hz ▸ b.2)
  have habVal : a.1 ≠ b.1 := fun h ↦ hab (Subtype.ext h)
  have hfold : foldedResidue p a.1 = foldedResidue p b.1 := by
    have hsub := congrArg Fin.val habColor
    have hapos := foldedResidue_pos hp.pos (hpfree a.2)
    have hbpos := foldedResidue_pos hp.pos (hpfree b.2)
    dsimp [color] at hsub
    omega
  have hres := foldedResidue_eq_iff hp.pos (hpfree a.2) (hpfree b.2) hfold
  have hqa : a.1 / a.1.gcd b.1 < p :=
    (div_gcd_lt_card_of_not_grahamBound A hbad a.2 b.2 ha0).trans hlower
  have hqbRaw : b.1 / b.1.gcd a.1 < p :=
    (div_gcd_lt_card_of_not_grahamBound A hbad b.2 a.2 hb0).trans hlower
  have hqb : b.1 / a.1.gcd b.1 < p := by simpa [Nat.gcd_comm] using hqbRaw
  rcases hres with hsame | hsum
  · have hcast : (a.1 : ZMod p) = (b.1 : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff' a.1 b.1 p).mpr hsame
    exact (habVal (residue_inj_of_div_gcd_lt hp ha0 hb0 (hpfree a.2)
      hqa hqb hcast)).elim
  · refine ⟨a.1, a.2, b.1, b.2, habVal, ?_⟩
    let g := a.1.gcd b.1
    let x := a.1 / g
    let y := b.1 / g
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b.1 (Nat.pos_of_ne_zero ha0)
    have hga : g * x = a.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left a.1 b.1)
    have hgb : g * y = b.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right a.1 b.1)
    have hpg : ¬p ∣ g := fun h ↦ (hpfree a.2) (h.trans (Nat.gcd_dvd_left a.1 b.1))
    have hcg0 : (g : ZMod p) ≠ 0 := by
      intro hz
      exact hpg ((ZMod.natCast_eq_zero_iff g p).mp hz)
    have hpab : p ∣ a.1 + b.1 := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod, hsum, Nat.mod_self]
    have hcastsum : (a.1 : ZMod p) + (b.1 : ZMod p) = 0 := by
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      exact hpab
    have hfactor : (g : ZMod p) * ((x : ZMod p) + (y : ZMod p)) = 0 := by
      rw [mul_add]
      calc
        (g : ZMod p) * x + (g : ZMod p) * y =
            ((g * x : ℕ) : ZMod p) + ((g * y : ℕ) : ZMod p) := by
              rw [Nat.cast_mul, Nat.cast_mul]
        _ = (a.1 : ZMod p) + (b.1 : ZMod p) := by rw [hga, hgb]
        _ = 0 := hcastsum
    have hxycast : (x : ZMod p) + (y : ZMod p) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hcg0
    have hpxy : p ∣ x + y := by
      apply (ZMod.natCast_eq_zero_iff (x + y) p).mp
      simpa only [Nat.cast_add] using hxycast
    have hxpos : 0 < x := Nat.div_pos (Nat.gcd_le_left b.1 (Nat.pos_of_ne_zero ha0)) hgpos
    have hypos : 0 < y := Nat.div_pos (Nat.gcd_le_right a.1 (Nat.pos_of_ne_zero hb0)) hgpos
    have hxlt : x < p := by simpa only [x, g] using hqa
    have hylt : y < p := by simpa only [y, g] using hqb
    have hxy : x + y = p :=
      Nat.eq_of_dvd_of_lt_two_mul (by omega) hpxy (by omega)
    simpa only [g, x, y] using hxy

/-- Quantitative form of the folded-residue collision argument: the full
dependent set of represented pairs `(α,d)` has at least `|Jₚ|` members.
This is precisely the first inequality in Balasubramanian--Soundararajan,
Lemma 2.1, with `rₚ(α)` represented by a finite fiber cardinality. -/
private lemma card_J_le_representationPairs (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hlower : A.card < p) (hupper : p < 2 * A.card) :
    (Finset.Icc ((p + 1) / 2) A.card).card ≤ (representationPairs A p).card := by
  classical
  have hpfree {a : ℕ} (ha : a ∈ A) : ¬p ∣ a :=
    prime_not_dvd_of_card_le A h₀ hgcd hbad hp (Nat.le_of_lt hlower) ha
  let R := A.filter fun a ↦ foldedMin A p a = a
  let E := A.filter fun a ↦ foldedMin A p a ≠ a
  have hpartition : R.card + E.card = A.card := by
    simpa only [R, E] using
      (Finset.card_filter_add_card_filter_not
        (s := A) (p := fun a ↦ foldedMin A p a = a))
  let color : {a // a ∈ R} → Fin (p / 2) := fun a ↦
    ⟨foldedResidue p a.1 - 1, by
      have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
      have hpos := foldedResidue_pos hp.pos (hpfree haA)
      have hle := foldedResidue_le_div_two (a := a.1) hp.pos
      omega⟩
  have hcolor : Function.Injective color := by
    intro a b hab
    apply Subtype.ext
    have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
    have hbA : b.1 ∈ A := (Finset.mem_filter.mp b.2).1
    have hapos := foldedResidue_pos hp.pos (hpfree haA)
    have hbpos := foldedResidue_pos hp.pos (hpfree hbA)
    have hval := congrArg Fin.val hab
    have hfold : foldedResidue p a.1 = foldedResidue p b.1 := by
      dsimp only [color] at hval
      omega
    have hmins := foldedMin_eq_of_color haA hbA hfold
    have harep : foldedMin A p a.1 = a.1 := (Finset.mem_filter.mp a.2).2
    have hbrep : foldedMin A p b.1 = b.1 := (Finset.mem_filter.mp b.2).2
    exact harep.symm.trans (hmins.trans hbrep)
  have hRcard : R.card ≤ p / 2 := by
    have hle := Fintype.card_le_of_injective color hcolor
    simpa using hle
  have hpne : p ≠ 2 := by
    intro hp2
    rw [hp2] at hlower hupper
    omega
  have hpmod : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hpne)
  have hJcard : (Finset.Icc ((p + 1) / 2) A.card).card = A.card - p / 2 := by
    rw [Nat.card_Icc]
    omega
  have hJleE : (Finset.Icc ((p + 1) / 2) A.card).card ≤ E.card := by
    rw [hJcard]
    omega
  let collisionMap : ℕ → ((α : ℕ) × ℕ) := fun a ↦
    ⟨a / (foldedMin A p a).gcd a, (foldedMin A p a).gcd a⟩
  have hmaps : Set.MapsTo collisionMap (↑E : Set ℕ) (↑(representationPairs A p)) := by
    intro a haE
    have haE' : a ∈ E := haE
    have haA : a ∈ A := (Finset.mem_filter.mp haE').1
    have hne : foldedMin A p a ≠ a := (Finset.mem_filter.mp haE').2
    let b := foldedMin A p a
    let g := b.gcd a
    have hbA : b ∈ A := foldedMin_mem haA
    have hfold : foldedResidue p b = foldedResidue p a := foldedMin_color haA
    have hble : b ≤ a := foldedMin_le haA haA rfl
    have hblt : b < a := hble.lt_of_ne hne
    have hb0 : b ≠ 0 := fun hz ↦ h₀ (hz ▸ hbA)
    have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ haA)
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left a (Nat.pos_of_ne_zero hb0)
    have hgb : (b / g) * g = b := by
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left b a)
    have hga : (a / g) * g = a := by
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right b a)
    have hsum : b / g + a / g = p := by
      simpa only [b, g] using gcd_quotients_sum_prime_of_folded_eq A h₀ hgcd hbad hp
        hlower hbA haA hne hfold
    have hquotorder : b / g < a / g := by
      apply (Nat.mul_lt_mul_right hgpos).mp
      simpa only [hgb, hga] using hblt
    have hαpos : 0 < a / g := by omega
    have hαlower : (p + 1) / 2 ≤ a / g := by omega
    have hαlt : a / g < A.card := by
      have h := div_gcd_lt_card_of_not_grahamBound A hbad haA hbA ha0
      simpa only [g, Nat.gcd_comm] using h
    have hβ : p - a / g = b / g := by omega
    change (⟨a / g, g⟩ : (α : ℕ) × ℕ) ∈ representationPairs A p
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hαlower, hαlt.le⟩, ?_⟩
    rw [mem_representedMultipliers hαpos]
    refine ⟨hgpos, ?_, ?_⟩
    · rw [hga]
      exact haA
    rw [hβ]
    rw [hgb]
    exact hbA
  have hinj : Set.InjOn collisionMap (↑E : Set ℕ) := by
    intro a ha b hb hab
    have hprod := congrArg (fun z : (α : ℕ) × ℕ ↦ z.1 * z.2) hab
    dsimp only [collisionMap] at hprod
    calc
      a = (a / (foldedMin A p a).gcd a) * (foldedMin A p a).gcd a :=
        (Nat.div_mul_cancel (Nat.gcd_dvd_right (foldedMin A p a) a)).symm
      _ = (b / (foldedMin A p b).gcd b) * (foldedMin A p b).gcd b := hprod
      _ = b := Nat.div_mul_cancel (Nat.gcd_dvd_right (foldedMin A p b) b)
  exact hJleE.trans (Finset.card_le_card_of_injOn collisionMap hmaps hinj)

/-- The second inequality of Lemma 2.1: the excess of fibers with at least
two representations dominates the number of empty fibers. -/
private lemma zero_card_le_representation_excess (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hlower : A.card < p) (hupper : p < 2 * A.card) :
    ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        representationCount A p α = 0).card ≤
      ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        2 ≤ representationCount A p α).sum fun α ↦ representationCount A p α - 1 := by
  apply zero_card_le_excess
  calc
    (Finset.Icc ((p + 1) / 2) A.card).card ≤
        (representationPairs A p).card :=
      card_J_le_representationPairs A h₀ hgcd hbad hp hlower hupper
    _ = (Finset.Icc ((p + 1) / 2) A.card).sum
        (representationCount A p) := by
      rw [representationPairs, Finset.card_sigma]
      rfl

/-- A witness after division by the common gcd lifts to a witness in the
original finset. -/
private lemma grahamBound_of_normalize (A : Finset ℕ)
    (h : GrahamBound (normalize A)) : GrahamBound A := by
  classical
  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := h
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha₀
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb₀
  refine ⟨a, ha, b, hb, ?_⟩
  have hga : A.gcd id ∣ a := Finset.gcd_dvd ha
  have hgb : A.gcd id ∣ b := Finset.gcd_dvd hb
  have hggcd : A.gcd id ∣ a.gcd b := Nat.dvd_gcd hga hgb
  have hcard : (normalize A).card = A.card := normalize_card A
  rw [hcard, Nat.gcd_div hga hgb] at hab
  have hmul := Nat.mul_le_mul_right (A.gcd id) hab
  simpa only [mul_assoc, Nat.div_mul_cancel hggcd, Nat.div_mul_cancel hga] using hmul

/-! ## Reciprocal symmetry -/

/-- Winterle's identity.  If `a` and `b` divide a common nonzero multiple
`M`, complementing both exponent vectors inside the exponent vector of `M`
interchanges the direction of the gcd quotient. -/
private lemma div_gcd_div_eq (M a b : ℕ) (hM : M ≠ 0) (ha : a ∣ M) (hb : b ∣ M) :
    (M / a) / (M / a).gcd (M / b) = b / a.gcd b := by
  have ha0 : a ≠ 0 := fun h ↦ hM (zero_dvd_iff.mp (h ▸ ha))
  have hb0 : b ≠ 0 := fun h ↦ hM (zero_dvd_iff.mp (h ▸ hb))
  have hMa0 : M / a ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) ha) (Nat.pos_of_ne_zero ha0)).ne'
  have hMb0 : M / b ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hb) (Nat.pos_of_ne_zero hb0)).ne'
  refine Nat.eq_of_factorization_eq
    (a := (M / a) / (M / a).gcd (M / b)) (b := b / a.gcd b)
    (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hMa0) (Nat.gcd_dvd_left (M / a) (M / b)))
      (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hMa0))).ne'
    (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) (Nat.gcd_dvd_right a b))
      (Nat.gcd_pos_of_pos_right a (Nat.pos_of_ne_zero hb0))).ne' ?_
  intro p
  rw [Nat.factorization_div (Nat.gcd_dvd_left _ _),
    Nat.factorization_gcd hMa0 hMb0, Nat.factorization_div ha,
    Nat.factorization_div hb, Nat.factorization_div (Nat.gcd_dvd_right _ _),
    Nat.factorization_gcd ha0 hb0]
  have hpa : a.factorization p ≤ M.factorization p :=
    (Nat.factorization_le_iff_dvd ha0 hM).mpr ha p
  have hpb : b.factorization p ≤ M.factorization p :=
    (Nat.factorization_le_iff_dvd hb0 hM).mpr hb p
  change (M.factorization p - a.factorization p) -
      min (M.factorization p - a.factorization p) (M.factorization p - b.factorization p) =
    b.factorization p - min (a.factorization p) (b.factorization p)
  omega

/-- Replace every member of `A` by its complementary divisor in the lcm of
the set. -/
private def reciprocal (A : Finset ℕ) : Finset ℕ :=
  A.image fun a ↦ A.lcm id / a

private lemma reciprocal_mem (A : Finset ℕ) {a : ℕ} (ha : a ∈ A) :
    A.lcm id / a ∈ reciprocal A := by
  classical
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

private lemma reciprocal_card (A : Finset ℕ) (h₀ : 0 ∉ A) :
    (reciprocal A).card = A.card := by
  classical
  unfold reciprocal
  rw [Finset.card_image_of_injOn]
  intro a ha b hb hab
  change A.lcm id / a = A.lcm id / b at hab
  have hM : A.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr fun x hx h ↦ h₀ (h ▸ hx)
  have hMbpos : 0 < A.lcm id / b :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Finset.dvd_lcm hb))
      (Nat.pos_of_ne_zero fun hz ↦ h₀ (hz ▸ hb))
  apply Nat.mul_left_cancel hMbpos
  calc
    (A.lcm id / b) * a = (A.lcm id / a) * a := by rw [hab]
    _ = A.lcm id := Nat.div_mul_cancel (Finset.dvd_lcm ha)
    _ = (A.lcm id / b) * b := (Nat.div_mul_cancel (Finset.dvd_lcm hb)).symm

private lemma reciprocal_nonzero (A : Finset ℕ) (h₀ : 0 ∉ A) :
    0 ∉ reciprocal A := by
  classical
  intro hz
  obtain ⟨a, ha, ha0⟩ := Finset.mem_image.mp hz
  have hM : A.lcm id ≠ 0 :=
    Finset.lcm_ne_zero_iff.mpr fun x hx h ↦ h₀ (h ▸ hx)
  have ha_ne : a ≠ 0 := fun h ↦ h₀ (h ▸ ha)
  have hpos : 0 < A.lcm id / a :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Finset.dvd_lcm ha))
      (Nat.pos_of_ne_zero ha_ne)
  omega

/-- For each prime, some complementary divisor `lcm(A) / a` is prime-free:
choose `a` whose prime exponent attains the finite supremum defining the
exponent in the lcm. -/
private lemma exists_prime_free_reciprocal_member (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hA : A.Nonempty) {q : ℕ} (hq : q.Prime) :
    ∃ a ∈ A, ¬q ∣ A.lcm id / a := by
  classical
  have hM : A.lcm id ≠ 0 :=
    Finset.lcm_ne_zero_iff.mpr fun x hx h ↦ h₀ (h ▸ hx)
  have hf : ∀ a ∈ A, id a ≠ 0 := by
    intro a ha hz
    exact h₀ (hz ▸ ha)
  obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup A hA
    (fun a ↦ a.factorization q)
  refine ⟨a, ha, ?_⟩
  have ha_ne : a ≠ 0 := fun h ↦ h₀ (h ▸ ha)
  have hadiv : a ∣ A.lcm id := Finset.dvd_lcm ha
  have hquot_ne : A.lcm id / a ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hadiv)
      (Nat.pos_of_ne_zero ha_ne)).ne'
  intro hqdiv
  have hpos := hq.factorization_pos_of_dvd hquot_ne hqdiv
  have hfactor : (A.lcm id / a).factorization q = 0 := by
    rw [Nat.factorization_div hadiv, Finsupp.tsub_apply,
      Finset.factorization_lcm hf q]
    change (A.sup fun a ↦ a.factorization q) - a.factorization q = 0
    rw [hsup]
    exact Nat.sub_self _
  omega

/-- The strict counterexample property is invariant under taking
complementary divisors in the set lcm. -/
private lemma not_grahamBound_reciprocal (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hbad : ¬ GrahamBound A) : ¬ GrahamBound (reciprocal A) := by
  classical
  intro hrec
  obtain ⟨a', ha', b', hb', hab⟩ := hrec
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
  have hM : A.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr fun x hx h ↦ h₀ (h ▸ hx)
  have hcard := reciprocal_card A h₀
  rw [hcard] at hab
  have hgpos' : 0 < (A.lcm id / a).gcd (A.lcm id / b) :=
    Nat.gcd_pos_of_pos_left _ (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Finset.dvd_lcm ha))
      (Nat.pos_of_ne_zero fun hz ↦ h₀ (hz ▸ ha)))
  have hquot : A.card ≤ (A.lcm id / a) / (A.lcm id / a).gcd (A.lcm id / b) :=
    (Nat.le_div_iff_mul_le hgpos').mpr hab
  rw [div_gcd_div_eq (A.lcm id) a b hM (Finset.dvd_lcm ha)
    (Finset.dvd_lcm hb)] at hquot
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b
    (Nat.pos_of_ne_zero fun hz ↦ h₀ (hz ▸ ha))
  apply hbad
  refine ⟨b, hb, a, ha, ?_⟩
  simpa [Nat.gcd_comm] using (Nat.le_div_iff_mul_le hgpos).mp hquot

/-- The lcm of all directed gcd quotients from `a` has a closed form. -/
private lemma lcm_div_gcd_eq (a : ℕ) (ha : a ≠ 0) (S : Finset ℕ) :
    S.lcm (fun b ↦ a / a.gcd b) = a / a.gcd (S.gcd id) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Nat.div_self (Nat.pos_of_ne_zero ha)]
  | @insert b S hb ih =>
      rw [Finset.lcm_insert, Finset.gcd_insert, ih]
      change Nat.lcm (a / a.gcd b) (a / a.gcd (S.gcd id)) =
        a / a.gcd (b.gcd (S.gcd id))
      rw [Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_left a b)
        (Nat.gcd_dvd_left a (S.gcd id))]
      have hden : (a.gcd b).gcd (a.gcd (S.gcd id)) =
          a.gcd (b.gcd (S.gcd id)) := by
        rw [Nat.gcd_assoc, Nat.gcd_left_comm b a (S.gcd id), ← Nat.gcd_assoc,
          Nat.gcd_self]
      rw [hden]

/-- Balasubramanian--Soundararajan, Lemma 2.4.  Divide a nonempty
family of represented multipliers by their common gcd.  If the two
coefficients are coprime and lie in the factorization range of Lemma 2.3,
then every normalized multiplier divides their product.

For a normalized multiplier `d` and every other normalized multiplier
`e`, Lemma 2.3 applied after removing `gcd d e` proves
`d / gcd d e ∣ α * β`.  The lcm of these quotients is exactly `d`,
because the normalized family has gcd one. -/
private lemma normalize_represented_dvd_product (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α.Coprime β)
    (hsq : A.card * A.card < 2 * (α * α))
    (hD : (representedMultipliers A α β).Nonempty) :
    ∀ d ∈ normalize (representedMultipliers A α β), d ∣ α * β := by
  classical
  let D := representedMultipliers A α β
  let B := normalize D
  let c := D.gcd id
  have hD₀ : 0 ∉ D := representedMultipliers_nonzero hα
  have hc : 0 < c := gcd_pos D hD₀ hD
  have hBgcd : B.gcd id = 1 := normalize_gcd D hD₀ hD
  have hrepresented : ∀ {d}, d ∈ B →
      0 < d ∧ α * d * c ∈ A ∧ β * d * c ∈ A := by
    intro d hd
    change d ∈ D.image (fun e ↦ e / D.gcd id) at hd
    obtain ⟨e, heD, rfl⟩ := Finset.mem_image.mp hd
    have he := (mem_representedMultipliers hα).mp heD
    have hce : D.gcd id ∣ e := Finset.gcd_dvd heD
    have heq : e / D.gcd id * D.gcd id = e := Nat.div_mul_cancel hce
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd he.1 hce) hc
    · change α * (e / D.gcd id) * D.gcd id ∈ A
      rw [mul_assoc, heq]
      exact he.2.1
    · change β * (e / D.gcd id) * D.gcd id ∈ A
      rw [mul_assoc, heq]
      exact he.2.2
  intro d hdB
  have hdpos := (hrepresented hdB).1
  have hlocal : ∀ e ∈ B, d / d.gcd e ∣ α * β := by
    intro e heB
    have hepos := (hrepresented heB).1
    let g := d.gcd e
    let d' := d / g
    let e' := e / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_left e hdpos
    have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_left e hdpos) hg
    have he' : 0 < e' := Nat.div_pos (Nat.gcd_le_right d hepos) hg
    have hcop : d'.Coprime e' := Nat.coprime_div_gcd_div_gcd hg
    have hdexpand : d' * (g * c) = d * c := by
      calc
        d' * (g * c) = (d' * g) * c := by simp only [mul_assoc]
        _ = d * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
    have heexpand : e' * (g * c) = e * c := by
      calc
        e' * (g * c) = (e' * g) * c := by simp only [mul_assoc]
        _ = e * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
    have hfac := factor_closeness_of_counterexample A hbad hα hβ hd' he'
      (Nat.mul_pos hg hc) hαβ hcop hsq
      (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact (hrepresented hdB).2.1)
      (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact (hrepresented hdB).2.2)
      (by rw [mul_assoc, heexpand, ← mul_assoc]; exact (hrepresented heB).2.1)
      (by rw [mul_assoc, heexpand, ← mul_assoc]; exact (hrepresented heB).2.2)
    change d' ∣ α * β
    rw [hfac.1]
    exact Nat.mul_dvd_mul (Nat.gcd_dvd_right d' α) (Nat.gcd_dvd_right d' β)
  have hlcm : B.lcm (fun e ↦ d / d.gcd e) ∣ α * β := Finset.lcm_dvd hlocal
  rw [lcm_div_gcd_eq d hdpos.ne' B, hBgcd, Nat.gcd_one_right, Nat.div_one] at hlcm
  exact hlcm

/-- If `d` and `e` have been split into their `α`-part and `β`-part,
then removing `gcd d e` removes exactly `gcd (gcd d α) (gcd e α)`
from the `α`-part.  This is the component bookkeeping used twice in
Lemma 2.5. -/
private lemma gcd_div_gcd_eq_component {α β d e : ℕ}
    (hαβ : α.Coprime β) (hd : 0 < d) (he : 0 < e)
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β) :
    (d / d.gcd e).gcd α = d.gcd α / (d.gcd α).gcd (e.gcd α) := by
  let u := d.gcd α
  let v := d.gcd β
  let x := e.gcd α
  let y := e.gcd β
  have hu : 0 < u := Nat.gcd_pos_of_pos_left α hd
  have hv : 0 < v := Nat.gcd_pos_of_pos_left β hd
  have hx : 0 < x := Nat.gcd_pos_of_pos_left α he
  have hy : 0 < y := Nat.gcd_pos_of_pos_left β he
  have huα : u ∣ α := Nat.gcd_dvd_right d α
  have hvβ : v ∣ β := Nat.gcd_dvd_right d β
  have hxα : x ∣ α := Nat.gcd_dvd_right e α
  have hyβ : y ∣ β := Nat.gcd_dvd_right e β
  have huy : u.Coprime y := Nat.Coprime.of_dvd huα hyβ hαβ
  have hvx : v.Coprime x := Nat.Coprime.of_dvd hvβ hxα hαβ.symm
  have hgde : d.gcd e = u.gcd x * v.gcd y := by
    rw [hdfac, hefac]
    change (u * v).gcd (x * y) = u.gcd x * v.gcd y
    rw [mul_comm x y,
      gcd_mul_cross_of_coprime hu.ne' hy.ne' hv.ne' hx.ne' huy hvx]
    simp only [Nat.gcd_comm y v]
  have hdiv : d / d.gcd e =
      (u / u.gcd x) * (v / v.gcd y) := by
    rw [hgde, hdfac]
    exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left u x)
      (Nat.gcd_dvd_left v y)).symm
  have huv : u / u.gcd x ∣ α :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left u x)).trans huα
  have hvv : v / v.gcd y ∣ β :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left v y)).trans hvβ
  have hcop : (v / v.gcd y).Coprime α :=
    Nat.Coprime.of_dvd hvv dvd_rfl hαβ.symm
  rw [hdiv, mul_comm]
  exact Nat.gcd_mul_of_coprime_of_dvd hcop huv

/-- The finite set whose cardinality is the paper's `k_D(n)`.  The
ratio constraint `X₂ / X₁ ≤ N / n` is stored without division as
`n * X₂ ≤ N * X₁`. -/
private def factorTriples (N D n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.Icc 1 n ×ˢ (Finset.Icc 1 D ×ˢ Finset.Icc 1 D)).filter fun t ↦
    n = t.1 * t.2.1 * t.2.2 ∧ t.2.1 < t.2.2 ∧
      n * t.2.2 ≤ N * t.2.1

private def kCount (N D n : ℕ) : ℕ := (factorTriples N D n).card

private lemma mem_factorTriples {N D n l X₁ X₂ : ℕ} :
    (l, (X₁, X₂)) ∈ factorTriples N D n ↔
      1 ≤ l ∧ l ≤ n ∧ 1 ≤ X₁ ∧ X₁ ≤ D ∧ 1 ≤ X₂ ∧ X₂ ≤ D ∧
        n = l * X₁ * X₂ ∧ X₁ < X₂ ∧ n * X₂ ≤ N * X₁ := by
  simp only [factorTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc]
  tauto

/-- Once the two reduced factors are fixed, the equation
`n = l * X₁ * X₂` determines the multiplier.  Hence the elementary
pointwise bound `k_D(n) ≤ D²`. -/
private lemma kCount_le_sq (N D n : ℕ) : kCount N D n ≤ D ^ 2 := by
  let project : (ℕ × (ℕ × ℕ)) → (ℕ × ℕ) := fun t ↦ t.2
  change (factorTriples N D n).card ≤ D ^ 2
  calc
    (factorTriples N D n).card ≤
        (Finset.Icc 1 D ×ˢ Finset.Icc 1 D).card := by
      apply Finset.card_le_card_of_injOn project
      · rintro ⟨l, X₁, X₂⟩ ht
        have h := mem_factorTriples.mp ht
        exact Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2.1⟩,
            Finset.mem_Icc.mpr ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩
      · rintro ⟨l, X₁, X₂⟩ hl ⟨k, Y₁, Y₂⟩ hk heq
        have hl' := mem_factorTriples.mp hl
        have hk' := mem_factorTriples.mp hk
        change (X₁, X₂) = (Y₁, Y₂) at heq
        injection heq with hX₁ hX₂
        subst Y₁
        subst Y₂
        have hprod : 0 < X₁ * X₂ := Nat.mul_pos (by omega) (by omega)
        have hlk : l = k := by
          apply Nat.mul_right_cancel hprod
          simpa only [mul_assoc] using
            hl'.2.2.2.2.2.2.1.symm.trans hk'.2.2.2.2.2.2.1
        subst k
        rfl
    _ = D ^ 2 := by
      simp [Finset.card_product, Nat.card_Icc, pow_two]

/-- The exact multiplier cutoff at the start of Lemma 5.1: every triple
`n = l X₁ X₂` counted by `k_D(n)` satisfies
`l * N ≤ (N - n)²`. -/
private lemma factorTriple_multiplier_mul_le_gap_sq
    {N D n l X₁ X₂ : ℕ} (ht : (l, (X₁, X₂)) ∈ factorTriples N D n) :
    l * N ≤ (N - n) ^ 2 := by
  have h := mem_factorTriples.mp ht
  have hl : 0 < l := by omega
  have hX₁ : 0 < X₁ := by omega
  have hX₂ : 0 < X₂ := by omega
  have hn : 0 < n := by rw [h.2.2.2.2.2.2.1]; positivity
  have hnN : n ≤ N := by
    have hposX₂ : 0 < n * X₂ := Nat.mul_pos hn hX₂
    have hNX₁pos : 0 < N * X₁ := hposX₂.trans_le h.2.2.2.2.2.2.2.2
    by_contra hnot
    have hNn : N < n := Nat.lt_of_not_ge hnot
    have hstrict : N * X₁ < n * X₂ := by
      calc
        N * X₁ < n * X₁ := (Nat.mul_lt_mul_right hX₁).mpr hNn
        _ ≤ n * X₂ := Nat.mul_le_mul_left n (by omega)
    omega
  let δ := N - n
  have hδadd : δ + n = N := Nat.sub_add_cancel hnN
  have hsucc : X₁ + 1 ≤ X₂ := by omega
  have hnδX₁ : n ≤ δ * X₁ := by
    have haux : n * (X₁ + 1) ≤ N * X₁ :=
      (Nat.mul_le_mul_left n hsucc).trans h.2.2.2.2.2.2.2.2
    rw [← hδadd] at haux
    simp only [mul_add, mul_one, add_mul] at haux
    omega
  have hNδX₂ : N ≤ δ * X₂ := by
    rw [← hδadd]
    have hδmono : δ * X₁ + δ ≤ δ * X₂ := by
      calc
        δ * X₁ + δ = δ * (X₁ + 1) := by ring
        _ ≤ δ * X₂ := Nat.mul_le_mul_left δ hsucc
    omega
  have hmul : n * N ≤ (δ * X₁) * (δ * X₂) :=
    Nat.mul_le_mul hnδX₁ hNδX₂
  have hcancel : l * N * (X₁ * X₂) ≤ δ ^ 2 * (X₁ * X₂) := by
    calc
      l * N * (X₁ * X₂) = n * N := by
        rw [h.2.2.2.2.2.2.1]
        ring
      _ ≤ (δ * X₁) * (δ * X₂) := hmul
      _ = δ ^ 2 * (X₁ * X₂) := by ring
  exact Nat.le_of_mul_le_mul_right
    (by simpa only [mul_assoc] using hcancel) (Nat.mul_pos hX₁ hX₂)

private lemma factorTriple_multiplier_le_gap_sq_div
    {N D n l X₁ X₂ : ℕ} (hN : 0 < N)
    (ht : (l, (X₁, X₂)) ∈ factorTriples N D n) :
    l ≤ (N - n) ^ 2 / N := by
  apply (Nat.le_div_iff_mul_le hN).mpr
  simpa only [mul_comm] using factorTriple_multiplier_mul_le_gap_sq ht

/-- The other elementary multiplier restriction from Lemma 5.1. -/
private lemma factorTriple_value_le_multiplier_mul_D_sq
    {N D n l X₁ X₂ : ℕ} (ht : (l, (X₁, X₂)) ∈ factorTriples N D n) :
    n ≤ l * D ^ 2 := by
  have h := mem_factorTriples.mp ht
  rw [h.2.2.2.2.2.2.1]
  calc
    l * X₁ * X₂ ≤ l * D * D := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left l h.2.2.2.1)
        h.2.2.2.2.2.1
    _ = l * D ^ 2 := by ring

/-- The finite triple set obtained after interchanging the `n`-sum in the
first moment of `k_D`. -/
private def firstMomentTriples (N D x : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.Icc 1 ((N - x) ^ 2 / N) ×ˢ
      (Finset.Icc 1 D ×ˢ Finset.Icc 1 D)).filter fun t ↦
    t.2.1 < t.2.2 ∧ x ≤ t.1 * t.2.1 * t.2.2 ∧
      t.1 * t.2.1 * t.2.2 ≤ N ∧
      (t.1 * t.2.1 * t.2.2) * t.2.2 ≤ N * t.2.1

private lemma mem_firstMomentTriples {N D x l X₁ X₂ : ℕ} :
    (l, (X₁, X₂)) ∈ firstMomentTriples N D x ↔
      1 ≤ l ∧ l ≤ (N - x) ^ 2 / N ∧
      1 ≤ X₁ ∧ X₁ ≤ D ∧ 1 ≤ X₂ ∧ X₂ ≤ D ∧
      X₁ < X₂ ∧ x ≤ l * X₁ * X₂ ∧ l * X₁ * X₂ ≤ N ∧
      (l * X₁ * X₂) * X₂ ≤ N * X₁ := by
  simp only [firstMomentTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc]
  tauto

private lemma firstMomentTriples_mono_lower
    {N D x₁ x₂ : ℕ} (hxx : x₁ ≤ x₂) :
    firstMomentTriples N D x₂ ⊆ firstMomentTriples N D x₁ := by
  rintro ⟨l, X₁, X₂⟩ ht
  have h := mem_firstMomentTriples.mp ht
  have hgap : N - x₂ ≤ N - x₁ := Nat.sub_le_sub_left hxx N
  have hgapSq : (N - x₂) ^ 2 ≤ (N - x₁) ^ 2 :=
    pow_le_pow_left' hgap 2
  apply mem_firstMomentTriples.mpr
  exact ⟨h.1, h.2.1.trans (Nat.div_le_div_right hgapSq),
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, hxx.trans h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

private lemma firstMomentTriples_mono_cap
    {N D₁ D₂ x : ℕ} (hDD : D₁ ≤ D₂) :
    firstMomentTriples N D₁ x ⊆ firstMomentTriples N D₂ x := by
  rintro ⟨l, X₁, X₂⟩ ht
  have h := mem_firstMomentTriples.mp ht
  apply mem_firstMomentTriples.mpr
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans hDD,
    h.2.2.2.2.1, h.2.2.2.2.2.1.trans hDD,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- Exact finite reindexing at the beginning of Lemma 5.1. -/
private lemma sum_kCount_Icc_le_firstMomentTriples_card
    {N D x : ℕ} (hN : 0 < N) :
    (Finset.Icc x N).sum (kCount N D) ≤
      (firstMomentTriples N D x).card := by
  let S := (Finset.Icc x N).sigma fun n ↦ factorTriples N D n
  let forgetN : ((n : ℕ) × (ℕ × (ℕ × ℕ))) → (ℕ × (ℕ × ℕ)) :=
    fun z ↦ z.2
  have hmaps : Set.MapsTo forgetN (↑S : Set ((n : ℕ) × (ℕ × (ℕ × ℕ))))
      (↑(firstMomentTriples N D x) : Set (ℕ × (ℕ × ℕ))) := by
    rintro ⟨n, ⟨l, X₁, X₂⟩⟩ hz
    have hz' := Finset.mem_sigma.mp hz
    have hnI : n ∈ Finset.Icc x N := by simpa using hz'.1
    have htmem : (l, (X₁, X₂)) ∈ factorTriples N D n := by
      simpa using hz'.2
    have ht := mem_factorTriples.mp htmem
    have hgap : N - n ≤ N - x := by
      have hxn := (Finset.mem_Icc.mp hnI).1
      omega
    have hgapSq : (N - n) ^ 2 ≤ (N - x) ^ 2 :=
      pow_le_pow_left' hgap 2
    have hlcut : l ≤ (N - x) ^ 2 / N :=
      (factorTriple_multiplier_le_gap_sq_div hN htmem).trans
        (Nat.div_le_div_right hgapSq)
    apply mem_firstMomentTriples.mpr
    refine ⟨ht.1, hlcut, ht.2.2.1, ht.2.2.2.1,
      ht.2.2.2.2.1, ht.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2.1, ?_, ?_, ?_⟩
    · simpa only [← ht.2.2.2.2.2.2.1] using (Finset.mem_Icc.mp hnI).1
    · simpa only [← ht.2.2.2.2.2.2.1] using (Finset.mem_Icc.mp hnI).2
    · simpa only [← ht.2.2.2.2.2.2.1] using ht.2.2.2.2.2.2.2.2
  have hinj : Set.InjOn forgetN
      (↑S : Set ((n : ℕ) × (ℕ × (ℕ × ℕ)))) := by
    rintro ⟨n, ⟨l, X₁, X₂⟩⟩ hn
      ⟨m, ⟨k, Y₁, Y₂⟩⟩ hm heq
    have hnmem : (l, (X₁, X₂)) ∈ factorTriples N D n := by
      simpa using (Finset.mem_sigma.mp hn).2
    have hmmem : (k, (Y₁, Y₂)) ∈ factorTriples N D m := by
      simpa using (Finset.mem_sigma.mp hm).2
    have hn' := mem_factorTriples.mp hnmem
    have hm' := mem_factorTriples.mp hmmem
    change (l, (X₁, X₂)) = (k, (Y₁, Y₂)) at heq
    injection heq with hlk hXY
    injection hXY with hX₁ hX₂
    subst k
    subst Y₁
    subst Y₂
    have hnm : n = m :=
      hn'.2.2.2.2.2.2.1.trans hm'.2.2.2.2.2.2.1.symm
    subst m
    rfl
  calc
    (Finset.Icc x N).sum (kCount N D) = S.card := by
      simp only [S, Finset.card_sigma, kCount]
      rfl
    _ ≤ (firstMomentTriples N D x).card :=
      Finset.card_le_card_of_injOn forgetN hmaps hinj

/-- A coarse but completely explicit box bound for the reindexed first
moment.  The sharp Lemma 5.1 estimate improves this by exploiting the
coprimality and closeness conditions, but this bound is useful for finite
subranges and as a consistency check on sharper formulas. -/
private lemma firstMomentTriples_card_le_box {N D x : ℕ} :
    (firstMomentTriples N D x).card ≤
      ((N - x) ^ 2 / N) * D ^ 2 := by
  unfold firstMomentTriples
  calc
    ((Finset.Icc 1 ((N - x) ^ 2 / N) ×ˢ
        (Finset.Icc 1 D ×ˢ Finset.Icc 1 D)).filter fun t ↦
          t.2.1 < t.2.2 ∧ x ≤ t.1 * t.2.1 * t.2.2 ∧
            t.1 * t.2.1 * t.2.2 ≤ N ∧
            (t.1 * t.2.1 * t.2.2) * t.2.2 ≤ N * t.2.1).card ≤
        (Finset.Icc 1 ((N - x) ^ 2 / N) ×ˢ
          (Finset.Icc 1 D ×ˢ Finset.Icc 1 D)).card :=
      Finset.card_filter_le _ _
    _ = ((N - x) ^ 2 / N) * D ^ 2 := by
      simp [Finset.card_product, Nat.card_Icc, pow_two]

/-- An exact nested-sum envelope for the first moment.  For fixed
`l,X₂`, the lower product constraint gives
`ceil(x/(lX₂)) ≤ X₁`, while the closeness constraint gives
`lX₂² ≤ N`. -/
private def firstMomentEnvelope (N D x : ℕ) :
    Finset ((l : ℕ) × ((X₂ : ℕ) × ℕ)) :=
  (Finset.Icc 1 ((N - x) ^ 2 / N)).sigma fun l ↦
    ((Finset.Icc 1 D).filter fun X₂ ↦ l * X₂ ^ 2 ≤ N).sigma fun X₂ ↦
      Finset.Icc (x ⌈/⌉ (l * X₂)) (X₂ - 1)

private lemma firstMomentTriples_card_le_envelope {N D x : ℕ} :
    (firstMomentTriples N D x).card ≤
      (firstMomentEnvelope N D x).card := by
  let toEnvelope : (ℕ × (ℕ × ℕ)) →
      ((l : ℕ) × ((X₂ : ℕ) × ℕ)) :=
    fun t ↦ ⟨t.1, t.2.2, t.2.1⟩
  apply Finset.card_le_card_of_injOn
    (s := firstMomentTriples N D x) (t := firstMomentEnvelope N D x)
    toEnvelope
  · rintro ⟨l, X₁, X₂⟩ ht
    dsimp only [toEnvelope]
    have h := mem_firstMomentTriples.mp ht
    have hlpos : 0 < l := by omega
    have hX₁pos : 0 < X₁ := by omega
    have hX₂pos : 0 < X₂ := by omega
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩, ?_⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩, ?_⟩, ?_⟩
    · apply Nat.le_of_mul_le_mul_right (c := X₁) ?_ hX₁pos
      calc
        (l * X₂ ^ 2) * X₁ = (l * X₁ * X₂) * X₂ := by ring
        _ ≤ N * X₁ := h.2.2.2.2.2.2.2.2.2
    · apply Finset.mem_Icc.mpr
      change (x ⌈/⌉ (l * X₂)) ≤ X₁ ∧ X₁ ≤ X₂ - 1
      constructor
      · apply (ceilDiv_le_iff_le_mul (Nat.mul_pos hlpos hX₂pos)).2
        calc
          x ≤ l * X₁ * X₂ := h.2.2.2.2.2.2.2.1
          _ = (l * X₂) * X₁ := by ring
      · omega
  · rintro ⟨l, X₁, X₂⟩ _ ⟨k, Y₁, Y₂⟩ _ heq
    dsimp only [toEnvelope] at heq
    cases heq
    rfl

/-- Cardinality of the exact envelope, exposed as the nested interval
sum to which the harmonic estimates of Lemma 5.1 apply. -/
private lemma firstMomentEnvelope_card (N D x : ℕ) :
    (firstMomentEnvelope N D x).card =
      ∑ l ∈ Finset.Icc 1 ((N - x) ^ 2 / N),
        ∑ X₂ ∈ (Finset.Icc 1 D).filter (fun X₂ ↦ l * X₂ ^ 2 ≤ N),
          (X₂ - 1 + 1 - (x ⌈/⌉ (l * X₂))) := by
  simp only [firstMomentEnvelope, Finset.card_sigma, Nat.card_Icc]

/-- A symmetric square envelope for the first moment at lower endpoint
`N-H`.  For fixed `l`, both factor coordinates lie between
`ceil((N-H)/(l*sqrt(N/l)))` and `sqrt(N/l)`. -/
private def squareMomentSide (N H l : ℕ) : ℕ :=
  Nat.sqrt (N / l) + 1 -
    ((N - H) ⌈/⌉ (l * Nat.sqrt (N / l)))

private def squareMomentEnvelope (N H : ℕ) :
    Finset ((l : ℕ) × (ℕ × ℕ)) :=
  (Finset.Icc 1 (H ^ 2 / N)).sigma fun l ↦
    let s := Nat.sqrt (N / l)
    let lo := (N - H) ⌈/⌉ (l * s)
    Finset.Icc lo s ×ˢ Finset.Icc lo s

private lemma firstMomentTriples_card_le_squareMomentEnvelope
    {N H : ℕ} (hN : 0 < N) (hHN : H ≤ N) :
    (firstMomentTriples N N (N - H)).card ≤
      (squareMomentEnvelope N H).card := by
  let toEnvelope : (ℕ × (ℕ × ℕ)) → ((l : ℕ) × (ℕ × ℕ)) :=
    fun t ↦ ⟨t.1, t.2⟩
  apply Finset.card_le_card_of_injOn
    (s := firstMomentTriples N N (N - H))
    (t := squareMomentEnvelope N H) toEnvelope
  · rintro ⟨l, X₁, X₂⟩ ht
    dsimp only [toEnvelope]
    have h := mem_firstMomentTriples.mp ht
    have hlpos : 0 < l := by omega
    have hX₁pos : 0 < X₁ := by omega
    have hX₂pos : 0 < X₂ := by omega
    have hlcut : l ≤ H ^ 2 / N := by
      simpa only [Nat.sub_sub_self hHN] using h.2.1
    have hX₂sq : l * X₂ ^ 2 ≤ N := by
      apply Nat.le_of_mul_le_mul_right (c := X₁) ?_ hX₁pos
      calc
        (l * X₂ ^ 2) * X₁ = (l * X₁ * X₂) * X₂ := by ring
        _ ≤ N * X₁ := h.2.2.2.2.2.2.2.2.2
    have hX₂sqDiv : X₂ ^ 2 ≤ N / l :=
      (Nat.le_div_iff_mul_le hlpos).2 (by simpa only [mul_comm] using hX₂sq)
    have hX₂sqrt : X₂ ≤ Nat.sqrt (N / l) := by
      exact (Nat.le_sqrt).2 (by simpa only [pow_two] using hX₂sqDiv)
    have hspos : 0 < Nat.sqrt (N / l) := hX₂pos.trans_le hX₂sqrt
    have hlowerMul : N - H ≤
        (l * Nat.sqrt (N / l)) * X₁ := by
      calc
        N - H ≤ l * X₁ * X₂ := h.2.2.2.2.2.2.2.1
        _ ≤ l * X₁ * Nat.sqrt (N / l) :=
          Nat.mul_le_mul_left (l * X₁) hX₂sqrt
        _ = (l * Nat.sqrt (N / l)) * X₁ := by ring
    have hloX₁ : (N - H) ⌈/⌉ (l * Nat.sqrt (N / l)) ≤ X₁ :=
      (ceilDiv_le_iff_le_mul (Nat.mul_pos hlpos hspos)).2 hlowerMul
    have hloX₂ : (N - H) ⌈/⌉ (l * Nat.sqrt (N / l)) ≤ X₂ :=
      hloX₁.trans (Nat.le_of_lt h.2.2.2.2.2.2.1)
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨h.1, hlcut⟩, ?_⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hloX₁,
        (Nat.le_of_lt h.2.2.2.2.2.2.1).trans hX₂sqrt⟩,
      Finset.mem_Icc.mpr ⟨hloX₂, hX₂sqrt⟩⟩
  · rintro ⟨l, X₁, X₂⟩ _ ⟨k, Y₁, Y₂⟩ _ heq
    dsimp only [toEnvelope] at heq
    cases heq
    rfl

private lemma squareMomentEnvelope_card (N H : ℕ) :
    (squareMomentEnvelope N H).card =
      ∑ l ∈ Finset.Icc 1 (H ^ 2 / N), (squareMomentSide N H l) ^ 2 := by
  simp only [squareMomentEnvelope, squareMomentSide, Finset.card_sigma,
    Finset.card_product, Nat.card_Icc, pow_two]

private lemma firstMomentTriples_card_le_squareMoment_sum
    {N H : ℕ} (hN : 0 < N) (hHN : H ≤ N) :
    (firstMomentTriples N N (N - H)).card ≤
      ∑ l ∈ Finset.Icc 1 (H ^ 2 / N), (squareMomentSide N H l) ^ 2 := by
  calc
    (firstMomentTriples N N (N - H)).card ≤
        (squareMomentEnvelope N H).card :=
      firstMomentTriples_card_le_squareMomentEnvelope hN hHN
    _ = _ := squareMomentEnvelope_card N H

/-- The side length of the square envelope has the expected reciprocal
square-root scale.  This exact natural-number form is the input for the
harmonic estimate below. -/
private lemma squareMomentSide_le_div_add_one
    {N H l : ℕ} (hHN : H ≤ N) (hl : 0 < l) :
    squareMomentSide N H l ≤
      H / (l * Nat.sqrt (N / l)) + 1 := by
  let s := Nat.sqrt (N / l)
  let m := l * s
  let lo := (N - H) ⌈/⌉ m
  by_cases hs : s = 0
  · simp [squareMomentSide, s, m, hs]
  have hspos : 0 < s := Nat.pos_of_ne_zero hs
  have hmpos : 0 < m := Nat.mul_pos hl hspos
  have hms : m * s ≤ N := by
    have hsquare : s * s ≤ N / l := by
      simpa only [s] using Nat.sqrt_le (N / l)
    have := (Nat.le_div_iff_mul_le hl).1 hsquare
    simpa only [m, mul_assoc, mul_comm, mul_left_comm] using this
  by_cases hlo : lo ≤ s + 1
  · have hlower : N - H ≤ m * lo := by
      exact (ceilDiv_le_iff_le_mul hmpos).1 le_rfl
    have hsideLo : squareMomentSide N H l + lo = s + 1 := by
      simpa only [squareMomentSide, s, m, lo] using Nat.sub_add_cancel hlo
    have hsum :
        m * squareMomentSide N H l + m * lo = m * (s + 1) := by
      rw [← Nat.mul_add, hsideLo]
    have hsideMul : m * squareMomentSide N H l ≤ H + m := by
      have hNH : N - H + H = N := Nat.sub_add_cancel hHN
      have hmss : m * (s + 1) = m * s + m := by ring
      omega
    have hdiv : squareMomentSide N H l ≤ (H + m) / m :=
      (Nat.le_div_iff_mul_le hmpos).2 (by
        simpa only [mul_comm] using hsideMul)
    simpa only [m, Nat.add_div_right _ hmpos] using hdiv
  · have hslo : s + 1 ≤ lo := by omega
    simp only [squareMomentSide, s, m, lo]
    rw [Nat.sub_eq_zero_of_le hslo]
    exact Nat.zero_le _

/-- On the multiplier range of the square envelope, the integer square
root loses at most the harmless factor `4` after squaring. -/
private lemma squareMoment_denominator_sq_lower
    {N H l : ℕ} (hN : 0 < N) (hHN : H ≤ N) (hl : 1 ≤ l)
    (hlcut : l ≤ H ^ 2 / N) :
    N * l ≤ 4 * (l * Nat.sqrt (N / l)) ^ 2 := by
  have hHsq : H ^ 2 ≤ N * H := by
    have := Nat.mul_le_mul_left H hHN
    nlinarith
  have hLleH : H ^ 2 / N ≤ H := Nat.div_le_of_le_mul hHsq
  have hlN : l ≤ N := hlcut.trans (hLleH.trans hHN)
  have hlpos : 0 < l := by omega
  have hqpos : 0 < N / l := Nat.div_pos hlN hlpos
  let s := Nat.sqrt (N / l)
  have hspos : 0 < s := by
    exact Nat.sqrt_pos.mpr hqpos
  have hroot : N / l < (s + 1) * (s + 1) := by
    simpa only [s] using Nat.lt_succ_sqrt (N / l)
  have hqfour : N / l < 4 * s ^ 2 := by
    nlinarith
  have hNfour : N < (4 * s ^ 2) * l :=
    (Nat.div_lt_iff_lt_mul hlpos).1 hqfour
  have hmul := (Nat.mul_lt_mul_right hlpos).2 hNfour
  have hmul' : N * l < 4 * (l * s) ^ 2 := by
    calc
      N * l < (4 * s ^ 2) * l * l := hmul
      _ = 4 * (l * s) ^ 2 := by ring
  simpa only [s] using hmul'.le

/-- Pointwise real form of the square-envelope estimate.  Its main term
is `H²/(N*l)`, so summing over `l` costs only a harmonic factor. -/
private lemma squareMomentSide_sq_real_le
    {N H l : ℕ} (hN : 0 < N) (hHN : H ≤ N) (hl : 1 ≤ l)
    (hlcut : l ≤ H ^ 2 / N) :
    ((squareMomentSide N H l : ℕ) : ℝ) ^ 2 ≤
      8 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) + 2 := by
  let s := Nat.sqrt (N / l)
  let m := l * s
  have hlpos : 0 < l := by omega
  have hdenNat := squareMoment_denominator_sq_lower hN hHN hl hlcut
  have hLleH : H ^ 2 / N ≤ H := by
    apply Nat.div_le_of_le_mul
    have := Nat.mul_le_mul_left H hHN
    nlinarith
  have hlN : l ≤ N := hlcut.trans (hLleH.trans hHN)
  have hqpos : 0 < N / l := Nat.div_pos hlN hlpos
  have hspos : 0 < s := by exact Nat.sqrt_pos.mpr hqpos
  have hmpos : 0 < m := Nat.mul_pos hlpos hspos
  have hsideNat := squareMomentSide_le_div_add_one hHN hlpos
  have hside : ((squareMomentSide N H l : ℕ) : ℝ) ≤
      (H : ℝ) / (m : ℝ) + 1 := by
    calc
      ((squareMomentSide N H l : ℕ) : ℝ) ≤
          ((H / m : ℕ) : ℝ) + 1 := by exact_mod_cast hsideNat
      _ ≤ (H : ℝ) / (m : ℝ) + 1 := by
        gcongr
        exact Nat.cast_div_le
  have hNmpos : 0 < (N : ℝ) * (l : ℝ) := by positivity
  have hmrealpos : 0 < (m : ℝ) ^ 2 := by positivity
  have hinv : (1 : ℝ) / (m : ℝ) ^ 2 ≤
      4 / ((N : ℝ) * (l : ℝ)) := by
    rw [div_le_div_iff₀ hmrealpos hNmpos]
    norm_num
    exact_mod_cast hdenNat
  have hfrac : (H : ℝ) ^ 2 / (m : ℝ) ^ 2 ≤
      4 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) := by
    calc
      (H : ℝ) ^ 2 / (m : ℝ) ^ 2 =
          (H : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) := by ring
      _ ≤ (H : ℝ) ^ 2 *
          (4 / ((N : ℝ) * (l : ℝ))) := by gcongr
      _ = 4 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) := by ring
  have hnonneg : 0 ≤ ((squareMomentSide N H l : ℕ) : ℝ) := by positivity
  have hrhsnonneg : 0 ≤ (H : ℝ) / (m : ℝ) + 1 := by positivity
  calc
    ((squareMomentSide N H l : ℕ) : ℝ) ^ 2 ≤
        ((H : ℝ) / (m : ℝ) + 1) ^ 2 :=
      (sq_le_sq₀ hnonneg hrhsnonneg).2 hside
    _ ≤ 2 * ((H : ℝ) ^ 2 / (m : ℝ) ^ 2) + 2 := by
      have hsquare : 0 ≤ ((H : ℝ) - (m : ℝ)) ^ 2 := sq_nonneg _
      field_simp
      nlinarith
    _ ≤ 8 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) + 2 := by
      calc
        2 * ((H : ℝ) ^ 2 / (m : ℝ) ^ 2) + 2 ≤
            2 * (4 * (H : ℝ) ^ 2 /
              ((N : ℝ) * (l : ℝ))) + 2 := by gcongr
        _ = 8 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) + 2 := by ring

/-- Summed square-envelope estimate.  This is a fully explicit version of
the `O((H²/N) log(H²/N))` first-moment bound needed by the sieve-free
endgame. -/
private lemma squareMoment_sum_real_le
    {N H : ℕ} (hN : 0 < N) (hHN : H ≤ N) :
    ((∑ l ∈ Finset.Icc 1 (H ^ 2 / N),
        (squareMomentSide N H l) ^ 2 : ℕ) : ℝ) ≤
      (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
          (1 + Real.log (H ^ 2 / N : ℕ)) +
        2 * (H ^ 2 / N : ℕ) := by
  let L := H ^ 2 / N
  have hharm :
      (∑ l ∈ Finset.Icc 1 L, ((l : ℝ) : ℝ)⁻¹) ≤
        1 + Real.log (L : ℝ) := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast] using harmonic_le_one_add_log L
  rw [Nat.cast_sum]
  calc
    ∑ l ∈ Finset.Icc 1 (H ^ 2 / N),
        (((squareMomentSide N H l) ^ 2 : ℕ) : ℝ) ≤
        ∑ l ∈ Finset.Icc 1 (H ^ 2 / N),
          (8 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) + 2) := by
      apply Finset.sum_le_sum
      intro l hl
      have hlI := Finset.mem_Icc.mp hl
      simpa only [Nat.cast_pow] using
        squareMomentSide_sq_real_le hN hHN hlI.1 hlI.2
    _ = (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
          (∑ l ∈ Finset.Icc 1 L, ((l : ℝ) : ℝ)⁻¹) + 2 * L := by
      dsimp only [L]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        have hlpos : (0 : ℝ) < l := by
          exact_mod_cast (Finset.mem_Icc.mp hl).1
        field_simp
      · simp [Nat.card_Icc, mul_comm]
    _ ≤ (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
          (1 + Real.log (L : ℝ)) + 2 * L := by
      gcongr
    _ = (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
          (1 + Real.log (H ^ 2 / N : ℕ)) +
        2 * (H ^ 2 / N : ℕ) := by rfl

/-- Closed real first-moment bound, obtained by combining the exact
reindexing with the harmonic square envelope. -/
private lemma firstMomentTriples_card_real_le
    {N H : ℕ} (hN : 0 < N) (hHN : H ≤ N) :
    ((firstMomentTriples N N (N - H)).card : ℝ) ≤
      (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
          (1 + Real.log (H ^ 2 / N : ℕ)) +
        2 * (H ^ 2 / N : ℕ) := by
  have hnat := firstMomentTriples_card_le_squareMoment_sum hN hHN
  have hcast : ((firstMomentTriples N N (N - H)).card : ℝ) ≤
      ((∑ l ∈ Finset.Icc 1 (H ^ 2 / N),
        (squareMomentSide N H l) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (squareMoment_sum_real_le hN hHN)

private noncomputable def firstMomentRealBound (N H : ℕ) : ℝ :=
  (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
      (1 + Real.log (H ^ 2 / N : ℕ)) +
    2 * (H ^ 2 / N : ℕ)

private lemma firstMomentRealBound_nonneg (N H : ℕ) :
    0 ≤ firstMomentRealBound N H := by
  unfold firstMomentRealBound
  positivity [Real.log_natCast_nonneg]

private lemma firstMomentTriples_card_real_le_bound
    {N H : ℕ} (hN : 0 < N) (hHN : H ≤ N) :
    ((firstMomentTriples N N (N - H)).card : ℝ) ≤
      firstMomentRealBound N H := by
  simpa only [firstMomentRealBound] using
    firstMomentTriples_card_real_le hN hHN

/-- A simpler closed upper bound for the first-moment envelope. -/
private lemma firstMomentRealBound_le {N H : ℕ}
    (hN : 0 < N) (hH : H ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) :
    firstMomentRealBound N H ≤
      18 * (H : ℝ) ^ 2 * Real.log N / N := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  let q := H ^ 2 / N
  have hqN : q ≤ N := by
    dsimp only [q]
    apply Nat.div_le_of_le_mul
    simpa only [pow_two] using Nat.mul_self_le_mul_self hH
  have hqcast : (q : ℝ) ≤ (H : ℝ) ^ 2 / (N : ℝ) := by
    dsimp only [q]
    have hc := (Nat.cast_div_le :
      ((H ^ 2 / N : ℕ) : ℝ) ≤ ((H ^ 2 : ℕ) : ℝ) / (N : ℝ))
    simpa only [Nat.cast_pow] using hc
  have hlogq : Real.log (q : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases hq : q = 0
    · simp only [hq, Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hq))
        (by exact_mod_cast hqN)
  have hxnonneg : 0 ≤ (H : ℝ) ^ 2 / (N : ℝ) := by positivity
  have hfactor : 1 + Real.log (q : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    linarith
  unfold firstMomentRealBound
  change (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (1 + Real.log (q : ℝ)) +
      2 * (q : ℝ) ≤ _
  have hfirst :
      (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (1 + Real.log (q : ℝ)) ≤
        (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (2 * Real.log N) :=
    mul_le_mul_of_nonneg_left hfactor (by positivity)
  have hsecond : 2 * (q : ℝ) ≤
      2 * ((H : ℝ) ^ 2 / N) :=
    mul_le_mul_of_nonneg_left hqcast (by norm_num)
  have hthird : 2 * ((H : ℝ) ^ 2 / N) ≤
      2 * ((H : ℝ) ^ 2 / N) * Real.log N := by
    calc
      2 * ((H : ℝ) ^ 2 / N) =
          2 * ((H : ℝ) ^ 2 / N) * 1 := by ring
      _ ≤ 2 * ((H : ℝ) ^ 2 / N) * Real.log N :=
        mul_le_mul_of_nonneg_left hlog
          (mul_nonneg (by norm_num) hxnonneg)
  calc
    (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (1 + Real.log (q : ℝ)) +
        2 * (q : ℝ) ≤
        (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (2 * Real.log N) +
          2 * ((H : ℝ) ^ 2 / N) := add_le_add hfirst hsecond
    _ ≤ (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (2 * Real.log N) +
          2 * ((H : ℝ) ^ 2 / N) * Real.log N := by
      exact add_le_add (le_refl _) hthird
    _ = 18 * (H : ℝ) ^ 2 * Real.log N / N := by ring

/-! ### Exact bridges from Chebyshev's theta function to prime intervals -/

/-- The exact cardinality of a closed interval of primes, expressed as a
difference of values of the prime-counting function. -/
private lemma primeInterval_card_eq {u v : ℕ} (huv : u ≤ v) :
    ((Finset.Icc u v).filter Nat.Prime).card =
      Nat.primeCounting v - Nat.primeCounting (u - 1) := by
  have heq : (Finset.Icc u v).filter Nat.Prime =
      Nat.primesLE v \ Nat.primesLE (u - 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpu, hpv⟩, hp⟩
      exact ⟨⟨hpv, hp⟩, fun h ↦ by
        have hp2 := hp.two_le
        omega⟩
    · rintro ⟨⟨hpv, hp⟩, hnot⟩
      refine ⟨⟨?_, hpv⟩, hp⟩
      by_contra h
      apply hnot
      have hp2 := hp.two_le
      exact ⟨by omega, hp⟩
  rw [heq, Finset.card_sdiff_of_subset
    (Nat.primesLE_mono ((Nat.sub_le u 1).trans huv))]
  simp only [Nat.primesLE_card_eq_primeCounting]

/-- A theta difference is bounded above by the number of primes in the
corresponding interval times the logarithm of its upper endpoint. -/
private lemma theta_sub_le_primeInterval_card_mul_log {u v : ℕ}
    (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) ≤
      (((Finset.Icc u v).filter Nat.Prime).card : ℝ) * Real.log v := by
  have hsub : Nat.primesLE (u - 1) ⊆ Nat.primesLE v :=
    Nat.primesLE_mono ((Nat.sub_le u 1).trans huv)
  have hsum :
      ∑ p ∈ Nat.primesLE v \ Nat.primesLE (u - 1), Real.log p =
        Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) := by
    have hadd := Finset.sum_sdiff (f := fun p : ℕ ↦ Real.log p) hsub
    rw [← Chebyshev.theta_eq_sum_primesLE_log,
      ← Chebyshev.theta_eq_sum_primesLE_log] at hadd
    linarith
  rw [← hsum]
  calc
    ∑ p ∈ Nat.primesLE v \ Nat.primesLE (u - 1), Real.log p ≤
        ∑ _p ∈ Nat.primesLE v \ Nat.primesLE (u - 1), Real.log v := by
      apply Finset.sum_le_sum
      intro p hp
      apply Real.log_le_log
      · exact_mod_cast (Nat.Prime.pos (Nat.prime_of_mem_primesLE
          (Finset.mem_sdiff.mp hp).1))
      · exact_mod_cast Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
    _ = ((Nat.primesLE v \ Nat.primesLE (u - 1)).card : ℝ) * Real.log v := by
      simp
    _ = (((Finset.Icc u v).filter Nat.Prime).card : ℝ) * Real.log v := by
      congr 2
      exact_mod_cast (by
        rw [Finset.card_sdiff_of_subset hsub,
          Nat.primesLE_card_eq_primeCounting,
          Nat.primesLE_card_eq_primeCounting]
        exact (primeInterval_card_eq huv).symm)

/-- A lower bound for a theta difference gives an exact natural-valued
lower bound for the number of primes in the interval. -/
private lemma le_primeInterval_card_of_mul_log_le {u v Q : ℕ}
    (huv : u ≤ v) (hv : 1 < v)
    (hQ : (Q : ℝ) * Real.log v ≤
      Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ)) :
    Q ≤ ((Finset.Icc u v).filter Nat.Prime).card := by
  have htheta := theta_sub_le_primeInterval_card_mul_log huv
  have hlog : 0 < Real.log (v : ℝ) := Real.log_pos (by exact_mod_cast hv)
  have hmul : (Q : ℝ) * Real.log v ≤
      (((Finset.Icc u v).filter Nat.Prime).card : ℝ) * Real.log v :=
    hQ.trans htheta
  have hcast : (Q : ℝ) ≤
      (((Finset.Icc u v).filter Nat.Prime).card : ℝ) :=
    le_of_mul_le_mul_right hmul hlog
  exact_mod_cast hcast

/-- The elementary error bookkeeping behind every short-interval estimate:
two bounds for `ψ - id`, together with the prime-power correction at the
upper endpoint, give a lower bound for the theta difference. -/
private lemma theta_interval_lower_of_psi_bounds {u v : ℕ} {Eu Ev S : ℝ}
    (hEu : |Chebyshev.psi ((u - 1 : ℕ) : ℝ) - ((u - 1 : ℕ) : ℝ)| ≤ Eu)
    (hEv : |Chebyshev.psi v - (v : ℝ)| ≤ Ev)
    (hS : Chebyshev.psi v - Chebyshev.theta v ≤ S) :
    (v : ℝ) - ((u - 1 : ℕ) : ℝ) - Ev - Eu - S ≤
      Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) := by
  have hEu' := (abs_le.mp hEu).2
  have hEv' := (abs_le.mp hEv).1
  have htu := Chebyshev.theta_le_psi ((u - 1 : ℕ) : ℝ)
  linarith

/-- A pointwise, nonnegative version of the error estimate furnished by the
fully proved local medium prime number theorem. -/
private theorem exists_mediumPsi_error :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤
        C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C, hC⟩ := hO.bound
  refine ⟨c, |C|, hc, abs_nonneg C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 0] with x hxO hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg] at hxO
  · exact hxO.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  · positivity

/-- Every fixed power of `log x` is dominated by the exponential decay in
`MediumPNT`.  The proof substitutes `t = (log x)^(1/10)` into the standard
polynomial-times-exponential limit. -/
private lemma tendsto_log_pow_mul_mediumDecay (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Tendsto (fun x : ℝ ↦ Real.log x ^ k *
      Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) atTop (nhds 0) := by
  have ht : Tendsto (fun x : ℝ ↦ Real.log x ^ ((1 : ℝ) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)).comp
      Real.tendsto_log_atTop
  have hdecay :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((10 * k : ℕ) : ℝ) c hc).comp ht
  apply hdecay.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  change (Real.log x ^ ((1 : ℝ) / 10)) ^ ((10 * k : ℕ) : ℝ) *
      Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) =
    Real.log x ^ k * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hlog]
  congr 1
  push_cast
  ring

/-- The medium PNT error is eventually smaller than `δ x / log(x)^k`, for
an arbitrary fixed logarithmic power and arbitrary positive `δ`. -/
private theorem eventually_mediumPsi_error_div_log_pow (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ δ * x / Real.log x ^ k := by
  obtain ⟨c, C, hc, hC, hpsi⟩ := exists_mediumPsi_error
  have hlim := (tendsto_log_pow_mul_mediumDecay c hc k).const_mul C
  have hlim' : Tendsto (fun x : ℝ ↦ C * (Real.log x ^ k *
      Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))) atTop (nhds 0) := by
    simpa using hlim
  have hsmall : ∀ᶠ x : ℝ in atTop,
      C * (Real.log x ^ k *
        Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) < δ :=
    (Filter.Eventually.and
      (NormedAddGroup.tendsto_nhds_zero.mp hlim' δ hδ)
      (eventually_ge_atTop 1)).mono fun x hx ↦ by
      rw [Real.norm_of_nonneg] at hx
      · exact hx.1
      · exact mul_nonneg hC (mul_nonneg (pow_nonneg (Real.log_nonneg hx.2) k)
          (Real.exp_pos _).le)
  filter_upwards [hpsi, hsmall, eventually_gt_atTop 1] with x hxpsi hxsmall hx
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx.le
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogpow : 0 < Real.log x ^ k := pow_pos hlog k
  apply hxpsi.trans
  apply (le_div_iff₀ hlogpow).2
  calc
    C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) *
        Real.log x ^ k =
        x * (C * (Real.log x ^ k *
          Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))) := by ring
    _ ≤ x * δ := mul_le_mul_of_nonneg_left hxsmall.le hx0
    _ = δ * x := by ring

/-- A fixed logarithmic power divided by `sqrt x` tends to zero. -/
private lemma tendsto_log_pow_div_sqrt (k : ℕ) :
    Tendsto (fun x : ℝ ↦ Real.log x ^ k / Real.sqrt x) atTop (nhds 0) := by
  have h := Real.tendsto_pow_log_div_pow_atTop
    ((1 : ℝ) / 2) (k : ℝ) (by norm_num)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.rpow_natCast]
  rw [← Real.sqrt_eq_rpow]

/-- Prime powers contribute less than `δ x / log(x)^k` to `ψ - θ`
eventually.  This uses Mathlib's explicit `2 sqrt(x) log(x)` bound. -/
private theorem eventually_psi_sub_theta_div_log_pow (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop,
      Chebyshev.psi x - Chebyshev.theta x ≤
        δ * x / Real.log x ^ k := by
  have hlim := (tendsto_log_pow_div_sqrt (k + 1)).const_mul 2
  have hlim' : Tendsto (fun x : ℝ ↦
      2 * (Real.log x ^ (k + 1) / Real.sqrt x)) atTop (nhds 0) := by
    simpa using hlim
  have hsmall : ∀ᶠ x : ℝ in atTop,
      2 * (Real.log x ^ (k + 1) / Real.sqrt x) < δ := by
    have hnorm := NormedAddGroup.tendsto_nhds_zero.mp hlim' δ hδ
    filter_upwards [hnorm, eventually_gt_atTop 1] with x hxnorm hx
    rw [Real.norm_of_nonneg] at hxnorm
    · exact hxnorm
    · exact mul_nonneg (by norm_num) (div_nonneg
        (pow_nonneg (Real.log_nonneg hx.le) (k + 1)) (Real.sqrt_nonneg x))
  filter_upwards [hsmall, eventually_gt_atTop 1] with x hxsmall hx
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx.le
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogpow : 0 < Real.log x ^ k := pow_pos hlog k
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 (by positivity)
  apply (Chebyshev.psi_sub_theta_le hx.le).trans
  apply (le_div_iff₀ hlogpow).2
  have hsmall' : 2 * Real.log x ^ (k + 1) < δ * Real.sqrt x := by
    rw [← mul_div_assoc] at hxsmall
    exact (div_lt_iff₀ hsqrt).mp hxsmall
  have hmul := mul_le_mul_of_nonneg_left hsmall'.le (Real.sqrt_nonneg x)
  calc
    2 * Real.sqrt x * Real.log x * Real.log x ^ k =
        Real.sqrt x * (2 * Real.log x ^ (k + 1)) := by
      rw [pow_succ]
      ring
    _ ≤ Real.sqrt x * (δ * Real.sqrt x) := hmul
    _ = δ * Real.sqrt x ^ 2 := by ring
    _ = δ * x := by rw [Real.sq_sqrt hx0]

/-- If `x` and `y` differ by at most a factor of two, then their
`x / log(x)^k` scales differ by at most `2^k`. -/
private lemma div_log_pow_le_two_pow_mul {x y : ℝ} (k : ℕ)
    (hy : 4 ≤ y) (hxy : x ≤ y) (hhalf : y ≤ 2 * x) :
    x / Real.log x ^ k ≤ (2 : ℝ) ^ k * y / Real.log y ^ k := by
  have hypos : 0 < y := by linarith
  have hxpos : 0 < x := by linarith
  have hyhalf : 2 ≤ y / 2 := by linarith
  have hhalfpos : 0 < y / 2 := by linarith
  have hloghalf_le : Real.log (y / 2) ≤ Real.log x := by
    apply Real.log_le_log hhalfpos
    linarith
  have hlog2_le : Real.log 2 ≤ Real.log (y / 2) := by
    apply Real.log_le_log (by norm_num)
    exact hyhalf
  have hlogsplit : Real.log y = Real.log 2 + Real.log (y / 2) := by
    calc
      Real.log y = Real.log (2 * (y / 2)) := by congr 1; field_simp
      _ = Real.log 2 + Real.log (y / 2) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hhalfpos.ne']
  have hlogcomp : Real.log y ≤ 2 * Real.log x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hpows : Real.log y ^ k ≤ (2 * Real.log x) ^ k :=
    pow_le_pow_left₀ hlogy.le hlogcomp k
  have hcross : x * Real.log y ^ k ≤
      ((2 : ℝ) ^ k * y) * Real.log x ^ k := by
    calc
      x * Real.log y ^ k ≤ y * Real.log y ^ k :=
        mul_le_mul_of_nonneg_right hxy (pow_nonneg hlogy.le k)
      _ ≤ y * (2 * Real.log x) ^ k :=
        mul_le_mul_of_nonneg_left hpows hypos.le
      _ = ((2 : ℝ) ^ k * y) * Real.log x ^ k := by rw [mul_pow]; ring
  exact (div_le_div_iff₀ (pow_pos hlogx k) (pow_pos hlogy k)).2 hcross

/-- Uniform shrinking-interval prime count.  Eventually, every natural
interval `[u,v]` contained in the upper half of `[0,v]` and of length at
least `v / log(v)^k` contains at least
`(v-(u-1))/(2 log v)` primes (as a real-valued cardinality bound). -/
private theorem eventually_primeInterval_card_real_lower (k : ℕ) :
    ∀ᶠ v : ℕ in atTop, ∀ u : ℕ, u ≤ v → v ≤ 2 * (u - 1) →
      (v : ℝ) / Real.log v ^ k ≤
        (v : ℝ) - ((u - 1 : ℕ) : ℝ) →
      ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) / (2 * Real.log v) ≤
        (((Finset.Icc u v).filter Nat.Prime).card : ℝ) := by
  let ε : ℝ := 1 / (4 * (2 + (2 : ℝ) ^ k))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hpsi := eventually_mediumPsi_error_div_log_pow k hε
  have hcorr := eventually_psi_sub_theta_div_log_pow k hε
  rw [eventually_atTop] at hpsi hcorr
  obtain ⟨Xp, hXp⟩ := hpsi
  obtain ⟨Xc, hXc⟩ := hcorr
  let R := max 4 (max Xp Xc)
  obtain ⟨V, hV⟩ := exists_nat_ge (2 * R)
  rw [eventually_atTop]
  refine ⟨V, ?_⟩
  intro v hv u huv hhalf hwidth
  have hR4 : 4 ≤ R := le_max_left _ _
  have hRXp : Xp ≤ R := (le_max_left Xp Xc).trans (le_max_right 4 _)
  have hRXc : Xc ≤ R := (le_max_right Xp Xc).trans (le_max_right 4 _)
  have hvR : 2 * R ≤ (v : ℝ) := hV.trans (by exact_mod_cast hv)
  have hv4 : (4 : ℝ) ≤ v := hR4.trans (by linarith)
  have hu0v : ((u - 1 : ℕ) : ℝ) ≤ v := by
    exact_mod_cast (Nat.sub_le u 1).trans huv
  have hvu0 : (v : ℝ) ≤ 2 * ((u - 1 : ℕ) : ℝ) := by
    exact_mod_cast hhalf
  have hu0R : R ≤ ((u - 1 : ℕ) : ℝ) := by linarith
  have hEu0 := hXp ((u - 1 : ℕ) : ℝ) (hRXp.trans hu0R)
  have hEv := hXp (v : ℝ) (hRXp.trans (by linarith))
  have hS := hXc (v : ℝ) (hRXc.trans (by linarith))
  have htransfer := div_log_pow_le_two_pow_mul k hv4 hu0v hvu0
  have hEu : |Chebyshev.psi ((u - 1 : ℕ) : ℝ) - ((u - 1 : ℕ) : ℝ)| ≤
      ε * ((2 : ℝ) ^ k * (v : ℝ) / Real.log v ^ k) :=
    hEu0.trans (by
      simpa only [mul_div_assoc] using
        (mul_le_mul_of_nonneg_left htransfer hε.le))
  have htheta := theta_interval_lower_of_psi_bounds hEu hEv hS
  have hlogv : 0 < Real.log (v : ℝ) := Real.log_pos (by linarith)
  let B : ℝ := (v : ℝ) / Real.log v ^ k
  let W : ℝ := (v : ℝ) - ((u - 1 : ℕ) : ℝ)
  have herrors :
      ε * B + ε * B + ε * ((2 : ℝ) ^ k * B) ≤ W / 4 := by
    have heq : ε * B + ε * B + ε * ((2 : ℝ) ^ k * B) = B / 4 := by
      dsimp only [ε]
      field_simp
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hwidth (by norm_num)
  have htheta' : W / 2 ≤
      Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) := by
    have hEuRewrite :
        ε * ((2 : ℝ) ^ k * (v : ℝ) / Real.log v ^ k) =
          ε * ((2 : ℝ) ^ k * ((v : ℝ) / Real.log v ^ k)) := by ring
    rw [hEuRewrite] at hEu
    have hthetaNorm : W - ε * B - ε * ((2 : ℝ) ^ k * B) - ε * B ≤
        Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) := by
      calc
        W - ε * B - ε * ((2 : ℝ) ^ k * B) - ε * B =
            (v : ℝ) - ((u - 1 : ℕ) : ℝ) -
              ε * (v : ℝ) / Real.log v ^ k -
              ε * ((2 : ℝ) ^ k * (v : ℝ) / Real.log v ^ k) -
              ε * (v : ℝ) / Real.log v ^ k := by
                dsimp only [B, W]
                ring
        _ ≤ _ := htheta
    have hW0 : 0 ≤ W := by dsimp only [W]; exact sub_nonneg.mpr hu0v
    linarith
  have hcount := theta_sub_le_primeInterval_card_mul_log huv
  have hhalfcount : W / 2 ≤
      (((Finset.Icc u v).filter Nat.Prime).card : ℝ) * Real.log v :=
    htheta'.trans hcount
  apply (div_le_iff₀ (mul_pos (by norm_num) hlogv)).2
  nlinarith

/-- The integer analytic parameter used for the large-cardinality endgame. -/
private noncomputable def analyticG (N : ℕ) : ℕ :=
  ⌊(N : ℝ) / Real.log N ^ 4⌋₊

/-- The floor in `analyticG` loses at most a factor of two eventually. -/
private lemma eventually_analyticG_bounds :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (2 * Real.log N ^ 4) ≤ (analyticG N : ℝ) ∧
      (analyticG N : ℝ) ≤ (N : ℝ) / Real.log N ^ 4 ∧
      0 < analyticG N := by
  have hratioReal := Real.tendsto_pow_log_div_pow_atTop 1 4 (by norm_num)
  have hratio := hratioReal.comp tendsto_natCast_atTop_atTop
  simp only [Real.rpow_natCast, Real.rpow_one] at hratio
  have hsmall : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ 4 / (N : ℝ) < 1 / 2 := by
    have hnorm := NormedAddGroup.tendsto_nhds_zero.mp hratio
      (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnorm, eventually_ge_atTop 3] with N hnorm hN
    have hpow : Real.log (N : ℝ) ^ (4 : ℝ) =
        Real.log (N : ℝ) ^ (4 : ℕ) := by
      simpa using Real.rpow_natCast (Real.log (N : ℝ)) 4
    have hnorm' : |Real.log (N : ℝ) ^ 4 / (N : ℝ)| < 1 / 2 := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, hpow] using hnorm
    rw [abs_of_nonneg] at hnorm'
    · exact hnorm'
    · positivity
  filter_upwards [hsmall, eventually_ge_atTop 3] with N hsmall hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (by omega : 1 < N))
  have hlogpow : 0 < Real.log (N : ℝ) ^ 4 := pow_pos hlog 4
  have hx : 2 < (N : ℝ) / Real.log N ^ 4 := by
    rw [div_lt_iff₀ hNreal] at hsmall
    apply (lt_div_iff₀ hlogpow).2
    nlinarith
  have hfloorUpper : (analyticG N : ℝ) ≤
      (N : ℝ) / Real.log N ^ 4 := by
    exact Nat.floor_le (div_nonneg hNreal.le hlogpow.le)
  have hfloorLower : (N : ℝ) / Real.log N ^ 4 - 1 <
      (analyticG N : ℝ) := by
    exact Nat.sub_one_lt_floor _
  refine ⟨?_, hfloorUpper, ?_⟩
  · calc
      (N : ℝ) / (2 * Real.log N ^ 4) =
          ((N : ℝ) / Real.log N ^ 4) / 2 := by ring
      _ ≤ (N : ℝ) / Real.log N ^ 4 - 1 := by linarith
      _ ≤ (analyticG N : ℝ) := hfloorLower.le
  · exact_mod_cast (show (0 : ℝ) < (analyticG N : ℝ) by
      linarith [hfloorLower])

/-- The explicit real inequality which makes the sieve-free endgame close
for the choice `G ≍ N/log(N)^4`. -/
private lemma analytic_numeric_separation {N G : ℕ}
    (hN : 0 < N) (hG2 : 2 * G ≤ N)
    (hlog : 20000 ≤ Real.log (N : ℝ))
    (hGlower : (N : ℝ) / (2 * Real.log N ^ 4) ≤ (G : ℝ))
    (hGupper : (G : ℝ) ≤ (N : ℝ) / Real.log N ^ 4)
    (hGpos : 0 < G) :
    ((G + 1 : ℕ) : ℝ) * firstMomentRealBound N (2 * G) +
        firstMomentRealBound N G * firstMomentRealBound N (2 * G) <
      ((G : ℝ) / (4 * Real.log N)) * ((G : ℝ) / (2 * Real.log N)) := by
  let L := Real.log (N : ℝ)
  change 20000 ≤ L at hlog
  change (N : ℝ) / (2 * L ^ 4) ≤ (G : ℝ) at hGlower
  change (G : ℝ) ≤ (N : ℝ) / L ^ 4 at hGupper
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < L := by dsimp only [L]; linarith
  have hlogone : 1 ≤ Real.log (N : ℝ) := by linarith
  have hB1 := firstMomentRealBound_le hN (by omega : G ≤ N) hlogone
  have hB2 := firstMomentRealBound_le hN hG2 hlogone
  have hGsq : (G : ℝ) ^ 2 ≤ ((N : ℝ) / L ^ 4) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg G) hGupper 2
  have hB1' : firstMomentRealBound N G ≤ 72 * (N : ℝ) / L ^ 7 := by
    calc
      firstMomentRealBound N G ≤ 18 * (G : ℝ) ^ 2 * L / N := hB1
      _ ≤ 18 * ((N : ℝ) / L ^ 4) ^ 2 * L / N := by gcongr
      _ ≤ 72 * (N : ℝ) / L ^ 7 := by
        field_simp
        nlinarith [sq_nonneg L]
  have hB2' : firstMomentRealBound N (2 * G) ≤ 72 * (N : ℝ) / L ^ 7 := by
    calc
      firstMomentRealBound N (2 * G) ≤
          18 * ((2 * G : ℕ) : ℝ) ^ 2 * L / N := hB2
      _ = 72 * (G : ℝ) ^ 2 * L / N := by push_cast; ring
      _ ≤ 72 * ((N : ℝ) / L ^ 4) ^ 2 * L / N := by gcongr
      _ = 72 * (N : ℝ) / L ^ 7 := by field_simp
  have hxone : 1 ≤ (N : ℝ) / L ^ 4 :=
    hGupper.trans' (by exact_mod_cast hGpos)
  have hGadd : ((G + 1 : ℕ) : ℝ) ≤ 2 * ((N : ℝ) / L ^ 4) := by
    rw [Nat.cast_add, Nat.cast_one]
    calc
      (G : ℝ) + 1 ≤ (N : ℝ) / L ^ 4 + 1 :=
        add_le_add hGupper (le_refl 1)
      _ ≤ 2 * ((N : ℝ) / L ^ 4) := by linarith
  have hB1nonneg : 0 ≤ firstMomentRealBound N G :=
    firstMomentRealBound_nonneg N G
  have hB2nonneg : 0 ≤ firstMomentRealBound N (2 * G) :=
    firstMomentRealBound_nonneg N (2 * G)
  have hupper :
      ((G + 1 : ℕ) : ℝ) * firstMomentRealBound N (2 * G) +
          firstMomentRealBound N G * firstMomentRealBound N (2 * G) ≤
        144 * (N : ℝ) ^ 2 / L ^ 11 +
          5184 * (N : ℝ) ^ 2 / L ^ 14 := by
    calc
      _ ≤ (2 * ((N : ℝ) / L ^ 4)) * (72 * (N : ℝ) / L ^ 7) +
          (72 * (N : ℝ) / L ^ 7) * (72 * (N : ℝ) / L ^ 7) := by
            gcongr
      _ = _ := by field_simp; ring
  have hcoeff :
      144 * (N : ℝ) ^ 2 / L ^ 11 +
          5184 * (N : ℝ) ^ 2 / L ^ 14 <
        (N : ℝ) ^ 2 / (32 * L ^ 10) := by
    have hL1 : 1 < L := by linarith
    have h144 : (144 : ℝ) / L < 1 / 64 := by
      apply (div_lt_iff₀ hL).2
      nlinarith
    have h5184 : (5184 : ℝ) / L ^ 4 < 1 / 64 := by
      apply (div_lt_iff₀ (pow_pos hL 4)).2
      have hp : (12800 : ℝ) < L ^ 2 := by nlinarith
      nlinarith [sq_nonneg (L ^ 2 - 12800)]
    have hsum : (144 : ℝ) / L + 5184 / L ^ 4 < 1 / 32 := by linarith
    have hscale : 0 < (N : ℝ) ^ 2 / L ^ 10 := by positivity
    calc
      144 * (N : ℝ) ^ 2 / L ^ 11 + 5184 * (N : ℝ) ^ 2 / L ^ 14 =
          ((N : ℝ) ^ 2 / L ^ 10) * (144 / L + 5184 / L ^ 4) := by
            field_simp
      _ < ((N : ℝ) ^ 2 / L ^ 10) * (1 / 32) :=
        mul_lt_mul_of_pos_left hsum hscale
      _ = (N : ℝ) ^ 2 / (32 * L ^ 10) := by ring
  have hlower : (N : ℝ) ^ 2 / (32 * L ^ 10) ≤
      ((G : ℝ) / (4 * L)) * ((G : ℝ) / (2 * L)) := by
    have hsq := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ (N : ℝ) / (2 * L ^ 4)) hGlower 2
    calc
      (N : ℝ) ^ 2 / (32 * L ^ 10) =
          ((N : ℝ) / (2 * L ^ 4)) ^ 2 / (8 * L ^ 2) := by
            field_simp
            ring
      _ ≤ (G : ℝ) ^ 2 / (8 * L ^ 2) := by gcongr
      _ = ((G : ℝ) / (4 * L)) * ((G : ℝ) / (2 * L)) := by ring
  exact hupper.trans_lt (hcoeff.trans_le hlower)

/-- The canonical factor triple obtained from an ordered pair `x < y`.
Its last two coordinates are the coprime reductions of `x,y`. -/
private def pairTriple (n x y : ℕ) : ℕ × (ℕ × ℕ) :=
  let g := x.gcd y
  let X₁ := x / g
  let X₂ := y / g
  (n / (X₁ * X₂), (X₁, X₂))

private lemma pairTriple_mem {N D n x y : ℕ} (hn : 0 < n)
    (hx : 0 < x) (hy : 0 < y) (hxy : x < y)
    (hxn : x ∣ n) (hyn : y ∣ n)
    (hD : y / x.gcd y ≤ D)
    (hclose : n * (y / x.gcd y) ≤ N * (x / x.gcd y)) :
    pairTriple n x y ∈ factorTriples N D n := by
  let g := x.gcd y
  let X₁ := x / g
  let X₂ := y / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left y hx
  have hX₁ : 0 < X₁ := Nat.div_pos (Nat.gcd_le_left y hx) hg
  have hX₂ : 0 < X₂ := Nat.div_pos (Nat.gcd_le_right x hy) hg
  have hcop : X₁.Coprime X₂ := Nat.coprime_div_gcd_div_gcd hg
  have hX₁n : X₁ ∣ n := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)).trans hxn
  have hX₂n : X₂ ∣ n := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)).trans hyn
  have hprod : X₁ * X₂ ∣ n := hcop.mul_dvd_of_dvd_of_dvd hX₁n hX₂n
  have hprodpos : 0 < X₁ * X₂ := Nat.mul_pos hX₁ hX₂
  have hlpos : 0 < n / (X₁ * X₂) :=
    Nat.div_pos (Nat.le_of_dvd hn hprod) hprodpos
  have hXX : X₁ < X₂ :=
    (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_left x y)
      (Nat.gcd_dvd_right x y)).mpr hxy
  rw [mem_factorTriples]
  refine ⟨hlpos, Nat.div_le_self n _, hX₁, ?_, hX₂, ?_, ?_, hXX, ?_⟩
  · exact hXX.le.trans hD
  · exact hD
  · simpa only [pairTriple, g, X₁, X₂, mul_assoc] using
      (Nat.div_mul_cancel hprod).symm
  · change n * (y / x.gcd y) ≤ N * (x / x.gcd y)
    exact hclose

/-- For fixed positive first entry, the coprime-reduced coordinate pair
remembers the second entry.  Hence the factor triples used in Lemma 2.5
are genuinely distinct. -/
private lemma pairTriple_injective_right {n x : ℕ} (hx : 0 < x) :
    Set.InjOn (pairTriple n x) (Set.Ioi 0) := by
  intro y hy z hz heq
  have hypos : 0 < y := hy
  have hzpos : 0 < z := hz
  let gy := x.gcd y
  let gz := x.gcd z
  let Xy₁ := x / gy
  let Xz₁ := x / gz
  let Xy₂ := y / gy
  let Xz₂ := z / gz
  have h₁ : Xy₁ = Xz₁ := congrArg (fun t ↦ t.2.1) heq
  have h₂ : Xy₂ = Xz₂ := congrArg (fun t ↦ t.2.2) heq
  have hgy : 0 < gy := Nat.gcd_pos_of_pos_left y hx
  have hgz : 0 < gz := Nat.gcd_pos_of_pos_left z hx
  have hX₁ : 0 < Xy₁ := Nat.div_pos (Nat.gcd_le_left y hx) hgy
  have hgeq : gy = gz := by
    apply Nat.mul_left_cancel hX₁
    calc
      Xy₁ * gy = x := Nat.div_mul_cancel (Nat.gcd_dvd_left x y)
      _ = Xz₁ * gz := (Nat.div_mul_cancel (Nat.gcd_dvd_left x z)).symm
      _ = Xy₁ * gz := by rw [h₁]
  calc
    y = Xy₂ * gy := (Nat.div_mul_cancel (Nat.gcd_dvd_right x y)).symm
    _ = Xz₂ * gz := by rw [h₂, hgeq]
    _ = z := Nat.div_mul_cancel (Nat.gcd_dvd_right x z)

/-- If every ordered pair formed from the least element of a positive
finite set produces a `k_D(n)` triple, then the set has at most
`k_D(n)+1` elements. -/
private lemma card_le_kCount_add_one {N D n : ℕ} (S : Finset ℕ)
    (hpos : ∀ x ∈ S, 0 < x)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x < y →
      pairTriple n x y ∈ factorTriples N D n) :
    S.card ≤ kCount N D n + 1 := by
  classical
  by_cases hS : S.Nonempty
  · let x := S.min' hS
    have hxS : x ∈ S := S.min'_mem hS
    have hx : 0 < x := hpos x hxS
    have hmap : ∀ y ∈ S.erase x,
        pairTriple n x y ∈ factorTriples N D n := by
      intro y hy
      have hyS := Finset.mem_of_mem_erase hy
      have hyne := (Finset.mem_erase.mp hy).1
      apply hpair x hxS y hyS
      exact (S.min'_le y hyS).lt_of_ne (Ne.symm hyne)
    have hinj : Set.InjOn (pairTriple n x) (↑(S.erase x) : Set ℕ) := by
      apply (pairTriple_injective_right hx).mono
      intro y hy
      exact hpos y (Finset.mem_of_mem_erase hy)
    have hcard : (S.erase x).card ≤ (factorTriples N D n).card :=
      Finset.card_le_card_of_injOn (pairTriple n x) hmap hinj
    rw [Finset.card_erase_of_mem hxS] at hcard
    rw [kCount]
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty] at hS
    simp [hS, kCount]

/-- Two represented multipliers whose `α`-components are strictly
ordered give a canonical triple counted by `k_D(α)`. -/
private lemma component_pairTriple_mem (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β d e c D : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α.Coprime β)
    (hsq : A.card * A.card < 2 * (α * α))
    (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β)
    (hαd : α * d * c ∈ A) (hβd : β * d * c ∈ A)
    (hαe : α * e * c ∈ A) (hβe : β * e * c ∈ A)
    (hlt : d.gcd α < e.gcd α)
    (hD : e.gcd α / (d.gcd α).gcd (e.gcd α) ≤ D) :
    pairTriple α (d.gcd α) (e.gcd α) ∈
      factorTriples A.card D α := by
  let g := d.gcd e
  let d' := d / g
  let e' := e / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hd
  have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_left e hd) hg
  have he' : 0 < e' := Nat.div_pos (Nat.gcd_le_right d he) hg
  have hcop : d'.Coprime e' := Nat.coprime_div_gcd_div_gcd hg
  have hdexpand : d' * (g * c) = d * c := by
    calc
      d' * (g * c) = (d' * g) * c := by simp only [mul_assoc]
      _ = d * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
  have heexpand : e' * (g * c) = e * c := by
    calc
      e' * (g * c) = (e' * g) * c := by simp only [mul_assoc]
      _ = e * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
  have hfac := factor_closeness_of_counterexample A hbad hα hβ hd' he'
    (Nat.mul_pos hg hc) hαβ hcop hsq
    (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact hαd)
    (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact hβd)
    (by rw [mul_assoc, heexpand, ← mul_assoc]; exact hαe)
    (by rw [mul_assoc, heexpand, ← mul_assoc]; exact hβe)
  have hdcomp : d'.gcd α = d.gcd α / (d.gcd α).gcd (e.gcd α) := by
    exact gcd_div_gcd_eq_component hαβ hd he hdfac hefac
  have hecomp : e'.gcd α = e.gcd α / (d.gcd α).gcd (e.gcd α) := by
    simpa only [e', g, Nat.gcd_comm e d,
      Nat.gcd_comm (e.gcd α) (d.gcd α)] using
      (gcd_div_gcd_eq_component hαβ he hd hefac hdfac)
  apply pairTriple_mem hα (Nat.gcd_pos_of_pos_left α hd)
    (Nat.gcd_pos_of_pos_left α he) hlt
    (Nat.gcd_dvd_right d α) (Nat.gcd_dvd_right e α) hD
  rw [← hdcomp, ← hecomp]
  exact hfac.2.2.2.1.le

/-- Quantitative form of Balasubramanian--Soundararajan, Lemma 2.5.
The two hypotheses ending in `D` say that every coprime-reduced
`α`-component and `β`-component is at most the global parameter `D`.
They are separated here from the later definition of that global maximum,
so the finite two-stage counting argument can be checked independently. -/
private lemma representationCount_le_kCount (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α D : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsqα : A.card * A.card < 2 * (α * α))
    (hsqβ : A.card * A.card < 2 * ((p - α) * (p - α)))
    (hDα : ∀ d ∈ normalize (representedMultipliers A α (p - α)),
      ∀ e ∈ normalize (representedMultipliers A α (p - α)),
        e.gcd α / (d.gcd α).gcd (e.gcd α) ≤ D)
    (hDβ : ∀ d ∈ normalize (representedMultipliers A α (p - α)),
      ∀ e ∈ normalize (representedMultipliers A α (p - α)),
        e.gcd (p - α) / (d.gcd (p - α)).gcd (e.gcd (p - α)) ≤ D) :
    representationCount A p α ≤
      (kCount A.card D α + 1) * (kCount A.card D (p - α) + 1) := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  by_cases hR : R.Nonempty
  · have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
    let c := R.gcd id
    have hc : 0 < c := gcd_pos R hR₀ hR
    have hrepresented : ∀ {d}, d ∈ B →
        0 < d ∧ α * d * c ∈ A ∧ β * d * c ∈ A := by
      intro d hd
      change d ∈ R.image (fun e ↦ e / R.gcd id) at hd
      obtain ⟨e, heR, rfl⟩ := Finset.mem_image.mp hd
      have he := (mem_representedMultipliers hα).mp heR
      have hce : R.gcd id ∣ e := Finset.gcd_dvd heR
      have heq : e / R.gcd id * R.gcd id = e := Nat.div_mul_cancel hce
      refine ⟨Nat.div_pos (Nat.le_of_dvd he.1 hce) hc, ?_, ?_⟩
      · change α * (e / R.gcd id) * R.gcd id ∈ A
        rw [mul_assoc, heq]
        exact he.2.1
      · change β * (e / R.gcd id) * R.gcd id ∈ A
        rw [mul_assoc, heq]
        exact he.2.2
    have hdvd : ∀ d ∈ B, d ∣ α * β := by
      exact normalize_represented_dvd_product A hbad hα hβ hαβ hsqα hR
    have hfac : ∀ d ∈ B, d = d.gcd α * d.gcd β := by
      intro d hd
      exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr
        (hdvd d hd)).symm
    let U := B.image fun d ↦ d.gcd α
    have hU : U.card ≤ kCount A.card D α + 1 := by
      apply card_le_kCount_add_one U
      · intro u hu
        obtain ⟨d, hdB, rfl⟩ := Finset.mem_image.mp hu
        exact Nat.gcd_pos_of_pos_left α (hrepresented hdB).1
      · intro u hu v hv huv
        obtain ⟨d, hdB, hdu⟩ := Finset.mem_image.mp hu
        obtain ⟨e, heB, hev⟩ := Finset.mem_image.mp hv
        subst u
        subst v
        apply component_pairTriple_mem A hbad hα hβ hαβ hsqα
          (hrepresented hdB).1 (hrepresented heB).1 hc
          (hfac d hdB) (hfac e heB)
          (hrepresented hdB).2.1 (hrepresented hdB).2.2
          (hrepresented heB).2.1 (hrepresented heB).2.2 huv
        simpa only [β] using hDα d hdB e heB
    have hfiber : ∀ u ∈ U,
        (B.filter fun d ↦ d.gcd α = u).card ≤
          kCount A.card D β + 1 := by
      intro u hu
      let T := B.filter fun d ↦ d.gcd α = u
      let V := T.image fun d ↦ d.gcd β
      have hTV : T.card = V.card := by
        change T.card = (T.image fun d ↦ d.gcd β).card
        rw [Finset.card_image_of_injOn]
        intro d hdT e heT hde
        have hdcomp := (Finset.mem_filter.mp hdT).2
        have hecomp := (Finset.mem_filter.mp heT).2
        change d.gcd β = e.gcd β at hde
        calc
          d = d.gcd α * d.gcd β := hfac d (Finset.mem_filter.mp hdT).1
          _ = e.gcd α * e.gcd β := by rw [hdcomp, hecomp, hde]
          _ = e := (hfac e (Finset.mem_filter.mp heT).1).symm
      rw [hTV]
      apply card_le_kCount_add_one V
      · intro v hv
        obtain ⟨d, hdT, rfl⟩ := Finset.mem_image.mp hv
        exact Nat.gcd_pos_of_pos_left β
          (hrepresented (Finset.mem_filter.mp hdT).1).1
      · intro v hv w hw hvw
        obtain ⟨d, hdT, hdv⟩ := Finset.mem_image.mp hv
        obtain ⟨e, heT, hew⟩ := Finset.mem_image.mp hw
        have hdB := (Finset.mem_filter.mp hdT).1
        have heB := (Finset.mem_filter.mp heT).1
        subst v
        subst w
        apply component_pairTriple_mem A hbad hβ hα hαβ.symm hsqβ
          (hrepresented hdB).1 (hrepresented heB).1 hc
          (by simpa only [mul_comm] using hfac d hdB)
          (by simpa only [mul_comm] using hfac e heB)
          (hrepresented hdB).2.2 (hrepresented hdB).2.1
          (hrepresented heB).2.2 (hrepresented heB).2.1 hvw
        simpa only [β] using hDβ d hdB e heB
    have hcardB : B.card ≤
        (kCount A.card D α + 1) * (kCount A.card D β + 1) := by
      calc
        B.card = ∑ u ∈ U, (B.filter fun d ↦ d.gcd α = u).card :=
          Finset.card_eq_sum_card_image (fun d ↦ d.gcd α) B
        _ ≤ ∑ _u ∈ U, (kCount A.card D β + 1) :=
          Finset.sum_le_sum hfiber
        _ = U.card * (kCount A.card D β + 1) := by
          exact Finset.sum_const_nat fun _ _ ↦ rfl
        _ ≤ (kCount A.card D α + 1) *
            (kCount A.card D β + 1) :=
          Nat.mul_le_mul_right _ hU
    change R.card ≤ _
    rw [← normalize_card R]
    simpa only [B, β] using hcardB
  · simp only [Finset.not_nonempty_iff_eq_empty] at hR
    simp [representationCount, R, β, hR]

/-! ## The global reduced-pair set and its maximum coordinate -/

/-- All ordered coprime reductions of two normalized multipliers for one
`(p, α)`. -/
private def reducedPairs (A : Finset ℕ) (p α : ℕ) : Finset (ℕ × ℕ) :=
  let B := normalize (representedMultipliers A α (p - α))
  (B ×ˢ B).image fun de ↦
    (de.1 / de.1.gcd de.2, de.2 / de.1.gcd de.2)

/-- The paper's finite set `S`, for a fixed window parameter `G`. -/
private def globalReducedPairs (A : Finset ℕ) (G : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G)).filter Nat.Prime).biUnion
    fun p ↦ (Finset.Icc ((p + 1) / 2) A.card).biUnion fun α ↦
      reducedPairs A p α

/-- The least coordinate bound for `globalReducedPairs`; it is zero only
when that set is empty. -/
private def globalD (A : Finset ℕ) (G : ℕ) : ℕ :=
  (globalReducedPairs A G).sup fun de ↦ max de.1 de.2

private lemma reducedPair_mem_global {A : Finset ℕ} {G p α d e : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) (hα : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hd : d ∈ normalize (representedMultipliers A α (p - α)))
    (he : e ∈ normalize (representedMultipliers A α (p - α))) :
    (d / d.gcd e, e / d.gcd e) ∈ globalReducedPairs A G := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨p, Finset.mem_filter.mpr ⟨hpwin, hp⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨α, hα, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨(d, e), Finset.mem_product.mpr ⟨hd, he⟩, rfl⟩

private lemma pair_right_le_globalD {A : Finset ℕ} {G : ℕ} {de : ℕ × ℕ}
    (hde : de ∈ globalReducedPairs A G) : de.2 ≤ globalD A G := by
  exact le_max_right de.1 de.2 |>.trans
    (Finset.le_sup (f := fun de : ℕ × ℕ ↦ max de.1 de.2) hde)

private lemma pair_left_le_globalD {A : Finset ℕ} {G : ℕ} {de : ℕ × ℕ}
    (hde : de ∈ globalReducedPairs A G) : de.1 ≤ globalD A G := by
  exact le_max_left de.1 de.2 |>.trans
    (Finset.le_sup (f := fun de : ℕ × ℕ ↦ max de.1 de.2) hde)

/-- A reduced component is bounded by the corresponding full reduced
multiplier. -/
private lemma component_div_le_div_gcd {α β d e : ℕ}
    (hαβ : α.Coprime β) (hd : 0 < d) (he : 0 < e)
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β) :
    e.gcd α / (d.gcd α).gcd (e.gcd α) ≤ e / d.gcd e := by
  have hcomp : (e / d.gcd e).gcd α =
      e.gcd α / (d.gcd α).gcd (e.gcd α) := by
    simpa only [Nat.gcd_comm e d, Nat.gcd_comm (e.gcd α) (d.gcd α)] using
      (gcd_div_gcd_eq_component hαβ he hd hefac hdfac)
  rw [← hcomp]
  exact Nat.gcd_le_left α (Nat.div_pos
    (Nat.gcd_le_right d he) (Nat.gcd_pos_of_pos_left e hd))

/-- The global maximum `D` supplies the two coordinate bounds required by
the already proved finite version of Lemma 2.5. -/
private lemma component_le_globalD (A : Finset ℕ) (G : ℕ)
    (hbad : ¬ GrahamBound A) {p α d e : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hαpos : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hd : d ∈ normalize (representedMultipliers A α (p - α)))
    (he : e ∈ normalize (representedMultipliers A α (p - α))) :
    e.gcd α / (d.gcd α).gcd (e.gcd α) ≤ globalD A G := by
  let R := representedMultipliers A α (p - α)
  let B := normalize R
  have hβ : 0 < p - α := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime (p - α) := coprime_prime_sub hp hαpos hαp
  have hR : R.Nonempty := by
    change d ∈ R.image (fun x ↦ x / R.gcd id) at hd
    obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hd
    exact ⟨x, hx⟩
  have hdvd : ∀ x ∈ B, x ∣ α * (p - α) :=
    normalize_represented_dvd_product A hbad hαpos hβ hαβ hsq hR
  have hfac : ∀ x ∈ B, x = x.gcd α * x.gcd (p - α) := by
    intro x hx
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr
      (hdvd x hx)).symm
  have hfull : e / d.gcd e ≤ globalD A G :=
    pair_right_le_globalD (reducedPair_mem_global hpwin hp hαJ hd he)
  exact (component_div_le_div_gcd hαβ
    (Nat.pos_of_ne_zero fun hz ↦
      normalize_nonzero R (representedMultipliers_nonzero hαpos) (hz ▸ hd))
    (Nat.pos_of_ne_zero fun hz ↦
      normalize_nonzero R (representedMultipliers_nonzero hαpos) (hz ▸ he))
    (hfac d hd) (hfac e he)).trans hfull

private lemma complementary_component_le_globalD (A : Finset ℕ) (G : ℕ)
    (hbad : ¬ GrahamBound A) {p α d e : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hαpos : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hd : d ∈ normalize (representedMultipliers A α (p - α)))
    (he : e ∈ normalize (representedMultipliers A α (p - α))) :
    e.gcd (p - α) / (d.gcd (p - α)).gcd (e.gcd (p - α)) ≤ globalD A G := by
  let R := representedMultipliers A α (p - α)
  let B := normalize R
  have hβ : 0 < p - α := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime (p - α) := coprime_prime_sub hp hαpos hαp
  have hR : R.Nonempty := by
    change d ∈ R.image (fun x ↦ x / R.gcd id) at hd
    obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hd
    exact ⟨x, hx⟩
  have hdvd : ∀ x ∈ B, x ∣ α * (p - α) :=
    normalize_represented_dvd_product A hbad hαpos hβ hαβ hsq hR
  have hfac : ∀ x ∈ B, x = x.gcd α * x.gcd (p - α) := by
    intro x hx
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr
      (hdvd x hx)).symm
  have hfull : e / d.gcd e ≤ globalD A G :=
    pair_right_le_globalD (reducedPair_mem_global hpwin hp hαJ hd he)
  exact (component_div_le_div_gcd hαβ.symm
    (Nat.pos_of_ne_zero fun hz ↦
      normalize_nonzero R (representedMultipliers_nonzero hαpos) (hz ▸ hd))
    (Nat.pos_of_ne_zero fun hz ↦
      normalize_nonzero R (representedMultipliers_nonzero hαpos) (hz ▸ he))
    (by simpa only [mul_comm] using hfac d hd)
    (by simpa only [mul_comm] using hfac e he)).trans hfull

/-- Lemma 2.5 with the paper's actual global maximum coordinate. -/
private lemma representationCount_le_globalD (A : Finset ℕ) (G : ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hαpos : 0 < α) (hαp : α < p)
    (hsqα : A.card * A.card < 2 * (α * α))
    (hsqβ : A.card * A.card < 2 * ((p - α) * (p - α))) :
    representationCount A p α ≤
      (kCount A.card (globalD A G) α + 1) *
        (kCount A.card (globalD A G) (p - α) + 1) := by
  apply representationCount_le_kCount A hbad hp hαpos hαp hsqα hsqβ
  · intro d hd e he
    exact component_le_globalD A G hbad hpwin hp hαJ hαpos hαp hsqα hd he
  · intro d hd e he
    exact complementary_component_le_globalD A G hbad hpwin hp hαJ
      hαpos hαp hsqα hd he

/-- Expanded form of Lemma 2.5.  After subtracting the compulsory first
representation, the excess in one fiber is bounded by the two one-sided
restricted-divisor counts and their product. -/
private lemma representationCount_sub_one_le_kCounts (A : Finset ℕ) (G : ℕ)
    (hbad : ¬GrahamBound A) {p α : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hαpos : 0 < α) (hαp : α < p)
    (hsqα : A.card * A.card < 2 * (α * α))
    (hsqβ : A.card * A.card < 2 * ((p - α) * (p - α))) :
    representationCount A p α - 1 ≤
      kCount A.card (globalD A G) α +
        kCount A.card (globalD A G) (p - α) +
          kCount A.card (globalD A G) α *
            kCount A.card (globalD A G) (p - α) := by
  let x := kCount A.card (globalD A G) α
  let y := kCount A.card (globalD A G) (p - α)
  have h : representationCount A p α ≤ (x + 1) * (y + 1) :=
    representationCount_le_globalD A G hbad hpwin hp hαJ
    hαpos hαp hsqα hsqβ
  have hexpand : (x + 1) * (y + 1) = x * y + x + y + 1 := by ring
  calc
    representationCount A p α - 1 ≤ (x + 1) * (y + 1) - 1 :=
      Nat.sub_le_sub_right h 1
    _ = x * y + x + y := by rw [hexpand]; omega
    _ = x + y + x * y := by ac_rfl

/-- In the analytic window, the complementary coordinate `p-α` is also
larger than `N/√2`; this is the second square hypothesis in Lemma 2.5. -/
private lemma complement_square_lt_of_analytic_window {N G p α : ℕ}
    (hG : 0 < G) (hGN : 10 * G ≤ N)
    (hpwin : p ∈ Finset.Icc (2 * N - 2 * G) (2 * N - G))
    (hαJ : α ∈ Finset.Icc ((p + 1) / 2) N) :
    N * N < 2 * ((p - α) * (p - α)) := by
  have h2G : 2 * G ≤ N := by omega
  have hsplit : N - 2 * G + 2 * G = N := Nat.sub_add_cancel h2G
  have hβlower : N - 2 * G ≤ p - α := by
    have hp := (Finset.mem_Icc.mp hpwin).1
    have hα := (Finset.mem_Icc.mp hαJ).2
    omega
  have hbase : N * N < 2 * ((N - 2 * G) * (N - 2 * G)) := by
    nlinarith [sq_nonneg ((N : ℤ) - 4 * G)]
  exact hbase.trans_le (Nat.mul_le_mul_left 2 (Nat.mul_self_le_mul_self hβlower))

private def kUpperAt (N D p α : ℕ) : ℕ :=
  kCount N D α + kCount N D (p - α) +
    kCount N D α * kCount N D (p - α)

private def collisionExcess (A : Finset ℕ) (p : ℕ) : ℕ :=
  ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
    2 ≤ representationCount A p α).sum fun α ↦
      representationCount A p α - 1

/-- For an odd prime `p`, reflection `α ↦ p-α` identifies the lower
half of `[p-N,N]` with the reflected copy of `J_p`. -/
private lemma sum_Icc_eq_sum_J_add_reflection {M : Type*}
    [AddCommMonoid M] {N p : ℕ} (hp : p.Prime) (hpN : N < p)
    (hp2 : 2 < p)
    (f : ℕ → M) :
    (Finset.Icc ((p + 1) / 2) N).sum (fun α ↦ f α + f (p - α)) =
      (Finset.Icc (p - N) N).sum f := by
  classical
  let J := Finset.Icc ((p + 1) / 2) N
  let H := Finset.Icc (p - N) (p - ((p + 1) / 2))
  let I := Finset.Icc (p - N) N
  have hpne : p ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpne
  have hinj : Set.InjOn (fun α : ℕ ↦ p - α) (↑J : Set ℕ) := by
    intro α hα β hβ hab
    change p - α = p - β at hab
    have hαp : α ≤ p := (Finset.mem_Icc.mp hα).2.trans hpN.le
    have hβp : β ≤ p := (Finset.mem_Icc.mp hβ).2.trans hpN.le
    have hsum : p - α + α = p - α + β := by
      calc
        p - α + α = p := Nat.sub_add_cancel hαp
        _ = p - β + β := (Nat.sub_add_cancel hβp).symm
        _ = p - α + β := by rw [hab]
    exact Nat.add_left_cancel hsum
  have himage : J.image (fun α : ℕ ↦ p - α) = H := by
    ext β
    constructor
    · intro hβ
      obtain ⟨α, hαJ, rfl⟩ := Finset.mem_image.mp hβ
      have hα := Finset.mem_Icc.mp hαJ
      exact Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le_sub_left hα.1 p⟩
    · intro hβ
      have hβI := Finset.mem_Icc.mp hβ
      have hβp : β ≤ p := hβI.2.trans (Nat.sub_le p _)
      apply Finset.mem_image.mpr
      refine ⟨p - β, Finset.mem_Icc.mpr ⟨?_, ?_⟩, Nat.sub_sub_self hβp⟩
      · omega
      · omega
  have hreflect : J.sum (fun α ↦ f (p - α)) = H.sum f := by
    rw [← himage]
    exact (Finset.sum_image hinj).symm
  have hdisj : Disjoint H J := by
    rw [Finset.disjoint_left]
    intro n hnH hnJ
    have hh := Finset.mem_Icc.mp hnH
    have hj := Finset.mem_Icc.mp hnJ
    omega
  have hunion : H ∪ J = I := by
    ext n
    simp only [H, J, I, Finset.mem_union, Finset.mem_Icc]
    omega
  calc
    J.sum (fun α ↦ f α + f (p - α)) =
        J.sum f + J.sum (fun α ↦ f (p - α)) := Finset.sum_add_distrib
    _ = H.sum f + J.sum f := by rw [hreflect, add_comm]
    _ = (H ∪ J).sum f := (Finset.sum_union hdisj).symm
    _ = I.sum f := by rw [hunion]

/-- Pointwise Lemma 2.5 summed over every collision fiber.  This is the
finite exact precursor of the upper split in Section 5. -/
private lemma collisionExcess_le_sum_kUpper (A : Finset ℕ) (G : ℕ)
    (hbad : ¬GrahamBound A) (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    {p : ℕ} (hpwin : p ∈ Finset.Icc
      (2 * A.card - 2 * G) (2 * A.card - G)) (hp : p.Prime) :
    collisionExcess A p ≤
      (Finset.Icc ((p + 1) / 2) A.card).sum fun α ↦
        kUpperAt A.card (globalD A G) p α := by
  let J := Finset.Icc ((p + 1) / 2) A.card
  let M := J.filter fun α ↦ 2 ≤ representationCount A p α
  have hsmall : 4 * G ≤ A.card := by omega
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hpoint : ∀ α ∈ M, representationCount A p α - 1 ≤
      kUpperAt A.card (globalD A G) p α := by
    intro α hαM
    have hαJ := (Finset.mem_filter.mp hαM).1
    have hαN := (Finset.mem_Icc.mp hαJ).2
    have hα : 0 < α := by
      have hlo := (Finset.mem_Icc.mp hαJ).1
      have hp2 := hp.two_le
      have hhalf : 0 < (p + 1) / 2 := Nat.div_pos (by omega) (by norm_num)
      omega
    have hαp : α < p := hαN.trans_lt hpN
    have hsqα : A.card * A.card < 2 * (α * α) := by
      have hGN' : G ≤ A.card := by omega
      have hsub : A.card - G + G = A.card := Nat.sub_add_cancel hGN'
      have halower : A.card - G ≤ α := by
        have hplower := (Finset.mem_Icc.mp hpwin).1
        have hαlower := (Finset.mem_Icc.mp hαJ).1
        omega
      have hthree : 3 * G ≤ A.card - G := by omega
      nlinarith [sq_nonneg (((A.card - G : ℕ) : ℤ) - 3 * G),
        sq_nonneg ((α : ℤ) - (A.card - G))]
    have hsqβ := complement_square_lt_of_analytic_window hG hGN hpwin hαJ
    exact representationCount_sub_one_le_kCounts A G hbad hpwin hp hαJ
      hα hαp hsqα hsqβ
  change M.sum (fun α ↦ representationCount A p α - 1) ≤ _
  calc
    M.sum (fun α ↦ representationCount A p α - 1) ≤
        M.sum (fun α ↦ kUpperAt A.card (globalD A G) p α) := by
      exact Finset.sum_le_sum hpoint
    _ ≤ J.sum (fun α ↦ kUpperAt A.card (globalD A G) p α) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ Nat.zero_le _)

/-- Equation (5.1) before summing over primes: the two linear `k_D`
terms combine into a single interval sum, leaving only the bilinear term
on `J_p`. -/
private lemma collisionExcess_le_upper_split (A : Finset ℕ) (G : ℕ)
    (hbad : ¬GrahamBound A) (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    {p : ℕ} (hpwin : p ∈ Finset.Icc
      (2 * A.card - 2 * G) (2 * A.card - G)) (hp : p.Prime) :
    collisionExcess A p ≤
      (Finset.Icc (p - A.card) A.card).sum
          (kCount A.card (globalD A G)) +
        (Finset.Icc ((p + 1) / 2) A.card).sum (fun α ↦
          kCount A.card (globalD A G) α *
            kCount A.card (globalD A G) (p - α)) := by
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hp2 : 2 < p := by
    have hN : 10 ≤ A.card := by nlinarith
    omega
  refine (collisionExcess_le_sum_kUpper A G hbad hG hGN hpwin hp).trans_eq ?_
  rw [← sum_Icc_eq_sum_J_add_reflection hp hpN hp2
    (kCount A.card (globalD A G))]
  simp only [kUpperAt, Finset.sum_add_distrib]

private def primeWindow (N G : ℕ) : Finset ℕ :=
  (Finset.Icc (2 * N - 2 * G) (2 * N - G)).filter Nat.Prime

/-- Prime counts on an inclusive natural interval are differences of the
standard prime-counting function. -/
private lemma card_filter_prime_Icc_eq {l u : ℕ} (hlu : l ≤ u) :
    ((Finset.Icc l u).filter Nat.Prime).card =
      Nat.primeCounting u - Nat.primeCounting (l - 1) := by
  have heq : (Finset.Icc l u).filter Nat.Prime =
      Nat.primesLE u \ Nat.primesLE (l - 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hl, hu⟩, hp⟩
      refine ⟨⟨hu, hp⟩, ?_⟩
      intro h
      have hp2 := hp.two_le
      omega
    · rintro ⟨⟨hu, hp⟩, hn⟩
      refine ⟨⟨?_, hu⟩, hp⟩
      by_contra h
      exact hn ⟨by omega, hp⟩
  rw [heq, Finset.card_sdiff_of_subset]
  · simp only [Nat.primesLE_card_eq_primeCounting]
  · intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (by omega), hp.2⟩

private lemma primeWindow_card_eq_primeCounting {N G : ℕ}
    (hGN : G ≤ N) :
    (primeWindow N G).card =
      Nat.primeCounting (2 * N - G) -
        Nat.primeCounting (2 * N - 2 * G - 1) := by
  unfold primeWindow
  exact card_filter_prime_Icc_eq (by omega)

private def totalCollisionExcess (A : Finset ℕ) (G : ℕ) : ℕ :=
  (primeWindow A.card G).sum (collisionExcess A)

/-- Boyle's elementary contribution, summed over the same outer prime
window as the collision excess. -/
private def basicPrimeCollisionLower (N G : ℕ) : ℕ :=
  (primeWindow N G).sum fun p ↦
    ((Finset.Icc (p - N) N).filter Nat.Prime).card

private lemma mul_le_basicPrimeCollisionLower
    {N G P Q : ℕ}
    (hP : P ≤ (primeWindow N G).card)
    (hQ : ∀ p ∈ primeWindow N G,
      Q ≤ ((Finset.Icc (p - N) N).filter Nat.Prime).card) :
    P * Q ≤ basicPrimeCollisionLower N G := by
  unfold basicPrimeCollisionLower
  calc
    P * Q ≤ (primeWindow N G).card * Q := Nat.mul_le_mul_right Q hP
    _ = ∑ p ∈ primeWindow N G, Q := by simp
    _ ≤ ∑ p ∈ primeWindow N G,
        ((Finset.Icc (p - N) N).filter Nat.Prime).card := by
      exact Finset.sum_le_sum hQ

/-- Real-valued form of the preceding product lower bound.  This avoids
rounding the analytic prime-count estimates before using them. -/
private lemma real_mul_le_basicPrimeCollisionLower
    {N G : ℕ} {RP RQ : ℝ} (hRQ : 0 ≤ RQ)
    (hP : RP ≤ ((primeWindow N G).card : ℝ))
    (hQ : ∀ p ∈ primeWindow N G,
      RQ ≤ (((Finset.Icc (p - N) N).filter Nat.Prime).card : ℝ)) :
    RP * RQ ≤ (basicPrimeCollisionLower N G : ℝ) := by
  unfold basicPrimeCollisionLower
  calc
    RP * RQ ≤ ((primeWindow N G).card : ℝ) * RQ :=
      mul_le_mul_of_nonneg_right hP hRQ
    _ = ∑ _p ∈ primeWindow N G, RQ := by simp
    _ ≤ ∑ p ∈ primeWindow N G,
        (((Finset.Icc (p - N) N).filter Nat.Prime).card : ℝ) := by
      exact Finset.sum_le_sum hQ
    _ = ((∑ p ∈ primeWindow N G,
        ((Finset.Icc (p - N) N).filter Nat.Prime).card : ℕ) : ℝ) := by
      simp

private def totalLinearUpper (N G D : ℕ) : ℕ :=
  (primeWindow N G).sum fun p ↦
    (Finset.Icc (p - N) N).sum (kCount N D)

private def totalBilinearUpper (N G D : ℕ) : ℕ :=
  (primeWindow N G).sum fun p ↦
    (Finset.Icc ((p + 1) / 2) N).sum fun α ↦
      kCount N D α * kCount N D (p - α)

/-- The bilinear term as one finite dependent set.  This is the exact
starting point for the reindexing used in Lemma 5.2. -/
private def bilinearTuples (N G D : ℕ) :
    Finset ((p : ℕ) × ((α : ℕ) ×
      ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))) :=
  (primeWindow N G).sigma fun p ↦
    (Finset.Icc ((p + 1) / 2) N).sigma fun α ↦
      factorTriples N D α ×ˢ factorTriples N D (p - α)

private lemma totalBilinearUpper_eq_card_bilinearTuples
    (N G D : ℕ) :
    totalBilinearUpper N G D = (bilinearTuples N G D).card := by
  simp only [totalBilinearUpper, bilinearTuples, Finset.card_sigma,
    Finset.card_product, kCount]

private def factorValue (t : ℕ × (ℕ × ℕ)) : ℕ :=
  t.1 * t.2.1 * t.2.2

/-- The union of all factor triples, with the represented integer
recovered as `factorValue`. -/
private def factorParameters (N D : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.Icc 1 N ×ˢ (Finset.Icc 1 D ×ˢ Finset.Icc 1 D)).filter fun t ↦
    t.2.1 < t.2.2 ∧ factorValue t ≤ N ∧
      factorValue t * t.2.2 ≤ N * t.2.1

private lemma mem_factorParameters {N D l X₁ X₂ : ℕ} :
    (l, (X₁, X₂)) ∈ factorParameters N D ↔
      1 ≤ l ∧ l ≤ N ∧ 1 ≤ X₁ ∧ X₁ ≤ D ∧
        1 ≤ X₂ ∧ X₂ ≤ D ∧ X₁ < X₂ ∧
        l * X₁ * X₂ ≤ N ∧
        (l * X₁ * X₂) * X₂ ≤ N * X₁ := by
  rw [factorParameters, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product]
  simp only [Finset.mem_Icc, factorValue]
  tauto

private lemma factorTriple_mem_factorParameters
    {N D n : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ factorTriples N D n) :
    t ∈ factorParameters N D ∧ factorValue t = n := by
  rcases t with ⟨l, X₁, X₂⟩
  have h := mem_factorTriples.mp ht
  have hX₂pos : 0 < X₂ := by omega
  have hvalueLe : l * X₁ * X₂ ≤ N := by
    apply Nat.le_of_mul_le_mul_right (c := X₂) ?_ hX₂pos
    calc
      (l * X₁ * X₂) * X₂ = n * X₂ := by rw [h.2.2.2.2.2.2.1]
      _ ≤ N * X₁ := h.2.2.2.2.2.2.2.2
      _ ≤ N * X₂ := Nat.mul_le_mul_left N (Nat.le_of_lt h.2.2.2.2.2.2.2.1)
  constructor
  · apply mem_factorParameters.mpr
    exact ⟨h.1, h.2.1.trans (h.2.2.2.2.2.2.1.symm ▸ hvalueLe),
      h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, hvalueLe, by
        simpa only [h.2.2.2.2.2.2.1] using h.2.2.2.2.2.2.2.2⟩
  · exact h.2.2.2.2.2.2.1.symm

private lemma factorValue_le_of_mem_factorParameters
    {N D : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ factorParameters N D) : factorValue t ≤ N := by
  exact (Finset.mem_filter.mp ht).2.2.1

private lemma factorParameter_mem_factorTriple
    {N D : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ factorParameters N D) :
    t ∈ factorTriples N D (factorValue t) := by
  rcases t with ⟨l, X₁, X₂⟩
  have h := mem_factorParameters.mp ht
  have hX₁pos : 0 < X₁ := by omega
  have hX₂pos : 0 < X₂ := by omega
  have hlvalue : l ≤ l * X₁ * X₂ := by
    calc
      l ≤ l * (X₁ * X₂) :=
        Nat.le_mul_of_pos_right l (Nat.mul_pos hX₁pos hX₂pos)
      _ = l * X₁ * X₂ := by ring
  apply mem_factorTriples.mpr
  simp only [factorValue]
  exact ⟨h.1,
    hlvalue,
    h.2.2.1,
    h.2.2.2.1,
    h.2.2.2.2.1,
    h.2.2.2.2.2.1,
    trivial, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

private lemma factorValue_pos_of_mem_factorTriples
    {N D n : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ factorTriples N D n) : 0 < factorValue t := by
  rcases t with ⟨l, X₁, X₂⟩
  have h := mem_factorTriples.mp ht
  simp only [factorValue]
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)

/-- Reindex the bilinear sum by the two factor triples.  Primality is
now a single condition on the sum of their recovered values. -/
private def bilinearParameterPairs (N G D : ℕ) :
    Finset ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) :=
  (factorParameters N D ×ˢ factorParameters N D).filter fun ts ↦
    let α := factorValue ts.1
    let β := factorValue ts.2
    let p := α + β
    p ∈ primeWindow N G ∧ (p + 1) / 2 ≤ α

/-- For a fixed factor triple representing `α`, the possible second
triples are precisely the prime-progression fiber estimated in Lemma 5.2. -/
private def primePartnerFactors
    (N G D : ℕ) (t₁ : ℕ × (ℕ × ℕ)) : Finset (ℕ × (ℕ × ℕ)) :=
  (factorParameters N D).filter fun t₂ ↦
    let α := factorValue t₁
    let β := factorValue t₂
    let p := α + β
    p ∈ primeWindow N G ∧ (p + 1) / 2 ≤ α

private def highFactorParameters (N G D : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (factorParameters N D).filter fun t ↦ N - G ≤ factorValue t

private lemma mem_primePartnerFactors
    {N G D : ℕ} {t₁ : ℕ × (ℕ × ℕ)} {μ Y₁ Y₂ : ℕ} :
    (μ, (Y₁, Y₂)) ∈ primePartnerFactors N G D t₁ ↔
      1 ≤ μ ∧ μ ≤ N ∧ 1 ≤ Y₁ ∧ Y₁ ≤ D ∧
      1 ≤ Y₂ ∧ Y₂ ≤ D ∧ Y₁ < Y₂ ∧
      μ * Y₁ * Y₂ ≤ N ∧
      (μ * Y₁ * Y₂) * Y₂ ≤ N * Y₁ ∧
      factorValue t₁ + μ * Y₁ * Y₂ ∈ primeWindow N G ∧
      (factorValue t₁ + μ * Y₁ * Y₂ + 1) / 2 ≤ factorValue t₁ := by
  rw [primePartnerFactors, Finset.mem_filter, mem_factorParameters]
  simp only [factorValue]
  tauto

private lemma primePartnerFactors_eq_empty_of_value_lt
    {N G D : ℕ} {t₁ : ℕ × (ℕ × ℕ)}
    (hGN : G ≤ N) (ht₁ : factorValue t₁ < N - G) :
    primePartnerFactors N G D t₁ = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨t₂, ht₂⟩
  rcases t₂ with ⟨μ, Y₁, Y₂⟩
  have h := mem_primePartnerFactors.mp ht₂
  have hpwin := (Finset.mem_filter.mp h.2.2.2.2.2.2.2.2.2.1).1
  have hplower := (Finset.mem_Icc.mp hpwin).1
  have hj := h.2.2.2.2.2.2.2.2.2.2
  omega

/-- Multipliers in a single arithmetic progression that produce a prime
in the outer window. -/
private def progressionMultipliers
    (N G α m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun μ ↦ α + μ * m ∈ primeWindow N G

/-- The elementary fallback bound for one progression.  It uses no
primality saving: a progression of step `m` meets a window of length `G`
at most `G / m + 2` times. -/
private lemma progressionMultipliers_card_le_trivial
    {N G α m : ℕ} (hGN : 2 * G ≤ N) (hαN : α ≤ N) (hm : 0 < m) :
    (progressionMultipliers N G α m).card ≤ G / m + 2 := by
  let L := 2 * N - 2 * G
  let U := 2 * N - G
  let a := L - α
  let b := U - α
  have hαL : α ≤ L := by dsimp only [L]; omega
  have hLU : L ≤ U := by dsimp only [L, U]; omega
  have hab : a ≤ b := by dsimp only [a, b]; omega
  have hba : b = a + G := by dsimp only [a, b, L, U]; omega
  have hsub : progressionMultipliers N G α m ⊆
      Finset.Icc (a ⌈/⌉ m) (b / m) := by
    intro μ hμ
    have h := Finset.mem_filter.mp hμ
    have hpwin := (Finset.mem_filter.mp h.2).1
    have hpI := Finset.mem_Icc.mp hpwin
    apply Finset.mem_Icc.mpr
    constructor
    · apply (ceilDiv_le_iff_le_mul hm).2
      dsimp only [a]
      rw [mul_comm]
      omega
    · apply (Nat.le_div_iff_mul_le hm).2
      dsimp only [b]
      omega
  calc
    (progressionMultipliers N G α m).card ≤
        (Finset.Icc (a ⌈/⌉ m) (b / m)).card :=
      Finset.card_le_card hsub
    _ = b / m + 1 - (a ⌈/⌉ m) := Nat.card_Icc _ _
    _ ≤ G / m + 2 := by
      have hfloorceil : a / m ≤ a ⌈/⌉ m := by
        rw [Nat.ceilDiv_eq_add_pred_div]
        apply Nat.div_le_div_right
        omega
      have hadd := Nat.add_div_le_div_add_div_add_one a G m
      rw [← hba] at hadd
      rw [Nat.sub_le_iff_le_add]
      omega

/-- Dropping the remaining size and closeness restrictions decomposes a
partner fiber into the arithmetic progressions to which the
Montgomery--Vaughan estimate is applied. -/
private lemma primePartnerFactors_card_le_progression_sum
    {N G D : ℕ} (t₁ : ℕ × (ℕ × ℕ)) :
    (primePartnerFactors N G D t₁).card ≤
      ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
        (progressionMultipliers N G (factorValue t₁) (Y₁ * Y₂)).card := by
  let reorder : (ℕ × (ℕ × ℕ)) →
      ((Y₁ : ℕ) × ((Y₂ : ℕ) × ℕ)) :=
    fun t ↦ ⟨t.2.1, t.2.2, t.1⟩
  let T : Finset ((Y₁ : ℕ) × ((Y₂ : ℕ) × ℕ)) :=
    (Finset.Icc 1 D).sigma fun Y₁ ↦
      (Finset.Icc 1 D).sigma fun Y₂ ↦
        progressionMultipliers N G (factorValue t₁) (Y₁ * Y₂)
  calc
    (primePartnerFactors N G D t₁).card ≤ T.card := by
      apply Finset.card_le_card_of_injOn
        (s := primePartnerFactors N G D t₁) (t := T) reorder
      · rintro ⟨μ, Y₁, Y₂⟩ ht
        dsimp only [reorder, T]
        have h := mem_primePartnerFactors.mp ht
        apply Finset.mem_sigma.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2.1⟩, ?_⟩
        apply Finset.mem_sigma.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨h.2.2.2.2.1,
          h.2.2.2.2.2.1⟩, ?_⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩, ?_⟩
        simpa only [mul_assoc] using h.2.2.2.2.2.2.2.2.2.1
      · rintro ⟨μ, Y₁, Y₂⟩ _ ⟨ν, Z₁, Z₂⟩ _ heq
        dsimp only [reorder] at heq
        cases heq
        rfl
    _ = ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
        (progressionMultipliers N G (factorValue t₁) (Y₁ * Y₂)).card := by
      simp only [T, Finset.card_sigma]

private lemma bilinearParameterPairs_card_eq_sum_partnerFactors
    (N G D : ℕ) :
    (bilinearParameterPairs N G D).card =
      ∑ t₁ ∈ factorParameters N D,
        (primePartnerFactors N G D t₁).card := by
  simp only [bilinearParameterPairs, primePartnerFactors,
    Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

private lemma bilinearParameterPairs_card_eq_sum_high_partnerFactors
    {N G D : ℕ} (hGN : G ≤ N) :
    (bilinearParameterPairs N G D).card =
      ∑ t₁ ∈ highFactorParameters N G D,
        (primePartnerFactors N G D t₁).card := by
  rw [bilinearParameterPairs_card_eq_sum_partnerFactors]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro t₁ ht₁ htnot
  have hlt : factorValue t₁ < N - G := by
    by_contra h
    exact htnot (Finset.mem_filter.mpr ⟨ht₁, Nat.le_of_not_gt h⟩)
  rw [primePartnerFactors_eq_empty_of_value_lt hGN hlt]
  rfl

/-- The possible first triples in the bilinear term are already contained
in the same first-moment envelope used for the linear term. -/
private lemma highFactorParameters_card_le_firstMomentTriples
    {N G D : ℕ} (hN : 0 < N) :
    (highFactorParameters N G D).card ≤
      (firstMomentTriples N D (N - G)).card := by
  apply Finset.card_le_card
  intro t ht
  rcases t with ⟨l, X₁, X₂⟩
  have hhigh := Finset.mem_filter.mp ht
  have htriple := factorParameter_mem_factorTriple hhigh.1
  have h := mem_factorTriples.mp htriple
  have hgap : N - factorValue (l, (X₁, X₂)) ≤ N - (N - G) := by
    have hnN := factorValue_le_of_mem_factorParameters hhigh.1
    omega
  have hgapSq : (N - factorValue (l, (X₁, X₂))) ^ 2 ≤
      (N - (N - G)) ^ 2 := pow_le_pow_left' hgap 2
  have hlcut : l ≤ (N - (N - G)) ^ 2 / N :=
    (factorTriple_multiplier_le_gap_sq_div hN htriple).trans
      (Nat.div_le_div_right hgapSq)
  apply mem_firstMomentTriples.mpr
  refine ⟨h.1, hlcut, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · simpa only [factorValue] using hhigh.2
  · simpa only [factorValue] using
      (factorValue_le_of_mem_factorParameters hhigh.1)
  · simpa only [factorValue] using h.2.2.2.2.2.2.2.2

/-- In every bilinear pair, the first factor value lies in `[N-G,N]`
and the second lies in `[N-2G,N]`.  Keeping both restrictions gives a
direct product bound which is asymptotically stronger than the elementary
progression fallback when `G` is of order `N^(2/3)`. -/
private lemma bilinearParameterPairs_subset_high_product
    {N G D : ℕ} (hGN : 2 * G ≤ N) :
    bilinearParameterPairs N G D ⊆
      highFactorParameters N G D ×ˢ highFactorParameters N (2 * G) D := by
  rintro ⟨t₁, t₂⟩ hpair
  simp only [bilinearParameterPairs, Finset.mem_filter, Finset.mem_product] at hpair
  have hpwindow := (Finset.mem_filter.mp hpair.2.1).1
  have hplower := (Finset.mem_Icc.mp hpwindow).1
  have ht₁le := factorValue_le_of_mem_factorParameters hpair.1.1
  have ht₂le := factorValue_le_of_mem_factorParameters hpair.1.2
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨hpair.1.1, ?_⟩
    change N - G ≤ factorValue t₁
    omega
  · apply Finset.mem_filter.mpr
    refine ⟨hpair.1.2, ?_⟩
    change N - 2 * G ≤ factorValue t₂
    omega

private lemma totalBilinearUpper_le_parameterPairs (N G D : ℕ) :
    totalBilinearUpper N G D ≤
      (bilinearParameterPairs N G D).card := by
  rw [totalBilinearUpper_eq_card_bilinearTuples]
  let forgetValues :
      ((p : ℕ) × ((α : ℕ) ×
        ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))) →
        ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) :=
    fun z ↦ z.2.2
  apply Finset.card_le_card_of_injOn
    (s := bilinearTuples N G D) (t := bilinearParameterPairs N G D)
    forgetValues
  · rintro ⟨p, α, t₁, t₂⟩ hz
    dsimp only [forgetValues]
    have hzmem : p ∈ primeWindow N G ∧
        α ∈ Finset.Icc ((p + 1) / 2) N ∧
        t₁ ∈ factorTriples N D α ∧ t₂ ∈ factorTriples N D (p - α) := by
      simpa only [Finset.mem_coe, bilinearTuples, Finset.mem_sigma,
        Finset.mem_product]
        using hz
    have ht₁ := factorTriple_mem_factorParameters hzmem.2.2.1
    have ht₂ := factorTriple_mem_factorParameters hzmem.2.2.2
    have hβpos : 0 < p - α := by
      rw [← ht₂.2]
      exact factorValue_pos_of_mem_factorTriples hzmem.2.2.2
    have hαp : α ≤ p := by omega
    have hpvalue : factorValue t₁ + factorValue t₂ = p := by
      rw [ht₁.2, ht₂.2]
      omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨ht₁.1, ht₂.1⟩, ?_⟩
    dsimp only
    constructor
    · simpa only [hpvalue] using hzmem.1
    · have hpsum : factorValue t₁ + factorValue t₂ = p := hpvalue
      have hαvalue : factorValue t₁ = α := ht₁.2
      have hsum : α + factorValue t₂ = p := by omega
      rw [hαvalue, hsum]
      exact (Finset.mem_Icc.mp hzmem.2.1).1
  · rintro ⟨p, α, t₁, t₂⟩ hz ⟨q, β, u₁, u₂⟩ hw heq
    dsimp only [forgetValues] at heq
    have hzmem : p ∈ primeWindow N G ∧
        α ∈ Finset.Icc ((p + 1) / 2) N ∧
        t₁ ∈ factorTriples N D α ∧ t₂ ∈ factorTriples N D (p - α) := by
      simpa only [Finset.mem_coe, bilinearTuples, Finset.mem_sigma,
        Finset.mem_product]
        using hz
    have hwmem : q ∈ primeWindow N G ∧
        β ∈ Finset.Icc ((q + 1) / 2) N ∧
        u₁ ∈ factorTriples N D β ∧ u₂ ∈ factorTriples N D (q - β) := by
      simpa only [Finset.mem_coe, bilinearTuples, Finset.mem_sigma,
        Finset.mem_product]
        using hw
    injection heq with ht₁u₁ ht₂u₂
    subst u₁
    subst u₂
    have hαeq : α = β := by
      have h₁ := (factorTriple_mem_factorParameters hzmem.2.2.1).2
      have h₂ := (factorTriple_mem_factorParameters hwmem.2.2.1).2
      omega
    subst β
    have hpq : p = q := by
      have h₁ := (factorTriple_mem_factorParameters hzmem.2.2.2).2
      have h₂ := (factorTriple_mem_factorParameters hwmem.2.2.2).2
      have hvpos : 0 < factorValue t₂ :=
        factorValue_pos_of_mem_factorTriples hzmem.2.2.2
      have hpα : α ≤ p := by omega
      have hqα : α ≤ q := by omega
      omega
    subst q
    rfl

/-- The bilinear term is bounded by two first moments.  This avoids any
prime-in-progression estimate: primality only cuts down the product set. -/
private lemma totalBilinearUpper_le_firstMoment_product
    {N G D : ℕ} (hN : 0 < N) (hGN : 2 * G ≤ N) :
    totalBilinearUpper N G D ≤
      (firstMomentTriples N D (N - G)).card *
        (firstMomentTriples N D (N - 2 * G)).card := by
  calc
    totalBilinearUpper N G D ≤
        (bilinearParameterPairs N G D).card :=
      totalBilinearUpper_le_parameterPairs N G D
    _ ≤ (highFactorParameters N G D ×ˢ
          highFactorParameters N (2 * G) D).card :=
      Finset.card_le_card (bilinearParameterPairs_subset_high_product hGN)
    _ = (highFactorParameters N G D).card *
          (highFactorParameters N (2 * G) D).card := Finset.card_product _ _
    _ ≤ (firstMomentTriples N D (N - G)).card *
          (firstMomentTriples N D (N - 2 * G)).card := by
      exact Nat.mul_le_mul
        (highFactorParameters_card_le_firstMomentTriples
          (N := N) (G := G) (D := D) hN)
        (highFactorParameters_card_le_firstMomentTriples
          (N := N) (G := 2 * G) (D := D) hN)

/-- Pointwise arithmetic-progression estimates can be inserted directly
into the full bilinear term.  This is the formal interface for the
Montgomery--Vaughan bound in Lemma 5.2. -/
private lemma totalBilinearUpper_le_of_progression_bounds
    {N G D : ℕ}
    (B : (ℕ × (ℕ × ℕ)) → ℕ → ℕ → ℕ)
    (hB : ∀ t₁ ∈ factorParameters N D,
      ∀ Y₁ ∈ Finset.Icc 1 D, ∀ Y₂ ∈ Finset.Icc 1 D,
        (progressionMultipliers N G (factorValue t₁) (Y₁ * Y₂)).card ≤
          B t₁ Y₁ Y₂) :
    totalBilinearUpper N G D ≤
      ∑ t₁ ∈ factorParameters N D,
        ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
          B t₁ Y₁ Y₂ := by
  calc
    totalBilinearUpper N G D ≤
        (bilinearParameterPairs N G D).card :=
      totalBilinearUpper_le_parameterPairs N G D
    _ = ∑ t₁ ∈ factorParameters N D,
        (primePartnerFactors N G D t₁).card :=
      bilinearParameterPairs_card_eq_sum_partnerFactors N G D
    _ ≤ ∑ t₁ ∈ factorParameters N D,
        ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
          (progressionMultipliers N G (factorValue t₁) (Y₁ * Y₂)).card := by
      apply Finset.sum_le_sum
      intro t₁ _ht₁
      exact primePartnerFactors_card_le_progression_sum t₁
    _ ≤ ∑ t₁ ∈ factorParameters N D,
        ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
          B t₁ Y₁ Y₂ := by
      apply Finset.sum_le_sum
      intro t₁ ht₁
      apply Finset.sum_le_sum
      intro Y₁ hY₁
      apply Finset.sum_le_sum
      intro Y₂ hY₂
      exact hB t₁ ht₁ Y₁ hY₁ Y₂ hY₂

private lemma totalBilinearUpper_le_of_high_progression_bounds
    {N G D : ℕ} (hGN : G ≤ N)
    (B : (ℕ × (ℕ × ℕ)) → ℕ → ℕ → ℕ)
    (hB : ∀ t₁ ∈ highFactorParameters N G D,
      ∀ Y₁ ∈ Finset.Icc 1 D, ∀ Y₂ ∈ Finset.Icc 1 D,
        (progressionMultipliers N G (factorValue t₁) (Y₁ * Y₂)).card ≤
          B t₁ Y₁ Y₂) :
    totalBilinearUpper N G D ≤
      ∑ t₁ ∈ highFactorParameters N G D,
        ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
          B t₁ Y₁ Y₂ := by
  calc
    totalBilinearUpper N G D ≤
        (bilinearParameterPairs N G D).card :=
      totalBilinearUpper_le_parameterPairs N G D
    _ = ∑ t₁ ∈ highFactorParameters N G D,
        (primePartnerFactors N G D t₁).card :=
      bilinearParameterPairs_card_eq_sum_high_partnerFactors hGN
    _ ≤ ∑ t₁ ∈ highFactorParameters N G D,
        ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
          (progressionMultipliers N G (factorValue t₁) (Y₁ * Y₂)).card := by
      apply Finset.sum_le_sum
      intro t₁ _ht₁
      exact primePartnerFactors_card_le_progression_sum t₁
    _ ≤ ∑ t₁ ∈ highFactorParameters N G D,
        ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
          B t₁ Y₁ Y₂ := by
      apply Finset.sum_le_sum
      intro t₁ ht₁
      apply Finset.sum_le_sum
      intro Y₁ hY₁
      apply Finset.sum_le_sum
      intro Y₂ hY₂
      exact hB t₁ ht₁ Y₁ hY₁ Y₂ hY₂

/-- A fully elementary, non-sieve specialization of the bilinear bound.
It is intentionally retained as a fallback for finite parameter ranges. -/
private lemma totalBilinearUpper_le_trivial_progression_sum
    {N G D : ℕ} (hGN : 2 * G ≤ N) :
    totalBilinearUpper N G D ≤
      ∑ t₁ ∈ factorParameters N D,
        ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
          (G / (Y₁ * Y₂) + 2) := by
  apply totalBilinearUpper_le_of_progression_bounds
  intro t₁ ht₁ Y₁ hY₁ Y₂ hY₂
  apply progressionMultipliers_card_le_trivial hGN
  · exact factorValue_le_of_mem_factorParameters ht₁
  · exact Nat.mul_pos (Finset.mem_Icc.mp hY₁).1 (Finset.mem_Icc.mp hY₂).1

/-- The elementary progression estimate after discarding all first triples
below the prime window.  This is strictly sharper than the preceding
fallback and uses the first-moment envelope through
`highFactorParameters_card_le_firstMomentTriples`. -/
private lemma totalBilinearUpper_le_high_trivial_progression_sum
    {N G D : ℕ} (hGN : 2 * G ≤ N) :
    totalBilinearUpper N G D ≤
      ∑ t₁ ∈ highFactorParameters N G D,
        ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
          (G / (Y₁ * Y₂) + 2) := by
  apply totalBilinearUpper_le_of_high_progression_bounds (by omega)
  intro t₁ ht₁ Y₁ hY₁ Y₂ hY₂
  apply progressionMultipliers_card_le_trivial hGN
  · exact factorValue_le_of_mem_factorParameters (Finset.mem_filter.mp ht₁).1
  · exact Nat.mul_pos (Finset.mem_Icc.mp hY₁).1 (Finset.mem_Icc.mp hY₂).1

/-- Closed elementary bound for the bilinear term.  It is deliberately
coarse, but every factor is now the cardinality of an executable finite
set or an explicit polynomial in `G,D`. -/
private lemma totalBilinearUpper_le_high_trivial_closed
    {N G D : ℕ} (hN : 0 < N) (hGN : 2 * G ≤ N) :
    totalBilinearUpper N G D ≤
      (firstMomentTriples N D (N - G)).card * D ^ 2 * (G + 2) := by
  have hcardIcc : (Finset.Icc 1 D).card = D := by
    rw [Nat.card_Icc]
    omega
  calc
    totalBilinearUpper N G D ≤
        ∑ t₁ ∈ highFactorParameters N G D,
          ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
            (G / (Y₁ * Y₂) + 2) :=
      totalBilinearUpper_le_high_trivial_progression_sum hGN
    _ ≤ ∑ t₁ ∈ highFactorParameters N G D,
          ∑ Y₁ ∈ Finset.Icc 1 D, ∑ Y₂ ∈ Finset.Icc 1 D,
            (G + 2) := by
      apply Finset.sum_le_sum
      intro t₁ _ht₁
      apply Finset.sum_le_sum
      intro Y₁ _hY₁
      apply Finset.sum_le_sum
      intro Y₂ _hY₂
      exact Nat.add_le_add_right (Nat.div_le_self G (Y₁ * Y₂)) 2
    _ = (highFactorParameters N G D).card * D ^ 2 * (G + 2) := by
      simp only [Finset.sum_const, hcardIcc, nsmul_eq_mul]
      simp only [pow_two, mul_add]
      ac_rfl
    _ ≤ (firstMomentTriples N D (N - G)).card * D ^ 2 * (G + 2) := by
      simpa only [mul_assoc] using
        (Nat.mul_le_mul_right (D ^ 2 * (G + 2))
          (highFactorParameters_card_le_firstMomentTriples
            (N := N) (G := G) (D := D) hN))

/-- The full linear term in (5.1), reindexed prime by prime into the
standalone finite sets used by Lemma 5.1. -/
private lemma totalLinearUpper_le_sum_firstMomentTriples
    {N G D : ℕ} (hN : 0 < N) :
    totalLinearUpper N G D ≤
      (primeWindow N G).sum fun p ↦
        (firstMomentTriples N D (p - N)).card := by
  unfold totalLinearUpper
  apply Finset.sum_le_sum
  intro p _hp
  exact sum_kCount_Icc_le_firstMomentTriples_card hN

/-- A uniform first-moment bound for the complete linear contribution in
the prime window. -/
private lemma totalLinearUpper_le_primeWindow_mul_firstMoment
    {N G D : ℕ} (hN : 0 < N) (hGN : 2 * G ≤ N) :
    totalLinearUpper N G D ≤
      (primeWindow N G).card *
        (firstMomentTriples N D (N - 2 * G)).card := by
  calc
    totalLinearUpper N G D ≤
        (primeWindow N G).sum fun p ↦
          (firstMomentTriples N D (p - N)).card :=
      totalLinearUpper_le_sum_firstMomentTriples hN
    _ ≤ (primeWindow N G).sum fun _p ↦
          (firstMomentTriples N D (N - 2 * G)).card := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.card_le_card
      apply firstMomentTriples_mono_lower
      have hpwindow := (Finset.mem_filter.mp hp).1
      have hplower := (Finset.mem_Icc.mp hpwindow).1
      omega
    _ = (primeWindow N G).card *
          (firstMomentTriples N D (N - 2 * G)).card := by
      simp

/-- Any pointwise estimate for the standalone first-moment set may be
summed directly to control the complete linear term.  This is the formal
insertion point for the numerical estimate in Lemma 5.1. -/
private lemma totalLinearUpper_le_sum_of_firstMomentTriples_card_le
    {N G D : ℕ} (hN : 0 < N) (F : ℕ → ℕ)
    (hF : ∀ p ∈ primeWindow N G,
      (firstMomentTriples N D (p - N)).card ≤ F p) :
    totalLinearUpper N G D ≤ (primeWindow N G).sum F := by
  calc
    totalLinearUpper N G D ≤
        (primeWindow N G).sum fun p ↦
          (firstMomentTriples N D (p - N)).card :=
      totalLinearUpper_le_sum_firstMomentTriples hN
    _ ≤ (primeWindow N G).sum F := by
      apply Finset.sum_le_sum
      intro p hp
      exact hF p hp

/-- The complete linear term in the exact nested-sum envelope on which
the first-moment estimates are performed. -/
private lemma totalLinearUpper_le_sum_firstMomentEnvelope
    {N G D : ℕ} (hN : 0 < N) :
    totalLinearUpper N G D ≤
      (primeWindow N G).sum fun p ↦
        (firstMomentEnvelope N D (p - N)).card := by
  calc
    totalLinearUpper N G D ≤
        (primeWindow N G).sum fun p ↦
          (firstMomentTriples N D (p - N)).card :=
      totalLinearUpper_le_sum_firstMomentTriples hN
    _ ≤ (primeWindow N G).sum (fun p ↦
        (firstMomentEnvelope N D (p - N)).card) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact firstMomentTriples_card_le_envelope

/-- The finite, exact form of equation (5.1), summed over the prime
window.  All later analytic estimates act only on the two right-hand
sums. -/
private lemma totalCollisionExcess_le_upper (A : Finset ℕ) (G : ℕ)
    (hbad : ¬GrahamBound A) (hG : 0 < G) (hGN : 10 * G ≤ A.card) :
    totalCollisionExcess A G ≤
      totalLinearUpper A.card G (globalD A G) +
        totalBilinearUpper A.card G (globalD A G) := by
  unfold totalCollisionExcess totalLinearUpper totalBilinearUpper
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  exact collisionExcess_le_upper_split A G hbad hG hGN
    (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2

/-- Every coordinate of a reduced represented pair is strictly smaller
than the cardinality.  This is the arithmetic estimate behind `D ≤ N`
in the paper. -/
private lemma reducedPair_coordinates_lt_card (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α d e : ℕ}
    (hp : p.Prime) (hαpos : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hd : d ∈ normalize (representedMultipliers A α (p - α)))
    (he : e ∈ normalize (representedMultipliers A α (p - α))) :
    d / d.gcd e < A.card ∧ e / d.gcd e < A.card := by
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hαpos hαp
  have hR : R.Nonempty := by
    change d ∈ R.image (fun x ↦ x / R.gcd id) at hd
    obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hd
    exact ⟨x, hx⟩
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hαpos
  let c := R.gcd id
  have hc : 0 < c := gcd_pos R hR₀ hR
  have hrepresented : ∀ {x}, x ∈ B →
      0 < x ∧ α * x * c ∈ A ∧ β * x * c ∈ A := by
    intro x hx
    change x ∈ R.image (fun z ↦ z / R.gcd id) at hx
    obtain ⟨z, hzR, rfl⟩ := Finset.mem_image.mp hx
    have hz := (mem_representedMultipliers hαpos).mp hzR
    have hcz : R.gcd id ∣ z := Finset.gcd_dvd hzR
    have hzeq : z / R.gcd id * R.gcd id = z := Nat.div_mul_cancel hcz
    refine ⟨Nat.div_pos (Nat.le_of_dvd hz.1 hcz) hc, ?_, ?_⟩
    · change α * (z / R.gcd id) * R.gcd id ∈ A
      rw [mul_assoc, hzeq]
      exact hz.2.1
    · change β * (z / R.gcd id) * R.gcd id ∈ A
      rw [mul_assoc, hzeq]
      exact hz.2.2
  have hdpos := (hrepresented hd).1
  have hepos := (hrepresented he).1
  let g := d.gcd e
  let d' := d / g
  let e' := e / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hdpos
  have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_left e hdpos) hg
  have he' : 0 < e' := Nat.div_pos (Nat.gcd_le_right d hepos) hg
  have hcop : d'.Coprime e' := Nat.coprime_div_gcd_div_gcd hg
  have hdexpand : d' * (g * c) = d * c := by
    calc
      d' * (g * c) = (d' * g) * c := by simp only [mul_assoc]
      _ = d * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
  have heexpand : e' * (g * c) = e * c := by
    calc
      e' * (g * c) = (e' * g) * c := by simp only [mul_assoc]
      _ = e * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
  rcases factor_closeness_of_counterexample A hbad hαpos hβ hd' he'
      (Nat.mul_pos hg hc) hαβ hcop hsq
      (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact (hrepresented hd).2.1)
      (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact (hrepresented hd).2.2)
      (by rw [mul_assoc, heexpand, ← mul_assoc]; exact (hrepresented he).2.1)
      (by rw [mul_assoc, heexpand, ← mul_assoc]; exact (hrepresented he).2.2) with
    ⟨hdfac, hefac, hαde, hαed, hβde, hβed⟩
  have hdvd : ∀ x ∈ B, x ∣ α * β :=
    normalize_represented_dvd_product A hbad hαpos hβ hαβ hsq hR
  have hd'dvd : d' ∣ α * β :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d e)).trans (hdvd d hd)
  have he'dvd : e' ∣ α * β :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right d e)).trans (hdvd e he)
  have hprodDvd : d' * e' ∣ α * β :=
    hcop.mul_dvd_of_dvd_of_dvd hd'dvd he'dvd
  have hprodLe : d' * e' ≤ α * β :=
    Nat.le_of_dvd (Nat.mul_pos hαpos hβ) hprodDvd
  have hprodLeft : α * β * d' < A.card * A.card * e' := by
    have hm := mul_lt_mul hαde hβde.le
      (Nat.mul_pos hβ (Nat.gcd_pos_of_pos_left β hd'))
      (Nat.zero_le (A.card * e'.gcd α))
    calc
      α * β * d' = α * β * (d'.gcd α * d'.gcd β) :=
        congrArg (fun x ↦ α * β * x) hdfac
      _ = (α * d'.gcd α) * (β * d'.gcd β) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ < (A.card * e'.gcd α) * (A.card * e'.gcd β) := hm
      _ = A.card * A.card * (e'.gcd α * e'.gcd β) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = A.card * A.card * e' :=
        congrArg (fun x ↦ A.card * A.card * x) hefac.symm
  have hprodRight : α * β * e' < A.card * A.card * d' := by
    have hm := mul_lt_mul hαed hβed.le
      (Nat.mul_pos hβ (Nat.gcd_pos_of_pos_left β he'))
      (Nat.zero_le (A.card * d'.gcd α))
    calc
      α * β * e' = α * β * (e'.gcd α * e'.gcd β) :=
        congrArg (fun x ↦ α * β * x) hefac
      _ = (α * e'.gcd α) * (β * e'.gcd β) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ < (A.card * d'.gcd α) * (A.card * d'.gcd β) := hm
      _ = A.card * A.card * (d'.gcd α * d'.gcd β) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = A.card * A.card * d' :=
        congrArg (fun x ↦ A.card * A.card * x) hdfac.symm
  change d' < A.card ∧ e' < A.card
  constructor
  · apply Nat.mul_self_lt_mul_self_iff.mp
    apply (Nat.mul_lt_mul_right he').mp
    have hle := Nat.mul_le_mul_right d' hprodLe
    have hle' : d' * d' * e' ≤ α * β * d' := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hle
    exact hle'.trans_lt hprodLeft
  · apply Nat.mul_self_lt_mul_self_iff.mp
    apply (Nat.mul_lt_mul_right hd').mp
    have hle := Nat.mul_le_mul_right e' hprodLe
    have hle' : e' * e' * d' ≤ α * β * e' := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hle
    exact hle'.trans_lt hprodRight

private lemma square_lt_of_window {N G p α : ℕ} (hG : 0 < G)
    (hsmall : 4 * G ≤ N)
    (hp : p ∈ Finset.Icc (2 * N - 2 * G) (2 * N - G))
    (hα : α ∈ Finset.Icc ((p + 1) / 2) N) :
    N * N < 2 * (α * α) := by
  obtain ⟨hplower, _hpupper⟩ := Finset.mem_Icc.mp hp
  obtain ⟨hαlower, _hαupper⟩ := Finset.mem_Icc.mp hα
  have hGN : G ≤ N := by omega
  have hsub : N - G + G = N := Nat.sub_add_cancel hGN
  have halower : N - G ≤ α := by omega
  have hthree : 3 * G ≤ N - G := by omega
  nlinarith [sq_nonneg ((N - G : ℤ) - 3 * G),
    sq_nonneg ((α : ℤ) - (N - G))]

/-- Discrete form of the first step in Lemma 3.1.  Two positive divisors
of `α` whose coprime reductions satisfy both component-closeness
inequalities must be equal once `(N-α)^2 < α`. -/
private lemma component_eq_of_gap_square_lt {N α x y : ℕ}
    (hα : 0 < α) (hαN : α ≤ N)
    (hx : 0 < x) (hy : 0 < y) (hxα : x ∣ α) (hyα : y ∣ α)
    (hgap : (N - α) * (N - α) < α)
    (hxy : α * (x / x.gcd y) < N * (y / x.gcd y))
    (hyx : α * (y / x.gcd y) < N * (x / x.gcd y)) : x = y := by
  let g := x.gcd y
  let X := x / g
  let Y := y / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left y hx
  have hX : 0 < X := Nat.div_pos (Nat.gcd_le_left y hx) hg
  have hY : 0 < Y := Nat.div_pos (Nat.gcd_le_right x hy) hg
  have hcop : X.Coprime Y := Nat.coprime_div_gcd_div_gcd hg
  have hXα : X ∣ α := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)).trans hxα
  have hYα : Y ∣ α := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)).trans hyα
  have hprod : X * Y ∣ α := hcop.mul_dvd_of_dvd_of_dvd hXα hYα
  have hprodLe : X * Y ≤ α := Nat.le_of_dvd hα hprod
  have hNsplit : N - α + α = N := Nat.sub_add_cancel hαN
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hXY : X < Y :=
      (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_left x y)
        (Nat.gcd_dvd_right x y)).mpr hlt
    have hstep : α * (X + 1) < N * X := by
      apply (Nat.mul_le_mul_left α (Nat.succ_le_iff.mpr hXY)).trans_lt
      simpa only [g, X, Y] using hyx
    have hAX : α < (N - α) * X := by
      rw [← hNsplit, add_mul, mul_add] at hstep
      omega
    have hXsq : X * X ≤ α :=
      (Nat.mul_le_mul_left X hXY.le).trans hprodLe
    have hm := mul_lt_mul hgap hXsq
      (Nat.mul_pos hX hX) (Nat.zero_le α)
    have hm' : ((N - α) * X) * ((N - α) * X) < α * α := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    exact (Nat.not_lt_of_ge (Nat.mul_self_lt_mul_self hAX).le) hm'
  · have hYX : Y < X :=
      (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_right x y)
        (Nat.gcd_dvd_left x y)).mpr hgt
    have hstep : α * (Y + 1) < N * Y := by
      apply (Nat.mul_le_mul_left α (Nat.succ_le_iff.mpr hYX)).trans_lt
      simpa only [g, X, Y] using hxy
    have hAY : α < (N - α) * Y := by
      rw [← hNsplit, add_mul, mul_add] at hstep
      omega
    have hYsq : Y * Y ≤ α :=
      (Nat.mul_le_mul_left Y hYX.le).trans (by
        simpa only [mul_comm X Y] using hprodLe)
    have hm := mul_lt_mul hgap hYsq
      (Nat.mul_pos hY hY) (Nat.zero_le α)
    have hm' : ((N - α) * Y) * ((N - α) * Y) < α * α := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    exact (Nat.not_lt_of_ge (Nat.mul_self_lt_mul_self hAY).le) hm'

/-- Pairwise component inequalities after cancelling the gcd of two
scaled represented multipliers.  This packages the repeated use of Lemma
2.3 needed in the proof of Lemma 3.1. -/
private lemma scaled_component_closeness (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β d e c : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hαβ : α.Coprime β)
    (hsq : A.card * A.card < 2 * (α * α))
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β)
    (hαd : α * d * c ∈ A) (hβd : β * d * c ∈ A)
    (hαe : α * e * c ∈ A) (hβe : β * e * c ∈ A) :
    α * (d.gcd α / (d.gcd α).gcd (e.gcd α)) <
        A.card * (e.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
    α * (e.gcd α / (d.gcd α).gcd (e.gcd α)) <
        A.card * (d.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
    β * (d.gcd β / (d.gcd β).gcd (e.gcd β)) <
        A.card * (e.gcd β / (d.gcd β).gcd (e.gcd β)) ∧
    β * (e.gcd β / (d.gcd β).gcd (e.gcd β)) <
        A.card * (d.gcd β / (d.gcd β).gcd (e.gcd β)) := by
  let g := d.gcd e
  let d' := d / g
  let e' := e / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hd
  have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_left e hd) hg
  have he' : 0 < e' := Nat.div_pos (Nat.gcd_le_right d he) hg
  have hcop : d'.Coprime e' := Nat.coprime_div_gcd_div_gcd hg
  have hdexpand : d' * (g * c) = d * c := by
    calc
      d' * (g * c) = (d' * g) * c := by rw [mul_assoc]
      _ = d * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
  have heexpand : e' * (g * c) = e * c := by
    calc
      e' * (g * c) = (e' * g) * c := by rw [mul_assoc]
      _ = e * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
  have hfac := factor_closeness_of_counterexample A hbad hα hβ hd' he'
    (Nat.mul_pos hg hc) hαβ hcop hsq
    (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact hαd)
    (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact hβd)
    (by rw [mul_assoc, heexpand, ← mul_assoc]; exact hαe)
    (by rw [mul_assoc, heexpand, ← mul_assoc]; exact hβe)
  have hdα : d'.gcd α = d.gcd α / (d.gcd α).gcd (e.gcd α) :=
    gcd_div_gcd_eq_component hαβ hd he hdfac hefac
  have heα : e'.gcd α = e.gcd α / (d.gcd α).gcd (e.gcd α) := by
    simpa only [e', g, Nat.gcd_comm e d,
      Nat.gcd_comm (e.gcd α) (d.gcd α)] using
      (gcd_div_gcd_eq_component hαβ he hd hefac hdfac)
  have hdβ : d'.gcd β = d.gcd β / (d.gcd β).gcd (e.gcd β) :=
    gcd_div_gcd_eq_component hαβ.symm hd he
      (by simpa only [mul_comm] using hdfac)
      (by simpa only [mul_comm] using hefac)
  have heβ : e'.gcd β = e.gcd β / (d.gcd β).gcd (e.gcd β) := by
    simpa only [e', g, Nat.gcd_comm e d,
      Nat.gcd_comm (e.gcd β) (d.gcd β)] using
      (gcd_div_gcd_eq_component hαβ.symm he hd
        (by simpa only [mul_comm] using hefac)
        (by simpa only [mul_comm] using hdfac))
  have hα₁ := hfac.2.2.1
  have hα₂ := hfac.2.2.2.1
  have hβ₁ := hfac.2.2.2.2.1
  have hβ₂ := hfac.2.2.2.2.2
  rw [hdα, heα] at hα₁ hα₂
  rw [hdβ, heβ] at hβ₁ hβ₂
  exact ⟨hα₁, hα₂, hβ₁, hβ₂⟩

/-- Three divisors of `n` with no common factor satisfy the denominator-cleared
three-variable lcm estimate.  Prime by prime, after ordering the three
valuations, the least valuation is zero and the largest is bounded by the
valuation of `n`. -/
private lemma triple_product_dvd_mul_pairwise_gcds {n x y z : ℕ}
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxn : x ∣ n) (hyn : y ∣ n) (hzn : z ∣ n)
    (hxyz : x.gcd (y.gcd z) = 1) :
    x * y * z ∣ n * x.gcd y * x.gcd z * y.gcd z := by
  rw [← Nat.factorization_le_iff_dvd
    (Nat.mul_ne_zero (Nat.mul_ne_zero hx.ne' hy.ne') hz.ne')
    (Nat.mul_ne_zero
      (Nat.mul_ne_zero (Nat.mul_ne_zero hn.ne'
        (Nat.gcd_pos_of_pos_left y hx).ne')
        (Nat.gcd_pos_of_pos_left z hx).ne')
      (Nat.gcd_pos_of_pos_left z hy).ne')]
  intro q
  have hxn' := (Nat.factorization_le_iff_dvd hx.ne' hn.ne').mpr hxn q
  have hyn' := (Nat.factorization_le_iff_dvd hy.ne' hn.ne').mpr hyn q
  have hzn' := (Nat.factorization_le_iff_dvd hz.ne' hn.ne').mpr hzn q
  have hmin := congrArg (fun f : ℕ →₀ ℕ ↦ f q)
    (Nat.factorization_gcd hx.ne'
      (Nat.gcd_pos_of_pos_left z hy).ne')
  rw [hxyz] at hmin
  simp only [Nat.factorization_one, Finsupp.inf_apply,
    Nat.factorization_gcd hy.ne' hz.ne'] at hmin
  rw [Nat.factorization_mul (Nat.mul_ne_zero hx.ne' hy.ne') hz.ne',
    Nat.factorization_mul hx.ne' hy.ne',
    Nat.factorization_mul
      (Nat.mul_ne_zero
        (Nat.mul_ne_zero hn.ne' (Nat.gcd_pos_of_pos_left y hx).ne')
        (Nat.gcd_pos_of_pos_left z hx).ne')
      (Nat.gcd_pos_of_pos_left z hy).ne',
    Nat.factorization_mul
      (Nat.mul_ne_zero hn.ne' (Nat.gcd_pos_of_pos_left y hx).ne')
      (Nat.gcd_pos_of_pos_left z hx).ne',
    Nat.factorization_mul hn.ne' (Nat.gcd_pos_of_pos_left y hx).ne',
    Nat.factorization_gcd hx.ne' hy.ne',
    Nat.factorization_gcd hx.ne' hz.ne',
    Nat.factorization_gcd hy.ne' hz.ne']
  simp only [Finsupp.add_apply, Finsupp.inf_apply]
  omega

/-- The gap estimate used for the three complementary components in Lemma
3.1.  If two ordered divisors of `β` have their larger reduced component
pulled below the smaller one by the factor `N/β`, and
`(N-β)² ≤ 4N`, their coprime reductions are consecutive. -/
private lemma reduced_divisors_diff_eq_one {N β y z : ℕ}
    (hβ : 0 < β) (hβN : β ≤ N)
    (hy : 0 < y) (hz : 0 < z) (hyz : y < z)
    (hyβ : y ∣ β) (hzβ : z ∣ β)
    (hgap : (N - β) * (N - β) ≤ 4 * N)
    (hclose : β * (z / y.gcd z) < N * (y / y.gcd z)) :
    z / y.gcd z = y / y.gcd z + 1 := by
  let g := y.gcd z
  let u := y / g
  let v := z / g
  let k := v - u
  have hg : 0 < g := Nat.gcd_pos_of_pos_left z hy
  have hu : 0 < u := Nat.div_pos (Nat.gcd_le_left z hy) hg
  have hv : 0 < v := Nat.div_pos (Nat.gcd_le_right y hz) hg
  have huv : u < v :=
    (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_left y z)
      (Nat.gcd_dvd_right y z)).mpr hyz
  have hk : 0 < k := Nat.sub_pos_of_lt huv
  have hvsplit : u + k = v := Nat.add_sub_of_le huv.le
  have hcop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  have huβ : u ∣ β := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left y z)).trans hyβ
  have hvβ : v ∣ β := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right y z)).trans hzβ
  have huvβ : u * v ∣ β := hcop.mul_dvd_of_dvd_of_dvd huβ hvβ
  have huvle : u * v ≤ β := Nat.le_of_dvd hβ huvβ
  have hN : 0 < N := hβ.trans_le hβN
  have hNsplit : N - β + β = N := Nat.sub_add_cancel hβN
  have hβk : β * k < (N - β) * u := by
    change β * v < N * u at hclose
    rw [← hvsplit, mul_add, ← hNsplit, add_mul] at hclose
    omega
  have hNk : N * k < (N - β) * v := by
    calc
      N * k = (β + (N - β)) * k := by rw [add_comm, hNsplit]
      _ = β * k + (N - β) * k := by rw [add_mul]
      _ < (N - β) * u + (N - β) * k :=
        Nat.add_lt_add_right hβk _
      _ = (N - β) * v := by rw [← hvsplit, mul_add]
  have hm := mul_lt_mul hβk hNk.le (Nat.mul_pos hN hk)
    (Nat.zero_le ((N - β) * u))
  have hm' : β * N * (k * k) <
      ((N - β) * (N - β)) * (u * v) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
  have hright : ((N - β) * (N - β)) * (u * v) ≤
      (4 * N) * β := Nat.mul_le_mul hgap huvle
  have hkk : k * k < 4 := by
    apply (Nat.mul_lt_mul_left (Nat.mul_pos hβ hN)).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm'.trans_le hright
  have hkone : k = 1 := by
    have hklt : k < 2 := Nat.mul_self_lt_mul_self_iff.mp (by
      simpa only [show 2 * 2 = 4 by norm_num] using hkk)
    omega
  simpa only [u, v, k, hkone] using hvsplit.symm

/-- Denominator-free form of the final `25/8` optimization in Lemma 3.1.
Here `a,c` are the two adjacent gcds and `b=a+c` is the outer gcd.
The displayed strict inequality is exactly the lower bound for the lcm
after all positive denominators have been cleared. -/
private lemma spacing_polynomial_contradiction {N δ a b c : ℕ}
    (hN : 10 ≤ N) (hδ : 0 < δ) (ha : 0 < a) (hc : 0 < c)
    (hb : a + c = b) (hgap : δ * δ ≤ 4 * N)
    (hmain : (b * N) * (b * N) <
      (a * c * δ) * (δ * δ) + (b * N) * (c * δ)) : False := by
  have hNpos : 0 < N := by omega
  have hbpos : 0 < b := by omega
  let K := 4 * a + b
  have hfirst : (a * c * δ) * (δ * δ) ≤
      (a * c * δ) * (4 * N) := Nat.mul_le_mul_left _ hgap
  have hsmall : b * b * N < c * δ * K := by
    apply (Nat.mul_lt_mul_left hNpos).mp
    have ht := hmain.trans_le (Nat.add_le_add_right hfirst _)
    simpa only [K, mul_assoc, mul_comm, mul_left_comm,
      Nat.mul_add, Nat.add_mul] using ht
  have hsquare := Nat.mul_self_lt_mul_self hsmall
  have hright : (c * δ * K) * (c * δ * K) ≤
      4 * N * (c * c * (K * K)) := by
    have := Nat.mul_le_mul_left (c * c * (K * K)) hgap
    simpa only [mul_assoc, mul_comm, mul_left_comm] using this
  have hcore : b * b * b * b * N < 4 * c * c * (K * K) := by
    apply (Nat.mul_lt_mul_left hNpos).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      hsquare.trans_le hright
  have hmax : 16 * c * K ≤ 25 * (b * b) := by
    have hs : 0 ≤ (5 * (a : ℤ) - 3 * (c : ℤ)) ^ 2 := sq_nonneg _
    dsimp only [K]
    nlinarith
  have hmaxsq := Nat.mul_le_mul hmax hmax
  have hmaxsq' : 256 * (c * c * (K * K)) ≤
      625 * (b * b * b * b) := by
    calc
      256 * (c * c * (K * K)) = (16 * c * K) * (16 * c * K) := by ring
      _ ≤ (25 * (b * b)) * (25 * (b * b)) := hmaxsq
      _ = 625 * (b * b * b * b) := by ring
  have hscaled := (Nat.mul_lt_mul_left (by norm_num : 0 < 256)).mpr hcore
  have hfinal : 256 * N * (b * b * b * b) <
      2500 * (b * b * b * b) := by
    calc
      256 * N * (b * b * b * b) =
          256 * (b * b * b * b * N) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
      _ < 256 * (4 * c * c * (K * K)) := hscaled
      _ ≤ 4 * (625 * (b * b * b * b)) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_le_mul_left 4 hmaxsq'
      _ = 2500 * (b * b * b * b) := by ring
  have hpowpos : 0 < b * b * b * b := by positivity
  have : 256 * N < 2500 := by
    apply (Nat.mul_lt_mul_right hpowpos).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hfinal
  omega

/-- Pure divisor form of Balasubramanian--Soundararajan, Lemma 3.1.
Three increasingly ordered divisors with gcd one cannot all satisfy the
pairwise complementary-component inequalities in the short prime window. -/
private lemma no_three_close_divisors {N β y₁ y₂ y₃ : ℕ}
    (hN : 10 ≤ N) (hβ : 0 < β) (hβN : β < N)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hy₃ : 0 < y₃)
    (h₁₂ : y₁ < y₂) (h₂₃ : y₂ < y₃)
    (hy₁β : y₁ ∣ β) (hy₂β : y₂ ∣ β) (hy₃β : y₃ ∣ β)
    (hgcd : y₁.gcd (y₂.gcd y₃) = 1)
    (hgap : (N - β) * (N - β) ≤ 4 * N)
    (hclose₁₂ : β * (y₂ / y₁.gcd y₂) < N * (y₁ / y₁.gcd y₂))
    (hclose₁₃ : β * (y₃ / y₁.gcd y₃) < N * (y₁ / y₁.gcd y₃))
    (hclose₂₃ : β * (y₃ / y₂.gcd y₃) < N * (y₂ / y₂.gcd y₃)) :
    False := by
  let a := y₁.gcd y₂
  let b := y₁.gcd y₃
  let c := y₂.gcd y₃
  let δ := N - β
  have ha : 0 < a := Nat.gcd_pos_of_pos_left y₂ hy₁
  have hb : 0 < b := Nat.gcd_pos_of_pos_left y₃ hy₁
  have hc : 0 < c := Nat.gcd_pos_of_pos_left y₃ hy₂
  have hδ : 0 < δ := Nat.sub_pos_of_lt hβN
  have hdiff₁₂ : y₂ / a = y₁ / a + 1 := by
    exact reduced_divisors_diff_eq_one hβ hβN.le hy₁ hy₂ h₁₂
      hy₁β hy₂β hgap hclose₁₂
  have hdiff₁₃ : y₃ / b = y₁ / b + 1 := by
    exact reduced_divisors_diff_eq_one hβ hβN.le hy₁ hy₃ (h₁₂.trans h₂₃)
      hy₁β hy₃β hgap hclose₁₃
  have hdiff₂₃ : y₃ / c = y₂ / c + 1 := by
    exact reduced_divisors_diff_eq_one hβ hβN.le hy₂ hy₃ h₂₃
      hy₂β hy₃β hgap hclose₂₃
  have hy₂eq : y₂ = y₁ + a := by
    calc
      y₂ = (y₂ / a) * a := (Nat.div_mul_cancel (Nat.gcd_dvd_right y₁ y₂)).symm
      _ = (y₁ / a + 1) * a := by rw [hdiff₁₂]
      _ = y₁ + a := by rw [add_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left y₁ y₂)]; simp
  have hy₃eq₁ : y₃ = y₁ + b := by
    calc
      y₃ = (y₃ / b) * b := (Nat.div_mul_cancel (Nat.gcd_dvd_right y₁ y₃)).symm
      _ = (y₁ / b + 1) * b := by rw [hdiff₁₃]
      _ = y₁ + b := by rw [add_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left y₁ y₃)]; simp
  have hy₃eq₂ : y₃ = y₂ + c := by
    calc
      y₃ = (y₃ / c) * c := (Nat.div_mul_cancel (Nat.gcd_dvd_right y₂ y₃)).symm
      _ = (y₂ / c + 1) * c := by rw [hdiff₂₃]
      _ = y₂ + c := by rw [add_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left y₂ y₃)]; simp
  have habc : a + c = b := by omega
  have hNsplit : δ + β = N := Nat.sub_add_cancel hβN.le
  have hβb : β * b < δ * y₁ := by
    have hbase : β < δ * (y₁ / b) := by
      change β * (y₃ / b) < N * (y₁ / b) at hclose₁₃
      rw [hdiff₁₃] at hclose₁₃
      rw [← hNsplit, add_mul, mul_add] at hclose₁₃
      omega
    have hm := (Nat.mul_lt_mul_right hb).mpr hbase
    calc
      β * b < (δ * (y₁ / b)) * b := hm
      _ = δ * ((y₁ / b) * b) := by rw [mul_assoc]
      _ = δ * y₁ := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left y₁ y₃)]
  have hNb : N * b < δ * y₃ := by
    calc
      N * b = (β + δ) * b := by rw [add_comm, hNsplit]
      _ = β * b + δ * b := by rw [add_mul]
      _ < δ * y₁ + δ * b := Nat.add_lt_add_right hβb _
      _ = δ * y₃ := by rw [hy₃eq₁, mul_add]
  have hNbmid : N * b < δ * y₂ + δ * c := by
    simpa only [hy₃eq₂, mul_add] using hNb
  have hprodDvd : y₁ * y₂ * y₃ ∣ β * a * b * c := by
    exact triple_product_dvd_mul_pairwise_gcds hβ hy₁ hy₂ hy₃
      hy₁β hy₂β hy₃β hgcd
  have hprodLe : y₁ * y₂ * y₃ ≤ β * a * b * c :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hβ ha) hb) hc) hprodDvd
  let P := (β * b) * (N * b)
  have hP : 0 < P := by positivity
  have hpair : P < (δ * y₁) * (δ * y₃) := by
    exact mul_lt_mul hβb hNb.le (Nat.mul_pos (by omega) hb)
      (Nat.zero_le (δ * y₁))
  have hpairY₂ : P * (δ * y₂) <
      ((δ * y₁) * (δ * y₃)) * (δ * y₂) := by
    exact (Nat.mul_lt_mul_right (Nat.mul_pos hδ hy₂)).mpr hpair
  have hlarge : P * (N * b) <
      (δ * δ * δ) * (y₁ * y₂ * y₃) + P * (δ * c) := by
    calc
      P * (N * b) < P * (δ * y₂ + δ * c) :=
        (Nat.mul_lt_mul_left hP).mpr hNbmid
      _ = P * (δ * y₂) + P * (δ * c) := by rw [mul_add]
      _ < ((δ * y₁) * (δ * y₃)) * (δ * y₂) + P * (δ * c) :=
        Nat.add_lt_add_right hpairY₂ _
      _ = (δ * δ * δ) * (y₁ * y₂ * y₃) + P * (δ * c) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
  have hlarge' : P * (N * b) <
      (δ * δ * δ) * (β * a * b * c) + P * (δ * c) :=
    hlarge.trans_le (Nat.add_le_add_right
      (Nat.mul_le_mul_left (δ * δ * δ) hprodLe) _)
  have hmain : (b * N) * (b * N) <
      (a * c * δ) * (δ * δ) + (b * N) * (c * δ) := by
    apply (Nat.mul_lt_mul_left (Nat.mul_pos hβ hb)).mp
    calc
      (β * b) * ((b * N) * (b * N)) = P * (N * b) := by
        simp only [P]
        ring
      _ < (δ * δ * δ) * (β * a * b * c) + P * (δ * c) := hlarge'
      _ = (β * b) *
          ((a * c * δ) * (δ * δ) + (b * N) * (c * δ)) := by
        simp only [P]
        ring
  exact spacing_polynomial_contradiction hN hδ ha hc habc hgap hmain

private lemma exists_increasing_permutation {x y z : ℕ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ a b c, a < b ∧ b < c ∧ ({a, b, c} : Finset ℕ) = {x, y, z} := by
  by_cases h₁ : x < y
  · by_cases h₂ : y < z
    · exact ⟨x, y, z, h₁, h₂, rfl⟩
    · by_cases h₃ : x < z
      · refine ⟨x, z, y, h₃, by omega, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨z, x, y, by omega, h₁, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
  · by_cases h₂ : x < z
    · refine ⟨y, x, z, by omega, h₂, ?_⟩
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · by_cases h₃ : y < z
      · refine ⟨y, z, x, h₃, by omega, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨z, y, x, by omega, by omega, ?_⟩
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto

/-- Balasubramanian--Soundararajan, Lemma 3.1, with its elementary window
consequences exposed as hypotheses.  The later prime-window adapter proves
these inequalities directly from the endpoints. -/
private lemma representationCount_le_two_of_gaps (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hα : 0 < α) (hαN : α ≤ A.card)
    (hαp : α < p) (hβN : p - α < A.card)
    (hsq : A.card * A.card < 2 * (α * α))
    (hgapα : (A.card - α) * (A.card - α) < α)
    (hgapβ : (A.card - (p - α)) * (A.card - (p - α)) ≤ 4 * A.card) :
    representationCount A p α ≤ 2 := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  change R.card ≤ 2
  by_contra hcard
  have hthree : 2 < R.card := by omega
  obtain ⟨x, hxR, y, hyR, z, hzR, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hthree
  obtain ⟨e₁, e₂, e₃, he₁₂, he₂₃, hperm⟩ :=
    exists_increasing_permutation hxy hxz hyz
  have hsub : ({e₁, e₂, e₃} : Finset ℕ) ⊆ R := by
    rw [hperm]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hxR, hyR, hzR⟩
  have he₁R : e₁ ∈ R := hsub (by simp)
  have he₂R : e₂ ∈ R := hsub (by simp)
  have he₃R : e₃ ∈ R := hsub (by simp)
  have he₁data := (mem_representedMultipliers hα).mp he₁R
  have he₂data := (mem_representedMultipliers hα).mp he₂R
  have he₃data := (mem_representedMultipliers hα).mp he₃R
  let S : Finset ℕ := {e₁, e₂, e₃}
  let c := S.gcd id
  have hS₀ : 0 ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨he₁data.1.ne, he₂data.1.ne, he₃data.1.ne⟩
  have hSne : S.Nonempty := ⟨e₁, by simp [S]⟩
  have hc : 0 < c := gcd_pos S hS₀ hSne
  have he₁S : e₁ ∈ S := by simp [S]
  have he₂S : e₂ ∈ S := by simp [S]
  have he₃S : e₃ ∈ S := by simp [S]
  have hce₁ : c ∣ e₁ := Finset.gcd_dvd he₁S
  have hce₂ : c ∣ e₂ := Finset.gcd_dvd he₂S
  have hce₃ : c ∣ e₃ := Finset.gcd_dvd he₃S
  let d₁ := e₁ / c
  let d₂ := e₂ / c
  let d₃ := e₃ / c
  have hd₁ : 0 < d₁ := Nat.div_pos (Nat.le_of_dvd he₁data.1 hce₁) hc
  have hd₂ : 0 < d₂ := Nat.div_pos (Nat.le_of_dvd he₂data.1 hce₂) hc
  have hd₃ : 0 < d₃ := Nat.div_pos (Nat.le_of_dvd he₃data.1 hce₃) hc
  have hd₁₂ : d₁ < d₂ :=
    (Nat.div_lt_div_right hc.ne' hce₁ hce₂).mpr he₁₂
  have hd₂₃ : d₂ < d₃ :=
    (Nat.div_lt_div_right hc.ne' hce₂ hce₃).mpr he₂₃
  have hd₁c : d₁ * c = e₁ := Nat.div_mul_cancel hce₁
  have hd₂c : d₂ * c = e₂ := Nat.div_mul_cancel hce₂
  have hd₃c : d₃ * c = e₃ := Nat.div_mul_cancel hce₃
  have hRne : R.Nonempty := ⟨e₁, he₁R⟩
  have hRgcd_c : R.gcd id ∣ c := by
    apply Finset.dvd_gcd
    intro e heS
    exact Finset.gcd_dvd (hsub heS)
  have hdvd : ∀ i ∈ ({d₁, d₂, d₃} : Finset ℕ), i ∣ α * β := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact (Nat.div_dvd_div_left hce₁ hRgcd_c).trans
        (normalize_represented_dvd_product A hbad hα hβ hαβ hsq hRne
          (e₁ / R.gcd id) (normalize_mem R he₁R))
    · exact (Nat.div_dvd_div_left hce₂ hRgcd_c).trans
        (normalize_represented_dvd_product A hbad hα hβ hαβ hsq hRne
          (e₂ / R.gcd id) (normalize_mem R he₂R))
    · exact (Nat.div_dvd_div_left hce₃ hRgcd_c).trans
        (normalize_represented_dvd_product A hbad hα hβ hαβ hsq hRne
          (e₃ / R.gcd id) (normalize_mem R he₃R))
  have hfac : ∀ i ∈ ({d₁, d₂, d₃} : Finset ℕ),
      i = i.gcd α * i.gcd β := by
    intro i hi
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr
      (hdvd i hi)).symm
  have hfac₁ := hfac d₁ (by simp)
  have hfac₂ := hfac d₂ (by simp)
  have hfac₃ := hfac d₃ (by simp)
  have hmemα₁ : α * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.1
  have hmemβ₁ : β * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.2
  have hmemα₂ : α * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.1
  have hmemβ₂ : β * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.2
  have hmemα₃ : α * d₃ * c ∈ A := by rw [mul_assoc, hd₃c]; exact he₃data.2.1
  have hmemβ₃ : β * d₃ * c ∈ A := by rw [mul_assoc, hd₃c]; exact he₃data.2.2
  have hclose₁₂ := scaled_component_closeness A hbad hα hβ hd₁ hd₂ hc
    hαβ hsq hfac₁ hfac₂ hmemα₁ hmemβ₁ hmemα₂ hmemβ₂
  have hclose₁₃ := scaled_component_closeness A hbad hα hβ hd₁ hd₃ hc
    hαβ hsq hfac₁ hfac₃ hmemα₁ hmemβ₁ hmemα₃ hmemβ₃
  have hclose₂₃ := scaled_component_closeness A hbad hα hβ hd₂ hd₃ hc
    hαβ hsq hfac₂ hfac₃ hmemα₂ hmemβ₂ hmemα₃ hmemβ₃
  have hX₁₂ : d₁.gcd α = d₂.gcd α :=
    component_eq_of_gap_square_lt hα hαN
      (Nat.gcd_pos_of_pos_left α hd₁) (Nat.gcd_pos_of_pos_left α hd₂)
      (Nat.gcd_dvd_right d₁ α) (Nat.gcd_dvd_right d₂ α)
      hgapα hclose₁₂.1 hclose₁₂.2.1
  have hX₁₃ : d₁.gcd α = d₃.gcd α :=
    component_eq_of_gap_square_lt hα hαN
      (Nat.gcd_pos_of_pos_left α hd₁) (Nat.gcd_pos_of_pos_left α hd₃)
      (Nat.gcd_dvd_right d₁ α) (Nat.gcd_dvd_right d₃ α)
      hgapα hclose₁₃.1 hclose₁₃.2.1
  have hgcdNorm : d₁.gcd (d₂.gcd d₃) = 1 := by
    have hg := Finset.gcd_div_id_eq_one he₁S he₁data.1.ne'
    change S.gcd (fun e ↦ e / S.gcd id) = 1 at hg
    simpa only [S, c, d₁, d₂, d₃, Finset.gcd_insert,
      Finset.gcd_singleton, id_eq, normalize_eq, gcd_eq_nat_gcd] using hg
  have hXone : d₁.gcd α = 1 := by
    apply Nat.dvd_one.mp
    rw [← hgcdNorm]
    apply Nat.dvd_gcd (Nat.gcd_dvd_left d₁ α)
    apply Nat.dvd_gcd
    · rw [hX₁₂]
      exact Nat.gcd_dvd_left d₂ α
    · rw [hX₁₃]
      exact Nat.gcd_dvd_left d₃ α
  have hX₂one : d₂.gcd α = 1 := hX₁₂.symm.trans hXone
  have hX₃one : d₃.gcd α = 1 := hX₁₃.symm.trans hXone
  have hY₁ : d₁.gcd β = d₁ := by simpa [hXone] using hfac₁.symm
  have hY₂ : d₂.gcd β = d₂ := by simpa [hX₂one] using hfac₂.symm
  have hY₃ : d₃.gcd β = d₃ := by simpa [hX₃one] using hfac₃.symm
  have hd₁β : d₁ ∣ β := hY₁ ▸ Nat.gcd_dvd_right d₁ β
  have hd₂β : d₂ ∣ β := hY₂ ▸ Nat.gcd_dvd_right d₂ β
  have hd₃β : d₃ ∣ β := hY₃ ▸ Nat.gcd_dvd_right d₃ β
  apply no_three_close_divisors hN hβ hβN hd₁ hd₂ hd₃ hd₁₂ hd₂₃
    hd₁β hd₂β hd₃β hgcdNorm hgapβ
  · simpa only [hY₁, hY₂] using hclose₁₂.2.2.2
  · simpa only [hY₁, hY₃] using hclose₁₃.2.2.2
  · simpa only [hY₂, hY₃] using hclose₂₃.2.2.2

/-- The square-root-free prime-window formulation of Lemma 3.1.  The
hypothesis on `2N-p` is equivalent to `p ≥ 2N-2√N`. -/
private lemma representationCount_le_two_of_window (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hpupper : p ≤ 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ 4 * A.card)
    (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card) :
    representationCount A p α ≤ 2 := by
  let N := A.card
  let t := 2 * N - p
  obtain ⟨hαlower, hαN⟩ := Finset.mem_Icc.mp hαJ
  have htadd : t + p = 2 * N := Nat.sub_add_cancel hpupper
  have hpN : N < p := by
    nlinarith [sq_nonneg ((t : ℤ) - N)]
  have hpne : p ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpne
  have hp2α : p < 2 * α := by
    omega
  have hα : 0 < α := by omega
  have hαp : α < p := hαN.trans_lt hpN
  have hβN : p - α < N := by omega
  have hδadd : N - α + α = N := Nat.sub_add_cancel hαN
  have h2δ : 2 * (N - α) < t := by omega
  have hgapα : (N - α) * (N - α) < α := by
    nlinarith
  have hsq : N * N < 2 * (α * α) := by
    nlinarith [sq_nonneg ((N : ℤ) - 3 * (N - α))]
  have hδβle : N - (p - α) ≤ t := by omega
  have hgapβ : (N - (p - α)) * (N - (p - α)) ≤ 4 * N := by
    exact (Nat.mul_self_le_mul_self hδβle).trans hpwindow
  apply representationCount_le_two_of_gaps A hbad hp hN hα hαN hαp hβN
  · simpa only [N] using hsq
  · simpa only [N] using hgapα
  · simpa only [N] using hgapβ

private def primeFold (p q : ℕ) : ℕ := max q (p - q)

private lemma primeFold_injective_on_odd_primes {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp2 : 2 < p) (hq2 : 2 < q) (hr2 : 2 < r)
    (hqp : q ≤ p) (hrp : r ≤ p)
    (hfold : primeFold p q = primeFold p r) : q = r := by
  have hor : q = r ∨ q + r = p := by
    dsimp only [primeFold] at hfold
    by_cases hqside : q ≤ p - q
    · rw [max_eq_right hqside] at hfold
      by_cases hrside : r ≤ p - r
      · rw [max_eq_right hrside] at hfold
        left
        omega
      · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hrside))] at hfold
        right
        omega
    · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hqside))] at hfold
      by_cases hrside : r ≤ p - r
      · rw [max_eq_right hrside] at hfold
        right
        omega
      · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hrside))] at hfold
        left
        exact hfold
  rcases hor with h | hsum
  · exact h
  · obtain ⟨kp, hkp⟩ := hp.odd_of_ne_two (by omega)
    obtain ⟨kq, hkq⟩ := hq.odd_of_ne_two (by omega)
    obtain ⟨kr, hkr⟩ := hr.odd_of_ne_two (by omega)
    omega

private lemma primeFold_mem_J {N p q : ℕ} (hpN : N < p) (hpupper : p ≤ 2 * N)
    (hq : q ∈ Finset.Icc (p - N) N) :
    primeFold p q ∈ Finset.Icc ((p + 1) / 2) N := by
  obtain ⟨hqlower, hqupper⟩ := Finset.mem_Icc.mp hq
  have hqp : q ≤ p := hqupper.trans hpN.le
  have hsubupper : p - q ≤ N := by omega
  apply Finset.mem_Icc.mpr
  constructor
  · dsimp only [primeFold]
    omega
  · exact max_le hqupper hsubupper

/-- A large prime divisor in the short interval produces an empty
representation fiber, by Boyle's prime-divisor exclusion. -/
private lemma representationCount_primeFold_eq_zero (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p q : ℕ} (hq : q.Prime) (hqp : q ≤ p)
    (hlarge : A.card ≤ 2 * q) :
    representationCount A p (primeFold p q) = 0 := by
  rw [representationCount, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨d, hd⟩
  have hαpos : 0 < primeFold p q :=
    lt_max_of_lt_left hq.pos
  have hdata := (mem_representedMultipliers hαpos).mp hd
  by_cases hside : q ≤ p - q
  · have hfold : primeFold p q = p - q := max_eq_right hside
    have hcomp : p - primeFold p q = q := by rw [hfold]; omega
    have hmem : q * d ∈ A := by simpa only [hcomp] using hdata.2.2
    exact (prime_not_dvd_of_card_le_two_mul A h₀ hgcd hbad hq hlarge hmem)
      (dvd_mul_right q d)
  · have hfold : primeFold p q = q :=
      max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hside))
    have hmem : q * d ∈ A := by simpa only [hfold] using hdata.2.1
    exact (prime_not_dvd_of_card_le_two_mul A h₀ hgcd hbad hq hlarge hmem)
      (dvd_mul_right q d)

/-- Lemma 2.2 in finite-set form: primes in `[p-N,N]` inject into the
empty fibers of `r_p`. -/
private lemma primeInterval_card_le_zeroFibers (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p : ℕ} (hp : p.Prime) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hlower : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q)
    (hq2 : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q) :
    ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card ≤
      ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        representationCount A p α = 0).card := by
  classical
  let Q := (Finset.Icc (p - A.card) A.card).filter Nat.Prime
  let Z := (Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
    representationCount A p α = 0
  apply Finset.card_le_card_of_injOn (primeFold p)
  · intro q hqQ
    have hqI := (Finset.mem_filter.mp hqQ).1
    have hqprime := (Finset.mem_filter.mp hqQ).2
    apply Finset.mem_filter.mpr
    refine ⟨primeFold_mem_J hpN hpupper.le hqI, ?_⟩
    exact representationCount_primeFold_eq_zero A h₀ hgcd hbad hqprime
      ((Finset.mem_Icc.mp hqI).2.trans hpN.le) (hlower q hqQ)
  · intro q hqQ r hrQ hfold
    have hqI := (Finset.mem_filter.mp hqQ).1
    have hrI := (Finset.mem_filter.mp hrQ).1
    exact primeFold_injective_on_odd_primes hp
      (Finset.mem_filter.mp hqQ).2 (Finset.mem_filter.mp hrQ).2
      (by omega) (hq2 q hqQ) (hq2 r hrQ)
      ((Finset.mem_Icc.mp hqI).2.trans hpN.le)
      ((Finset.mem_Icc.mp hrI).2.trans hpN.le) hfold

/-- In the analytic outer window, every prime in `[p-N,N]` is large
enough for Boyle's exclusion theorem.  Lemma 2.1 then turns these forced
zero fibers into collision excess. -/
private lemma primeInterval_card_le_collisionExcess_of_window
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    {p : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) :
    ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card ≤
      collisionExcess A p := by
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hpupper : p < 2 * A.card := by
    have hi := (Finset.mem_Icc.mp hpwin).2
    omega
  have hlower : ∀ q ∈
      (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q := by
    intro q hq
    have hqI := (Finset.mem_filter.mp hq).1
    have hqlo := (Finset.mem_Icc.mp hqI).1
    have hpLo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hq2 : ∀ q ∈
      (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q := by
    intro q hq
    have hqI := (Finset.mem_filter.mp hq).1
    have hqlo := (Finset.mem_Icc.mp hqI).1
    have hpLo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hzero := primeInterval_card_le_zeroFibers
    A h₀ hgcd hbad hp hpN hpupper hlower hq2
  have hexcess := zero_card_le_representation_excess
    A h₀ hgcd hbad hp hpN hpupper
  exact hzero.trans (by simpa only [collisionExcess] using hexcess)

private lemma basicPrimeCollisionLower_le_totalCollisionExcess
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card) :
    basicPrimeCollisionLower A.card G ≤ totalCollisionExcess A G := by
  unfold basicPrimeCollisionLower totalCollisionExcess
  apply Finset.sum_le_sum
  intro p hp
  exact primeInterval_card_le_collisionExcess_of_window
    A G h₀ hgcd hbad hG hGN
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2

/-- Once every nontrivial fiber has multiplicity exactly two, more forced
empty fibers than possible collision fibers contradict Lemma 2.1. -/
private lemma grahamBound_of_collision_support_lt_primeInterval (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) {p : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ 4 * A.card)
    (hlower : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q)
    (hq2 : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q)
    (hsupport : ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        2 ≤ representationCount A p α).card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card) :
    GrahamBound A := by
  by_contra hbad
  let J := Finset.Icc ((p + 1) / 2) A.card
  let M := J.filter fun α ↦ 2 ≤ representationCount A p α
  have hmult : ∀ α ∈ M, representationCount A p α ≤ 2 := by
    intro α hαM
    exact representationCount_le_two_of_window A hbad hp hN hpupper.le hpwindow
      (Finset.mem_filter.mp hαM).1
  have hexcess : M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card := by
    calc
      M.sum (fun α ↦ representationCount A p α - 1) ≤ M.sum (fun _ ↦ 1) := by
        apply Finset.sum_le_sum
        intro α hαM
        have := hmult α hαM
        omega
      _ = M.card := by simp
  have hprimeZero := primeInterval_card_le_zeroFibers A h₀ hgcd hbad hp hpN hpupper
    hlower hq2
  have hzeroExcess := zero_card_le_representation_excess A h₀ hgcd hbad hp hpN hpupper
  change M.card < _ at hsupport
  change _ ≤ (J.filter fun α ↦ 2 ≤ representationCount A p α).sum
    (fun α ↦ representationCount A p α - 1) at hzeroExcess
  change M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card at hexcess
  exact (not_lt_of_ge (hprimeZero.trans (hzeroExcess.trans hexcess))) hsupport

/-- A small algebraic estimate used in the collision-shape argument. -/
private lemma square_lt_twice_of_gap {N α : ℕ} (hN : 10 ≤ N)
    (hα : 0 < α) (hαN : α ≤ N) (hgap : (N - α) * (N - α) < α) :
    N * N < 2 * (α * α) := by
  have hδadd : N - α + α = N := Nat.sub_add_cancel hαN
  nlinarith [sq_nonneg ((N : ℤ) - 3 * (N - α))]

/-- Shape of every collision fiber in Lemma 3.3.  The window is encoded
without square roots. -/
private lemma collision_fiber_shape (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α j : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hj : j ≤ 3) (hpupper : p ≤ 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ (j + 1) * A.card)
    (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hr : 2 ≤ representationCount A p α) :
    ∃ ell Y : ℕ, 1 ≤ ell ∧ 1 ≤ Y ∧ ell ≤ j ∧
      p - α = ell * Y * (Y + 1) := by
  classical
  let N := A.card
  let β := p - α
  let t := 2 * N - p
  obtain ⟨hαlower, hαN⟩ := Finset.mem_Icc.mp hαJ
  have hwindow4 : t * t ≤ 4 * N := by
    exact hpwindow.trans (Nat.mul_le_mul_right N (by omega))
  have htadd : t + p = 2 * N := Nat.sub_add_cancel hpupper
  have hpN : N < p := by
    nlinarith [sq_nonneg ((t : ℤ) - N)]
  have hpne : p ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpne
  have hp2α : p < 2 * α := by omega
  have hα : 0 < α := by omega
  have hαp : α < p := hαN.trans_lt hpN
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hβN : β < N := by omega
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hδadd : N - α + α = N := Nat.sub_add_cancel hαN
  have h2δ : 2 * (N - α) < t := by omega
  have hgapα : (N - α) * (N - α) < α := by nlinarith
  have hsq : N * N < 2 * (α * α) := by
    exact square_lt_twice_of_gap hN hα hαN hgapα
  have hgapβ : (N - β) * (N - β) ≤ 4 * N := by
    have hle : N - β ≤ t := by omega
    exact (Nat.mul_self_le_mul_self hle).trans hwindow4
  let R := representedMultipliers A α β
  change 2 ≤ R.card at hr
  have hRtwo : 1 < R.card := hr
  obtain ⟨x, hxR, y, hyR, hxy⟩ := Finset.one_lt_card.mp hRtwo
  have hxdata := (mem_representedMultipliers hα).mp hxR
  have hydata := (mem_representedMultipliers hα).mp hyR
  let e₁ := min x y
  let e₂ := max x y
  have he₁R : e₁ ∈ R := by
    change min x y ∈ R
    rcases min_choice x y with h | h <;> rw [h]
    · exact hxR
    · exact hyR
  have he₂R : e₂ ∈ R := by
    change max x y ∈ R
    rcases max_choice x y with h | h <;> rw [h]
    · exact hxR
    · exact hyR
  have he₁data := (mem_representedMultipliers hα).mp he₁R
  have he₂data := (mem_representedMultipliers hα).mp he₂R
  have he₁₂ : e₁ < e₂ := by
    dsimp only [e₁, e₂]
    omega
  let c := e₁.gcd e₂
  let d₁ := e₁ / c
  let d₂ := e₂ / c
  have hc : 0 < c := Nat.gcd_pos_of_pos_left e₂ he₁data.1
  have hd₁ : 0 < d₁ := Nat.div_pos (Nat.gcd_le_left e₂ he₁data.1) hc
  have hd₂ : 0 < d₂ := Nat.div_pos (Nat.gcd_le_right e₁ he₂data.1) hc
  have hd₁₂ : d₁ < d₂ :=
    (Nat.div_lt_div_right hc.ne' (Nat.gcd_dvd_left e₁ e₂)
      (Nat.gcd_dvd_right e₁ e₂)).mpr he₁₂
  have hcop : d₁.Coprime d₂ := Nat.coprime_div_gcd_div_gcd hc
  have hd₁c : d₁ * c = e₁ := Nat.div_mul_cancel (Nat.gcd_dvd_left e₁ e₂)
  have hd₂c : d₂ * c = e₂ := Nat.div_mul_cancel (Nat.gcd_dvd_right e₁ e₂)
  have hmemα₁ : α * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.1
  have hmemβ₁ : β * d₁ * c ∈ A := by rw [mul_assoc, hd₁c]; exact he₁data.2.2
  have hmemα₂ : α * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.1
  have hmemβ₂ : β * d₂ * c ∈ A := by rw [mul_assoc, hd₂c]; exact he₂data.2.2
  have hfac := factor_closeness_of_counterexample A hbad hα hβ hd₁ hd₂ hc
    hαβ hcop hsq hmemα₁ hmemβ₁ hmemα₂ hmemβ₂
  have hXcop : (d₁.gcd α).Coprime (d₂.gcd α) :=
    (hcop.of_dvd_left (Nat.gcd_dvd_left d₁ α)).of_dvd_right
      (Nat.gcd_dvd_left d₂ α)
  have hXeq : d₁.gcd α = d₂.gcd α :=
    component_eq_of_gap_square_lt hα hαN
      (Nat.gcd_pos_of_pos_left α hd₁) (Nat.gcd_pos_of_pos_left α hd₂)
      (Nat.gcd_dvd_right d₁ α) (Nat.gcd_dvd_right d₂ α)
      hgapα
      (by simpa only [hXcop.gcd_eq_one, Nat.div_one] using hfac.2.2.1)
      (by simpa only [hXcop.gcd_eq_one, Nat.div_one] using hfac.2.2.2.1)
  have hXone : d₁.gcd α = 1 := by
    apply Nat.dvd_one.mp
    rw [← hcop.gcd_eq_one]
    apply Nat.dvd_gcd (Nat.gcd_dvd_left d₁ α)
    rw [hXeq]
    exact Nat.gcd_dvd_left d₂ α
  have hX₂one : d₂.gcd α = 1 := hXeq.symm.trans hXone
  have hY₁ : d₁.gcd β = d₁ := by simpa [hXone] using hfac.1.symm
  have hY₂ : d₂.gcd β = d₂ := by simpa [hX₂one] using hfac.2.1.symm
  have hd₁β : d₁ ∣ β := hY₁ ▸ Nat.gcd_dvd_right d₁ β
  have hd₂β : d₂ ∣ β := hY₂ ▸ Nat.gcd_dvd_right d₂ β
  have hdiff : d₂ = d₁ + 1 := by
    have h := reduced_divisors_diff_eq_one hβ hβN.le hd₁ hd₂ hd₁₂
      hd₁β hd₂β hgapβ
      (by simpa only [hY₁, hY₂, hcop.gcd_eq_one, Nat.div_one] using
        hfac.2.2.2.2.2)
    simpa only [hcop.gcd_eq_one, Nat.div_one] using h
  have hprodβ : d₁ * d₂ ∣ β := hcop.mul_dvd_of_dvd_of_dvd hd₁β hd₂β
  let ell := β / (d₁ * d₂)
  have hell : 0 < ell := Nat.div_pos (Nat.le_of_dvd hβ hprodβ)
    (Nat.mul_pos hd₁ hd₂)
  have hβeq : β = ell * d₁ * d₂ := by
    rw [← Nat.div_mul_cancel hprodβ]
    dsimp only [ell]
    ac_rfl
  have hcloseβ : β * d₂ < N * d₁ := by
    simpa only [hY₁, hY₂, N] using hfac.2.2.2.2.2
  let δ := N - β
  have hNsplit : δ + β = N := Nat.sub_add_cancel hβN.le
  have hβδ : β < δ * d₁ := by
    rw [hdiff, mul_add, ← hNsplit, add_mul] at hcloseβ
    omega
  have hellδ : ell * d₂ < δ := by
    apply (Nat.mul_lt_mul_right hd₁).mp
    calc
      ell * d₂ * d₁ = β := by rw [hβeq]; ac_rfl
      _ < δ * d₁ := hβδ
  have hδα : 0 < N - α := by
    have halphaClose : α < N := by
      simpa only [hXone, hX₂one, Nat.mul_one, N] using hfac.2.2.1
    exact Nat.sub_pos_of_lt halphaClose
  have htdecomp : t = (N - α) + δ := by omega
  have hellN : ell * N < t * t := by
    have hpart : ell * β < ell * (δ * d₁) := (Nat.mul_lt_mul_left hell).mpr hβδ
    have hδ : 0 < δ := (Nat.mul_pos hell hd₂).trans hellδ
    calc
      ell * N = ell * δ + ell * β := by rw [← hNsplit, mul_add]
      _ < ell * δ + ell * (δ * d₁) := Nat.add_lt_add_left hpart _
      _ = δ * (ell * d₂) := by rw [hdiff]; simp only [Nat.mul_add]; ac_rfl
      _ < δ * δ := (Nat.mul_lt_mul_left hδ).mpr hellδ
      _ < t * t := Nat.mul_self_lt_mul_self (by omega)
  have hellj : ell ≤ j := by
    have : ell * N < (j + 1) * N := hellN.trans_le hpwindow
    exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_right (by omega : 0 < N)).mp this)
  refine ⟨ell, d₁, hell, hd₁, hellj, ?_⟩
  simpa only [β, hdiff] using hβeq

/-- The arithmetically possible collision positions in Lemma 3.3.  The
upper bound `Y ≤ sqrt p` makes the set directly executable; it loses nothing
because every positive solution of `p-α = ell*Y*(Y+1)` has `Y^2 ≤ p`. -/
private def collisionShapes (N p j : ℕ) : Finset ℕ :=
  Finset.Icc ((p + 1) / 2) N ∩
    (Finset.Icc 1 j).biUnion fun ell ↦
      (Finset.Icc 1 p.sqrt).image fun Y ↦ p - ell * Y * (Y + 1)

private lemma collision_support_subset_shapes (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p j : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hj : j ≤ 3) (hpupper : p ≤ 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ (j + 1) * A.card) :
    (Finset.Icc ((p + 1) / 2) A.card).filter
        (fun α ↦ 2 ≤ representationCount A p α) ⊆
      collisionShapes A.card p j := by
  intro α hα
  obtain ⟨hαJ, hr⟩ := Finset.mem_filter.mp hα
  obtain ⟨ell, Y, hell, hY, hellj, hshape⟩ :=
    collision_fiber_shape A hbad hp hN hj hpupper hpwindow hαJ hr
  apply Finset.mem_inter.mpr
  refine ⟨hαJ, Finset.mem_biUnion.mpr ⟨ell,
    Finset.mem_Icc.mpr ⟨hell, hellj⟩, ?_⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨Y, Finset.mem_Icc.mpr ⟨hY, ?_⟩, ?_⟩
  · apply Nat.le_sqrt.mpr
    calc
      Y * Y ≤ Y * (ell * (Y + 1)) := Nat.mul_le_mul_left Y
        ((Nat.le_succ Y).trans (Nat.le_mul_of_pos_left (Y + 1) hell))
      _ = ell * Y * (Y + 1) := by ac_rfl
      _ = p - α := hshape.symm
      _ ≤ p := Nat.sub_le p α
  · have hprod : 0 < ell * Y * (Y + 1) := Nat.mul_pos (Nat.mul_pos hell hY) (by omega)
    omega

/-- Fully finite form of Lemma 3.3.  All hypotheses after the structural
ones are decidable arithmetic conditions on `N`, `p`, and `j`. -/
private lemma grahamBound_of_shape_certificate (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) {p j : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hj : j ≤ 3) (hthree : 3 * A.card ≤ 2 * p)
    (hqmin : 3 < p - A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ (j + 1) * A.card)
    (hcert : (collisionShapes A.card p j).card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card) :
    GrahamBound A := by
  by_contra hbad
  apply hbad
  apply grahamBound_of_collision_support_lt_primeInterval A h₀ hgcd hp hN hpN hpupper
  · exact hpwindow.trans (Nat.mul_le_mul_right A.card (by omega))
  · intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  · intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  · exact (Finset.card_le_card
      (collision_support_subset_shapes A hbad hp hN hj hpupper.le hpwindow)).trans_lt hcert

/-- The square-root-window criterion used in the paper's medium range.
If `p` lies below `2N` by at most `sqrt N`, then the `j = 0` instance of
the collision-shape lemma says that no nontrivial representation fiber can
exist.  A prime in the reflected interval `[p-N,N]`, on the other hand,
forces such a fiber in every counterexample. -/
private lemma grahamBound_of_short_prime_pair (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hN : 10 ≤ A.card)
    {p q : ℕ} (hp : p.Prime) (hpN : A.card < p)
    (hpupper : p < 2 * A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ A.card)
    (hq : q.Prime) (hqlower : p - A.card ≤ q) (hqupper : q ≤ A.card) :
    GrahamBound A := by
  apply grahamBound_of_shape_certificate A h₀ hgcd hp hN hpN hpupper
      (j := 0)
  · norm_num
  · have htadd : 2 * A.card - p + p = 2 * A.card :=
      Nat.sub_add_cancel hpupper.le
    have hsplit : p - A.card + (2 * A.card - p) = A.card := by
      omega
    nlinarith
  · have htadd : 2 * A.card - p + p = 2 * A.card :=
      Nat.sub_add_cancel hpupper.le
    have hsplit : p - A.card + (2 * A.card - p) = A.card := by
      omega
    nlinarith
  · simpa using hpwindow
  · have hqmem : q ∈
        (Finset.Icc (p - A.card) A.card).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqlower, hqupper⟩, hq⟩
    have hprimepos : 0 <
        ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card :=
      Finset.card_pos.mpr ⟨q, hqmem⟩
    have hshapezero : (collisionShapes A.card p 0).card = 0 := by
      simp [collisionShapes]
    omega

/-- One executable candidate certificate. -/
private def isShapeCertificate (N p j : ℕ) : Bool := decide
  (p.Prime ∧ N < p ∧ p < 2 * N ∧ j ≤ 3 ∧
    3 * N ≤ 2 * p ∧ 3 < p - N ∧
    (2 * N - p) * (2 * N - p) ≤ (j + 1) * N ∧
    (collisionShapes N p j).card <
      ((Finset.Icc (p - N) N).filter Nat.Prime).card)

/-- Search the finite range used by Lemma 3.3 for a certificate. -/
private def hasShapeCertificate (N : ℕ) : Bool :=
  ((List.range (2 * N.sqrt + 1)).map fun k ↦ 2 * N - 1 - k).any fun p ↦
    ((Finset.Icc 0 3).sort (· ≤ ·)).any fun j ↦ isShapeCertificate N p j

private lemma grahamBound_of_hasShapeCertificate (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hA : A.Nonempty) (hN : 10 ≤ A.card)
    (hcert : hasShapeCertificate A.card = true) : GrahamBound A := by
  rw [hasShapeCertificate, List.any_eq_true] at hcert
  obtain ⟨p, hpMem, hcert⟩ := hcert
  rw [List.any_eq_true] at hcert
  obtain ⟨j, hjMem, hcert⟩ := hcert
  have hc : p.Prime ∧ A.card < p ∧ p < 2 * A.card ∧ j ≤ 3 ∧
      3 * A.card ≤ 2 * p ∧ 3 < p - A.card ∧
      (2 * A.card - p) * (2 * A.card - p) ≤ (j + 1) * A.card ∧
      (collisionShapes A.card p j).card <
        ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card := by
    exact of_decide_eq_true hcert
  apply grahamBound_of_normalize A
  let B := normalize A
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = A.card := normalize_card A
  apply grahamBound_of_shape_certificate B hB₀ hBgcd hc.1
  · simpa only [hBcard] using hN
  · simpa only [hBcard] using hc.2.1
  · simpa only [hBcard] using hc.2.2.1
  · exact hc.2.2.2.1
  · simpa only [hBcard] using hc.2.2.2.2.1
  · simpa only [hBcard] using hc.2.2.2.2.2.1
  · simpa only [hBcard] using hc.2.2.2.2.2.2.1
  · simpa only [hBcard] using hc.2.2.2.2.2.2.2

private def shapeCertificateFailures : Finset ℕ :=
  (Finset.Icc 10 7000).filter fun N ↦ hasShapeCertificate N = false

/-- Kernel-checked version of the finite table in Lemma 3.3: the only
cardinalities through `7000` not settled by the uniform shape certificate
are `27` and `65`. -/
private lemma shapeCertificateFailures_eq :
    shapeCertificateFailures = {27, 65} := by native_decide

private lemma hasShapeCertificate_of_range {N : ℕ} (hlo : 10 ≤ N)
    (hhi : N ≤ 7000) (h27 : N ≠ 27) (h65 : N ≠ 65) :
    hasShapeCertificate N = true := by
  by_cases h : hasShapeCertificate N = true
  · exact h
  have hfalse : hasShapeCertificate N = false := by
    cases hh : hasShapeCertificate N
    · rfl
    · exact False.elim (h hh)
  have hmem : N ∈ shapeCertificateFailures :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hfalse⟩
  rw [shapeCertificateFailures_eq] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  exact False.elim (hmem.elim h27 h65)

private lemma grahamBound_of_card_le_7000_except (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hA : A.Nonempty) (hlo : 10 ≤ A.card)
    (hhi : A.card ≤ 7000) (h27 : A.card ≠ 27) (h65 : A.card ≠ 65) :
    GrahamBound A :=
  grahamBound_of_hasShapeCertificate A h₀ hA hlo
    (hasShapeCertificate_of_range hlo hhi h27 h65)

/-! ### Exact finite configuration certificates for `N=27,65` -/

private def componentClose (N α β d e : ℕ) : Prop :=
  α * (d.gcd α / (d.gcd α).gcd (e.gcd α)) <
      N * (e.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
  α * (e.gcd α / (d.gcd α).gcd (e.gcd α)) <
      N * (d.gcd α / (d.gcd α).gcd (e.gcd α)) ∧
  β * (d.gcd β / (d.gcd β).gcd (e.gcd β)) <
      N * (e.gcd β / (d.gcd β).gcd (e.gcd β)) ∧
  β * (e.gcd β / (d.gcd β).gcd (e.gcd β)) <
      N * (d.gcd β / (d.gcd β).gcd (e.gcd β))

private def pairConfiguration (N α β d e : ℕ) : Prop :=
  0 < d ∧ d < e ∧
  d = d.gcd α * d.gcd β ∧ e = e.gcd α * e.gcd β ∧
  componentClose N α β d e

private def tripleConfiguration (N α β d₁ d₂ d₃ : ℕ) : Prop :=
  0 < d₁ ∧ d₁ < d₂ ∧ d₂ < d₃ ∧
  d₁ = d₁.gcd α * d₁.gcd β ∧
  d₂ = d₂.gcd α * d₂.gcd β ∧
  d₃ = d₃.gcd α * d₃.gcd β ∧
  componentClose N α β d₁ d₂ ∧
  componentClose N α β d₁ d₃ ∧
  componentClose N α β d₂ d₃

private instance instDecidablePairConfiguration (N α β d e : ℕ) :
    Decidable (pairConfiguration N α β d e) := by
  unfold pairConfiguration componentClose
  infer_instance

private instance instDecidableTripleConfiguration (N α β d₁ d₂ d₃ : ℕ) :
    Decidable (tripleConfiguration N α β d₁ d₂ d₃) := by
  unfold tripleConfiguration componentClose
  infer_instance

private def possiblePair (N α β : ℕ) : Bool :=
  let D := (Nat.divisors (α * β)).sort (· ≤ ·)
  D.any fun d ↦ D.any fun e ↦ decide (pairConfiguration N α β d e)

private def possibleTriple (N α β : ℕ) : Bool :=
  let D := (Nat.divisors (α * β)).sort (· ≤ ·)
  D.any fun d₁ ↦ D.any fun d₂ ↦ D.any fun d₃ ↦
    decide (tripleConfiguration N α β d₁ d₂ d₃)

private lemma possiblePair_eq_true {N α β : ℕ} :
    possiblePair N α β = true ↔
      ∃ d ∈ Nat.divisors (α * β), ∃ e ∈ Nat.divisors (α * β),
        pairConfiguration N α β d e := by
  simp only [possiblePair, List.any_eq_true, decide_eq_true_eq, Finset.mem_sort]

/-- If both coordinates lie closer to `N` than their own square-root
scale, the two normalized factors in any putative collision agree in both
coprime components, contradicting their strict order.  This is the
arithmetic contradiction used in Lemma 3.2. -/
private lemma possiblePair_eq_false_of_double_gap {N α β : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hαN : α ≤ N) (hβN : β ≤ N)
    (hgapα : (N - α) * (N - α) < α)
    (hgapβ : (N - β) * (N - β) < β) :
    possiblePair N α β = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  rw [possiblePair_eq_true] at htrue
  obtain ⟨d, _hddiv, e, _hediv, hd, hde, hdfac, hefac, hclose⟩ := htrue
  have hXeq : d.gcd α = e.gcd α :=
    component_eq_of_gap_square_lt hα hαN
      (Nat.gcd_pos_of_pos_left α hd)
      (Nat.gcd_pos_of_pos_left α (hd.trans hde))
      (Nat.gcd_dvd_right d α) (Nat.gcd_dvd_right e α)
      hgapα hclose.1 hclose.2.1
  have hYeq : d.gcd β = e.gcd β :=
    component_eq_of_gap_square_lt hβ hβN
      (Nat.gcd_pos_of_pos_left β hd)
      (Nat.gcd_pos_of_pos_left β (hd.trans hde))
      (Nat.gcd_dvd_right d β) (Nat.gcd_dvd_right e β)
      hgapβ hclose.2.2.1 hclose.2.2.2
  have : d = e := by rw [hdfac, hefac, hXeq, hYeq]
  exact (Nat.ne_of_lt hde) this

private lemma possibleTriple_eq_true {N α β : ℕ} :
    possibleTriple N α β = true ↔
      ∃ d₁ ∈ Nat.divisors (α * β), ∃ d₂ ∈ Nat.divisors (α * β),
        ∃ d₃ ∈ Nat.divisors (α * β),
          tripleConfiguration N α β d₁ d₂ d₃ := by
  simp only [possibleTriple, List.any_eq_true, decide_eq_true_eq, Finset.mem_sort]

private def possiblePairAlphas (N p : ℕ) : Finset ℕ :=
  (Finset.Icc ((p + 1) / 2) N).filter fun α ↦
    possiblePair N α (p - α) = true

private def possibleTripleAlphas (N p : ℕ) : Finset ℕ :=
  (Finset.Icc ((p + 1) / 2) N).filter fun α ↦
    possibleTriple N α (p - α) = true

/-- Data carried by one member of a normalized representation fiber. -/
private lemma normalized_multiplier_data (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α d : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hR : (representedMultipliers A α (p - α)).Nonempty)
    (hd : d ∈ normalize (representedMultipliers A α (p - α))) :
    0 < d ∧ d ∣ α * (p - α) ∧
      d = d.gcd α * d.gcd (p - α) ∧
      α * d * (representedMultipliers A α (p - α)).gcd id ∈ A ∧
      (p - α) * d * (representedMultipliers A α (p - α)).gcd id ∈ A := by
  let β := p - α
  let R := representedMultipliers A α β
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
  have hc : 0 < R.gcd id := gcd_pos R hR₀ hR
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun hz ↦
    normalize_nonzero R hR₀ (hz ▸ hd)
  have hdvd : d ∣ α * β :=
    normalize_represented_dvd_product A hbad hα hβ hαβ hsq hR d hd
  have hfac : d = d.gcd α * d.gcd β :=
    ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr hdvd).symm
  change d ∈ R.image (fun e ↦ e / R.gcd id) at hd
  obtain ⟨e, heR, rfl⟩ := Finset.mem_image.mp hd
  have hedata := (mem_representedMultipliers hα).mp heR
  have hce : R.gcd id ∣ e := Finset.gcd_dvd heR
  have heq : e / R.gcd id * R.gcd id = e := Nat.div_mul_cancel hce
  refine ⟨hdpos, hdvd, hfac, ?_, ?_⟩
  · change α * (e / R.gcd id) * R.gcd id ∈ A
    rw [mul_assoc, heq]
    exact hedata.2.1
  · change β * (e / R.gcd id) * R.gcd id ∈ A
    rw [mul_assoc, heq]
    exact hedata.2.2

private lemma possiblePair_of_collision (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hr : 2 ≤ representationCount A p α) :
    possiblePair A.card α (p - α) = true := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  change 2 ≤ R.card at hr
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
  have hc : 0 < R.gcd id := gcd_pos R hR₀ hR
  have hBtwo : 1 < B.card := by
    change 1 < (normalize R).card
    rw [normalize_card]
    omega
  obtain ⟨x, hxB, y, hyB, hxy⟩ := Finset.one_lt_card.mp hBtwo
  let d := min x y
  let e := max x y
  have hdB : d ∈ B := by
    change min x y ∈ B
    rcases min_choice x y with h | h <;> rw [h]
    · exact hxB
    · exact hyB
  have heB : e ∈ B := by
    change max x y ∈ B
    rcases max_choice x y with h | h <;> rw [h]
    · exact hxB
    · exact hyB
  have hde : d < e := by dsimp only [d, e]; omega
  have hddata := normalized_multiplier_data A hbad hp hα hαp hsq hR hdB
  have hedata := normalized_multiplier_data A hbad hp hα hαp hsq hR heB
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hclose := scaled_component_closeness A hbad hα hβ hddata.1 hedata.1 hc
    hαβ hsq hddata.2.2.1 hedata.2.2.1
    hddata.2.2.2.1 hddata.2.2.2.2 hedata.2.2.2.1 hedata.2.2.2.2
  rw [possiblePair_eq_true]
  refine ⟨d, Nat.mem_divisors.mpr ⟨hddata.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩,
    e, Nat.mem_divisors.mpr ⟨hedata.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩, ?_⟩
  exact ⟨hddata.1, hde, hddata.2.2.1, hedata.2.2.1, hclose⟩

/-- Collision-free form of Lemma 3.2, with the two endpoint inequalities
stated without square roots. -/
private lemma representationCount_le_one_of_double_gap (A : Finset ℕ)
    (hbad : ¬GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαN : α ≤ A.card) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hβN : p - α ≤ A.card)
    (hgapα : (A.card - α) * (A.card - α) < α)
    (hgapβ : (A.card - (p - α)) * (A.card - (p - α)) < p - α) :
    representationCount A p α ≤ 1 := by
  by_contra htwo
  have hr : 2 ≤ representationCount A p α := by omega
  have hpair := possiblePair_of_collision A hbad hp hα hαp hsq hr
  have hfalse := possiblePair_eq_false_of_double_gap hα
    (Nat.sub_pos_of_lt hαp) hαN hβN hgapα hgapβ
  rw [hfalse] at hpair
  exact Bool.noConfusion hpair

/-- Finite certificate interface for Lemma 3.2.  A prime in `[p-N,N]`
forces at least one empty fiber, while the two endpoint-gap inequalities
rule out every collision fiber. -/
private lemma grahamBound_of_prime_interval_and_double_gap (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) {p q : ℕ} (hp : p.Prime)
    (hN : 10 ≤ A.card) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hthree : 3 * A.card ≤ 2 * p) (hqmin : 3 < p - A.card)
    (hpwindow : (2 * A.card - p) * (2 * A.card - p) ≤ 4 * A.card)
    (hq : q.Prime) (hqI : q ∈ Finset.Icc (p - A.card) A.card)
    (hgaps : ∀ α ∈ Finset.Icc ((p + 1) / 2) A.card,
      (A.card - α) * (A.card - α) < α ∧
      p - α ≤ A.card ∧
      (A.card - (p - α)) * (A.card - (p - α)) < p - α) :
    GrahamBound A := by
  by_contra hbad
  apply hbad
  apply grahamBound_of_collision_support_lt_primeInterval
    A h₀ hgcd hp hN hpN hpupper hpwindow
  · intro r hr
    have hrlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
    omega
  · intro r hr
    have hrlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
    omega
  · have hsupport :
        (Finset.Icc ((p + 1) / 2) A.card).filter
          (fun α ↦ 2 ≤ representationCount A p α) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro α hα
      have hαJ := (Finset.mem_filter.mp hα).1
      have hr := (Finset.mem_filter.mp hα).2
      have hαN := (Finset.mem_Icc.mp hαJ).2
      have hα : 0 < α := by
        have hlo := (Finset.mem_Icc.mp hαJ).1
        have hp2 := hp.two_le
        have hhalf : 0 < (p + 1) / 2 := Nat.div_pos (by omega) (by norm_num)
        omega
      have hαp : α < p := hαN.trans_lt hpN
      have hg := hgaps α hαJ
      have hsq := square_lt_twice_of_gap hN hα hαN hg.1
      have hle := representationCount_le_one_of_double_gap A hbad hp
        hα hαN hαp hsq hg.2.1 hg.1 hg.2.2
      omega
    rw [hsupport]
    simp only [Finset.card_empty]
    exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqI, hq⟩⟩

private lemma possibleTriple_of_three_representations (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hr : 3 ≤ representationCount A p α) :
    possibleTriple A.card α (p - α) = true := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  change 3 ≤ R.card at hr
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
  have hc : 0 < R.gcd id := gcd_pos R hR₀ hR
  have hBthree : 2 < B.card := by
    change 2 < (normalize R).card
    rw [normalize_card]
    omega
  obtain ⟨x, hxB, y, hyB, z, hzB, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hBthree
  obtain ⟨d₁, d₂, d₃, hd₁₂, hd₂₃, hperm⟩ :=
    exists_increasing_permutation hxy hxz hyz
  have hsub : ({d₁, d₂, d₃} : Finset ℕ) ⊆ B := by
    rw [hperm]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hxB, hyB, hzB⟩
  have hd₁B : d₁ ∈ B := hsub (by simp)
  have hd₂B : d₂ ∈ B := hsub (by simp)
  have hd₃B : d₃ ∈ B := hsub (by simp)
  have hd₁data := normalized_multiplier_data A hbad hp hα hαp hsq hR hd₁B
  have hd₂data := normalized_multiplier_data A hbad hp hα hαp hsq hR hd₂B
  have hd₃data := normalized_multiplier_data A hbad hp hα hαp hsq hR hd₃B
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hclose₁₂ := scaled_component_closeness A hbad hα hβ
    hd₁data.1 hd₂data.1 hc hαβ hsq hd₁data.2.2.1 hd₂data.2.2.1
    hd₁data.2.2.2.1 hd₁data.2.2.2.2 hd₂data.2.2.2.1 hd₂data.2.2.2.2
  have hclose₁₃ := scaled_component_closeness A hbad hα hβ
    hd₁data.1 hd₃data.1 hc hαβ hsq hd₁data.2.2.1 hd₃data.2.2.1
    hd₁data.2.2.2.1 hd₁data.2.2.2.2 hd₃data.2.2.2.1 hd₃data.2.2.2.2
  have hclose₂₃ := scaled_component_closeness A hbad hα hβ
    hd₂data.1 hd₃data.1 hc hαβ hsq hd₂data.2.2.1 hd₃data.2.2.1
    hd₂data.2.2.2.1 hd₂data.2.2.2.2 hd₃data.2.2.2.1 hd₃data.2.2.2.2
  rw [possibleTriple_eq_true]
  refine ⟨d₁, Nat.mem_divisors.mpr
      ⟨hd₁data.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩,
    d₂, Nat.mem_divisors.mpr
      ⟨hd₂data.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩,
    d₃, Nat.mem_divisors.mpr
      ⟨hd₃data.2.1, Nat.mul_ne_zero hα.ne' hβ.ne'⟩, ?_⟩
  exact ⟨hd₁data.1, hd₁₂, hd₂₃,
    hd₁data.2.2.1, hd₂data.2.2.1, hd₃data.2.2.1,
    hclose₁₂, hclose₁₃, hclose₂₃⟩

/-- A finite pair/triple configuration certificate implies Graham's bound.
This is the version of the collision count used only for the exceptional
cardinalities `27` and `65`. -/
private lemma grahamBound_of_configuration_certificate (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) {p : ℕ} (hp : p.Prime)
    (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hthree : 3 * A.card ≤ 2 * p) (hqmin : 3 < p - A.card)
    (hsq : ∀ α ∈ Finset.Icc ((p + 1) / 2) A.card,
      A.card * A.card < 2 * (α * α))
    (hpair : (possiblePairAlphas A.card p).card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card)
    (htriple : possibleTripleAlphas A.card p = ∅) :
    GrahamBound A := by
  by_contra hbad
  let J := Finset.Icc ((p + 1) / 2) A.card
  let M := J.filter fun α ↦ 2 ≤ representationCount A p α
  have hmult : ∀ α ∈ M, representationCount A p α ≤ 2 := by
    intro α hαM
    have hαJ := (Finset.mem_filter.mp hαM).1
    by_contra hnot
    have hr : 3 ≤ representationCount A p α := by omega
    have hαpos : 0 < α := by
      have := (Finset.mem_Icc.mp hαJ).1
      omega
    have hαp : α < p := (Finset.mem_Icc.mp hαJ).2.trans_lt hpN
    have hpossible := possibleTriple_of_three_representations A hbad hp
      hαpos hαp (hsq α hαJ) hr
    have hmem : α ∈ possibleTripleAlphas A.card p :=
      Finset.mem_filter.mpr ⟨hαJ, hpossible⟩
    rw [htriple] at hmem
    exact Finset.notMem_empty α hmem
  have hsupport : M.card <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card := by
    apply (Finset.card_le_card ?_).trans_lt hpair
    intro α hαM
    have hαJ := (Finset.mem_filter.mp hαM).1
    have hr := (Finset.mem_filter.mp hαM).2
    have hαpos : 0 < α := by
      have := (Finset.mem_Icc.mp hαJ).1
      omega
    have hαp : α < p := (Finset.mem_Icc.mp hαJ).2.trans_lt hpN
    apply Finset.mem_filter.mpr
    exact ⟨hαJ, possiblePair_of_collision A hbad hp hαpos hαp (hsq α hαJ) hr⟩
  have hexcess : M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card := by
    calc
      M.sum (fun α ↦ representationCount A p α - 1) ≤ M.sum (fun _ ↦ 1) := by
        apply Finset.sum_le_sum
        intro α hαM
        have := hmult α hαM
        omega
      _ = M.card := by simp
  have hlower : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q := by
    intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  have hq2 : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q := by
    intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  have hprimeZero := primeInterval_card_le_zeroFibers A h₀ hgcd hbad hp hpN hpupper
    hlower hq2
  have hzeroExcess := zero_card_le_representation_excess A h₀ hgcd hbad hp hpN hpupper
  change M.card < _ at hsupport
  change _ ≤ (J.filter fun α ↦ 2 ≤ representationCount A p α).sum
    (fun α ↦ representationCount A p α - 1) at hzeroExcess
  change M.sum (fun α ↦ representationCount A p α - 1) ≤ M.card at hexcess
  exact (not_lt_of_ge (hprimeZero.trans (hzeroExcess.trans hexcess))) hsupport

private lemma grahamBound_of_card_27 (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card = 27) : GrahamBound A := by
  apply grahamBound_of_normalize A
  let B := normalize A
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 27 := (normalize_card A).trans hcard
  apply grahamBound_of_configuration_certificate B hB₀ hBgcd (p := 43)
      (by native_decide) (by omega) (by omega) (by omega) (by omega)
  · intro α hα
    have hlo := (Finset.mem_Icc.mp hα).1
    have hs := Nat.mul_self_le_mul_self hlo
    norm_num [hBcard] at hs ⊢
    omega
  · simpa only [hBcard] using (show
      (possiblePairAlphas 27 43).card <
        ((Finset.Icc (43 - 27) 27).filter Nat.Prime).card by native_decide)
  · simpa only [hBcard] using (show
      possibleTripleAlphas 27 43 = ∅ by native_decide)

private lemma grahamBound_of_card_65 (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card = 65) : GrahamBound A := by
  apply grahamBound_of_normalize A
  let B := normalize A
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 65 := (normalize_card A).trans hcard
  apply grahamBound_of_configuration_certificate B hB₀ hBgcd (p := 113)
      (by native_decide) (by omega) (by omega) (by omega) (by omega)
  · intro α hα
    have hlo := (Finset.mem_Icc.mp hα).1
    have hs := Nat.mul_self_le_mul_self hlo
    norm_num [hBcard] at hs ⊢
    omega
  · simpa only [hBcard] using (show
      (possiblePairAlphas 65 113).card <
        ((Finset.Icc (113 - 65) 65).filter Nat.Prime).card by native_decide)
  · simpa only [hBcard] using (show
      possibleTripleAlphas 65 113 = ∅ by native_decide)

/-- The maximum coordinate in the paper's global reduced-pair set is at
most `N`.  The stronger pointwise proof above actually gives strict
inequality for every coordinate that occurs. -/
private lemma globalD_le_card (A : Finset ℕ) (G : ℕ)
    (hbad : ¬ GrahamBound A) (hG : 0 < G) (hsmall : 4 * G ≤ A.card) :
    globalD A G ≤ A.card := by
  classical
  rw [globalD, Finset.sup_le_iff]
  intro de hde
  rw [globalReducedPairs] at hde
  obtain ⟨p, hpF, hde⟩ := Finset.mem_biUnion.mp hde
  obtain ⟨hpwin, hp⟩ := Finset.mem_filter.mp hpF
  obtain ⟨α, hαJ, hde⟩ := Finset.mem_biUnion.mp hde
  have hpwinFin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G) := hpwin
  have hαJFin : α ∈ Finset.Icc ((p + 1) / 2) A.card := hαJ
  obtain ⟨hplower, _hpupper⟩ := Finset.mem_Icc.mp hpwinFin
  obtain ⟨hαlower, hαupper⟩ := Finset.mem_Icc.mp hαJFin
  simp only [reducedPairs] at hde
  obtain ⟨⟨d, e⟩, hdeB, rfl⟩ := Finset.mem_image.mp hde
  obtain ⟨hd, he⟩ := Finset.mem_product.mp hdeB
  have hpN : A.card < p := by omega
  have hαpos : 0 < α := by omega
  have hαp : α < p := hαupper.trans_lt hpN
  have hsq := square_lt_of_window hG hsmall hpwinFin hαJFin
  obtain ⟨hdlt, helt⟩ :=
    reducedPair_coordinates_lt_card A hbad hp hαpos hαp hsq hd he
  exact max_le hdlt.le helt.le

/-- Under the strict negation of Graham's bound and after normalization,
every member divides `lcm {1, ..., |A|-1}`. -/
private lemma dvd_lcm_Ico_of_not_grahamBound (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {a : ℕ} (ha : a ∈ A) :
    a ∣ (Finset.Ico 1 A.card).lcm id := by
  classical
  have ha0 : a ≠ 0 := fun h ↦ h₀ (h ▸ ha)
  have hquot : ∀ b ∈ A, a / a.gcd b ∈ Finset.Ico 1 A.card := by
    intro b hb
    have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    have hqpos : 0 < a / a.gcd b :=
      Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
    have hlt : a / a.gcd b < A.card := by
      rw [Nat.div_lt_iff_lt_mul hgpos]
      exact Nat.lt_of_not_ge fun hle ↦ hbad ⟨a, ha, b, hb, by simpa [mul_comm] using hle⟩
    exact Finset.mem_Ico.mpr ⟨hqpos, hlt⟩
  have hlcm : A.lcm (fun b ↦ a / a.gcd b) ∣ (Finset.Ico 1 A.card).lcm id :=
    Finset.lcm_dvd fun b hb ↦ Finset.dvd_lcm (hquot b hb)
  rw [lcm_div_gcd_eq a ha0 A, hgcd, Nat.gcd_one_right, Nat.div_one] at hlcm
  exact hlcm

/-- The elementary part of the Balasubramanian--Soundararajan proof: the
theorem for finsets of cardinality at most four. -/
private lemma grahamBound_of_card_le_four (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 4) : GrahamBound A := by
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = A.card := normalize_card A
  have hBne : B.Nonempty := by
    apply Finset.card_pos.mp
    rw [hBcard]
    exact Finset.card_pos.mpr hA
  have hdvd : ∀ b ∈ B, b ∣ (Finset.Ico 1 B.card).lcm id :=
    fun b hb ↦ dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
  have hBcard_le : B.card ≤ 4 := hBcard.trans_le hcard
  have hBcard_pos : 0 < B.card := Finset.card_pos.mpr hBne
  rcases (show B.card = 1 ∨ B.card = 2 ∨ B.card = 3 ∨ B.card = 4 by omega) with
    h₁ | h₂ | h₃ | h₄
  · obtain ⟨a, ha⟩ := hBne
    apply hbad
    refine ⟨a, ha, a, ha, ?_⟩
    simp [h₁]
  · have hsub : B ⊆ Nat.divisors 1 := by
      intro b hb
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by norm_num⟩
      simpa [h₂] using hdvd b hb
    have hle := Finset.card_le_card hsub
    rw [h₂, Nat.divisors_one, Finset.card_singleton] at hle
    omega
  · have hsub : B ⊆ Nat.divisors 2 := by
      intro b hb
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by norm_num⟩
      have hbdiv := hdvd b hb
      rw [h₃, show (Finset.Ico 1 3).lcm id = 2 by decide] at hbdiv
      exact hbdiv
    have hle := Finset.card_le_card hsub
    rw [h₃] at hle
    have hdivcard : (Nat.divisors 2).card = 2 := by decide
    rw [hdivcard] at hle
    omega
  · have hsub : B ⊆ Nat.divisors 6 := by
      intro b hb
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by norm_num⟩
      have hbdiv := hdvd b hb
      rw [h₄, show (Finset.Ico 1 4).lcm id = 6 by decide] at hbdiv
      exact hbdiv
    have heq : B = Nat.divisors 6 := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [h₄]
      decide
    have h6 : 6 ∈ B := heq ▸ by norm_num
    have h1 : 1 ∈ B := heq ▸ by norm_num
    apply hbad
    exact ⟨6, h6, 1, h1, by norm_num [h₄]⟩

/-- Turn a closed exhaustive certificate on the divisors of
`lcm {1, ..., n - 1}` into the theorem for every finset of cardinality
`n`.  Normalization and the lcm reduction are proved above; `hcert` is a
fully evaluated finite claim. -/
private lemma grahamBound_of_lcm_certificate (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) {n L : ℕ} (hcard : A.card = n) (hL₀ : L ≠ 0)
    (hlcm : (Finset.Ico 1 n).lcm id = L)
    (hcert : badSubsets (Nat.divisors L) n = ∅) : GrahamBound A := by
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcardA : B.card = A.card := normalize_card A
  have hBcard : B.card = n := hBcardA.trans hcard
  have hsub : B ⊆ Nat.divisors L := by
    intro b hb
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hL₀⟩
    have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
    simpa [hBcard, hlcm] using hdvd
  exact hbad (grahamBound_of_badSubsets_eq_empty hcert hsub hBcard)

/-- Closed exhaustive certificates extend the elementary proof through
cardinality seven without using Boyle's large-prime lemma. -/
private lemma grahamBound_of_card_le_seven (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 7) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 4
  · exact grahamBound_of_card_le_four A h₀ hA hsmall
  have hpos : 0 < A.card := Finset.card_pos.mpr hA
  rcases (show A.card = 5 ∨ A.card = 6 ∨ A.card = 7 by omega) with h₅ | h₆ | h₇
  · apply grahamBound_of_lcm_certificate A h₀ hA (n := 5) (L := 12) h₅ (by norm_num)
      (by native_decide)
    native_decide
  · apply grahamBound_of_lcm_certificate A h₀ hA (n := 6) (L := 60) h₆ (by norm_num)
      (by native_decide)
    native_decide
  · apply grahamBound_of_lcm_certificate A h₀ hA (n := 7) (L := 60) h₇ (by norm_num)
      (by native_decide)
    native_decide

/-- The same exhaustive method remains small enough at cardinality eight:
there are `Nat.choose 24 8` candidate subsets of the divisors of `420`. -/
private lemma grahamBound_of_card_le_eight (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 8) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 7
  · exact grahamBound_of_card_le_seven A h₀ hA hsmall
  have h₈ : A.card = 8 := by omega
  apply grahamBound_of_lcm_certificate A h₀ hA (n := 8) (L := 420) h₈ (by norm_num)
      (by native_decide)
  native_decide

/-- At cardinality nine the strict lcm reduction puts every normalized
member among the divisors of `840`; Boyle's lemma excludes the prime
factors `5` and `7`, leaving only eight possible divisors. -/
private lemma grahamBound_of_card_le_nine (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 9) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 8
  · exact grahamBound_of_card_le_eight A h₀ hA hsmall
  have hcard9 : A.card = 9 := by omega
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 9 := (normalize_card A).trans hcard9
  let T := (Nat.divisors 840).filter fun b ↦ ¬5 ∣ b ∧ ¬7 ∣ b
  have hsub : B ⊆ T := by
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, by norm_num⟩, ?_, ?_⟩
    · have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
      rw [hBcard, show (Finset.Ico 1 9).lcm id = 840 by native_decide] at hdvd
      exact hdvd
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 5) (by native_decide) (by norm_num [hBcard]) hb
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 7) (by native_decide) (by norm_num [hBcard]) hb
  have hle := Finset.card_le_card hsub
  have hTcard : T.card = 8 := by native_decide
  rw [hBcard, hTcard] at hle
  omega

/-- At cardinality ten, the endpoint form of Boyle's lemma excludes both
`5` and `7`.  Only twelve divisors of `lcm {1, ..., 9} = 2520` remain,
and the resulting 66 ten-element candidates are checked exhaustively. -/
private lemma grahamBound_of_card_le_ten (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 10) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 9
  · exact grahamBound_of_card_le_nine A h₀ hA hsmall
  have hcard10 : A.card = 10 := by omega
  apply grahamBound_of_normalize A
  by_contra hbad
  let B := normalize A
  change ¬ GrahamBound B at hbad
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBcard : B.card = 10 := (normalize_card A).trans hcard10
  let T := (Nat.divisors 2520).filter fun b ↦ ¬5 ∣ b ∧ ¬7 ∣ b
  have hsub : B ⊆ T := by
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, by norm_num⟩, ?_, ?_⟩
    · have hdvd := dvd_lcm_Ico_of_not_grahamBound B hB₀ hBgcd hbad hb
      rw [hBcard, show (Finset.Ico 1 10).lcm id = 2520 by native_decide] at hdvd
      exact hdvd
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 5) (by native_decide) (by norm_num [hBcard]) hb
    · exact prime_not_dvd_of_card_le_two_mul B hB₀ hBgcd hbad
        (q := 7) (by native_decide) (by norm_num [hBcard]) hb
  have hcert : badSubsets T 10 = ∅ := by native_decide
  exact hbad (grahamBound_of_badSubsets_eq_empty hcert hsub hBcard)

/-- The elementary, shape-certificate, and exceptional-configuration
arguments together settle every cardinality through `7000`. -/
private lemma grahamBound_of_card_le_7000 (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 7000) : GrahamBound A := by
  by_cases hsmall : A.card ≤ 10
  · exact grahamBound_of_card_le_ten A h₀ hA hsmall
  have hlo : 10 ≤ A.card := by omega
  by_cases h27 : A.card = 27
  · exact grahamBound_of_card_27 A h₀ hA h27
  by_cases h65 : A.card = 65
  · exact grahamBound_of_card_65 A h₀ hA h65
  exact grahamBound_of_card_le_7000_except A h₀ hA hlo hcard h27 h65

/-- The exact Formal Conjectures statement, already closed for every set
of cardinality at most `7000`. -/
theorem erdos_402_of_card_le_7000 (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hA : A.Nonempty) (hcard : A.card ≤ 7000) :
    ∃ᵉ (a ∈ A) (b ∈ A), a.gcd b ≤ (a / A.card : ℚ) := by
  exact erdos_402_of_grahamBound A hA
    (grahamBound_of_card_le_7000 A h₀ hA hcard)

/-! ## The algebraic core of the large-prime exclusion step -/

/-- The prime-exponent inequality behind the four-gcd bookkeeping in
Balasubramanian--Soundararajan, Lemma 4.1. -/
private lemma min_four_rectangle_le (u a b d e : ℕ)
    (hab : min a b = 0) (hde : min d e = 0)
    (hd : d ≤ a + b) (he : e ≤ a + b) :
    min u (a + d) + min u (a + e) +
        min u (b + d) + min u (b + e) ≤
      u + (a + b) + (d + e) := by
  rcases min_choice a b with h | h <;>
    rcases min_choice d e with h' | h' <;>
      rw [h] at hab <;> rw [h'] at hde <;> omega

/-- If `d₁,d₂` are coprime divisors of `αβ`, where `α,β` are
coprime, the product of the four rectangular gcds has this sharp bound.
This packages the paper's auxiliary `Bᵢ,Fᵢ` construction into one
prime-exponent calculation. -/
private lemma four_gcd_product_le {u α β d₁ d₂ : ℕ}
    (hu : 0 < u) (hα : 0 < α) (hβ : 0 < β)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hαβ : α.Coprime β) (hd₁₂ : d₁.Coprime d₂)
    (hd₁div : d₁ ∣ α * β) (hd₂div : d₂ ∣ α * β) :
    u.gcd (α * d₁) * u.gcd (α * d₂) *
        u.gcd (β * d₁) * u.gcd (β * d₂) ≤
      u * (α * β) * (d₁ * d₂) := by
  have hα0 := hα.ne'
  have hβ0 := hβ.ne'
  have hu0 := hu.ne'
  have hd₁0 := hd₁.ne'
  have hd₂0 := hd₂.ne'
  have hαd₁0 : α * d₁ ≠ 0 := Nat.mul_ne_zero hα0 hd₁0
  have hαd₂0 : α * d₂ ≠ 0 := Nat.mul_ne_zero hα0 hd₂0
  have hβd₁0 : β * d₁ ≠ 0 := Nat.mul_ne_zero hβ0 hd₁0
  have hβd₂0 : β * d₂ ≠ 0 := Nat.mul_ne_zero hβ0 hd₂0
  have hleft0 : u.gcd (α * d₁) * u.gcd (α * d₂) *
      u.gcd (β * d₁) * u.gcd (β * d₂) ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.mul_ne_zero
      (Nat.mul_ne_zero (Nat.gcd_ne_zero_left hu0) (Nat.gcd_ne_zero_left hu0))
      (Nat.gcd_ne_zero_left hu0)) (Nat.gcd_ne_zero_left hu0)
  have hright0 : u * (α * β) * (d₁ * d₂) ≠ 0 := by positivity
  have hdvd : u.gcd (α * d₁) * u.gcd (α * d₂) *
      u.gcd (β * d₁) * u.gcd (β * d₂) ∣
      u * (α * β) * (d₁ * d₂) := by
    rw [← Nat.factorization_le_iff_dvd hleft0 hright0]
    intro p
    have hab : min (α.factorization p) (β.factorization p) = 0 := by
      have h := congrArg (fun f ↦ f p) (Nat.factorization_gcd hα0 hβ0)
      rw [hαβ.gcd_eq_one, Nat.factorization_one] at h
      exact h.symm
    have hde : min (d₁.factorization p) (d₂.factorization p) = 0 := by
      have h := congrArg (fun f ↦ f p) (Nat.factorization_gcd hd₁0 hd₂0)
      rw [hd₁₂.gcd_eq_one, Nat.factorization_one] at h
      exact h.symm
    have hdle : d₁.factorization p ≤
        α.factorization p + β.factorization p := by
      have h := (Nat.factorization_le_iff_dvd hd₁0
        (Nat.mul_ne_zero hα0 hβ0)).mpr hd₁div p
      simpa only [Nat.factorization_mul hα0 hβ0, Finsupp.add_apply] using h
    have hele : d₂.factorization p ≤
        α.factorization p + β.factorization p := by
      have h := (Nat.factorization_le_iff_dvd hd₂0
        (Nat.mul_ne_zero hα0 hβ0)).mpr hd₂div p
      simpa only [Nat.factorization_mul hα0 hβ0, Finsupp.add_apply] using h
    rw [Nat.factorization_mul
        (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.gcd_ne_zero_left hu0)
          (Nat.gcd_ne_zero_left hu0)) (Nat.gcd_ne_zero_left hu0))
        (Nat.gcd_ne_zero_left hu0),
      Nat.factorization_mul
        (Nat.mul_ne_zero (Nat.gcd_ne_zero_left hu0) (Nat.gcd_ne_zero_left hu0))
        (Nat.gcd_ne_zero_left hu0),
      Nat.factorization_mul (Nat.gcd_ne_zero_left hu0) (Nat.gcd_ne_zero_left hu0),
      Nat.factorization_gcd hu0 hαd₁0, Nat.factorization_gcd hu0 hαd₂0,
      Nat.factorization_gcd hu0 hβd₁0, Nat.factorization_gcd hu0 hβd₂0,
      Nat.factorization_mul hα0 hd₁0, Nat.factorization_mul hα0 hd₂0,
      Nat.factorization_mul hβ0 hd₁0, Nat.factorization_mul hβ0 hd₂0,
      Nat.factorization_mul
        (Nat.mul_ne_zero hu0 (Nat.mul_ne_zero hα0 hβ0))
        (Nat.mul_ne_zero hd₁0 hd₂0),
      Nat.factorization_mul hu0 (Nat.mul_ne_zero hα0 hβ0),
      Nat.factorization_mul hα0 hβ0,
      Nat.factorization_mul hd₁0 hd₂0]
    change min (u.factorization p) (α.factorization p + d₁.factorization p) +
        min (u.factorization p) (α.factorization p + d₂.factorization p) +
        min (u.factorization p) (β.factorization p + d₁.factorization p) +
        min (u.factorization p) (β.factorization p + d₂.factorization p) ≤
      u.factorization p + (α.factorization p + β.factorization p) +
        (d₁.factorization p + d₂.factorization p)
    exact min_four_rectangle_le _ _ _ _ _ hab hde hdle hele
  exact Nat.le_of_dvd (by positivity) hdvd

/-- Removing the common gcd of `a` and a scale `C` removes the remaining
`C`-factor from a gcd. -/
private lemma gcd_scaled_eq {a C s : ℕ} (ha : 0 < a) (hC : 0 < C) :
    a.gcd (s * C) = a.gcd C * (a / a.gcd C).gcd s := by
  let g := a.gcd C
  let u := a / g
  let v := C / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left C ha
  have hau : g * u = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a C)
  have hCv : g * v = C := Nat.mul_div_cancel' (Nat.gcd_dvd_right a C)
  have huv : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  calc
    a.gcd (s * C) = (g * u).gcd (g * (s * v)) := by
      rw [← hau, ← hCv]
      congr 1
      ring
    _ = g * u.gcd (s * v) := Nat.gcd_mul_left _ _ _
    _ = g * u.gcd s := by rw [huv.symm.gcd_mul_right_cancel_right s]
    _ = a.gcd C * (a / a.gcd C).gcd s := rfl

/-- Direct form of the paper's four-gcd product estimate. -/
private lemma four_scaled_gcd_product_le {a C α β d₁ d₂ : ℕ}
    (ha : 0 < a) (hC : 0 < C) (hα : 0 < α) (hβ : 0 < β)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hαβ : α.Coprime β) (hd₁₂ : d₁.Coprime d₂)
    (hd₁div : d₁ ∣ α * β) (hd₂div : d₂ ∣ α * β) :
    a.gcd (α * d₁ * C) * a.gcd (α * d₂ * C) *
        a.gcd (β * d₁ * C) * a.gcd (β * d₂ * C) ≤
      a * (α * β) * (a.gcd C) ^ 3 * (d₁ * d₂) := by
  let g := a.gcd C
  let u := a / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left C ha
  have hu : 0 < u := Nat.div_pos (Nat.gcd_le_left C ha) hg
  have hau : g * u = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a C)
  rw [show α * d₁ * C = (α * d₁) * C by ring,
    show α * d₂ * C = (α * d₂) * C by ring,
    show β * d₁ * C = (β * d₁) * C by ring,
    show β * d₂ * C = (β * d₂) * C by ring,
    gcd_scaled_eq ha hC, gcd_scaled_eq ha hC,
    gcd_scaled_eq ha hC, gcd_scaled_eq ha hC]
  have hsmall := four_gcd_product_le hu hα hβ hd₁ hd₂ hαβ hd₁₂ hd₁div hd₂div
  change (g * u.gcd (α * d₁)) * (g * u.gcd (α * d₂)) *
      (g * u.gcd (β * d₁)) * (g * u.gcd (β * d₂)) ≤
    a * (α * β) * g ^ 3 * (d₁ * d₂)
  calc
    (g * u.gcd (α * d₁)) * (g * u.gcd (α * d₂)) *
        (g * u.gcd (β * d₁)) * (g * u.gcd (β * d₂)) =
      g ^ 4 * (u.gcd (α * d₁) * u.gcd (α * d₂) *
        u.gcd (β * d₁) * u.gcd (β * d₂)) := by ring
    _ ≤ g ^ 4 * (u * (α * β) * (d₁ * d₂)) := Nat.mul_le_mul_left _ hsmall
    _ = a * (α * β) * g ^ 3 * (d₁ * d₂) := by rw [← hau]; ring

/-- Eliminating the four gcds from their two product lower bounds.  This
is the root-free version of the geometric-mean calculation on page 14 of
the paper. -/
private lemma sixth_power_of_four_gcd_bounds {N q a C R g P : ℕ}
    (hN : 0 < N) (hq : 0 < q) (ha : 0 < a) (hC : 0 < C)
    (hR : 0 < R) (hg : 0 < g) (hP : 0 < P)
    (hPupper : P ≤ a * R * g ^ 3)
    (haLower : a ^ 4 ≤ N ^ 4 * P)
    (hRLower : R ^ 2 * C ^ 4 ≤ N ^ 4 * P)
    (hqg : q * g ≤ C) :
    q ^ 6 * R ≤ N ^ 8 := by
  have hcombo : a ^ 4 * R ^ 6 * C ^ 12 ≤ N ^ 16 * P ^ 4 := by
    have h := Nat.mul_le_mul haLower (pow_le_pow_left' hRLower 3)
    calc
      a ^ 4 * R ^ 6 * C ^ 12 = a ^ 4 * (R ^ 2 * C ^ 4) ^ 3 := by ring
      _ ≤ (N ^ 4 * P) * (N ^ 4 * P) ^ 3 := h
      _ = N ^ 16 * P ^ 4 := by ring
  have hcombo' : a ^ 4 * R ^ 6 * C ^ 12 ≤
      N ^ 16 * (a * R * g ^ 3) ^ 4 :=
    hcombo.trans (Nat.mul_le_mul_left _ (pow_le_pow_left' hPupper 4))
  have hRC : R ^ 2 * C ^ 12 ≤ N ^ 16 * g ^ 12 := by
    have hfactor : 0 < a ^ 4 * R ^ 4 := by positivity
    apply Nat.le_of_mul_le_mul_left (c := a ^ 4 * R ^ 4) ?_ hfactor
    calc
      (a ^ 4 * R ^ 4) * (R ^ 2 * C ^ 12) =
          a ^ 4 * R ^ 6 * C ^ 12 := by ring
      _ ≤ N ^ 16 * (a * R * g ^ 3) ^ 4 := hcombo'
      _ = (a ^ 4 * R ^ 4) * (N ^ 16 * g ^ 12) := by ring
  have hqpow : q ^ 12 * g ^ 12 ≤ C ^ 12 := by
    simpa only [mul_pow] using pow_le_pow_left' hqg 12
  have hqR : q ^ 12 * R ^ 2 ≤ N ^ 16 := by
    have hfactor : 0 < g ^ 12 := by positivity
    apply Nat.le_of_mul_le_mul_left (c := g ^ 12) ?_ hfactor
    calc
      g ^ 12 * (q ^ 12 * R ^ 2) = R ^ 2 * (q ^ 12 * g ^ 12) := by ring
      _ ≤ R ^ 2 * C ^ 12 := Nat.mul_le_mul_left _ hqpow
      _ ≤ N ^ 16 * g ^ 12 := hRC
      _ = g ^ 12 * N ^ 16 := by ring
  have hsq : (q ^ 6 * R) ^ 2 ≤ (N ^ 8) ^ 2 := by
    calc
      (q ^ 6 * R) ^ 2 = q ^ 12 * R ^ 2 := by ring
      _ ≤ N ^ 16 := hqR
      _ = (N ^ 8) ^ 2 := by ring
  exact (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp hsq

private lemma fourfold_mul_le {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℕ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄) :
    a₁ * a₂ * a₃ * a₄ ≤ b₁ * b₂ * b₃ * b₄ := by
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃) h₄

private lemma member_lt_card_mul_gcd (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (ha0 : a ≠ 0) : a < A.card * a.gcd b := by
  have hg : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have h := div_gcd_lt_card_of_not_grahamBound A hbad ha hb ha0
  rw [Nat.div_lt_iff_lt_mul hg] at h
  simpa only [mul_comm] using h

/-- If a prime divides the common scale of an extremal represented
rectangle but misses one member of a normalized strict counterexample,
then the sixth-power estimate needed by Lemma 4.1 holds. -/
private lemma largePrime_sixth_power_of_dvd_scale (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hbad : ¬ GrahamBound A)
    {q a α β d₁ d₂ C : ℕ} (hq : q.Prime) (haA : a ∈ A) (hqa : ¬q ∣ a)
    (hα : 0 < α) (hβ : 0 < β) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hC : 0 < C) (hαβ : α.Coprime β) (hd₁₂ : d₁.Coprime d₂)
    (hd₁div : d₁ ∣ α * β) (hd₂div : d₂ ∣ α * β)
    (hα₁ : α * d₁ * C ∈ A) (hα₂ : α * d₂ * C ∈ A)
    (hβ₁ : β * d₁ * C ∈ A) (hβ₂ : β * d₂ * C ∈ A)
    (hqC : q ∣ C) :
    q ^ 6 * (α * β) * (d₁ * d₂) ≤ A.card ^ 8 := by
  let N := A.card
  let r₁ := α * d₁ * C
  let r₂ := α * d₂ * C
  let r₃ := β * d₁ * C
  let r₄ := β * d₂ * C
  let g := a.gcd C
  let P := a.gcd r₁ * a.gcd r₂ * a.gcd r₃ * a.gcd r₄
  let R := (α * β) * (d₁ * d₂)
  have ha : 0 < a := Nat.pos_of_ne_zero fun hz ↦ h₀ (hz ▸ haA)
  have hN : 0 < N := by
    change 0 < A.card
    exact Finset.card_pos.mpr ⟨a, haA⟩
  have hg : 0 < g := Nat.gcd_pos_of_pos_left C ha
  have hR : 0 < R := by positivity
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have ha₁ : a ≤ N * a.gcd r₁ :=
    (member_lt_card_mul_gcd A hbad haA hα₁ ha.ne').le
  have ha₂ : a ≤ N * a.gcd r₂ :=
    (member_lt_card_mul_gcd A hbad haA hα₂ ha.ne').le
  have ha₃ : a ≤ N * a.gcd r₃ :=
    (member_lt_card_mul_gcd A hbad haA hβ₁ ha.ne').le
  have ha₄ : a ≤ N * a.gcd r₄ :=
    (member_lt_card_mul_gcd A hbad haA hβ₂ ha.ne').le
  have hr₁ : r₁ ≤ N * a.gcd r₁ := by
    have h := member_lt_card_mul_gcd A hbad hα₁ haA
      (by positivity)
    simpa only [Nat.gcd_comm] using h.le
  have hr₂ : r₂ ≤ N * a.gcd r₂ := by
    have h := member_lt_card_mul_gcd A hbad hα₂ haA
      (by positivity)
    simpa only [Nat.gcd_comm] using h.le
  have hr₃ : r₃ ≤ N * a.gcd r₃ := by
    have h := member_lt_card_mul_gcd A hbad hβ₁ haA
      (by positivity)
    simpa only [Nat.gcd_comm] using h.le
  have hr₄ : r₄ ≤ N * a.gcd r₄ := by
    have h := member_lt_card_mul_gcd A hbad hβ₂ haA
      (by positivity)
    simpa only [Nat.gcd_comm] using h.le
  have haLower : a ^ 4 ≤ N ^ 4 * P := by
    calc
      a ^ 4 = a * a * a * a := by ring
      _ ≤ (N * a.gcd r₁) * (N * a.gcd r₂) *
          (N * a.gcd r₃) * (N * a.gcd r₄) :=
        fourfold_mul_le ha₁ ha₂ ha₃ ha₄
      _ = N ^ 4 * P := by dsimp only [P]; ring
  have hRLower : R ^ 2 * C ^ 4 ≤ N ^ 4 * P := by
    calc
      R ^ 2 * C ^ 4 = r₁ * r₂ * r₃ * r₄ := by
        dsimp only [R, r₁, r₂, r₃, r₄]
        ring
      _ ≤ (N * a.gcd r₁) * (N * a.gcd r₂) *
          (N * a.gcd r₃) * (N * a.gcd r₄) :=
        fourfold_mul_le hr₁ hr₂ hr₃ hr₄
      _ = N ^ 4 * P := by dsimp only [P]; ring
  have hPupper : P ≤ a * R * g ^ 3 := by
    have h := four_scaled_gcd_product_le ha hC hα hβ hd₁ hd₂
      hαβ hd₁₂ hd₁div hd₂div
    dsimp only [P, r₁, r₂, r₃, r₄, R, g]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hgC : g ∣ C := Nat.gcd_dvd_right a C
  have hqgnot : ¬q ∣ g := fun h ↦ hqa (h.trans (Nat.gcd_dvd_left a C))
  have hqquot : q ∣ C / g := by
    have hprod : (C / g) * g = C := Nat.div_mul_cancel hgC
    have hqprod : q ∣ (C / g) * g := by
      rw [hprod]
      exact hqC
    exact (hq.dvd_mul.mp hqprod).resolve_right hqgnot
  have hquotpos : 0 < C / g := Nat.div_pos (Nat.le_of_dvd hC hgC) hg
  have hqg : q * g ≤ C := by
    calc
      q * g ≤ (C / g) * g := Nat.mul_le_mul_right g (Nat.le_of_dvd hquotpos hqquot)
      _ = C := Nat.div_mul_cancel hgC
  have hsix := sixth_power_of_four_gcd_bounds hN hq.pos ha hC hR hg hP
    hPupper haLower hRLower hqg
  simpa only [N, R, mul_assoc] using hsix

/-- Two distinct normalized represented multipliers, ordered after
pairwise gcd reduction, furnish the exact extremal rectangle used in
Lemma 4.1. -/
private lemma exists_reduced_rectangle (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α x y : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hx : x ∈ normalize (representedMultipliers A α (p - α)))
    (hy : y ∈ normalize (representedMultipliers A α (p - α)))
    (hxy : x ≠ y) :
    ∃ d₁ d₂ C : ℕ,
      0 < d₁ ∧ d₁ < d₂ ∧ 0 < C ∧ d₁.Coprime d₂ ∧
      d₁ ∣ α * (p - α) ∧ d₂ ∣ α * (p - α) ∧
      α * d₁ * C ∈ A ∧ α * d₂ * C ∈ A ∧
      (p - α) * d₁ * C ∈ A ∧ (p - α) * d₂ * C ∈ A ∧
      α * (p - α) * d₂ < A.card ^ 2 * d₁ ∧
      d₂ = max (x / x.gcd y) (y / x.gcd y) := by
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  have hR : R.Nonempty := by
    change x ∈ R.image (fun z ↦ z / R.gcd id) at hx
    obtain ⟨z, hz, _⟩ := Finset.mem_image.mp hx
    exact ⟨z, hz⟩
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
  let c := R.gcd id
  have hc : 0 < c := gcd_pos R hR₀ hR
  have hxdata := normalized_multiplier_data A hbad hp hα hαp hsq hR hx
  have hydata := normalized_multiplier_data A hbad hp hα hαp hsq hR hy
  let g := x.gcd y
  let u := x / g
  let v := y / g
  let C := g * c
  have hg : 0 < g := Nat.gcd_pos_of_pos_left y hxdata.1
  have hu : 0 < u := Nat.div_pos (Nat.gcd_le_left y hxdata.1) hg
  have hv : 0 < v := Nat.div_pos (Nat.gcd_le_right x hydata.1) hg
  have huc : u * g = x := Nat.div_mul_cancel (Nat.gcd_dvd_left x y)
  have hvc : v * g = y := Nat.div_mul_cancel (Nat.gcd_dvd_right x y)
  have huv : u ≠ v := by
    intro h
    apply hxy
    calc
      x = u * g := huc.symm
      _ = v * g := by rw [h]
      _ = y := hvc
  have hcop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  have huDiv : u ∣ α * β :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)).trans hxdata.2.1
  have hvDiv : v ∣ α * β :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)).trans hydata.2.1
  have hC : 0 < C := Nat.mul_pos hg hc
  have hαu : α * u * C ∈ A := by
    rw [show α * u * C = α * x * c by
      dsimp only [C]
      rw [← huc]
      ring]
    exact hxdata.2.2.2.1
  have hβu : β * u * C ∈ A := by
    rw [show β * u * C = β * x * c by
      dsimp only [C]
      rw [← huc]
      ring]
    exact hxdata.2.2.2.2
  have hαv : α * v * C ∈ A := by
    rw [show α * v * C = α * y * c by
      dsimp only [C]
      rw [← hvc]
      ring]
    exact hydata.2.2.2.1
  have hβv : β * v * C ∈ A := by
    rw [show β * v * C = β * y * c by
      dsimp only [C]
      rw [← hvc]
      ring]
    exact hydata.2.2.2.2
  by_cases huvlt : u < v
  · have hfac := factor_closeness_of_counterexample A hbad hα hβ hu hv hC
      hαβ hcop hsq hαu hβu hαv hβv
    have hprod : α * β * v < A.card ^ 2 * u := by
      have hm := mul_lt_mul hfac.2.2.2.1 hfac.2.2.2.2.2.le
        (Nat.mul_pos hβ (Nat.gcd_pos_of_pos_left β hv))
        (Nat.zero_le (A.card * u.gcd α))
      calc
        α * β * v = α * β * (v.gcd α * v.gcd β) := by
          congr 1
          exact hfac.2.1
        _ = (α * v.gcd α) * (β * v.gcd β) := by ring
        _ < (A.card * u.gcd α) * (A.card * u.gcd β) := hm
        _ = A.card ^ 2 * (u.gcd α * u.gcd β) := by ring
        _ = A.card ^ 2 * u := by rw [← hfac.1]
    refine ⟨u, v, C, hu, huvlt, hC, hcop, huDiv, hvDiv,
      hαu, hαv, hβu, hβv, ?_, ?_⟩
    · simpa only [β] using hprod
    · dsimp only [u, v, g]
      exact (max_eq_right huvlt.le).symm
  · have hvult : v < u := lt_of_le_of_ne (Nat.le_of_not_gt huvlt) (Ne.symm huv)
    have hfac := factor_closeness_of_counterexample A hbad hα hβ hv hu hC
      hαβ hcop.symm hsq hαv hβv hαu hβu
    have hprod : α * β * u < A.card ^ 2 * v := by
      have hm := mul_lt_mul hfac.2.2.2.1 hfac.2.2.2.2.2.le
        (Nat.mul_pos hβ (Nat.gcd_pos_of_pos_left β hu))
        (Nat.zero_le (A.card * v.gcd α))
      calc
        α * β * u = α * β * (u.gcd α * u.gcd β) := by
          congr 1
          exact hfac.2.1
        _ = (α * u.gcd α) * (β * u.gcd β) := by ring
        _ < (A.card * v.gcd α) * (A.card * v.gcd β) := hm
        _ = A.card ^ 2 * (v.gcd α * v.gcd β) := by ring
        _ = A.card ^ 2 * v := by rw [← hfac.1]
    refine ⟨v, u, C, hv, hvult, hC, hcop.symm, hvDiv, huDiv,
      hαv, hαu, hβv, hβu, ?_, ?_⟩
    · simpa only [β] using hprod
    · dsimp only [u, v, g]
      exact (max_eq_left hvult.le).symm

private lemma product_ge_of_near_sum {N G α β : ℕ}
    (hα : α ≤ N) (hβ : β ≤ N) (hG : 2 * G ≤ N)
    (hsum : 2 * N - 2 * G ≤ α + β) :
    N * (N - 2 * G) ≤ α * β := by
  have hαZ : (0 : ℤ) ≤ N - α := by
    apply sub_nonneg.mpr
    exact_mod_cast hα
  have hβZ : (0 : ℤ) ≤ N - β := by
    apply sub_nonneg.mpr
    exact_mod_cast hβ
  have hsumZ : (2 * (N : ℤ) - 2 * G) ≤ α + β := by
    have hcast : (((2 * N - 2 * G : ℕ) : ℤ)) ≤ (α + β : ℕ) := by
      exact_mod_cast hsum
    rw [Nat.cast_sub (by omega : 2 * G ≤ 2 * N)] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hprodZ : (0 : ℤ) ≤ ((N : ℤ) - α) * ((N : ℤ) - β) :=
    mul_nonneg hαZ hβZ
  have hsubZ : ((N - 2 * G : ℕ) : ℤ) = (N : ℤ) - 2 * G := by
    rw [Nat.cast_sub hG]
    norm_num
  have hfinal : (N : ℤ) * ((N - 2 * G : ℕ) : ℤ) ≤ α * β := by
    rw [hsubZ]
    nlinarith
  exact_mod_cast hfinal

/-- The supremum defining `globalD` is attained by a genuinely distinct
reduced pair as soon as one collision fiber exists. -/
private lemma exists_globalD_rectangle (A : Finset ℕ) (G : ℕ)
    (hbad : ¬ GrahamBound A) (hG : 0 < G) (hsmall : 4 * G ≤ A.card)
    (hcollision : ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α) :
    ∃ p α d₁ d₂ C : ℕ,
      p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G) ∧
      p.Prime ∧ α ∈ Finset.Icc ((p + 1) / 2) A.card ∧
      0 < d₁ ∧ d₁ < d₂ ∧ d₂ = globalD A G ∧ 0 < C ∧
      d₁.Coprime d₂ ∧ d₁ ∣ α * (p - α) ∧ d₂ ∣ α * (p - α) ∧
      α * d₁ * C ∈ A ∧ α * d₂ * C ∈ A ∧
      (p - α) * d₁ * C ∈ A ∧ (p - α) * d₂ * C ∈ A ∧
      α * (p - α) * d₂ < A.card ^ 2 * d₁ := by
  classical
  obtain ⟨p₀, hp₀win, hp₀, α₀, hα₀J, hr₀⟩ := hcollision
  have hp₀N : A.card < p₀ := by
    have hlo := (Finset.mem_Icc.mp hp₀win).1
    omega
  have hα₀ : 0 < α₀ := by
    have hlo := (Finset.mem_Icc.mp hα₀J).1
    omega
  have hα₀p : α₀ < p₀ := (Finset.mem_Icc.mp hα₀J).2.trans_lt hp₀N
  let R₀ := representedMultipliers A α₀ (p₀ - α₀)
  let B₀ := normalize R₀
  have hB₀card : B₀.card = R₀.card := normalize_card R₀
  have hB₀two : 1 < B₀.card := by
    change 2 ≤ R₀.card at hr₀
    omega
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := Finset.one_lt_card.mp hB₀two
  have hsq₀ := square_lt_of_window hG hsmall hp₀win hα₀J
  obtain ⟨d₁₀, d₂₀, C₀, hd₁₀, hd₁₂₀, hC₀, hcop₀,
      hd₁div₀, hd₂div₀, hα₁₀, hα₂₀, hβ₁₀, hβ₂₀, hprod₀, hd₂max₀⟩ :=
    exists_reduced_rectangle A hbad hp₀ hα₀ hα₀p hsq₀ hx₀ hy₀ hxy₀
  have hpair₀ : (x₀ / x₀.gcd y₀, y₀ / x₀.gcd y₀) ∈
      globalReducedPairs A G :=
    reducedPair_mem_global hp₀win hp₀ hα₀J hx₀ hy₀
  have hd₂D : d₂₀ ≤ globalD A G := by
    rw [hd₂max₀]
    exact Finset.le_sup
      (f := fun de : ℕ × ℕ ↦ max de.1 de.2) hpair₀
  have hDtwo : 2 ≤ globalD A G := by omega
  have hglobal : (globalReducedPairs A G).Nonempty := ⟨_, hpair₀⟩
  obtain ⟨de, hde, hDeq⟩ := Finset.exists_mem_eq_sup
    (globalReducedPairs A G) hglobal (fun z : ℕ × ℕ ↦ max z.1 z.2)
  rw [globalReducedPairs] at hde
  obtain ⟨p, hpF, hde⟩ := Finset.mem_biUnion.mp hde
  obtain ⟨hpwin, hp⟩ := Finset.mem_filter.mp hpF
  obtain ⟨α, hαJ, hde⟩ := Finset.mem_biUnion.mp hde
  rw [reducedPairs] at hde
  obtain ⟨⟨x, y⟩, hxyB, rfl⟩ := Finset.mem_image.mp hde
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxyB
  have hxy : x ≠ y := by
    intro h
    subst y
    have hxx : x / x.gcd x = 1 := by
      rw [Nat.gcd_self, Nat.div_self]
      exact Nat.pos_of_ne_zero fun hz ↦
        normalize_nonzero (representedMultipliers A α (p - α))
          (representedMultipliers_nonzero (by
            have hlo := (Finset.mem_Icc.mp hαJ).1
            have hp2 := hp.two_le
            have hhalf : 0 < (p + 1) / 2 := Nat.div_pos (by omega) (by norm_num)
            omega)) (hz ▸ hx)
    have hDone : globalD A G = 1 := by
      simpa only [globalD, Prod.fst, Prod.snd, hxx, max_self] using hDeq
    omega
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hαpos : 0 < α := by
    have hlo := (Finset.mem_Icc.mp hαJ).1
    omega
  have hαp : α < p := (Finset.mem_Icc.mp hαJ).2.trans_lt hpN
  have hsq := square_lt_of_window hG hsmall hpwin hαJ
  obtain ⟨d₁, d₂, C, hd₁, hd₁₂, hC, hcop, hd₁div, hd₂div,
      hα₁, hα₂, hβ₁, hβ₂, hprod, hd₂max⟩ :=
    exists_reduced_rectangle A hbad hp hαpos hαp hsq hx hy hxy
  have hd₂eq : d₂ = globalD A G := by
    calc
      d₂ = max (x / x.gcd y) (y / x.gcd y) := hd₂max
      _ = globalD A G := hDeq.symm
  exact ⟨p, α, d₁, d₂, C, hpwin, hp, hαJ, hd₁, hd₁₂, hd₂eq,
    hC, hcop, hd₁div, hd₂div, hα₁, hα₂, hβ₁, hβ₂, hprod⟩

/-- The extremal reduced coordinate cannot be small.  This is the exact
integer form of the estimate obtained from the last inequality of the
extremal rectangle: `N < 2 G D`. -/
private lemma card_lt_two_mul_G_mul_globalD (A : Finset ℕ) (G : ℕ)
    (hbad : ¬ GrahamBound A) (hG : 0 < G) (hsmall : 4 * G ≤ A.card)
    (hcollision : ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α) :
    A.card < 2 * G * globalD A G := by
  obtain ⟨p, α, d₁, d₂, _C, hpwin, _hp, hαJ, hd₁, hd₁₂, hd₂eq,
      _hC, _hcop, _hd₁div, _hd₂div, _hα₁, _hα₂, _hβ₁, _hβ₂, hprod⟩ :=
    exists_globalD_rectangle A G hbad hG hsmall hcollision
  have hN : 0 < A.card := by omega
  have htwog : 2 * G ≤ A.card := by omega
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hαle : α ≤ A.card := (Finset.mem_Icc.mp hαJ).2
  have hβle : p - α ≤ A.card := by
    have hlo := (Finset.mem_Icc.mp hαJ).1
    omega
  have hαp : α < p := hαle.trans_lt hpN
  have hsum : 2 * A.card - 2 * G ≤ α + (p - α) := by
    rw [Nat.add_sub_of_le hαp.le]
    exact (Finset.mem_Icc.mp hpwin).1
  have hproduct : A.card * (A.card - 2 * G) ≤ α * (p - α) :=
    product_ge_of_near_sum hαle hβle htwog hsum
  subst d₂
  have hscaled :
      A.card * (A.card - 2 * G) * globalD A G ≤
        α * (p - α) * globalD A G :=
    Nat.mul_le_mul_right (globalD A G) hproduct
  have hleft :
      A.card * (A.card - 2 * G) * globalD A G < A.card ^ 2 * d₁ :=
    hscaled.trans_lt hprod
  have hcancel :
      (A.card - 2 * G) * globalD A G < A.card * d₁ := by
    apply (Nat.mul_lt_mul_left hN).mp
    calc
      A.card * ((A.card - 2 * G) * globalD A G) =
          A.card * (A.card - 2 * G) * globalD A G := by ring
      _ < A.card ^ 2 * d₁ := hleft
      _ = A.card * (A.card * d₁) := by ring
  have hDpos : 0 < globalD A G := hd₁.trans hd₁₂
  have hd₁pred : d₁ ≤ globalD A G - 1 := by omega
  have hupper :
      A.card * d₁ ≤ A.card * (globalD A G - 1) :=
    Nat.mul_le_mul_left A.card hd₁pred
  have hstrict :
      (A.card - 2 * G) * globalD A G <
        A.card * (globalD A G - 1) := hcancel.trans_le hupper
  have hsumLeft :
      (A.card - 2 * G) * globalD A G +
          2 * G * globalD A G = A.card * globalD A G := by
    rw [← add_mul, Nat.sub_add_cancel htwog]
  have hsumRight :
      A.card * (globalD A G - 1) + A.card =
        A.card * globalD A G := by
    calc
      A.card * (globalD A G - 1) + A.card =
          A.card * ((globalD A G - 1) + 1) := by
        rw [mul_add, mul_one]
      _ = A.card * globalD A G := by
        rw [Nat.sub_add_cancel hDpos]
  omega

private lemma exists_prime_free_member_of_gcd_one (A : Finset ℕ)
    (hgcd : A.gcd id = 1) {q : ℕ} (hq : q.Prime) :
    ∃ a ∈ A, ¬q ∣ a := by
  by_contra h
  push Not at h
  have hqgcd : q ∣ A.gcd id := Finset.dvd_gcd fun a ha ↦ h a ha
  rw [hgcd] at hqgcd
  exact hq.not_dvd_one hqgcd

/-- The last, purely polynomial, part of Balasubramanian--Soundararajan
Lemma 4.1.  The preceding gcd argument supplies `hsix`; the lower bound for
the smaller reduced multiplier supplies `hd₁`.  Keeping this statement over
`ℕ` avoids cube roots in the formal proof. -/
private lemma largePrime_cube_bound {N G D q α β d₁ d₂ : ℕ}
    (hN : 0 < N) (hGN : 10 * G ≤ N)
    (hαβ : N * (N - 2 * G) ≤ α * β)
    (hd₂ : d₂ = D) (hd₁ : α * β * D ≤ N ^ 2 * d₁)
    (hsix : q ^ 6 * (α * β) * (d₁ * d₂) ≤ N ^ 8) :
    q ^ 3 * D ≤ (N + G) ^ 3 := by
  subst d₂
  have hGN' : G ≤ N := by omega
  have hten : 10 * G ≤ N := by omega
  have hDstep :
      q ^ 6 * (α * β * D) ^ 2 ≤ N ^ 2 * (q ^ 6 * (α * β) * (d₁ * D)) := by
    calc
      q ^ 6 * (α * β * D) ^ 2 =
          (q ^ 6 * (α * β) * D) * (α * β * D) := by ring
      _ ≤ (q ^ 6 * (α * β) * D) * (N ^ 2 * d₁) :=
        Nat.mul_le_mul_left _ hd₁
      _ = N ^ 2 * (q ^ 6 * (α * β) * (d₁ * D)) := by ring
  have hsq : (q ^ 3 * (α * β) * D) ^ 2 ≤ (N ^ 5) ^ 2 := by
    calc
      (q ^ 3 * (α * β) * D) ^ 2 = q ^ 6 * (α * β * D) ^ 2 := by ring
      _ ≤ N ^ 2 * (q ^ 6 * (α * β) * (d₁ * D)) := hDstep
      _ ≤ N ^ 2 * N ^ 8 := Nat.mul_le_mul_left _ hsix
      _ = (N ^ 5) ^ 2 := by ring
  have hbase : q ^ 3 * (α * β) * D ≤ N ^ 5 := by
    exact (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp hsq
  have hwindow : q ^ 3 * D * (N * (N - 2 * G)) ≤ N ^ 5 := by
    calc
      q ^ 3 * D * (N * (N - 2 * G)) ≤ q ^ 3 * D * (α * β) :=
        Nat.mul_le_mul_left _ hαβ
      _ = q ^ 3 * (α * β) * D := by ring
      _ ≤ N ^ 5 := hbase
  have hcancel : q ^ 3 * D * (N - 2 * G) ≤ N ^ 4 := by
    apply (Nat.mul_le_mul_left_iff hN).mp
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hwindow
  have hGsq : G ^ 2 ≤ N * G := by
    simpa [pow_two] using Nat.mul_le_mul_right G hGN'
  have hGcube : G ^ 3 ≤ N ^ 2 * G := by
    calc
      G ^ 3 = G ^ 2 * G := by ring
      _ ≤ (N * G) * G := Nat.mul_le_mul_right G hGsq
      _ ≤ (N * N) * G := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_le_mul_left N (Nat.mul_le_mul_left G hGN')
      _ = N ^ 2 * G := by ring
  have hNGsq : N * G ^ 2 ≤ N ^ 2 * G := by
    calc
      N * G ^ 2 ≤ N * (N * G) := Nat.mul_le_mul_left N hGsq
      _ = N ^ 2 * G := by ring
  have hloss : 3 * (N ^ 2 * G) + 5 * (N * G ^ 2) + 2 * G ^ 3 ≤
      10 * (N ^ 2 * G) := by
    omega
  have hgain : 10 * (N ^ 2 * G) ≤ N ^ 3 := by
    calc
      10 * (N ^ 2 * G) = N ^ 2 * (10 * G) := by ring
      _ ≤ N ^ 2 * N := Nat.mul_le_mul_left _ hten
      _ = N ^ 3 := by ring
  have hpoly : N ^ 4 ≤ (N + G) ^ 3 * (N - 2 * G) := by
    have h2G : 2 * G ≤ N := by omega
    have hscaled :
        3 * (N ^ 2 * G ^ 2) + 5 * (N * G ^ 3) + 2 * G ^ 4 ≤
          N ^ 3 * G := by
      calc
        3 * (N ^ 2 * G ^ 2) + 5 * (N * G ^ 3) + 2 * G ^ 4 =
            G * (3 * (N ^ 2 * G) + 5 * (N * G ^ 2) + 2 * G ^ 3) := by ring
        _ ≤ G * (10 * (N ^ 2 * G)) := Nat.mul_le_mul_left G hloss
        _ ≤ G * N ^ 3 := Nat.mul_le_mul_left G hgain
        _ = N ^ 3 * G := by ring
    have hscaledZ :
        3 * ((N : ℤ) ^ 2 * (G : ℤ) ^ 2) +
            5 * ((N : ℤ) * (G : ℤ) ^ 3) + 2 * (G : ℤ) ^ 4 ≤
          (N : ℤ) ^ 3 * G := by exact_mod_cast hscaled
    exact_mod_cast (show (N : ℤ) ^ 4 ≤
        ((N : ℤ) + G) ^ 3 * ((N : ℤ) - 2 * G) by nlinarith)
  have hpos : 0 < N - 2 * G := Nat.sub_pos_of_lt (by omega)
  exact (Nat.mul_le_mul_right_iff hpos).mp (hcancel.trans hpoly)

private lemma coprime_rectangle_dvd {M k d e : ℕ} (hde : d.Coprime e)
    (hd : k * d ∣ M) (he : k * e ∣ M) : k * (d * e) ∣ M := by
  have h := Nat.lcm_dvd hd he
  have hlcm : Nat.lcm d e = d * e :=
    Nat.lcm_eq_mul_iff.mpr (Or.inr (Or.inr hde.gcd_eq_one))
  rw [Nat.lcm_mul_left, hlcm] at h
  exact h

/-- The product of all five factors in a represented rectangle divides the
set lcm. -/
private lemma rectangle_product_dvd_lcm (A : Finset ℕ)
    {α β d₁ d₂ C : ℕ} (hαβ : α.Coprime β) (hd₁₂ : d₁.Coprime d₂)
    (hα₁ : α * d₁ * C ∈ A) (hα₂ : α * d₂ * C ∈ A)
    (hβ₁ : β * d₁ * C ∈ A) (hβ₂ : β * d₂ * C ∈ A) :
    α * β * d₁ * d₂ * C ∣ A.lcm id := by
  have hα₁Nat : α * d₁ * C ∣ A.lcm id := Finset.dvd_lcm hα₁
  have hα₂Nat : α * d₂ * C ∣ A.lcm id := Finset.dvd_lcm hα₂
  have hβ₁Nat : β * d₁ * C ∣ A.lcm id := Finset.dvd_lcm hβ₁
  have hβ₂Nat : β * d₂ * C ∣ A.lcm id := Finset.dvd_lcm hβ₂
  have hα₁' : (α * C) * d₁ ∣ A.lcm id := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hα₁Nat
  have hα₂' : (α * C) * d₂ ∣ A.lcm id := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hα₂Nat
  have hβ₁' : (β * C) * d₁ ∣ A.lcm id := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hβ₁Nat
  have hβ₂' : (β * C) * d₂ ∣ A.lcm id := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hβ₂Nat
  have hαrect := coprime_rectangle_dvd hd₁₂ hα₁' hα₂'
  have hβrect := coprime_rectangle_dvd hd₁₂ hβ₁' hβ₂'
  have hfull := coprime_rectangle_dvd hαβ
    (k := C * (d₁ * d₂))
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hαrect)
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hβrect)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hfull

private lemma div_factor_eq_complement {M x y K : ℕ}
    (hx : 0 < x) (hK : K ∣ M) (hxy : x * y = K) :
    M / x = y * (M / K) := by
  have hxdvd : x ∣ M := by
    have : x ∣ K := ⟨y, hxy.symm⟩
    exact this.trans hK
  apply Nat.eq_of_mul_eq_mul_left hx
  calc
    x * (M / x) = M := by
      rw [mul_comm]
      exact Nat.div_mul_cancel hxdvd
    _ = K * (M / K) := (Nat.mul_div_cancel' hK).symm
    _ = x * (y * (M / K)) := by rw [← hxy, mul_assoc]

/-- Complementing a represented rectangle in `lcm(A)` gives a second
represented rectangle with the same coprime factors and a complementary
common scale. -/
private lemma exists_reciprocal_rectangle (A : Finset ℕ) (h₀ : 0 ∉ A)
    {α β d₁ d₂ C : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hC : 0 < C) (hαβ : α.Coprime β) (hd₁₂ : d₁.Coprime d₂)
    (hα₁ : α * d₁ * C ∈ A) (hα₂ : α * d₂ * C ∈ A)
    (hβ₁ : β * d₁ * C ∈ A) (hβ₂ : β * d₂ * C ∈ A) :
    ∃ C' : ℕ, 0 < C' ∧
      α * d₁ * C' ∈ reciprocal A ∧ α * d₂ * C' ∈ reciprocal A ∧
      β * d₁ * C' ∈ reciprocal A ∧ β * d₂ * C' ∈ reciprocal A ∧
      C' = A.lcm id / (α * β * d₁ * d₂ * C) := by
  let M := A.lcm id
  let K := α * β * d₁ * d₂ * C
  let C' := M / K
  have hM : M ≠ 0 := by
    dsimp only [M]
    exact Finset.lcm_ne_zero_iff.mpr fun x hx h ↦ h₀ (h ▸ hx)
  have hKpos : 0 < K := by positivity
  have hK : K ∣ M := rectangle_product_dvd_lcm A hαβ hd₁₂ hα₁ hα₂ hβ₁ hβ₂
  have hC' : 0 < C' :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hK) hKpos
  have hα₁eq : M / (β * d₂ * C) = α * d₁ * C' := by
    apply div_factor_eq_complement (M := M) (K := K)
      (x := β * d₂ * C) (y := α * d₁) (by positivity) hK
    dsimp only [K]
    ring
  have hα₂eq : M / (β * d₁ * C) = α * d₂ * C' := by
    apply div_factor_eq_complement (M := M) (K := K)
      (x := β * d₁ * C) (y := α * d₂) (by positivity) hK
    dsimp only [K]
    ring
  have hβ₁eq : M / (α * d₂ * C) = β * d₁ * C' := by
    apply div_factor_eq_complement (M := M) (K := K)
      (x := α * d₂ * C) (y := β * d₁) (by positivity) hK
    dsimp only [K]
    ring
  have hβ₂eq : M / (α * d₁ * C) = β * d₂ * C' := by
    apply div_factor_eq_complement (M := M) (K := K)
      (x := α * d₁ * C) (y := β * d₂) (by positivity) hK
    dsimp only [K]
    ring
  refine ⟨C', hC', ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hα₁eq]
    exact reciprocal_mem A hβ₂
  · rw [← hα₂eq]
    exact reciprocal_mem A hβ₁
  · rw [← hβ₁eq]
    exact reciprocal_mem A hα₂
  · rw [← hβ₂eq]
    exact reciprocal_mem A hα₁

/-- Direct half of the large-prime exclusion.  A prime above the
cube-form threshold, and coprime to the two complementary factors, cannot
divide the common scale of the extremal rectangle. -/
private lemma largePrime_not_dvd_global_scale (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hcollision : ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α)
    {q : ℕ} (hq : q.Prime)
    (hqLarge : (A.card + G) ^ 3 < q ^ 3 * globalD A G) :
    ∃ p α d₁ d₂ C : ℕ,
      p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G) ∧
      p.Prime ∧ α ∈ Finset.Icc ((p + 1) / 2) A.card ∧
      0 < d₁ ∧ d₁ < d₂ ∧ d₂ = globalD A G ∧ 0 < C ∧
      d₁.Coprime d₂ ∧ d₁ ∣ α * (p - α) ∧ d₂ ∣ α * (p - α) ∧
      α * d₁ * C ∈ A ∧ α * d₂ * C ∈ A ∧
      (p - α) * d₁ * C ∈ A ∧ (p - α) * d₂ * C ∈ A ∧
      α * (p - α) * d₂ < A.card ^ 2 * d₁ ∧
      (¬q ∣ α * (p - α) → ¬q ∣ C) := by
  have hsmall : 4 * G ≤ A.card := by omega
  obtain ⟨p, α, d₁, d₂, C, hpwin, hp, hαJ, hd₁, hd₁₂, hd₂eq,
      hC, hcop, hd₁div, hd₂div, hα₁, hα₂, hβ₁, hβ₂, hprod⟩ :=
    exists_globalD_rectangle A G hbad hG hsmall hcollision
  refine ⟨p, α, d₁, d₂, C, hpwin, hp, hαJ, hd₁, hd₁₂, hd₂eq,
    hC, hcop, hd₁div, hd₂div, hα₁, hα₂, hβ₁, hβ₂, hprod, ?_⟩
  intro _hqαβ hqC
  obtain ⟨a, haA, hqa⟩ := exists_prime_free_member_of_gcd_one A hgcd hq
  have hα : 0 < α := by
    have hp2 := hp.two_le
    have hlo := (Finset.mem_Icc.mp hαJ).1
    have hhalf : 0 < (p + 1) / 2 := Nat.div_pos (by omega) (by norm_num)
    omega
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hαp : α < p := (Finset.mem_Icc.mp hαJ).2.trans_lt hpN
  have hβ : 0 < p - α := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime (p - α) := coprime_prime_sub hp hα hαp
  have hαle : α ≤ A.card := (Finset.mem_Icc.mp hαJ).2
  have hβle : p - α ≤ A.card := by
    have hlo := (Finset.mem_Icc.mp hαJ).1
    omega
  have htwog : 2 * G ≤ A.card := by omega
  have hsum : 2 * A.card - 2 * G ≤ α + (p - α) := by
    rw [Nat.add_sub_of_le hαp.le]
    exact (Finset.mem_Icc.mp hpwin).1
  have hproduct : A.card * (A.card - 2 * G) ≤ α * (p - α) :=
    product_ge_of_near_sum hαle hβle htwog hsum
  have hsix := largePrime_sixth_power_of_dvd_scale A h₀ hbad hq haA hqa
    hα hβ hd₁ (hd₁.trans hd₁₂) hC hαβ hcop hd₁div hd₂div
    hα₁ hα₂ hβ₁ hβ₂ hqC
  have hprod' : α * (p - α) * globalD A G ≤ A.card ^ 2 * d₁ := by
    rw [← hd₂eq]
    exact hprod.le
  have hcube := largePrime_cube_bound
    (N := A.card) (G := G) (D := globalD A G) (q := q)
    (α := α) (β := p - α) (d₁ := d₁) (d₂ := d₂)
    (by
      rw [Finset.card_pos]
      exact ⟨a, haA⟩)
    hGN hproduct hd₂eq hprod' hsix
  omega

/-- Full cube-form version of Balasubramanian--Soundararajan Lemma 4.1.
The extremal collision rectangle is chosen once.  Every prime above its
threshold which does not divide the two complementary factors misses every
member of the normalized counterexample. -/
private lemma exists_extremal_largePrime_exclusion (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hcollision : ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α) :
    ∃ p α d₁ d₂ C : ℕ,
      p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G) ∧
      p.Prime ∧ α ∈ Finset.Icc ((p + 1) / 2) A.card ∧
      0 < d₁ ∧ d₁ < d₂ ∧ d₂ = globalD A G ∧ 0 < C ∧
      d₁.Coprime d₂ ∧ d₁ ∣ α * (p - α) ∧ d₂ ∣ α * (p - α) ∧
      α * d₁ * C ∈ A ∧ α * d₂ * C ∈ A ∧
      (p - α) * d₁ * C ∈ A ∧ (p - α) * d₂ * C ∈ A ∧
      α * (p - α) * d₂ < A.card ^ 2 * d₁ ∧
      ∀ q : ℕ, q.Prime →
        (A.card + G) ^ 3 < q ^ 3 * globalD A G →
        ¬q ∣ α * (p - α) → ∀ a ∈ A, ¬q ∣ a := by
  have hsmall : 4 * G ≤ A.card := by omega
  obtain ⟨p, α, d₁, d₂, C, hpwin, hp, hαJ, hd₁, hd₁₂, hd₂eq,
      hC, hcop, hd₁div, hd₂div, hα₁, hα₂, hβ₁, hβ₂, hprod⟩ :=
    exists_globalD_rectangle A G hbad hG hsmall hcollision
  have hα : 0 < α := by
    have hp2 := hp.two_le
    have hlo := (Finset.mem_Icc.mp hαJ).1
    have hhalf : 0 < (p + 1) / 2 := Nat.div_pos (by omega) (by norm_num)
    omega
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hαp : α < p := (Finset.mem_Icc.mp hαJ).2.trans_lt hpN
  have hβ : 0 < p - α := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime (p - α) := coprime_prime_sub hp hα hαp
  have hαle : α ≤ A.card := (Finset.mem_Icc.mp hαJ).2
  have hβle : p - α ≤ A.card := by
    have hlo := (Finset.mem_Icc.mp hαJ).1
    omega
  have htwog : 2 * G ≤ A.card := by omega
  have hsum : 2 * A.card - 2 * G ≤ α + (p - α) := by
    rw [Nat.add_sub_of_le hαp.le]
    exact (Finset.mem_Icc.mp hpwin).1
  have hproduct : A.card * (A.card - 2 * G) ≤ α * (p - α) :=
    product_ge_of_near_sum hαle hβle htwog hsum
  have hprod' : α * (p - α) * globalD A G ≤ A.card ^ 2 * d₁ := by
    rw [← hd₂eq]
    exact hprod.le
  have hA : A.Nonempty := ⟨α * d₁ * C, hα₁⟩
  have hN : 0 < A.card := Finset.card_pos.mpr hA
  obtain ⟨C', hC', hrecα₁, hrecα₂, hrecβ₁, hrecβ₂, hC'eq⟩ :=
    exists_reciprocal_rectangle A h₀ hα hβ hd₁ (hd₁.trans hd₁₂) hC
      hαβ hcop hα₁ hα₂ hβ₁ hβ₂
  have hK : α * (p - α) * d₁ * d₂ * C ∣ A.lcm id :=
    rectangle_product_dvd_lcm A hαβ hcop hα₁ hα₂ hβ₁ hβ₂
  refine ⟨p, α, d₁, d₂, C, hpwin, hp, hαJ, hd₁, hd₁₂, hd₂eq,
    hC, hcop, hd₁div, hd₂div, hα₁, hα₂, hβ₁, hβ₂, hprod, ?_⟩
  intro q hq hqLarge hqαβ a haA
  have hqC : ¬q ∣ C := by
    intro hqC
    obtain ⟨z, hzA, hqz⟩ := exists_prime_free_member_of_gcd_one A hgcd hq
    have hsix := largePrime_sixth_power_of_dvd_scale A h₀ hbad hq hzA hqz
      hα hβ hd₁ (hd₁.trans hd₁₂) hC hαβ hcop hd₁div hd₂div
      hα₁ hα₂ hβ₁ hβ₂ hqC
    have hcube := largePrime_cube_bound
      (N := A.card) (G := G) (D := globalD A G) (q := q)
      (α := α) (β := p - α) (d₁ := d₁) (d₂ := d₂)
      hN hGN hproduct hd₂eq hprod' hsix
    omega
  intro hqa
  have hqM : q ∣ A.lcm id := hqa.trans (Finset.dvd_lcm haA)
  have hqK₀ : ¬q ∣ α * (p - α) * d₁ * d₂ := by
    intro h
    rcases hq.dvd_mul.mp h with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · exact hqαβ h
      · exact hqαβ (h.trans hd₁div)
    · exact hqαβ (h.trans hd₂div)
  have hMprod :
      (α * (p - α) * d₁ * d₂) * (C * C') = A.lcm id := by
    calc
      (α * (p - α) * d₁ * d₂) * (C * C') =
          (α * (p - α) * d₁ * d₂ * C) *
            (A.lcm id / (α * (p - α) * d₁ * d₂ * C)) := by
              rw [hC'eq]
              ring
      _ = A.lcm id := Nat.mul_div_cancel' hK
  have hqprod : q ∣ (α * (p - α) * d₁ * d₂) * (C * C') := by
    rw [hMprod]
    exact hqM
  have hqCC' : q ∣ C * C' := (hq.dvd_mul.mp hqprod).resolve_left hqK₀
  have hqC' : q ∣ C' := (hq.dvd_mul.mp hqCC').resolve_left hqC
  obtain ⟨z, hzA, hqzrec⟩ :=
    exists_prime_free_reciprocal_member A h₀ hA hq
  have hsixRec := largePrime_sixth_power_of_dvd_scale (reciprocal A)
    (reciprocal_nonzero A h₀) (not_grahamBound_reciprocal A h₀ hbad)
    hq (reciprocal_mem A hzA) hqzrec hα hβ hd₁ (hd₁.trans hd₁₂)
    hC' hαβ hcop hd₁div hd₂div hrecα₁ hrecα₂ hrecβ₁ hrecβ₂ hqC'
  have hsix : q ^ 6 * (α * (p - α)) * (d₁ * d₂) ≤ A.card ^ 8 := by
    rw [reciprocal_card A h₀] at hsixRec
    exact hsixRec
  have hcube := largePrime_cube_bound
    (N := A.card) (G := G) (D := globalD A G) (q := q)
    (α := α) (β := p - α) (d₁ := d₁) (d₂ := d₂)
    hN hGN hproduct hd₂eq hprod' hsix
  omega

private def exceptionalPrimeFactors (N G D n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun q ↦ (N + G) ^ 3 < q ^ 3 * D

/-- Three distinct primes above the cube threshold would have product
larger than `N²`; hence an integer at most `N²` has at most two such prime
factors.  This is the second assertion of Lemma 4.1 without cube roots. -/
private lemma exceptionalPrimeFactors_card_le_two {N G D n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (hnN : n ≤ N ^ 2) (hD : D ≤ N) :
    (exceptionalPrimeFactors N G D n).card ≤ 2 := by
  by_contra hcard
  have hthree : 2 < (exceptionalPrimeFactors N G D n).card := by omega
  obtain ⟨q₁, hq₁, q₂, hq₂, q₃, hq₃, h₁₂, h₁₃, h₂₃⟩ :=
    Finset.two_lt_card.mp hthree
  have hq₁' := Finset.mem_filter.mp hq₁
  have hq₂' := Finset.mem_filter.mp hq₂
  have hq₃' := Finset.mem_filter.mp hq₃
  have hp₁ : q₁.Prime := (Nat.mem_primeFactors.mp hq₁'.1).1
  have hp₂ : q₂.Prime := (Nat.mem_primeFactors.mp hq₂'.1).1
  have hp₃ : q₃.Prime := (Nat.mem_primeFactors.mp hq₃'.1).1
  have hd₁ : q₁ ∣ n := (Nat.mem_primeFactors.mp hq₁'.1).2.1
  have hd₂ : q₂ ∣ n := (Nat.mem_primeFactors.mp hq₂'.1).2.1
  have hd₃ : q₃ ∣ n := (Nat.mem_primeFactors.mp hq₃'.1).2.1
  have hc₁₂ : q₁.Coprime q₂ := (Nat.coprime_primes hp₁ hp₂).mpr h₁₂
  have hc₁₃ : q₁.Coprime q₃ := (Nat.coprime_primes hp₁ hp₃).mpr h₁₃
  have hc₂₃ : q₂.Coprime q₃ := (Nat.coprime_primes hp₂ hp₃).mpr h₂₃
  have hd₁₂ : q₁ * q₂ ∣ n := hc₁₂.mul_dvd_of_dvd_of_dvd hd₁ hd₂
  have hc₁₂₃ : (q₁ * q₂).Coprime q₃ :=
    Nat.coprime_mul_iff_left.mpr ⟨hc₁₃, hc₂₃⟩
  have hd₁₂₃ : q₁ * q₂ * q₃ ∣ n :=
    hc₁₂₃.mul_dvd_of_dvd_of_dvd hd₁₂ hd₃
  have hprodN : q₁ * q₂ * q₃ ≤ N ^ 2 :=
    (Nat.le_of_dvd hn hd₁₂₃).trans hnN
  let T := (N + G) ^ 3
  have hT : 0 < T := by dsimp only [T]; positivity
  have h₁ : T < q₁ ^ 3 * D := hq₁'.2
  have h₂ : T < q₂ ^ 3 * D := hq₂'.2
  have h₃ : T < q₃ ^ 3 * D := hq₃'.2
  have h₁₂mul : T * T < (q₁ ^ 3 * D) * (q₂ ^ 3 * D) :=
    mul_lt_mul h₁ h₂.le hT (by positivity)
  have hmul : T ^ 3 < ((q₁ * q₂ * q₃) * D) ^ 3 := by
    calc
      T ^ 3 = (T * T) * T := by ring
      _ < ((q₁ ^ 3 * D) * (q₂ ^ 3 * D)) * (q₃ ^ 3 * D) :=
        mul_lt_mul h₁₂mul h₃.le (by positivity) (by positivity)
      _ = ((q₁ * q₂ * q₃) * D) ^ 3 := by ring
  have hroot : T < (q₁ * q₂ * q₃) * D :=
    (Nat.pow_lt_pow_iff_left (by omega : 3 ≠ 0)).mp hmul
  have hupper : (q₁ * q₂ * q₃) * D ≤ N ^ 3 := by
    calc
      (q₁ * q₂ * q₃) * D ≤ N ^ 2 * N :=
        Nat.mul_le_mul hprodN hD
      _ = N ^ 3 := by ring
  have hTN : N ^ 3 ≤ T := by
    dsimp only [T]
    exact pow_le_pow_left' (Nat.le_add_right N G) 3
  omega

private lemma at_most_one_large_prime_factor {N G D n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (hnN : n ≤ N) (hD : D ≤ N) :
    ((n.primeFactors.filter fun q ↦ (N + G) ^ 3 < q ^ 3 * D).card) ≤ 1 := by
  by_contra hcard
  have htwo : 1 < (n.primeFactors.filter fun q ↦
      (N + G) ^ 3 < q ^ 3 * D).card := by omega
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp htwo
  have hq' := Finset.mem_filter.mp hq
  have hr' := Finset.mem_filter.mp hr
  have hpq : q.Prime := (Nat.mem_primeFactors.mp hq'.1).1
  have hpr : r.Prime := (Nat.mem_primeFactors.mp hr'.1).1
  have hqd : q ∣ n := (Nat.mem_primeFactors.mp hq'.1).2.1
  have hrd : r ∣ n := (Nat.mem_primeFactors.mp hr'.1).2.1
  have hcop : q.Coprime r := (Nat.coprime_primes hpq hpr).mpr hqr
  have hqrd : q * r ∣ n := hcop.mul_dvd_of_dvd_of_dvd hqd hrd
  have hqrN : q * r ≤ N := (Nat.le_of_dvd hn hqrd).trans hnN
  have hfour : 4 ≤ q * r := by
    simpa using Nat.mul_le_mul hpq.two_le hpr.two_le
  have hNone : 1 < N := by omega
  let T := (N + G) ^ 3
  have hT : 0 < T := by dsimp only [T]; positivity
  have hmul : T ^ 2 < (q * r) ^ 3 * D ^ 2 := by
    calc
      T ^ 2 = T * T := by ring
      _ < (q ^ 3 * D) * (r ^ 3 * D) :=
        mul_lt_mul hq'.2 hr'.2.le hT (by positivity)
      _ = (q * r) ^ 3 * D ^ 2 := by ring
  have hupper : (q * r) ^ 3 * D ^ 2 ≤ N ^ 5 := by
    calc
      (q * r) ^ 3 * D ^ 2 ≤ N ^ 3 * N ^ 2 :=
        Nat.mul_le_mul (pow_le_pow_left' hqrN 3) (pow_le_pow_left' hD 2)
      _ = N ^ 5 := by ring
  have hlower : N ^ 6 ≤ T ^ 2 := by
    dsimp only [T]
    have h := pow_le_pow_left' (Nat.le_add_right N G) 6
    simpa only [← pow_mul] using h
  have hstrict : N ^ 5 < N ^ 6 := by
    exact Nat.pow_lt_pow_right hNone (by omega)
  omega

/-- A represented fiber is empty when either factor contains a
nonexceptional prime excluded from every member of `A`. -/
private lemma representationCount_eq_zero_of_excluded_prime
    (A : Finset ℕ) {p α q : ℕ} (hα : 0 < α) (hq : q.Prime)
    (hqα : q ∣ α) (hexcl : ∀ a ∈ A, ¬q ∣ a) :
    representationCount A p α = 0 := by
  rw [representationCount]
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro d hd
  have hdata := (mem_representedMultipliers hα).mp hd
  exact hexcl (α * d) hdata.2.1 (dvd_mul_of_dvd_left hqα d)

private lemma representationCount_eq_zero_of_excluded_complement_prime
    (A : Finset ℕ) {p α q : ℕ} (hα : 0 < α) (hq : q.Prime)
    (hβ : 0 < p - α) (hqβ : q ∣ p - α) (hexcl : ∀ a ∈ A, ¬q ∣ a) :
    representationCount A p α = 0 := by
  rw [representationCount]
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro d hd
  have hdata := (mem_representedMultipliers hα).mp hd
  exact hexcl ((p - α) * d) hdata.2.2 (dvd_mul_of_dvd_left hqβ d)

/-- Once the extremal product has been fixed, a threshold-large prime
outside its exceptional prime-factor set is excluded from every member of
`A`.  Consequently, if it divides either factor of another collision
parameter, that entire representation fiber is empty. -/
private lemma representationCount_eq_zero_of_nonexceptional_large_factor
    (A : Finset ℕ) {G D p₀ α₀ p α q : ℕ}
    (hα₀ : 0 < α₀) (hα₀p : α₀ < p₀)
    (hα : 0 < α) (hβ : 0 < p - α)
    (hq : q.Prime) (hqlarge : (A.card + G) ^ 3 < q ^ 3 * D)
    (hexcl : ∀ r : ℕ, r.Prime → (A.card + G) ^ 3 < r ^ 3 * D →
      ¬r ∣ α₀ * (p₀ - α₀) → ∀ a ∈ A, ¬r ∣ a)
    (hqnon : q ∉ exceptionalPrimeFactors A.card G D
      (α₀ * (p₀ - α₀)))
    (hqfactor : q ∣ α ∨ q ∣ p - α) :
    representationCount A p α = 0 := by
  have hn : 0 < α₀ * (p₀ - α₀) :=
    Nat.mul_pos hα₀ (Nat.sub_pos_of_lt hα₀p)
  have hqbase : ¬q ∣ α₀ * (p₀ - α₀) := by
    intro hqdvd
    apply hqnon
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_primeFactors.mpr ⟨hq, hqdvd, hn.ne'⟩, hqlarge⟩
  have hmiss : ∀ a ∈ A, ¬q ∣ a := hexcl q hq hqlarge hqbase
  rcases hqfactor with hqα | hqβ
  · exact representationCount_eq_zero_of_excluded_prime A hα hq hqα hmiss
  · exact representationCount_eq_zero_of_excluded_complement_prime
      A hα hq hβ hqβ hmiss

/-- Uniform consequence of Lemma 4.1.  There is one fixed set of at most
two exceptional primes such that, throughout the whole short prime window,
every coordinate having a nonexceptional threshold-large prime factor has
zero representation multiplicity. -/
private lemma exists_fixed_exceptional_primes (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hcollision : ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α) :
    ∃ E : Finset ℕ, E.card ≤ 2 ∧ (∀ q ∈ E, q.Prime) ∧
      (∀ q ∈ E, (A.card + G) ^ 3 < q ^ 3 * globalD A G) ∧
      ∀ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
        p.Prime → ∀ α ∈ Finset.Icc ((p + 1) / 2) A.card,
          ∀ q : ℕ, q.Prime →
            (A.card + G) ^ 3 < q ^ 3 * globalD A G → q ∉ E →
            (q ∣ α ∨ q ∣ p - α) →
            representationCount A p α = 0 := by
  have hsmall : 4 * G ≤ A.card := by omega
  obtain ⟨p₀, α₀, d₁, d₂, C, hp₀win, hp₀, hα₀J,
      _hd₁, _hd₁₂, _hd₂eq, _hC, _hcop, _hd₁div, _hd₂div,
      _hα₁, _hα₂, _hβ₁, _hβ₂, _hprod, hexcl⟩ :=
    exists_extremal_largePrime_exclusion A G h₀ hgcd hbad hG hGN hcollision
  let E := exceptionalPrimeFactors A.card G (globalD A G)
    (α₀ * (p₀ - α₀))
  have hN : 0 < A.card := by omega
  have hp₀N : A.card < p₀ := by
    have hlo := (Finset.mem_Icc.mp hp₀win).1
    omega
  have hα₀ : 0 < α₀ := by
    have hlo := (Finset.mem_Icc.mp hα₀J).1
    have hp2 := hp₀.two_le
    have hhalf : 0 < (p₀ + 1) / 2 := Nat.div_pos (by omega) (by norm_num)
    omega
  have hα₀p : α₀ < p₀ := (Finset.mem_Icc.mp hα₀J).2.trans_lt hp₀N
  have hβ0le : p₀ - α₀ ≤ A.card := by
    have hlo := (Finset.mem_Icc.mp hα₀J).1
    have hpceil : p₀ ≤ 2 * ((p₀ + 1) / 2) := by omega
    have hpdouble : p₀ ≤ 2 * α₀ :=
      hpceil.trans (Nat.mul_le_mul_left 2 hlo)
    have hsub : p₀ - α₀ ≤ α₀ := by omega
    exact hsub.trans (Finset.mem_Icc.mp hα₀J).2
  have hprodN : α₀ * (p₀ - α₀) ≤ A.card ^ 2 := by
    calc
      α₀ * (p₀ - α₀) ≤ A.card * A.card :=
        Nat.mul_le_mul (Finset.mem_Icc.mp hα₀J).2 hβ0le
      _ = A.card ^ 2 := by ring
  have hEcard : E.card ≤ 2 := by
    apply exceptionalPrimeFactors_card_le_two hN
      (Nat.mul_pos hα₀ (Nat.sub_pos_of_lt hα₀p)) hprodN
    exact globalD_le_card A G hbad hG hsmall
  have hEprime : ∀ q ∈ E, q.Prime := by
    intro q hqE
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hqE).1).1
  have hElarge : ∀ q ∈ E,
      (A.card + G) ^ 3 < q ^ 3 * globalD A G := by
    intro q hqE
    exact (Finset.mem_filter.mp hqE).2
  refine ⟨E, hEcard, hEprime, hElarge, ?_⟩
  intro p hpwin hp α hαJ q hq hqlarge hqE hqfactor
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hα : 0 < α := by
    have hlo := (Finset.mem_Icc.mp hαJ).1
    have hp2 := hp.two_le
    have hhalf : 0 < (p + 1) / 2 := Nat.div_pos (by omega) (by norm_num)
    omega
  have hαp : α < p := (Finset.mem_Icc.mp hαJ).2.trans_lt hpN
  exact representationCount_eq_zero_of_nonexceptional_large_factor A
    hα₀ hα₀p hα (Nat.sub_pos_of_lt hαp) hq hqlarge hexcl hqE hqfactor

private def largePrimeFactors (N G D n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun q ↦ (N + G) ^ 3 < q ^ 3 * D

private def nonexceptionalLargePrimeFactors
    (N G D : ℕ) (E : Finset ℕ) (n : ℕ) : Finset ℕ :=
  largePrimeFactors N G D n \ E

private def nonexceptionalLargePrimeIncidences
    (N G D p : ℕ) (E : Finset ℕ) : Finset ((n : ℕ) × ℕ) :=
  (Finset.Icc (p - N) N).sigma fun n ↦
    nonexceptionalLargePrimeFactors N G D E n

private def largePrimeIncidences (N G D p : ℕ) : Finset ((n : ℕ) × ℕ) :=
  (Finset.Icc (p - N) N).sigma fun n ↦ largePrimeFactors N G D n

/-- Multipliers for which the lower endpoint of the interval already
forces the cube-form large-prime threshold. -/
private def safeLargePrimeMultipliers (N G D p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun r ↦
    (N + G) ^ 3 * r ^ 3 < (p - N) ^ 3 * D

/-- Prime/multiplier pairs counted in the lower-bound argument of
Lemma 4.2.  The product condition is kept integral to avoid floor and
ceiling artifacts. -/
private def safeLargePrimeCandidates
    (N G D p : ℕ) : Finset ((r : ℕ) × ℕ) :=
  (safeLargePrimeMultipliers N G D p).sigma fun r ↦
    (Finset.Icc 2 N).filter fun q ↦
      q.Prime ∧ p - N ≤ q * r ∧ q * r ≤ N

/-- For a positive multiplier, the product interval for its prime factor
is exactly an ordinary prime interval after applying floor and ceiling
division. -/
private lemma primeProductCandidates_eq_Icc
    {N lo r : ℕ} (hr : 0 < r) :
    (Finset.Icc 2 N).filter (fun q ↦
        q.Prime ∧ lo ≤ q * r ∧ q * r ≤ N) =
      (Finset.Icc (max 2 (lo ⌈/⌉ r)) (N / r)).filter Nat.Prime := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff]
  constructor
  · rintro ⟨⟨hq2, _hqN⟩, hp, hlo, hi⟩
    refine ⟨⟨⟨hq2, ?_⟩, (Nat.le_div_iff_mul_le hr).2 hi⟩, hp⟩
    apply (ceilDiv_le_iff_le_mul hr).2
    simpa only [mul_comm] using hlo
  · rintro ⟨⟨⟨hq2, hlo⟩, hi⟩, hp⟩
    have hir := (Nat.le_div_iff_mul_le hr).1 hi
    refine ⟨⟨hq2, (Nat.le_mul_of_pos_right q hr).trans hir⟩,
      hp, ?_, hir⟩
    have hceil := (ceilDiv_le_iff_le_mul hr).1 hlo
    simpa only [mul_comm] using hceil

private lemma primeProductCandidates_card_eq_primeCounting
    {N lo r : ℕ} (hr : 0 < r)
    (hinterval : max 2 (lo ⌈/⌉ r) ≤ N / r) :
    ((Finset.Icc 2 N).filter (fun q ↦
        q.Prime ∧ lo ≤ q * r ∧ q * r ≤ N)).card =
      Nat.primeCounting (N / r) -
        Nat.primeCounting (max 2 (lo ⌈/⌉ r) - 1) := by
  rw [primeProductCandidates_eq_Icc hr]
  exact card_filter_prime_Icc_eq hinterval

/-- Reindexing `n=qr`: every safe prime/multiplier pair is a genuinely
large-prime incidence. -/
private lemma safeLargePrimeCandidates_card_le_incidence
    {N G D p : ℕ} :
    (safeLargePrimeCandidates N G D p).card ≤
      (largePrimeIncidences N G D p).card := by
  classical
  let S := safeLargePrimeCandidates N G D p
  let L := largePrimeIncidences N G D p
  let toIncidence : ((r : ℕ) × ℕ) → ((n : ℕ) × ℕ) :=
    fun rq ↦ ⟨rq.2 * rq.1, rq.2⟩
  apply Finset.card_le_card_of_injOn toIncidence
  · intro rq hrq
    have hmem := Finset.mem_sigma.mp hrq
    rcases rq with ⟨r, q⟩
    have hr := Finset.mem_filter.mp hmem.1
    have hq := Finset.mem_filter.mp hmem.2
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr.1).1
    have hqpos : 0 < q := hq.2.1.pos
    have hlargeMul :
        (N + G) ^ 3 * r ^ 3 < (q ^ 3 * D) * r ^ 3 := by
      calc
        (N + G) ^ 3 * r ^ 3 < (p - N) ^ 3 * D := hr.2
        _ ≤ (q * r) ^ 3 * D :=
          Nat.mul_le_mul_right D (pow_le_pow_left' hq.2.2.1 3)
        _ = (q ^ 3 * D) * r ^ 3 := by ring
    have hlarge : (N + G) ^ 3 < q ^ 3 * D :=
      (Nat.mul_lt_mul_right (pow_pos hrpos 3)).mp hlargeMul
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hq.2.2.1, hq.2.2.2⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_primeFactors.mpr ⟨hq.2.1, dvd_mul_right q r,
      (Nat.mul_pos hqpos hrpos).ne'⟩, hlarge⟩
  · intro rq hrq st _ heq
    have hrqmem := Finset.mem_sigma.mp hrq
    rcases rq with ⟨r, q⟩
    rcases st with ⟨s, t⟩
    have hqpos : 0 < q := (Finset.mem_filter.mp hrqmem.2).2.1.pos
    simp only [toIncidence, Sigma.mk.injEq] at heq ⊢
    have hqt : q = t := eq_of_heq heq.2
    subst t
    have hrs : r = s := Nat.mul_left_cancel hqpos heq.1
    exact ⟨hrs, HEq.rfl⟩

/-- Packing bound for multiples in an inclusive natural interval. -/
private lemma card_multiples_Icc_le {l u q : ℕ} (hq : 0 < q) :
    ((Finset.Icc l u).filter fun n ↦ q ∣ n).card ≤ (u - l) / q + 1 := by
  classical
  let S := (Finset.Icc l u).filter fun n ↦ q ∣ n
  let f : ℕ → ℕ := fun n ↦ (n - l) / q
  change S.card ≤ (u - l) / q + 1
  rw [← Finset.card_range ((u - l) / q + 1)]
  apply Finset.card_le_card_of_injOn f
  · intro n hn
    have hnI := (Finset.mem_filter.mp hn).1
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    exact Nat.div_le_div_right (Nat.sub_le_sub_right (Finset.mem_Icc.mp hnI).2 l)
  · intro n hn m hm heq
    have hn' := Finset.mem_filter.mp hn
    have hm' := Finset.mem_filter.mp hm
    have hnl : l ≤ n := (Finset.mem_Icc.mp hn'.1).1
    have hml : l ≤ m := (Finset.mem_Icc.mp hm'.1).1
    dsimp only [f] at heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · have hdiff : q ∣ m - n := Nat.dvd_sub hm'.2 hn'.2
      have hqdiff : q ≤ m - n := Nat.le_of_dvd (Nat.sub_pos_of_lt hnm) hdiff
      have hnmod := Nat.mod_lt (n - l) hq
      have hmmod := Nat.mod_lt (m - l) hq
      have hnalg := Nat.mod_add_div (n - l) q
      have hmalg := Nat.mod_add_div (m - l) q
      rw [← heq] at hmalg
      have hnrec := Nat.sub_add_cancel hnl
      have hmrec := Nat.sub_add_cancel hml
      omega
    · have hdiff : q ∣ n - m := Nat.dvd_sub hn'.2 hm'.2
      have hqdiff : q ≤ n - m := Nat.le_of_dvd (Nat.sub_pos_of_lt hmn) hdiff
      have hnmod := Nat.mod_lt (n - l) hq
      have hmmod := Nat.mod_lt (m - l) hq
      have hnalg := Nat.mod_add_div (n - l) q
      have hmalg := Nat.mod_add_div (m - l) q
      rw [heq] at hnalg
      have hnrec := Nat.sub_add_cancel hnl
      have hmrec := Nat.sub_add_cancel hml
      omega

private def exceptionalLargePrimeIncidences
    (N G D p : ℕ) (E : Finset ℕ) : Finset ((n : ℕ) × ℕ) :=
  (Finset.Icc (p - N) N).sigma fun n ↦ largePrimeFactors N G D n ∩ E

/-- The incidences supplied by primes belonging to the fixed exceptional
set are bounded by the elementary count of their multiples in the interval. -/
private lemma exceptionalLargePrimeIncidences_card_le
    {N G D p : ℕ} (E : Finset ℕ) (hNp : N ≤ p) (hp2 : p ≤ 2 * N)
    (hEprime : ∀ q ∈ E, q.Prime) :
    (exceptionalLargePrimeIncidences N G D p E).card ≤
      E.sum fun q ↦ (2 * N - p) / q + 1 := by
  classical
  let S := exceptionalLargePrimeIncidences N G D p E
  let T : Finset ((q : ℕ) × ℕ) := E.sigma fun q ↦
    (Finset.Icc (p - N) N).filter fun n ↦ q ∣ n
  let swap : ((n : ℕ) × ℕ) → ((q : ℕ) × ℕ) :=
    fun nq ↦ ⟨nq.2, nq.1⟩
  have hmaps : Set.MapsTo swap (↑S : Set ((n : ℕ) × ℕ))
      (↑T : Set ((q : ℕ) × ℕ)) := by
    intro nq hnq
    have hmem := Finset.mem_sigma.mp hnq
    rcases nq with ⟨n, q⟩
    apply Finset.mem_sigma.mpr
    refine ⟨(Finset.mem_inter.mp hmem.2).2, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hmem.1, ?_⟩
    exact (Nat.mem_primeFactors.mp
      (Finset.mem_filter.mp (Finset.mem_inter.mp hmem.2).1).1).2.1
  have hinj : Set.InjOn swap (↑S : Set ((n : ℕ) × ℕ)) := by
    intro nq _ mr _ heq
    rcases nq with ⟨n, q⟩
    rcases mr with ⟨m, r⟩
    simp only [swap, Sigma.mk.injEq] at heq ⊢
    exact ⟨eq_of_heq heq.2, heq_of_eq heq.1⟩
  calc
    S.card ≤ T.card := Finset.card_le_card_of_injOn swap hmaps hinj
    _ = ∑ q ∈ E, ((Finset.Icc (p - N) N).filter fun n ↦ q ∣ n).card := by
      simp only [T, Finset.card_sigma]
    _ ≤ ∑ q ∈ E, ((2 * N - p) / q + 1) := by
      apply Finset.sum_le_sum
      intro q hqE
      have hqpos := (hEprime q hqE).pos
      have hlen : N - (p - N) = 2 * N - p := by omega
      simpa only [hlen] using
        (card_multiples_Icc_le (l := p - N) (u := N) hqpos)
    _ = E.sum fun q ↦ (2 * N - p) / q + 1 := rfl

/-- Partition all threshold-large incidences into nonexceptional and
exceptional ones. -/
private lemma largePrimeIncidences_card_eq_partition
    (N G D p : ℕ) (E : Finset ℕ) :
    (largePrimeIncidences N G D p).card =
      (nonexceptionalLargePrimeIncidences N G D p E).card +
        (exceptionalLargePrimeIncidences N G D p E).card := by
  classical
  let L := largePrimeIncidences N G D p
  let S := nonexceptionalLargePrimeIncidences N G D p E
  let X := exceptionalLargePrimeIncidences N G D p E
  have hunion : S ∪ X = L := by
    ext nq
    rcases nq with ⟨n, q⟩
    simp only [S, X, L, nonexceptionalLargePrimeIncidences,
      exceptionalLargePrimeIncidences, largePrimeIncidences,
      nonexceptionalLargePrimeFactors, Finset.mem_union, Finset.mem_sigma,
      Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdisj : Disjoint S X := by
    rw [Finset.disjoint_left]
    intro nq hnS hnX
    have hs := Finset.mem_sigma.mp hnS
    have hx := Finset.mem_sigma.mp hnX
    exact (Finset.mem_sdiff.mp hs.2).2 (Finset.mem_inter.mp hx.2).2
  calc
    L.card = (S ∪ X).card := congrArg Finset.card hunion.symm
    _ = S.card + X.card := Finset.card_union_of_disjoint hdisj

/-- The factor-incidence version of the first combinatorial estimate in
Lemma 4.2.  Every integer in `[p-N,N]` has at most one threshold-large
prime divisor.  Folding `n` and `p-n` into `J_p` is at most two-to-one, and
each nonexceptional incidence lands in an empty representation fiber. -/
private lemma nonexceptionalLargePrimeIncidences_card_le_two_mul_zeroFibers
    (A : Finset ℕ) {G D p : ℕ} (E : Finset ℕ)
    (hN : 0 < A.card) (hpN : A.card < p) (hpupper : p ≤ 2 * A.card)
    (hD : D ≤ A.card)
    (hzero : ∀ α ∈ Finset.Icc ((p + 1) / 2) A.card,
      ∀ q : ℕ, q.Prime → (A.card + G) ^ 3 < q ^ 3 * D → q ∉ E →
        (q ∣ α ∨ q ∣ p - α) → representationCount A p α = 0) :
    (nonexceptionalLargePrimeIncidences A.card G D p E).card ≤
      2 * ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        representationCount A p α = 0).card := by
  classical
  let S := nonexceptionalLargePrimeIncidences A.card G D p E
  let Z := (Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
    representationCount A p α = 0
  let side : ℕ → Bool := fun n ↦ decide (n ≤ p - n)
  let foldSide : ((n : ℕ) × ℕ) → ℕ × Bool := fun nq ↦
    (primeFold p nq.1, side nq.1)
  have hmaps : Set.MapsTo foldSide (↑S : Set ((n : ℕ) × ℕ))
      (↑(Z.product (Finset.univ : Finset Bool)) : Set (ℕ × Bool)) := by
    intro nq hnq
    have hmem := Finset.mem_sigma.mp hnq
    rcases nq with ⟨n, q⟩
    have hnI : n ∈ Finset.Icc (p - A.card) A.card := hmem.1
    have hqdiff := Finset.mem_sdiff.mp hmem.2
    have hqfilter := Finset.mem_filter.mp hqdiff.1
    have hq : q.Prime := (Nat.mem_primeFactors.mp hqfilter.1).1
    have hqdvd : q ∣ n := (Nat.mem_primeFactors.mp hqfilter.1).2.1
    have hqfactor : q ∣ primeFold p n ∨ q ∣ p - primeFold p n := by
      by_cases hnside : n ≤ p - n
      · right
        have hnp : n ≤ p := (Finset.mem_Icc.mp hnI).2.trans hpN.le
        simpa only [primeFold, max_eq_right hnside, Nat.sub_sub_self hnp] using hqdvd
      · left
        have hrev : p - n ≤ n := by omega
        simpa only [primeFold, max_eq_left hrev] using hqdvd
    have hfoldJ : primeFold p n ∈
        Finset.Icc ((p + 1) / 2) A.card :=
      primeFold_mem_J hpN hpupper hnI
    have hfoldzero : representationCount A p (primeFold p n) = 0 :=
      hzero (primeFold p n) hfoldJ q hq hqfilter.2 hqdiff.2 hqfactor
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_filter.mpr ⟨hfoldJ, hfoldzero⟩, Finset.mem_univ _⟩
  have hinj : Set.InjOn foldSide (↑S : Set ((n : ℕ) × ℕ)) := by
    intro nq hnq mr hmr heq
    have hnqmem := Finset.mem_sigma.mp hnq
    have hmrmem := Finset.mem_sigma.mp hmr
    rcases nq with ⟨n, q⟩
    rcases mr with ⟨m, r⟩
    have hnI : n ∈ Finset.Icc (p - A.card) A.card := hnqmem.1
    have hmI : m ∈ Finset.Icc (p - A.card) A.card := hmrmem.1
    have hfold : primeFold p n = primeFold p m := congrArg Prod.fst heq
    have hside : side n = side m := congrArg Prod.snd heq
    have hnm : n = m := by
      by_cases hnside : n ≤ p - n
      · have hmside : m ≤ p - m := by
          by_contra hm
          simp only [side, decide_eq_true_eq, hnside, decide_true,
            Bool.true_eq] at hside
          simp only [side, decide_eq_false_iff_not, hm, decide_false] at hside
        have hnp : n ≤ p := (Finset.mem_Icc.mp hnI).2.trans hpN.le
        have hmp : m ≤ p := (Finset.mem_Icc.mp hmI).2.trans hpN.le
        rw [primeFold, max_eq_right hnside, primeFold, max_eq_right hmside] at hfold
        omega
      · have hmside : ¬m ≤ p - m := by
          intro hm
          simp only [side, decide_eq_false_iff_not, hnside, decide_false] at hside
          simp only [side, decide_eq_true_eq, hm, decide_true] at hside
          exact Bool.noConfusion hside
        have hnrev : p - n ≤ n := by omega
        have hmrev : p - m ≤ m := by omega
        simpa only [primeFold, max_eq_left hnrev, max_eq_left hmrev] using hfold
    subst m
    have hnpos : 0 < n := by
      have hlo := (Finset.mem_Icc.mp hnI).1
      omega
    have hcard := at_most_one_large_prime_factor (G := G) hN hnpos
      (Finset.mem_Icc.mp hnI).2 hD
    have hqmem : q ∈ largePrimeFactors A.card G D n :=
      (Finset.mem_sdiff.mp hnqmem.2).1
    have hrmem : r ∈ largePrimeFactors A.card G D n :=
      (Finset.mem_sdiff.mp hmrmem.2).1
    have hqr : q = r := Finset.card_le_one.mp hcard q hqmem r hrmem
    exact Sigma.ext rfl (heq_of_eq hqr)
  calc
    S.card ≤ (Z.product (Finset.univ : Finset Bool)).card :=
      Finset.card_le_card_of_injOn foldSide hmaps hinj
    _ = 2 * Z.card := by simp [mul_comm]

/-- Root-free, finite-cardinality form of the lower-bound setup in
Lemma 4.2.  Analytic estimates are needed only to lower-bound the left
side and upper-bound the explicit exceptional correction on the right. -/
private lemma largePrimeIncidences_card_le_zeroFibers_add_exceptional
    (A : Finset ℕ) {G D p : ℕ} (E : Finset ℕ)
    (hN : 0 < A.card) (hpN : A.card < p) (hpupper : p ≤ 2 * A.card)
    (hD : D ≤ A.card) (hEprime : ∀ q ∈ E, q.Prime)
    (hzero : ∀ α ∈ Finset.Icc ((p + 1) / 2) A.card,
      ∀ q : ℕ, q.Prime → (A.card + G) ^ 3 < q ^ 3 * D → q ∉ E →
        (q ∣ α ∨ q ∣ p - α) → representationCount A p α = 0) :
    (largePrimeIncidences A.card G D p).card ≤
      2 * ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        representationCount A p α = 0).card +
      E.sum fun q ↦ (2 * A.card - p) / q + 1 := by
  rw [largePrimeIncidences_card_eq_partition A.card G D p E]
  exact Nat.add_le_add
    (nonexceptionalLargePrimeIncidences_card_le_two_mul_zeroFibers
      A E hN hpN hpupper hD hzero)
    (exceptionalLargePrimeIncidences_card_le E hpN.le hpupper hEprime)

/-- Combine the large-prime incidence estimate with Lemma 2.1, which says
that collision excess dominates the number of empty fibers. -/
private lemma largePrimeIncidences_card_le_collisionExcess_add_exceptional
    (A : Finset ℕ) {G D p : ℕ} (E : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬GrahamBound A)
    (hp : p.Prime) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hD : D ≤ A.card) (hEprime : ∀ q ∈ E, q.Prime)
    (hzero : ∀ α ∈ Finset.Icc ((p + 1) / 2) A.card,
      ∀ q : ℕ, q.Prime → (A.card + G) ^ 3 < q ^ 3 * D → q ∉ E →
        (q ∣ α ∨ q ∣ p - α) → representationCount A p α = 0) :
    (largePrimeIncidences A.card G D p).card ≤
      2 * collisionExcess A p + E.sum fun q ↦ (2 * A.card - p) / q + 1 := by
  have hN : 0 < A.card := by omega
  have hinc := largePrimeIncidences_card_le_zeroFibers_add_exceptional
    A E hN hpN hpupper.le hD hEprime hzero
  have hZE := zero_card_le_representation_excess
    A h₀ hgcd hbad hp hpN hpupper
  dsimp only [collisionExcess]
  omega

/-- Uniform finite statement at the end of the combinatorial part of
Section 4: one fixed exceptional set works for every prime in the window,
and the only remaining terms are the collision excess and an explicit sum
over at most two primes. -/
private lemma exists_fixed_exceptional_primes_with_excess_bound
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hcollision : ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α) :
    ∃ E : Finset ℕ, E.card ≤ 2 ∧ (∀ q ∈ E, q.Prime) ∧
      (∀ q ∈ E, (A.card + G) ^ 3 <
        q ^ 3 * globalD A G) ∧
      ∀ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
        p.Prime →
        (largePrimeIncidences A.card G (globalD A G) p).card ≤
          2 * collisionExcess A p +
            E.sum fun q ↦ (2 * A.card - p) / q + 1 := by
  obtain ⟨E, hEcard, hEprime, hElarge, hzero⟩ :=
    exists_fixed_exceptional_primes A G h₀ hgcd hbad hG hGN hcollision
  refine ⟨E, hEcard, hEprime, hElarge, ?_⟩
  intro p hpwin hp
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hpupper : p < 2 * A.card := by
    have hi := (Finset.mem_Icc.mp hpwin).2
    omega
  exact largePrimeIncidences_card_le_collisionExcess_add_exceptional
    A E h₀ hgcd hbad hp hpN hpupper
      (globalD_le_card A G hbad hG (by omega)) hEprime (hzero p hpwin hp)

/-- Lemma 4.1 and the two-to-one folding estimate, packaged with the same
fixed exceptional set for every prime in the short window. -/
private lemma exists_fixed_exceptional_primes_with_incidence_bound
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hcollision : ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α) :
    ∃ E : Finset ℕ, E.card ≤ 2 ∧ (∀ q ∈ E, q.Prime) ∧
      ∀ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
        p.Prime →
        (nonexceptionalLargePrimeIncidences A.card G (globalD A G) p E).card ≤
          2 * ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
            representationCount A p α = 0).card := by
  obtain ⟨E, hEcard, hEprime, _hElarge, hzero⟩ :=
    exists_fixed_exceptional_primes A G h₀ hgcd hbad hG hGN hcollision
  refine ⟨E, hEcard, hEprime, ?_⟩
  intro p hpwin hp
  have hN : 0 < A.card := by omega
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hpupper : p ≤ 2 * A.card := by
    have hi := (Finset.mem_Icc.mp hpwin).2
    omega
  apply nonexceptionalLargePrimeIncidences_card_le_two_mul_zeroFibers
    A E hN hpN hpupper
  · exact globalD_le_card A G hbad hG (by omega)
  · exact hzero p hpwin hp

private def totalSafeLargePrimeCandidates (N G D : ℕ) : ℕ :=
  (primeWindow N G).sum fun p ↦
    (safeLargePrimeCandidates N G D p).card

private def totalExceptionalCorrection
    (N G : ℕ) (E : Finset ℕ) : ℕ :=
  (primeWindow N G).sum fun p ↦
    E.sum fun q ↦ (2 * N - p) / q + 1

private lemma safeLargePrimeCandidates_card_eq
    (N G D p : ℕ) :
    (safeLargePrimeCandidates N G D p).card =
      (safeLargePrimeMultipliers N G D p).sum fun r ↦
        ((Finset.Icc 2 N).filter fun q ↦
          q.Prime ∧ p - N ≤ q * r ∧ q * r ≤ N).card := by
  simp only [safeLargePrimeCandidates, Finset.card_sigma]

/-- A single cubic inequality makes every multiplier in `[1,R]` safe,
uniformly for all primes in the outer window. -/
private lemma Icc_subset_safeLargePrimeMultipliers
    {N G D R p : ℕ} (hGN : 2 * G ≤ N) (hDN : D ≤ N)
    (hp : p ∈ primeWindow N G)
    (hscale : (N + G) ^ 3 * R ^ 3 < (N - 2 * G) ^ 3 * D) :
    Finset.Icc 1 R ⊆ safeLargePrimeMultipliers N G D p := by
  intro r hr
  have hrle : r ≤ R := (Finset.mem_Icc.mp hr).2
  have hpwin := (Finset.mem_filter.mp hp).1
  have hplower : N - 2 * G ≤ p - N := by
    have := (Finset.mem_Icc.mp hpwin).1
    omega
  have hRN : R ≤ N := by
    have hRpos : 0 < R :=
      Nat.zero_lt_one.trans_le ((Finset.mem_Icc.mp hr).1.trans hrle)
    have hminus : N - 2 * G ≤ N + G := by omega
    have hminusPow : (N - 2 * G) ^ 3 ≤ (N + G) ^ 3 :=
      pow_le_pow_left' hminus 3
    have hRD : R ^ 3 < D := by
      by_contra hnot
      have hDR : D ≤ R ^ 3 := Nat.le_of_not_gt hnot
      have hright : (N - 2 * G) ^ 3 * D ≤
          (N + G) ^ 3 * R ^ 3 := Nat.mul_le_mul hminusPow hDR
      exact (not_lt_of_ge hright) hscale
    have hRcube : R ≤ R ^ 3 := by
      exact Nat.le_pow (by norm_num : 0 < 3)
    exact hRcube.trans (hRD.le.trans hDN)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
    hrle.trans hRN⟩, ?_⟩
  calc
    (N + G) ^ 3 * r ^ 3 ≤ (N + G) ^ 3 * R ^ 3 := by
      exact Nat.mul_le_mul_left _ (pow_le_pow_left' hrle 3)
    _ < (N - 2 * G) ^ 3 * D := hscale
    _ ≤ (p - N) ^ 3 * D := by
      exact Nat.mul_le_mul_right D (pow_le_pow_left' hplower 3)

/-- Exact lower-bound interface for the safe-candidate total.  Once a
uniform multiplier cutoff `R` is known to be safe, the remaining summands
are precisely prime counts in the product intervals `[p-N,N]`. -/
private lemma sum_prime_product_counts_le_totalSafe
    {N G D R : ℕ} (hGN : 2 * G ≤ N) (hDN : D ≤ N)
    (hscale : (N + G) ^ 3 * R ^ 3 < (N - 2 * G) ^ 3 * D) :
    (primeWindow N G).sum (fun p ↦
        (Finset.Icc 1 R).sum fun r ↦
          ((Finset.Icc 2 N).filter fun q ↦
            q.Prime ∧ p - N ≤ q * r ∧ q * r ≤ N).card) ≤
      totalSafeLargePrimeCandidates N G D := by
  unfold totalSafeLargePrimeCandidates
  apply Finset.sum_le_sum
  intro p hp
  rw [safeLargePrimeCandidates_card_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Icc_subset_safeLargePrimeMultipliers hGN hDN hp hscale)
    (fun _ _ _ ↦ Nat.zero_le _)

/-- Pointwise prime-count estimates in the product intervals can be
summed and inserted directly into the safe-candidate lower bound.  Thus
the eventual prime-distribution theorem need only expose a natural-valued
lower bound `Q p r` for each individual interval. -/
private lemma sum_prime_product_lowerBounds_le_totalSafe
    {N G D R : ℕ} (Q : ℕ → ℕ → ℕ)
    (hGN : 2 * G ≤ N) (hDN : D ≤ N)
    (hscale : (N + G) ^ 3 * R ^ 3 < (N - 2 * G) ^ 3 * D)
    (hQ : ∀ p ∈ primeWindow N G, ∀ r ∈ Finset.Icc 1 R,
      Q p r ≤ ((Finset.Icc 2 N).filter fun q ↦
        q.Prime ∧ p - N ≤ q * r ∧ q * r ≤ N).card) :
    (primeWindow N G).sum (fun p ↦
        (Finset.Icc 1 R).sum (Q p)) ≤
      totalSafeLargePrimeCandidates N G D := by
  calc
    (primeWindow N G).sum (fun p ↦
        (Finset.Icc 1 R).sum (Q p)) ≤
        (primeWindow N G).sum (fun p ↦
          (Finset.Icc 1 R).sum fun r ↦
            ((Finset.Icc 2 N).filter fun q ↦
              q.Prime ∧ p - N ≤ q * r ∧ q * r ≤ N).card) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      exact hQ p hp r hr
    _ ≤ totalSafeLargePrimeCandidates N G D :=
      sum_prime_product_counts_le_totalSafe hGN hDN hscale

/-- The two fixed exceptional primes contribute at most their elementary
multiple-count with the full window length `2G`. -/
private lemma totalExceptionalCorrection_le
    {N G : ℕ} (E : Finset ℕ) :
    totalExceptionalCorrection N G E ≤
      (primeWindow N G).card *
        (E.sum fun q ↦ (2 * G) / q + 1) := by
  unfold totalExceptionalCorrection
  calc
    (primeWindow N G).sum (fun p ↦
        E.sum fun q ↦ (2 * N - p) / q + 1) ≤
        (primeWindow N G).sum (fun _ ↦
          E.sum fun q ↦ (2 * G) / q + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q _
      apply Nat.add_le_add_right
      apply Nat.div_le_div_right
      have hpwin := (Finset.mem_filter.mp hp).1
      have hlo := (Finset.mem_Icc.mp hpwin).1
      omega
    _ = (primeWindow N G).card *
          (E.sum fun q ↦ (2 * G) / q + 1) := by simp

/-- The prime window contains at most `G + 1` integers.  This elementary
bound is deliberately kept separate from every prime-density estimate. -/
private lemma primeWindow_card_le_add_one {N G : ℕ} (hGN : G ≤ N) :
    (primeWindow N G).card ≤ G + 1 := by
  calc
    (primeWindow N G).card ≤
        (Finset.Icc (2 * N - 2 * G) (2 * N - G)).card := by
      exact Finset.card_filter_le _ _
    _ = G + 1 := by
      rw [Nat.card_Icc]
      omega

/-- If both exceptional primes are at least `K`, their complete aggregate
correction is bounded by a closed expression.  This is the exact integral
counterpart of the negligible-exceptional-primes estimate in Section 4. -/
private lemma totalExceptionalCorrection_le_of_lower_bound
    {N G K : ℕ} (E : Finset ℕ) (hGN : G ≤ N) (hK : 0 < K)
    (hEcard : E.card ≤ 2) (hElower : ∀ q ∈ E, K ≤ q) :
    totalExceptionalCorrection N G E ≤
      (G + 1) * (2 * ((2 * G) / K + 1)) := by
  have hsum : (E.sum fun q ↦ (2 * G) / q + 1) ≤
      E.card * ((2 * G) / K + 1) := by
    calc
      (E.sum fun q ↦ (2 * G) / q + 1) ≤
          E.sum (fun _ ↦ (2 * G) / K + 1) := by
        apply Finset.sum_le_sum
        intro q hq
        apply Nat.add_le_add_right
        exact Nat.div_le_div_left (hElower q hq) hK
      _ = E.card * ((2 * G) / K + 1) := by simp
  calc
    totalExceptionalCorrection N G E ≤
        (primeWindow N G).card *
          (E.sum fun q ↦ (2 * G) / q + 1) :=
      totalExceptionalCorrection_le E
    _ ≤ (G + 1) * (E.card * ((2 * G) / K + 1)) :=
      Nat.mul_le_mul (primeWindow_card_le_add_one hGN) hsum
    _ ≤ (G + 1) * (2 * ((2 * G) / K + 1)) := by
      exact Nat.mul_le_mul_left (G + 1)
        (Nat.mul_le_mul_right ((2 * G) / K + 1) hEcard)

/-- A cube-form threshold immediately gives a concrete lower bound for an
exceptional prime once `D ≤ N`.  No roots or real casts are needed. -/
private lemma lt_exceptional_prime_of_cube_scale
    {N G D K q : ℕ} (hDpos : 0 < D) (hDN : D ≤ N)
    (hscale : K ^ 3 * N ≤ (N + G) ^ 3)
    (hlarge : (N + G) ^ 3 < q ^ 3 * D) :
    K < q := by
  have hKD : K ^ 3 * D ≤ (N + G) ^ 3 :=
    (Nat.mul_le_mul_left (K ^ 3) hDN).trans hscale
  have hpowersD : K ^ 3 * D < q ^ 3 * D := hKD.trans_lt hlarge
  have hpowers : K ^ 3 < q ^ 3 :=
    (Nat.mul_lt_mul_right hDpos).mp hpowersD
  exact lt_of_pow_lt_pow_left' 3 hpowers

/-- Closed aggregate exceptional-prime bound directly from the cube
threshold used in Lemma 4.1. -/
private lemma totalExceptionalCorrection_le_of_cube_scale
    {N G D K : ℕ} (E : Finset ℕ) (hGN : G ≤ N) (hK : 0 < K)
    (hDpos : 0 < D) (hDN : D ≤ N)
    (hscale : K ^ 3 * N ≤ (N + G) ^ 3)
    (hEcard : E.card ≤ 2)
    (hElarge : ∀ q ∈ E, (N + G) ^ 3 < q ^ 3 * D) :
    totalExceptionalCorrection N G E ≤
      (G + 1) * (2 * ((2 * G) / K + 1)) := by
  apply totalExceptionalCorrection_le_of_lower_bound E hGN hK hEcard
  intro q hq
  exact (lt_exceptional_prime_of_cube_scale hDpos hDN hscale
    (hElarge q hq)).le

/-- A prime in the outer window together with one prime in its reflected
interval forces a collision fiber in every counterexample.  This supplies
the non-vacuity hypothesis needed to choose the extremal rectangle. -/
private lemma exists_window_collision_of_prime_interval_nonempty
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hprime : ∃ p ∈ primeWindow A.card G,
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).Nonempty) :
    ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α := by
  obtain ⟨p, hpwindow, hQ⟩ := hprime
  have hpwin := (Finset.mem_filter.mp hpwindow).1
  have hp := (Finset.mem_filter.mp hpwindow).2
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hpupper : p < 2 * A.card := by
    have hi := (Finset.mem_Icc.mp hpwin).2
    omega
  have hlower : ∀ q ∈
      (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card ≤ 2 * q := by
    intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    have hplo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hq2 : ∀ q ∈
      (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q := by
    intro q hq
    have hqlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    have hplo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hQZ := primeInterval_card_le_zeroFibers
    A h₀ hgcd hbad hp hpN hpupper hlower hq2
  have hZE := zero_card_le_representation_excess
    A h₀ hgcd hbad hp hpN hpupper
  have hQpos : 0 <
      ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card :=
    Finset.card_pos.mpr hQ
  have hExcessPos : 0 < collisionExcess A p := by
    dsimp only [collisionExcess]
    exact hQpos.trans_le (hQZ.trans hZE)
  rw [collisionExcess, Finset.sum_pos_iff] at hExcessPos
  obtain ⟨α, hαM, _hterm⟩ := hExcessPos
  refine ⟨p, hpwin, hp, α, (Finset.mem_filter.mp hαM).1,
    (Finset.mem_filter.mp hαM).2⟩

/-- Exact aggregate lower-bound interface from Section 4.  It isolates
all analysis in the explicit cardinality of the safe prime/multiplier
candidates and in the correction from at most two fixed primes. -/
private lemma exists_exceptional_set_total_safe_le_excess
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hcollision : ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α) :
    ∃ E : Finset ℕ, E.card ≤ 2 ∧ (∀ q ∈ E, q.Prime) ∧
      (∀ q ∈ E, (A.card + G) ^ 3 <
        q ^ 3 * globalD A G) ∧
      totalSafeLargePrimeCandidates A.card G (globalD A G) ≤
        2 * totalCollisionExcess A G +
          totalExceptionalCorrection A.card G E := by
  obtain ⟨E, hEcard, hEprime, hElarge, hbound⟩ :=
    exists_fixed_exceptional_primes_with_excess_bound
      A G h₀ hgcd hbad hG hGN hcollision
  refine ⟨E, hEcard, hEprime, hElarge, ?_⟩
  unfold totalSafeLargePrimeCandidates totalExceptionalCorrection
  calc
    (primeWindow A.card G).sum (fun p ↦
        (safeLargePrimeCandidates A.card G (globalD A G) p).card) ≤
        (primeWindow A.card G).sum (fun p ↦
          (largePrimeIncidences A.card G (globalD A G) p).card) := by
      apply Finset.sum_le_sum
      intro p _
      exact safeLargePrimeCandidates_card_le_incidence
    _ ≤ (primeWindow A.card G).sum (fun p ↦
          2 * collisionExcess A p +
            E.sum fun q ↦ (2 * A.card - p) / q + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hbound p (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hp).2
    _ = 2 * totalCollisionExcess A G +
          (primeWindow A.card G).sum (fun p ↦
            E.sum fun q ↦ (2 * A.card - p) / q + 1) := by
      unfold totalCollisionExcess
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Sieve-free analytic endgame.  The two upper terms are controlled by
first-moment envelopes alone, while the lower term is Boyle's elementary
prime-interval contribution.  All three quantities depend only on `N,G`
after replacing the structural cutoff `globalD` by its universal bound
`N`. -/
private lemma grahamBound_of_basic_analytic_separation
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hseparate :
      (primeWindow A.card G).card *
          (firstMomentTriples A.card A.card (A.card - 2 * G)).card +
        (firstMomentTriples A.card A.card (A.card - G)).card *
          (firstMomentTriples A.card A.card (A.card - 2 * G)).card <
        basicPrimeCollisionLower A.card G) :
    GrahamBound A := by
  by_contra hbad
  have hN : 0 < A.card := by omega
  have htwoG : 2 * G ≤ A.card := by omega
  have hD : globalD A G ≤ A.card :=
    globalD_le_card A G hbad hG (by omega)
  have hF₁ :
      (firstMomentTriples A.card (globalD A G) (A.card - G)).card ≤
        (firstMomentTriples A.card A.card (A.card - G)).card :=
    Finset.card_le_card (firstMomentTriples_mono_cap hD)
  have hF₂ :
      (firstMomentTriples A.card (globalD A G) (A.card - 2 * G)).card ≤
        (firstMomentTriples A.card A.card (A.card - 2 * G)).card :=
    Finset.card_le_card (firstMomentTriples_mono_cap hD)
  have hlower := basicPrimeCollisionLower_le_totalCollisionExcess
    A G h₀ hgcd hbad hG hGN
  have hcollision := totalCollisionExcess_le_upper A G hbad hG hGN
  have hlinear := totalLinearUpper_le_primeWindow_mul_firstMoment
    (N := A.card) (G := G) (D := globalD A G) hN htwoG
  have hbilinear := totalBilinearUpper_le_firstMoment_product
    (N := A.card) (G := G) (D := globalD A G) hN htwoG
  have hlinear' :
      totalLinearUpper A.card G (globalD A G) ≤
        (primeWindow A.card G).card *
          (firstMomentTriples A.card A.card (A.card - 2 * G)).card :=
    hlinear.trans (Nat.mul_le_mul_left _ hF₂)
  have hbilinear' :
      totalBilinearUpper A.card G (globalD A G) ≤
        (firstMomentTriples A.card A.card (A.card - G)).card *
          (firstMomentTriples A.card A.card (A.card - 2 * G)).card :=
    hbilinear.trans (Nat.mul_le_mul hF₁ hF₂)
  omega

/-- A closed real-valued interface for the sieve-free endgame.  It reduces
the remaining analytic work to two uniform prime-count lower bounds and
one explicit inequality involving `firstMomentRealBound`. -/
private lemma grahamBound_of_basic_real_separation
    (A : Finset ℕ) (G P Q : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hP : P ≤ (primeWindow A.card G).card)
    (hQ : ∀ p ∈ primeWindow A.card G,
      Q ≤ ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card)
    (hseparate :
      ((G + 1 : ℕ) : ℝ) * firstMomentRealBound A.card (2 * G) +
          firstMomentRealBound A.card G *
            firstMomentRealBound A.card (2 * G) <
        (P : ℝ) * (Q : ℝ)) :
    GrahamBound A := by
  have hN : 0 < A.card := by omega
  have hGle : G ≤ A.card := by omega
  have htwoG : 2 * G ≤ A.card := by omega
  let F₁ := (firstMomentTriples A.card A.card (A.card - G)).card
  let F₂ := (firstMomentTriples A.card A.card (A.card - 2 * G)).card
  have hF₁ : (F₁ : ℝ) ≤ firstMomentRealBound A.card G := by
    dsimp only [F₁]
    exact firstMomentTriples_card_real_le_bound hN hGle
  have hF₂ : (F₂ : ℝ) ≤ firstMomentRealBound A.card (2 * G) := by
    dsimp only [F₂]
    exact firstMomentTriples_card_real_le_bound hN htwoG
  have hwindow : (primeWindow A.card G).card ≤ G + 1 :=
    primeWindow_card_le_add_one hGle
  have hwindowReal : ((primeWindow A.card G).card : ℝ) ≤
      ((G + 1 : ℕ) : ℝ) := by
    exact_mod_cast hwindow
  have hB₁nonneg : 0 ≤ firstMomentRealBound A.card G :=
    (Nat.cast_nonneg F₁).trans hF₁
  have hB₂nonneg : 0 ≤ firstMomentRealBound A.card (2 * G) :=
    (Nat.cast_nonneg F₂).trans hF₂
  have hupperReal :
      (((primeWindow A.card G).card * F₂ + F₁ * F₂ : ℕ) : ℝ) ≤
        ((G + 1 : ℕ) : ℝ) * firstMomentRealBound A.card (2 * G) +
          firstMomentRealBound A.card G *
            firstMomentRealBound A.card (2 * G) := by
    simp only [Nat.cast_add, Nat.cast_mul]
    apply add_le_add
    · have hmul :
          ((primeWindow A.card G).card : ℝ) * (F₂ : ℝ) ≤
            ((G + 1 : ℕ) : ℝ) * firstMomentRealBound A.card (2 * G) :=
        mul_le_mul hwindowReal hF₂ (Nat.cast_nonneg F₂) (by positivity)
      simpa only [Nat.cast_add] using hmul
    · exact mul_le_mul hF₁ hF₂ (Nat.cast_nonneg F₂) hB₁nonneg
  have hlower := mul_le_basicPrimeCollisionLower hP hQ
  have hlowerReal : (P : ℝ) * (Q : ℝ) ≤
      (basicPrimeCollisionLower A.card G : ℝ) := by
    exact_mod_cast hlower
  have hstrictReal :
      (((primeWindow A.card G).card * F₂ + F₁ * F₂ : ℕ) : ℝ) <
        (basicPrimeCollisionLower A.card G : ℝ) :=
    hupperReal.trans_lt (hseparate.trans_le hlowerReal)
  have hstrictNat :
      (primeWindow A.card G).card * F₂ + F₁ * F₂ <
        basicPrimeCollisionLower A.card G := by
    exact_mod_cast hstrictReal
  apply grahamBound_of_basic_analytic_separation A G h₀ hgcd hG hGN
  simpa only [F₁, F₂] using hstrictNat

/-- Apply the uniform short-interval theorem to the outer prime window and
to every inner interval occurring in Boyle's lower bound. -/
private lemma analytic_prime_bounds {N G V : ℕ}
    (hN : 0 < N) (hG : 0 < G) (h10 : 10 * G ≤ N)
    (hlog : 20000 ≤ Real.log (N : ℝ))
    (hGlower : (N : ℝ) / (2 * Real.log N ^ 4) ≤ (G : ℝ))
    (hshort : ∀ v : ℕ, V ≤ v → ∀ u : ℕ, u ≤ v → v ≤ 2 * (u - 1) →
      (v : ℝ) / Real.log v ^ 5 ≤ (v : ℝ) - ((u - 1 : ℕ) : ℝ) →
      ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) / (2 * Real.log v) ≤
        (((Finset.Icc u v).filter Nat.Prime).card : ℝ))
    (hVN : V ≤ N) :
    (G : ℝ) / (4 * Real.log N) ≤ ((primeWindow N G).card : ℝ) ∧
      ∀ p ∈ primeWindow N G,
        (G : ℝ) / (2 * Real.log N) ≤
          (((Finset.Icc (p - N) N).filter Nat.Prime).card : ℝ) := by
  have hN2 : 2 ≤ N := by
    have hLpos : 0 < Real.log (N : ℝ) := by linarith
    have : (1 : ℝ) < N := (Real.log_pos_iff (by positivity)).mp hLpos
    have hNat : 1 < N := by exact_mod_cast this
    omega
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hlog4 : (4 : ℝ) ≤ Real.log (N : ℝ) := by linarith
  have hGle : G ≤ N := by omega
  have h2Gle : 2 * G ≤ N := by omega
  let u := 2 * N - 2 * G
  let v := 2 * N - G
  have huv : u ≤ v := by dsimp only [u, v]; omega
  have hNv : N ≤ v := by dsimp only [v]; omega
  have hv2N : v ≤ 2 * N := by dsimp only [v]; omega
  have hvhalf : v ≤ 2 * (u - 1) := by dsimp only [u, v]; omega
  have hlogNv : Real.log (N : ℝ) ≤ Real.log (v : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hN)
    exact_mod_cast hNv
  have hlogvpos : 0 < Real.log (v : ℝ) := hlogpos.trans_le hlogNv
  have hlogv2 : Real.log (v : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have hvpos : (0 : ℝ) < v := by exact_mod_cast hN.trans_le hNv
    have hlogvle : Real.log (v : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
      apply Real.log_le_log hvpos
      exact_mod_cast hv2N
    have hlog2le : Real.log 2 ≤ Real.log (N : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hN2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by exact_mod_cast hN.ne')] at hlogvle
    linarith
  have hwidthNat : G ≤ v - (u - 1) := by dsimp only [u, v]; omega
  have hwidth : (v : ℝ) / Real.log v ^ 5 ≤
      (v : ℝ) - ((u - 1 : ℕ) : ℝ) := by
    have hlogNpow : 0 < Real.log (N : ℝ) ^ 5 := pow_pos hlogpos 5
    have hlogvpow : 0 < Real.log (v : ℝ) ^ 5 := pow_pos hlogvpos 5
    have hscale : 2 * (N : ℝ) / Real.log N ^ 5 ≤
        (N : ℝ) / (2 * Real.log N ^ 4) := by
      apply (div_le_div_iff₀ hlogNpow
        (mul_pos (by norm_num) (pow_pos hlogpos 4))).2
      calc
        2 * (N : ℝ) * (2 * Real.log N ^ 4) =
            4 * ((N : ℝ) * Real.log N ^ 4) := by ring
        _ ≤ Real.log N * ((N : ℝ) * Real.log N ^ 4) :=
          mul_le_mul_of_nonneg_right hlog4 (by positivity)
        _ = (N : ℝ) * Real.log N ^ 5 := by rw [pow_succ]; ring
    calc
      (v : ℝ) / Real.log v ^ 5 ≤
          (2 * (N : ℝ)) / Real.log v ^ 5 :=
        div_le_div_of_nonneg_right (by exact_mod_cast hv2N) hlogvpow.le
      _ ≤ (2 * (N : ℝ)) / Real.log N ^ 5 := by
        apply div_le_div_of_nonneg_left (by positivity) hlogNpow
        exact pow_le_pow_left₀ hlogpos.le hlogNv 5
      _ ≤ (N : ℝ) / (2 * Real.log N ^ 4) := hscale
      _ ≤ (G : ℝ) := hGlower
      _ ≤ (v : ℝ) - ((u - 1 : ℕ) : ℝ) := by
        rw [← Nat.cast_sub ((Nat.sub_le u 1).trans huv)]
        exact_mod_cast hwidthNat
  have houter := hshort v (hVN.trans hNv) u huv hvhalf hwidth
  have houterLower : (G : ℝ) / (4 * Real.log N) ≤
      ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) / (2 * Real.log v) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hlogpos)
      (mul_pos (by norm_num) hlogvpos)).2
    have hWnonneg : (0 : ℝ) ≤ (v : ℝ) - ((u - 1 : ℕ) : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast (Nat.sub_le u 1).trans huv)
    have hGwidth : (G : ℝ) ≤ (v : ℝ) - ((u - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_sub ((Nat.sub_le u 1).trans huv)]
      exact_mod_cast hwidthNat
    calc
      (G : ℝ) * (2 * Real.log v) ≤
          ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) * (2 * Real.log v) :=
        mul_le_mul_of_nonneg_right hGwidth (by positivity)
      _ ≤ ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) *
          (4 * Real.log N) := by
        apply mul_le_mul_of_nonneg_left _ hWnonneg
        linarith
  refine ⟨houterLower.trans ?_, ?_⟩
  · simpa only [primeWindow, u, v] using houter
  · intro p hp
    have hpI := (Finset.mem_filter.mp hp).1
    have hpBounds := Finset.mem_Icc.mp hpI
    let ui := p - N
    have hui : ui ≤ N := by dsimp only [ui]; omega
    have hhalf : N ≤ 2 * (ui - 1) := by dsimp only [ui]; omega
    have hwidthNatI : G ≤ N - (ui - 1) := by dsimp only [ui]; omega
    have hwidthI : (N : ℝ) / Real.log N ^ 5 ≤
        (N : ℝ) - ((ui - 1 : ℕ) : ℝ) := by
      have hscale : (N : ℝ) / Real.log N ^ 5 ≤
          (N : ℝ) / (2 * Real.log N ^ 4) := by
        apply (div_le_div_iff₀ (pow_pos hlogpos 5)
          (mul_pos (by norm_num) (pow_pos hlogpos 4))).2
        calc
          (N : ℝ) * (2 * Real.log N ^ 4) =
              2 * ((N : ℝ) * Real.log N ^ 4) := by ring
          _ ≤ Real.log N * ((N : ℝ) * Real.log N ^ 4) :=
            mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ Real.log N)
              (by positivity)
          _ = (N : ℝ) * Real.log N ^ 5 := by rw [pow_succ]; ring
      exact hscale.trans (hGlower.trans (by
        rw [← Nat.cast_sub ((Nat.sub_le ui 1).trans hui)]
        exact_mod_cast hwidthNatI))
    have hi := hshort N hVN ui hui hhalf hwidthI
    have hGwidth : (G : ℝ) ≤ (N : ℝ) - ((ui - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_sub ((Nat.sub_le ui 1).trans hui)]
      exact_mod_cast hwidthNatI
    calc
      (G : ℝ) / (2 * Real.log N) ≤
          ((N : ℝ) - ((ui - 1 : ℕ) : ℝ)) / (2 * Real.log N) := by gcongr
      _ ≤ (((Finset.Icc ui N).filter Nat.Prime).card : ℝ) := hi
      _ = (((Finset.Icc (p - N) N).filter Nat.Prime).card : ℝ) := by rfl

/-- Rounding-free real interface for the sieve-free endgame.  The lower
prime counts may be any nonnegative real estimates for the outer window and
all inner intervals. -/
private lemma grahamBound_of_basic_real_card_separation
    (A : Finset ℕ) (G : ℕ) (RP RQ : ℝ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hRQ : 0 ≤ RQ)
    (hP : RP ≤ ((primeWindow A.card G).card : ℝ))
    (hQ : ∀ p ∈ primeWindow A.card G,
      RQ ≤ (((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card : ℝ))
    (hseparate :
      ((G + 1 : ℕ) : ℝ) * firstMomentRealBound A.card (2 * G) +
          firstMomentRealBound A.card G *
            firstMomentRealBound A.card (2 * G) < RP * RQ) :
    GrahamBound A := by
  have hN : 0 < A.card := by omega
  have hGle : G ≤ A.card := by omega
  have htwoG : 2 * G ≤ A.card := by omega
  let F₁ := (firstMomentTriples A.card A.card (A.card - G)).card
  let F₂ := (firstMomentTriples A.card A.card (A.card - 2 * G)).card
  have hF₁ : (F₁ : ℝ) ≤ firstMomentRealBound A.card G := by
    dsimp only [F₁]
    exact firstMomentTriples_card_real_le_bound hN hGle
  have hF₂ : (F₂ : ℝ) ≤ firstMomentRealBound A.card (2 * G) := by
    dsimp only [F₂]
    exact firstMomentTriples_card_real_le_bound hN htwoG
  have hwindow : (primeWindow A.card G).card ≤ G + 1 :=
    primeWindow_card_le_add_one hGle
  have hwindowReal : ((primeWindow A.card G).card : ℝ) ≤
      ((G + 1 : ℕ) : ℝ) := by
    exact_mod_cast hwindow
  have hB₁nonneg : 0 ≤ firstMomentRealBound A.card G :=
    (Nat.cast_nonneg F₁).trans hF₁
  have hupperReal :
      (((primeWindow A.card G).card * F₂ + F₁ * F₂ : ℕ) : ℝ) ≤
        ((G + 1 : ℕ) : ℝ) * firstMomentRealBound A.card (2 * G) +
          firstMomentRealBound A.card G *
            firstMomentRealBound A.card (2 * G) := by
    simp only [Nat.cast_add, Nat.cast_mul]
    apply add_le_add
    · have hmul :
          ((primeWindow A.card G).card : ℝ) * (F₂ : ℝ) ≤
            ((G + 1 : ℕ) : ℝ) * firstMomentRealBound A.card (2 * G) :=
        mul_le_mul hwindowReal hF₂ (Nat.cast_nonneg F₂) (by positivity)
      simpa only [Nat.cast_add] using hmul
    · exact mul_le_mul hF₁ hF₂ (Nat.cast_nonneg F₂) hB₁nonneg
  have hlowerReal : RP * RQ ≤
      (basicPrimeCollisionLower A.card G : ℝ) :=
    real_mul_le_basicPrimeCollisionLower hRQ hP hQ
  have hstrictReal :
      (((primeWindow A.card G).card * F₂ + F₁ * F₂ : ℕ) : ℝ) <
        (basicPrimeCollisionLower A.card G : ℝ) :=
    hupperReal.trans_lt (hseparate.trans_le hlowerReal)
  have hstrictNat :
      (primeWindow A.card G).card * F₂ + F₁ * F₂ <
        basicPrimeCollisionLower A.card G := by
    exact_mod_cast hstrictReal
  apply grahamBound_of_basic_analytic_separation A G h₀ hgcd hG hGN
  simpa only [F₁, F₂] using hstrictNat

/-- The full Graham bound for every sufficiently large normalized finset.
The threshold is non-explicit because it is inherited from `MediumPNT`. -/
private theorem eventually_grahamBound_normalized :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A.card = N →
      0 ∉ A → A.gcd id = 1 → GrahamBound A := by
  have hshortEv := eventually_primeInterval_card_real_lower 5
  rw [eventually_atTop] at hshortEv
  obtain ⟨V, hshort⟩ := hshortEv
  have hlogEv : ∀ᶠ N : ℕ in atTop, 20000 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 20000)
  filter_upwards [eventually_analyticG_bounds, hlogEv,
    eventually_ge_atTop V] with N hGb hlog hVN
  intro A hcard h₀ hgcd
  let G := analyticG N
  have hGlower : (N : ℝ) / (2 * Real.log N ^ 4) ≤ (G : ℝ) := hGb.1
  have hGupper : (G : ℝ) ≤ (N : ℝ) / Real.log N ^ 4 := hGb.2.1
  have hG : 0 < G := by exact_mod_cast hGb.2.2
  have hN : 0 < N := by
    by_contra hn
    have hNzero : N = 0 := Nat.eq_zero_of_not_pos hn
    norm_num [hNzero] at hlog
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hL4 : (10 : ℝ) ≤ Real.log (N : ℝ) ^ 4 := by
    have : (10 : ℝ) ≤ Real.log (N : ℝ) := by linarith
    nlinarith [sq_nonneg (Real.log (N : ℝ)),
      sq_nonneg (Real.log (N : ℝ) ^ 2 - 10)]
  have h10real : (10 : ℝ) * (G : ℝ) ≤ N := by
    calc
      (10 : ℝ) * (G : ℝ) ≤ 10 * ((N : ℝ) / Real.log N ^ 4) :=
        mul_le_mul_of_nonneg_left hGupper (by norm_num)
      _ ≤ (N : ℝ) := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (pow_pos hlogpos 4)).2
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right hL4 (Nat.cast_nonneg N)
  have h10 : 10 * G ≤ N := by exact_mod_cast h10real
  have h2 : 2 * G ≤ N := by omega
  have hpcounts := analytic_prime_bounds hN hG h10 hlog hGlower
    hshort hVN
  have hsep := analytic_numeric_separation hN h2 hlog hGlower hGupper hG
  subst N
  apply grahamBound_of_basic_real_card_separation A G
      ((G : ℝ) / (4 * Real.log A.card))
      ((G : ℝ) / (2 * Real.log A.card)) h₀ hgcd hG h10
  · positivity
  · simpa only using hpcounts.1
  · intro p hp
    exact hpcounts.2 p hp
  · simpa only using hsep

/-- Eventual form of the exact Formal Conjectures statement, with no gcd
normalization assumption. -/
theorem erdos_402_of_sufficiently_large :
    ∃ N₀ : ℕ, ∀ A : Finset ℕ, N₀ ≤ A.card → 0 ∉ A → A.Nonempty →
      ∃ᵉ (a ∈ A) (b ∈ A), a.gcd b ≤ (a / A.card : ℚ) := by
  have hlargeEv := eventually_grahamBound_normalized
  rw [eventually_atTop] at hlargeEv
  obtain ⟨N₀, hlarge⟩ := hlargeEv
  refine ⟨N₀, ?_⟩
  intro A hcard h₀ hA
  let B := normalize A
  have hBcard : B.card = A.card := normalize_card A
  have hB₀ : 0 ∉ B := normalize_nonzero A h₀
  have hBgcd : B.gcd id = 1 := normalize_gcd A h₀ hA
  have hBbound : GrahamBound B :=
    hlarge B.card (hcard.trans_eq hBcard.symm) B rfl hB₀ hBgcd
  exact erdos_402_of_grahamBound A hA (grahamBound_of_normalize A hBbound)

/-- Exact finite endgame for Sections 4 and 5.  The hypothesis is now a
single strict inequality between four executable finite sums.  Thus every
subsequent analytic lemma can be checked independently of the gcd argument. -/
private lemma grahamBound_of_total_analytic_separation
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hG : 0 < G)
    (hGN : 10 * G ≤ A.card)
    (hcollision : ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α)
    (hseparate : ∀ E : Finset ℕ, E.card ≤ 2 →
      (∀ q ∈ E, q.Prime) →
      (∀ q ∈ E, (A.card + G) ^ 3 <
        q ^ 3 * globalD A G) →
      2 * (totalLinearUpper A.card G (globalD A G) +
          totalBilinearUpper A.card G (globalD A G)) +
          totalExceptionalCorrection A.card G E <
        totalSafeLargePrimeCandidates A.card G (globalD A G)) :
    GrahamBound A := by
  by_contra hbad
  obtain ⟨E, hEcard, hEprime, hElarge, hlower⟩ :=
    exists_exceptional_set_total_safe_le_excess
      A G h₀ hgcd hbad hG hGN hcollision
  have hupper := totalCollisionExcess_le_upper A G hbad hG hGN
  have hsep := hseparate E hEcard hEprime hElarge
  omega

/-- A numerical form of the analytic endgame.  The analytic development may
bound the three large finite sums by any convenient natural numbers `L`, `B`,
and `S`; the exceptional-prime term is then discharged uniformly from a
single cube-scale parameter `K`. -/
private lemma grahamBound_of_analytic_sum_bounds
    (A : Finset ℕ) (G K L B S : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hG : 0 < G)
    (hGN : 10 * G ≤ A.card) (hK : 0 < K)
    (hcollision : ∃ p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G),
      p.Prime ∧ ∃ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        2 ≤ representationCount A p α)
    (hscale : K ^ 3 * A.card ≤ (A.card + G) ^ 3)
    (hlinear : totalLinearUpper A.card G (globalD A G) ≤ L)
    (hbilinear : totalBilinearUpper A.card G (globalD A G) ≤ B)
    (hsafe : S ≤ totalSafeLargePrimeCandidates A.card G (globalD A G))
    (hnumeric :
      2 * (L + B) +
          (G + 1) * (2 * ((2 * G) / K + 1)) < S) :
    GrahamBound A := by
  by_cases hbound : GrahamBound A
  · exact hbound
  apply grahamBound_of_total_analytic_separation A G h₀ hgcd hG hGN hcollision
  intro E hEcard _hEprime hElarge
  have hsmall : 4 * G ≤ A.card := by omega
  have hDcard : globalD A G ≤ A.card :=
    globalD_le_card A G hbound hG hsmall
  have hDlower := card_lt_two_mul_G_mul_globalD
    A G hbound hG hsmall hcollision
  have hDpos : 0 < globalD A G := by
    by_contra hD
    have hDzero : globalD A G = 0 := Nat.eq_zero_of_not_pos hD
    simp only [hDzero, mul_zero] at hDlower
    exact (Nat.not_lt_zero A.card) hDlower
  have hcorr := totalExceptionalCorrection_le_of_cube_scale E
    (show G ≤ A.card by omega) hK hDpos hDcard hscale hEcard hElarge
  calc
    2 * (totalLinearUpper A.card G (globalD A G) +
          totalBilinearUpper A.card G (globalD A G)) +
        totalExceptionalCorrection A.card G E ≤
        2 * (L + B) +
          (G + 1) * (2 * ((2 * G) / K + 1)) := by omega
    _ < S := hnumeric
    _ ≤ totalSafeLargePrimeCandidates A.card G (globalD A G) := hsafe

end Erdos402

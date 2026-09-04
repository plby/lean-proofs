import ErdosProblems.Erdos67b.CRTComplex
import ErdosProblems.Erdos67b.LogBlockEntropy

/-!
# Finite prime-graph coordinate sums

The vertices are indexed by `Fin H`, representing offsets `1,...,H`.
An edge of length `p*h` is included exactly when its second endpoint
stays in the block. No periodic wrap-around is introduced.
-/

open scoped BigOperators ComplexConjugate NNReal
open Finset

namespace Erdos67b

noncomputable section

/-- A residue class has at most `H / p + 1` representatives in a block
of length `H`, by injectivity of the quotient within that class. -/
theorem card_fin_residue_le (H p : ℕ) [NeZero p] (r : ZMod p) :
    (Finset.univ.filter fun j : Fin H ↦ (j.1 : ZMod p) = r).card ≤ H / p + 1 := by
  classical
  let s : Finset (Fin H) := Finset.univ.filter fun j ↦ (j.1 : ZMod p) = r
  have hmap : Set.MapsTo (fun j : Fin H ↦ j.1 / p) s (Finset.range (H / p + 1)) := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right j.isLt.le))
  have hinj : Set.InjOn (fun j : Fin H ↦ j.1 / p) s := by
    intro i hi j hj hq
    change i.1 / p = j.1 / p at hq
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have hmod := congrArg ZMod.val (hi'.trans hj'.symm)
    simp only [ZMod.val_natCast] at hmod
    apply Fin.ext
    have hiDiv := Nat.mod_add_div i.1 p
    have hjDiv := Nat.mod_add_div j.1 p
    rw [hq, hmod] at hiDiv
    omega
  have h := Finset.card_le_card_of_injOn (fun j : Fin H ↦ j.1 / p) hmap hinj
  simpa only [Finset.card_range] using h

/-- Edge coefficient with an exact block-boundary cutoff. -/
def primeGraphEdge {H : ℕ} (b : Fin H → ℂ) (p h : ℕ) (j : Fin H) : ℂ :=
  if hj : j.1 + p * h < H then b j * conj (b ⟨j.1 + p * h, hj⟩) else 0

/-- The contribution of one prime, as a function of its residue only. -/
def primeGraphCoordinate {H : ℕ} (b : Fin H → ℂ) (p h : ℕ) (z : ZMod p) : ℂ :=
  ∑ j : Fin H, if z + (j.1 + 1 : ℕ) = 0 then primeGraphEdge b p h j else 0

theorem norm_primeGraphEdge_le {H : ℕ} (b : Fin H → ℂ) (p h : ℕ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ j, ‖b j‖ ≤ B) (j : Fin H) :
    ‖primeGraphEdge b p h j‖ ≤ B ^ 2 := by
  unfold primeGraphEdge
  split_ifs with hj
  · rw [norm_mul, Complex.norm_conj, pow_two]
    exact mul_le_mul (hb j) (hb _) (norm_nonneg _) hB
  · simpa only [norm_zero] using sq_nonneg B

theorem norm_primeGraphCoordinate_le {H : ℕ} (b : Fin H → ℂ) (p h : ℕ) [NeZero p]
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ j, ‖b j‖ ≤ B) (z : ZMod p) :
    ‖primeGraphCoordinate b p h z‖ ≤ (H / p + 1 : ℕ) * B ^ 2 := by
  classical
  let s : Finset (Fin H) := Finset.univ.filter fun j ↦ z + (j.1 + 1 : ℕ) = 0
  have hs : s = Finset.univ.filter (fun j : Fin H ↦ (j.1 : ZMod p) = -z - 1) := by
    ext j
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_add, Nat.cast_one]
    constructor <;> intro h <;> linear_combination h
  have hcard : s.card ≤ H / p + 1 := by rw [hs]; exact card_fin_residue_le H p (-z - 1)
  have hsum : primeGraphCoordinate b p h z = ∑ j ∈ s, primeGraphEdge b p h j := by
    simp only [primeGraphCoordinate, s, Finset.sum_filter]
  rw [hsum]
  calc
    ‖∑ j ∈ s, primeGraphEdge b p h j‖ ≤ ∑ j ∈ s, ‖primeGraphEdge b p h j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, B ^ 2 := Finset.sum_le_sum (fun j _ ↦ norm_primeGraphEdge_le b p h hB hb j)
    _ = s.card * B ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H / p + 1 : ℕ) * B ^ 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg B)

/-- Each edge is counted for exactly one residue, so the uniform
coordinate mean simply replaces the divisibility indicator by `1/p`. -/
theorem sum_primeGraphCoordinate {H : ℕ} (b : Fin H → ℂ) (p h : ℕ) [NeZero p] :
    (∑ z : ZMod p, primeGraphCoordinate b p h z) = ∑ j, primeGraphEdge b p h j := by
  classical
  simp only [primeGraphCoordinate]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hcond (z : ZMod p) : z + (j.1 + 1 : ℕ) = 0 ↔ z = -((j.1 + 1 : ℕ) : ZMod p) := by
    exact eq_neg_iff_add_eq_zero.symm
  simp_rw [hcond]
  simp

/-- On primes of size at least `δH`, each coordinate has a bound
independent of the block length. -/
theorem norm_primeGraphCoordinate_le_of_scale {H : ℕ} (b : Fin H → ℂ)
    (p h : ℕ) [NeZero p] {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hb : ∀ j, ‖b j‖ ≤ B) (hp : δ * H ≤ p) (z : ZMod p) :
    ‖primeGraphCoordinate b p h z‖ ≤ (1 / δ + 1) * B ^ 2 := by
  have hpr : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hdiv : (H / p : ℕ) ≤ (H : ℝ) / p := by
    apply (le_div_iff₀ hpr).mpr
    exact_mod_cast Nat.div_mul_le_self H p
  have hratio : (H : ℝ) / p ≤ 1 / δ := by
    apply (div_le_div_iff₀ hpr hδ).mpr
    nlinarith
  have hfloor : (H / p + 1 : ℕ) ≤ 1 / δ + (1 : ℝ) := by
    push_cast
    linarith
  exact (norm_primeGraphCoordinate_le b p h hB hb z).trans
    (mul_le_mul_of_nonneg_right hfloor (sq_nonneg B))

/-- All primes through the block length index the ambient CRT space. -/
abbrev PrimeGraphIndex (H : ℕ) := {p : ℕ // p ∈ Nat.primesLE H}

instance instNeZeroPrimeGraphIndex {H : ℕ} (p : PrimeGraphIndex H) : NeZero p.1 :=
  ⟨(Nat.prime_of_mem_primesLE p.2).ne_zero⟩

theorem primeGraphModuli_pairwise (H : ℕ) :
    Pairwise (Function.onFun Nat.Coprime (fun p : PrimeGraphIndex H ↦ p.1)) := by
  intro p q hpq
  exact (Nat.coprime_primes (Nat.prime_of_mem_primesLE p.2)
    (Nat.prime_of_mem_primesLE q.2)).mpr (fun h ↦ hpq (Subtype.ext h))

/-- Written as a product over the actual CRT index type. -/
def primeGraphModulus (H : ℕ) : ℕ := ∏ p : PrimeGraphIndex H, p.1

theorem primeGraphModulus_eq_primorial (H : ℕ) : primeGraphModulus H = primorial H := by
  calc
    primeGraphModulus H = ∏ p ∈ Nat.primesLE H, p :=
      Finset.prod_coe_sort (Nat.primesLE H) (fun p : ℕ ↦ p)
    _ = primorial H := (primorial_eq_prod_primesLE H).symm

instance instNeZeroPrimeGraphModulus (H : ℕ) : NeZero (primeGraphModulus H) := by
  rw [primeGraphModulus_eq_primorial]
  infer_instance

/-- Inactive prime coordinates contribute zero, allowing the full
primorial CRT space to be retained throughout the entropy argument. -/
def primeGraphObservable {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (p : PrimeGraphIndex H) (z : ZMod p.1) : ℂ :=
  if p.1 ∈ s then primeGraphCoordinate b p.1 h z else 0

def primeGraphSum {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (z : ZMod (primeGraphModulus H)) : ℂ :=
  crtComplexSum (fun p : PrimeGraphIndex H ↦ p.1) (primeGraphModuli_pairwise H)
    Finset.univ (primeGraphObservable b h s) z

def primeGraphMean {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ) : ℂ :=
  ∑ p : PrimeGraphIndex H, if p.1 ∈ s then (p.1 : ℝ)⁻¹ • ∑ j, primeGraphEdge b p.1 h j else 0

theorem crtComplexMean_primeGraphObservable {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ) :
    crtComplexMean (fun p : PrimeGraphIndex H ↦ p.1) Finset.univ
      (primeGraphObservable b h s) = primeGraphMean b h s := by
  unfold crtComplexMean primeGraphMean
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1 ∈ s
  · simp only [primeGraphObservable, hp, if_true, sum_primeGraphCoordinate]
  · simp only [primeGraphObservable, hp, if_false, Finset.sum_const_zero, smul_zero]

theorem norm_primeGraphObservable_le {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hb : ∀ j, ‖b j‖ ≤ B)
    (hs : ∀ p ∈ s, δ * H ≤ p) (p : PrimeGraphIndex H) (z : ZMod p.1) :
    ‖primeGraphObservable b h s p z‖ ≤ (1 / δ + 1) * B ^ 2 := by
  unfold primeGraphObservable
  split_ifs with hp
  · exact norm_primeGraphCoordinate_le_of_scale b p.1 h hB hδ hb (hs p.1 hp) z
  · simp only [norm_zero]
    positivity

/-- Evaluation on an integer has the original divisibility indicators,
not an unrelated CRT observable. -/
theorem primeGraphSum_natCast {H : ℕ} (b : Fin H → ℂ) (h n : ℕ) (s : Finset ℕ) :
    primeGraphSum b h s (n : ZMod (primeGraphModulus H)) =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if p.1 ∣ n + j.1 + 1 then primeGraphEdge b p.1 h j else 0
      else 0 := by
  have hcrt (p : PrimeGraphIndex H) :
      ZMod.prodEquivPi (fun q : PrimeGraphIndex H ↦ q.1) (primeGraphModuli_pairwise H)
        (n : ZMod (primeGraphModulus H)) p = (n : ZMod p.1) := by
    exact congrFun (map_natCast
      (ZMod.prodEquivPi (fun q : PrimeGraphIndex H ↦ q.1) (primeGraphModuli_pairwise H)) n) p
  simp only [primeGraphSum, crtComplexSum, primeGraphObservable, primeGraphCoordinate,
    hcrt, ← Nat.cast_add, ZMod.natCast_eq_zero_iff, Nat.add_assoc]

theorem card_primeGraphIndex (H : ℕ) : Fintype.card (PrimeGraphIndex H) = Nat.primeCounting H := by
  rw [Fintype.card_coe, Nat.primesLE_card_eq_primeCounting]

theorem primeGraphIndex_card_pos {H : ℕ} (hH : 2 ≤ H) :
    0 < Fintype.card (PrimeGraphIndex H) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨2, Nat.mem_primesLE.mpr ⟨hH, Nat.prime_two⟩⟩⟩

/-- An explicit block-length-independent radius for bounded blocks. -/
def primeGraphRadius (B δ : ℝ) : ℝ := (1 / δ + 1) * B ^ 2

theorem primeGraphRadius_nonneg {B δ : ℝ} (hδ : 0 < δ) : 0 ≤ primeGraphRadius B δ := by
  unfold primeGraphRadius
  positivity

/-- Exceptional graph residues have exponentially small cardinality
whenever the displayed finite scalar budget is met. -/
theorem primeGraph_tail_card_mul_exp_le {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    {B δ t r : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hb : ∀ j, ‖b j‖ ≤ B)
    (hs : ∀ p ∈ s, δ * H ≤ p) (ht : 0 ≤ t)
    (hr : r + Real.log 4 ≤ t ^ 2 /
      (8 * (Nat.primeCounting H : ℝ) * (primeGraphRadius B δ) ^ 2)) :
    ((Finset.univ.filter fun z : ZMod (primeGraphModulus H) ↦
      t ≤ ‖primeGraphSum b h s z - primeGraphMean b h s‖).card : ℝ) * Real.exp r ≤
        primeGraphModulus H := by
  classical
  let : NeZero (∏ p : PrimeGraphIndex H, p.1) :=
    ⟨show primeGraphModulus H ≠ 0 from NeZero.ne _⟩
  let R : ℝ≥0 := ⟨primeGraphRadius B δ, primeGraphRadius_nonneg hδ⟩
  have hbound : ∀ p : PrimeGraphIndex H, ∀ _ : p ∈ Finset.univ, ∀ z,
      ‖primeGraphObservable b h s p z‖ ≤ (R : ℝ) := by
    intro p _ z
    exact norm_primeGraphObservable_le b h s hB hδ hb hs p z
  have hsum : ((∑ _p : PrimeGraphIndex H, R ^ 2 : ℝ≥0) : ℝ) =
      (Nat.primeCounting H : ℝ) * primeGraphRadius B δ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul]
    simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]
    rfl
  have htail := crt_complex_tail_card_mul_exp_le
    (fun p : PrimeGraphIndex H ↦ p.1) (primeGraphModuli_pairwise H) Finset.univ
    (primeGraphObservable b h s) (fun _ ↦ R) hbound ht
    (by rw [hsum]; simpa only [mul_assoc] using hr)
  rw [crtComplexMean_primeGraphObservable] at htail
  exact htail

end

end Erdos67b

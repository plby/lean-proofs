/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerInduction
import ErdosProblems.Erdos240.BakerRationalExtrapolation
import ErdosProblems.Erdos240.InterpolationProducts
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Hermite interpolation on the nodes prime to the auxiliary prime

The second half of van der Poorten--Loxton's Lemma 6 (pp. 51--52) starts
with the successor auxiliary function vanishing only at the integers prime
to `q`.  It repeats the Hermite interpolation argument on precisely those
nodes and fills the missing multiples of `q` by the Liouville alternative.

This file supplies the exact repeated-node list and nodal product, its
cardinality for prime `q`, and a certificate-based completion theorem
parallel to `vdpl_lemma5_of_interpolation_certificates`.  The certificate
keeps every analytic and numerical estimate visible; in particular, it is
not an assumption that the desired value is already small or zero.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerCoprimeInterpolation

open Finset Metric
open BakerInduction BakerRationalExtrapolation
open HermiteInterpolation InterpolationProducts

/-- Indices `i = r-1` for the interpolation nodes `1 ≤ r ≤ R` prime to
`q`.  Using zero-based indices makes the definition compatible with the
existing integral-node interpolation API. -/
def coprimeNodeIndices (q R : ℕ) : Finset ℕ :=
  (Finset.range R).filter fun i ↦ (i + 1).Coprime q

/-- The coprime integral nodes, each repeated with Hermite multiplicity
`T`. -/
def coprimeNodes (q R T : ℕ) : List ℂ :=
  (coprimeNodeIndices q R).toList.flatMap fun i ↦
    List.replicate T ((i + 1 : ℕ) : ℂ)

/-- The product over the coprime integral nodes, each with multiplicity
`T`. -/
def coprimeNodalProduct (q R T : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ coprimeNodeIndices q R, (z - ((i + 1 : ℕ) : ℂ)) ^ T

@[simp] theorem mem_coprimeNodeIndices {q R i : ℕ} :
    i ∈ coprimeNodeIndices q R ↔ i < R ∧ (i + 1).Coprime q := by
  simp [coprimeNodeIndices]

@[simp] theorem length_coprimeNodes (q R T : ℕ) :
    (coprimeNodes q R T).length = (coprimeNodeIndices q R).card * T := by
  simp [coprimeNodes]

/-- Membership in the repeated list is exactly membership in the source's
coprime grid (provided the Hermite multiplicity is nonzero). -/
theorem mem_coprimeNodes_iff {q R T : ℕ} {a : ℂ} :
    a ∈ coprimeNodes q R T ↔
      ∃ r, 1 ≤ r ∧ r ≤ R ∧ r.Coprime q ∧ T ≠ 0 ∧ a = (r : ℂ) := by
  simp only [coprimeNodes, List.mem_flatMap, List.mem_replicate]
  constructor
  · rintro ⟨i, hi, hT, rfl⟩
    have hi' : i ∈ coprimeNodeIndices q R := by simpa using hi
    rw [mem_coprimeNodeIndices] at hi'
    refine ⟨i + 1, Nat.le_add_left 1 i, ?_, hi'.2, hT, rfl⟩
    exact Nat.succ_le_iff.mpr hi'.1
  · rintro ⟨r, hr1, hrR, hcop, hT, rfl⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr1)
    refine ⟨i, ?_, hT, rfl⟩
    simpa only [Finset.mem_toList, mem_coprimeNodeIndices] using
      And.intro (Nat.lt_of_succ_le hrR) hcop

/-- Bridge from the repeated coprime-node list to its finite-product form. -/
theorem nodeProduct_coprimeNodes (q R T : ℕ) (z : ℂ) :
    nodeProduct (coprimeNodes q R T) z =
      coprimeNodalProduct q R T z := by
  classical
  unfold nodeProduct coprimeNodes coprimeNodalProduct
  rw [List.map_flatMap]
  have hflat (l : List ℕ) :
      (l.flatMap fun i ↦
          (List.replicate T ((i + 1 : ℕ) : ℂ)).map (fun a ↦ z - a)).prod =
        (l.map fun i ↦ (z - ((i + 1 : ℕ) : ℂ)) ^ T).prod := by
    induction l with
    | nil => simp
    | cons i l ih =>
        rw [List.flatMap_cons, List.prod_append, ih]
        simp only [List.map_replicate, List.prod_replicate,
          List.map_cons, List.prod_cons]
  rw [hflat]
  exact Finset.prod_map_toList _ _

/-- Repeating every coprime node `T` times raises the unpowered nodal
product to the `T`th power. -/
theorem coprimeNodalProduct_eq_base_pow (q R T : ℕ) (z : ℂ) :
    coprimeNodalProduct q R T z =
      (coprimeNodalProduct q R 1 z) ^ T := by
  simp [coprimeNodalProduct, Finset.prod_pow]

/-- For prime `q`, there are `R - floor(R/q)` positive integers at most
`R` which are prime to `q`. -/
theorem card_coprimeNodeIndices_of_prime {q R : ℕ} (hq : q.Prime) :
    (coprimeNodeIndices q R).card = R - R / q := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.range R) (p := fun i ↦ (i + 1).Coprime q)
  have hbad :
      ((Finset.range R).filter fun i ↦ ¬(i + 1).Coprime q).card = R / q := by
    have hsets :
        ((Finset.range R).filter fun i ↦ ¬(i + 1).Coprime q) =
          (Finset.range R).filter fun i ↦ q ∣ i + 1 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
      intro _hi
      rw [Nat.coprime_comm, hq.coprime_iff_not_dvd, not_not]
    rw [hsets, Nat.card_multiples]
  rw [hbad, Finset.card_range] at hpartition
  unfold coprimeNodeIndices
  omega

/-- When `q ∣ R`, the preceding count is the source's
`R (q-1) / q`. -/
theorem card_coprimeNodeIndices_of_prime_of_dvd {q R : ℕ}
    (hq : q.Prime) (hdiv : q ∣ R) :
    (coprimeNodeIndices q R).card = R * (q - 1) / q := by
  rw [card_coprimeNodeIndices_of_prime hq]
  obtain ⟨M, rfl⟩ := hdiv
  rw [Nat.mul_div_cancel_left M hq.pos]
  rw [Nat.mul_assoc,
    Nat.mul_div_cancel_left (M * (q - 1)) hq.pos]
  rw [Nat.mul_comm M (q - 1), Nat.sub_mul, one_mul]

/-- Exact length of the source repeated-node list in complete residue
blocks. -/
theorem length_coprimeNodes_of_prime_of_dvd {q R T : ℕ}
    (hq : q.Prime) (hdiv : q ∣ R) :
    (coprimeNodes q R T).length = (R * (q - 1) / q) * T := by
  rw [length_coprimeNodes,
    card_coprimeNodeIndices_of_prime_of_dvd hq hdiv]

/-- A product-ratio estimate for the coprime nodes.  This is the reusable
finite-product step behind the source's outer ratio; a source-specific
geometric argument supplies the displayed per-node bound. -/
theorem norm_coprimeNodalProduct_div_le
    {q R T : ℕ} {x z : ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B)
    (hnum : ∀ i ∈ coprimeNodeIndices q R,
      ‖x - ((i + 1 : ℕ) : ℂ)‖ ≤ A)
    (hden : ∀ i ∈ coprimeNodeIndices q R,
      B ≤ ‖z - ((i + 1 : ℕ) : ℂ)‖) :
    ‖coprimeNodalProduct q R T x‖ /
        ‖coprimeNodalProduct q R T z‖ ≤
      (A / B) ^ ((coprimeNodeIndices q R).card * T) := by
  unfold coprimeNodalProduct
  rw [← norm_div]
  exact norm_prod_pow_div_prod_pow_le T hA hB hnum hden

/-- Source-shaped powering step for the p. 52 outer-product ratio.  The
nontrivial geometry is entirely in the unpowered estimate `hbase`; Hermite
multiplicity then contributes the outer `T`th power verbatim. -/
theorem norm_coprimeNodalProduct_div_le_source_power
    {q R T : ℕ} {x z : ℂ}
    (hbase : ‖coprimeNodalProduct q R 1 x‖ /
        ‖coprimeNodalProduct q R 1 z‖ ≤
      (3 : ℝ)⁻¹ ^ (coprimeNodeIndices q R).card) :
    ‖coprimeNodalProduct q R T x‖ /
        ‖coprimeNodalProduct q R T z‖ ≤
      ((3 : ℝ)⁻¹ ^ (coprimeNodeIndices q R).card) ^ T := by
  rw [coprimeNodalProduct_eq_base_pow q R T x,
    coprimeNodalProduct_eq_base_pow q R T z, norm_pow, norm_pow, ← div_pow]
  exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (norm_nonneg _))
    hbase T

/-- The literal source exponent when the radius is a complete collection
of residue blocks. -/
theorem norm_coprimeNodalProduct_div_le_source_power_of_prime_of_dvd
    {q R T : ℕ} {x z : ℂ} (hq : q.Prime) (hdiv : q ∣ R)
    (hbase : ‖coprimeNodalProduct q R 1 x‖ /
        ‖coprimeNodalProduct q R 1 z‖ ≤
      (3 : ℝ)⁻¹ ^ (R * (q - 1) / q)) :
    ‖coprimeNodalProduct q R T x‖ /
        ‖coprimeNodalProduct q R T z‖ ≤
      ((3 : ℝ)⁻¹ ^ (R * (q - 1) / q)) ^ T := by
  rw [← card_coprimeNodeIndices_of_prime_of_dvd hq hdiv] at hbase ⊢
  exact norm_coprimeNodalProduct_div_le_source_power hbase

/-- A Hermite certificate whose nodes are definitionally the repeated
coprime integral nodes.  All contour, polynomial, and strict-budget fields
are inherited from the general interpolation certificate. -/
structure CoprimeInterpolationCertificate
    (q R T : ℕ) (f : ℂ → ℂ) (z : ℂ) (lower : ℝ) where
  data : RationalInterpolationCertificate f z lower
  nodes_eq : data.nodes = coprimeNodes q R T

namespace CoprimeInterpolationCertificate

/-- The certificate forces the corresponding algebraic auxiliary value to
vanish by the same remainder/Liouville argument as in Lemmas 4 and 5. -/
theorem force_zero {q R T : ℕ} {f g : ℂ → ℂ} {z : ℂ} {lower : ℝ}
    (D : CoprimeInterpolationCertificate q R T f z lower)
    (hliouville : g z = 0 ∨ lower ≤ ‖f z‖) :
    g z = 0 :=
  D.data.force_zero hliouville

end CoprimeInterpolationCertificate

/-- Certificate form of the second interpolation on pp. 51--52.  The
already-known coprime nodes are used directly.  Every missing target carries
an explicit Hermite certificate based on those same repeated nodes, and the
Liouville alternative converts its strict upper estimate into vanishing. -/
theorem fill_integral_grid_of_coprime_certificates
    {n q R S T : ℕ} {F G : ℂ → VDPLMultiIndex n → ℂ}
    (lower : ℕ → VDPLMultiIndex n → ℝ)
    (hcoprime : ∀ l, 1 ≤ l → l ≤ R → l.Coprime q →
      ∀ m, VDPLMultiIndex.weight m ≤ S → G (l : ℂ) m = 0)
    (hcertificate : ∀ l, 1 ≤ l → l ≤ R → ¬l.Coprime q →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        CoprimeInterpolationCertificate q R T
          (fun z ↦ F z m) (l : ℂ) (lower l m))
    (hliouville : ∀ l, 1 ≤ l → l ≤ R →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        G (l : ℂ) m = 0 ∨ lower l m ≤ ‖F (l : ℂ) m‖) :
    VanishesOn G 1 R S := by
  intro l hl hlR m hm
  simp only [Nat.cast_one, div_one]
  by_cases hcop : l.Coprime q
  · exact hcoprime l hl hlR hcop m hm
  · exact (hcertificate l hl hlR hcop m hm).force_zero
      (g := fun z ↦ G z m)
      (hliouville l hl hlR m hm)

/-- Level-shaped adapter used by the concrete Lemma 6 continuation. -/
theorem coprimeCompletionAtLevel_of_certificates
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {P : VDPLParameters ι} {J T : ℕ}
    {F G : ℂ → VDPLMultiIndex P.rank → ℂ}
    (lower : ℕ → VDPLMultiIndex P.rank → ℝ)
    (hcertificate : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) → ¬l.Coprime P.q →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel (J + 1) →
        CoprimeInterpolationCertificate P.q (P.R (J + 1)) T
          (fun z ↦ F z m) (l : ℂ) (lower l m))
    (hliouville : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel (J + 1) →
        G (l : ℂ) m = 0 ∨ lower l m ≤ ‖F (l : ℂ) m‖) :
    CoprimeCompletionAtLevel P G J := by
  intro hcoprime
  apply fill_integral_grid_of_coprime_certificates lower
  · intro l hl hlR hcop m hm
    exact hcoprime l hl hlR hcop m
      (hm.trans (P.Slevel_succ_le_Sstep J))
  · exact hcertificate
  · exact hliouville

end Erdos240.BakerCoprimeInterpolation

#print axioms Erdos240.BakerCoprimeInterpolation.card_coprimeNodeIndices_of_prime_of_dvd
#print axioms Erdos240.BakerCoprimeInterpolation.norm_coprimeNodalProduct_div_le
#print axioms Erdos240.BakerCoprimeInterpolation.norm_coprimeNodalProduct_div_le_source_power_of_prime_of_dvd
#print axioms Erdos240.BakerCoprimeInterpolation.fill_integral_grid_of_coprime_certificates
#print axioms Erdos240.BakerCoprimeInterpolation.coprimeCompletionAtLevel_of_certificates

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.NegativeHybridTaylor

/-!
# Short additive blocks inside a dyadic interval

A finite support in `(A,2A]` is partitioned by the quotient
`(n-A-1)/H`.  Indexing only the nonempty fibres gives logarithmic block
centres with spacing at least `H/(2A)` and logarithmic offsets at most
`H/A`.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- Quotients indexing the nonempty additive blocks of `s`. -/
noncomputable def shortBlockIndices (s : Finset ℕ) (A H : ℕ) : Finset ℕ :=
  s.image fun n ↦ (n - A - 1) / H

/-- A nonempty quotient fibre of a finite support. -/
noncomputable def shortBlock (s : Finset ℕ) (A H : ℕ)
    (i : {i // i ∈ shortBlockIndices s A H}) : Finset ℕ :=
  s.filter fun n ↦ (n - A - 1) / H = i.1

/-- Left endpoint of a short additive block. -/
def shortBlockStart (A H : ℕ)
    (i : {i // i ∈ shortBlockIndices s A H}) : ℕ :=
  A + i.1 * H

/-- Logarithmic centre of a short additive block. -/
noncomputable def shortBlockCenter (A H : ℕ)
    (i : {i // i ∈ shortBlockIndices s A H}) : ℝ :=
  Real.log (((shortBlockStart A H i + 1 : ℕ) : ℝ))

private theorem log_sub_log_lower {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    (y - x) / y ≤ Real.log y - Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  calc
    (y - x) / y = 1 - (y / x)⁻¹ := by
      field_simp
    _ ≤ Real.log (y / x) := h
    _ = Real.log y - Real.log x := Real.log_div hy.ne' hx.ne'

private theorem log_sub_log_upper {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    Real.log y - Real.log x ≤ (y - x) / x := by
  have hy : 0 < y := hx.trans_le hxy
  calc
    Real.log y - Real.log x = Real.log (y / x) :=
      (Real.log_div hy.ne' hx.ne').symm
    _ ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy hx)
    _ = (y - x) / x := by field_simp

/-- The quotient fibres partition the original finite support. -/
theorem biUnion_shortBlock (s : Finset ℕ) (A H : ℕ) :
    (Finset.univ : Finset {i // i ∈ shortBlockIndices s A H}).biUnion
        (shortBlock s A H) = s := by
  classical
  ext n
  constructor
  · intro hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨i, _hi, hni⟩ := hn
    exact (Finset.mem_filter.mp hni).1
  · intro hn
    let i : ℕ := (n - A - 1) / H
    have hi : i ∈ shortBlockIndices s A H := by
      rw [shortBlockIndices, Finset.mem_image]
      exact ⟨n, hn, rfl⟩
    rw [Finset.mem_biUnion]
    refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
    rw [shortBlock, Finset.mem_filter]
    exact ⟨hn, rfl⟩

/-- Distinct quotient fibres are disjoint. -/
theorem pairwiseDisjoint_shortBlock (s : Finset ℕ) (A H : ℕ) :
    Set.PairwiseDisjoint
      ((Finset.univ : Finset {i // i ∈ shortBlockIndices s A H}) : Set _)
      (shortBlock s A H) := by
  classical
  intro i hi j hj hij
  change Disjoint (shortBlock s A H i) (shortBlock s A H j)
  rw [Finset.disjoint_left]
  intro n hni hnj
  have hiEq := (Finset.mem_filter.mp hni).2
  have hjEq := (Finset.mem_filter.mp hnj).2
  apply hij
  apply Subtype.ext
  exact hiEq.symm.trans hjEq

/-- Every quotient fibre lies in an additive interval of length `H`. -/
theorem shortBlock_subset_Ioc
    (s : Finset ℕ) (A H : ℕ) (hH : 0 < H)
    (hs : s ⊆ Finset.Ioc A (2 * A))
    (i : {i // i ∈ shortBlockIndices s A H}) :
    shortBlock s A H i ⊆
      Finset.Ioc (shortBlockStart A H i) (shortBlockStart A H i + H) := by
  intro n hn
  have hnData := Finset.mem_filter.mp hn
  have hnBounds := Finset.mem_Ioc.mp (hs hnData.1)
  have hquot : (n - A - 1) / H = i.1 := hnData.2
  have hle := Nat.div_mul_le_self (n - A - 1) H
  have hmod := Nat.mod_lt (n - A - 1) hH
  have hdecomp := Nat.div_add_mod (n - A - 1) H
  rw [hquot] at hle hdecomp
  rw [Nat.mul_comm H i.1] at hdecomp
  have hsub : A + 1 + (n - A - 1) = n := by omega
  rw [Finset.mem_Ioc]
  unfold shortBlockStart
  constructor <;> omega

private theorem shortBlock_index_bound
    {s : Finset ℕ} {A H : ℕ} (hA : 1 ≤ A) (hH : 0 < H)
    (hs : s ⊆ Finset.Ioc A (2 * A))
    (i : {i // i ∈ shortBlockIndices s A H}) :
    A + i.1 * H + 1 ≤ 2 * A := by
  have hiImage := i.2
  change i.1 ∈ s.image (fun n ↦ (n - A - 1) / H) at hiImage
  rw [Finset.mem_image] at hiImage
  obtain ⟨n, hn, hni⟩ := hiImage
  have hnBounds := Finset.mem_Ioc.mp (hs hn)
  have hle := Nat.div_mul_le_self (n - A - 1) H
  rw [hni] at hle
  omega

/-- The logarithmic centres of distinct nonempty blocks are uniformly
separated. -/
theorem shortBlockCenter_separated
    {s : Finset ℕ} {A H : ℕ} (hA : 1 ≤ A) (hH : 0 < H)
    (hs : s ⊆ Finset.Ioc A (2 * A)) :
    ∀ i j : {i // i ∈ shortBlockIndices s A H}, i ≠ j →
      (H : ℝ) / (2 * A : ℕ) ≤
        |shortBlockCenter A H i - shortBlockCenter A H j| := by
  intro i j hij
  have hival := shortBlock_index_bound hA hH hs i
  have hjval := shortBlock_index_bound hA hH hs j
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hdenPos : (0 : ℝ) < (2 * A : ℕ) := by positivity
  unfold shortBlockCenter shortBlockStart
  rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.mpr hij) with hijlt | hjilt
  · have hnatGap : H + (A + i.1 * H + 1) ≤
        A + j.1 * H + 1 := by
      have : i.1 + 1 ≤ j.1 := by omega
      have hmul := Nat.mul_le_mul_right H this
      rw [Nat.add_mul, one_mul] at hmul
      omega
    have hrealOrder : (0 : ℝ) < (A + i.1 * H + 1 : ℕ) := by positivity
    have hleCenters :
        ((A + i.1 * H + 1 : ℕ) : ℝ) ≤
          (A + j.1 * H + 1 : ℕ) := by exact_mod_cast (by omega :
            A + i.1 * H + 1 ≤ A + j.1 * H + 1)
    have hlog := log_sub_log_lower hrealOrder hleCenters
    have hfrac : (H : ℝ) / (2 * A : ℕ) ≤
        (((A + j.1 * H + 1 : ℕ) : ℝ) -
          ((A + i.1 * H + 1 : ℕ) : ℝ)) /
            (A + j.1 * H + 1 : ℕ) := by
      apply (div_le_div_iff₀ hdenPos (by positivity)).2
      have hgapReal : (H : ℝ) ≤
          ((A + j.1 * H + 1 : ℕ) : ℝ) -
            ((A + i.1 * H + 1 : ℕ) : ℝ) := by
        have hcast : (H : ℝ) + ((A + i.1 * H + 1 : ℕ) : ℝ) ≤
            ((A + j.1 * H + 1 : ℕ) : ℝ) := by
          exact_mod_cast hnatGap
        linarith
      have hjReal : ((A + j.1 * H + 1 : ℕ) : ℝ) ≤ (2 * A : ℕ) :=
        by exact_mod_cast hjval
      nlinarith
    rw [abs_sub_comm, abs_of_nonneg] 
    · exact hfrac.trans hlog
    · exact sub_nonneg.mpr (Real.log_le_log hrealOrder hleCenters)
  · have hnatGap : H + (A + j.1 * H + 1) ≤
        A + i.1 * H + 1 := by
      have : j.1 + 1 ≤ i.1 := by omega
      have hmul := Nat.mul_le_mul_right H this
      rw [Nat.add_mul, one_mul] at hmul
      omega
    have hrealOrder : (0 : ℝ) < (A + j.1 * H + 1 : ℕ) := by positivity
    have hleCenters :
        ((A + j.1 * H + 1 : ℕ) : ℝ) ≤
          (A + i.1 * H + 1 : ℕ) := by exact_mod_cast (by omega :
            A + j.1 * H + 1 ≤ A + i.1 * H + 1)
    have hlog := log_sub_log_lower hrealOrder hleCenters
    have hfrac : (H : ℝ) / (2 * A : ℕ) ≤
        (((A + i.1 * H + 1 : ℕ) : ℝ) -
          ((A + j.1 * H + 1 : ℕ) : ℝ)) /
            (A + i.1 * H + 1 : ℕ) := by
      apply (div_le_div_iff₀ hdenPos (by positivity)).2
      have hgapReal : (H : ℝ) ≤
          ((A + i.1 * H + 1 : ℕ) : ℝ) -
            ((A + j.1 * H + 1 : ℕ) : ℝ) := by
        have hcast : (H : ℝ) + ((A + j.1 * H + 1 : ℕ) : ℝ) ≤
            ((A + i.1 * H + 1 : ℕ) : ℝ) := by
          exact_mod_cast hnatGap
        linarith
      have hiReal : ((A + i.1 * H + 1 : ℕ) : ℝ) ≤ (2 * A : ℕ) :=
        by exact_mod_cast hival
      nlinarith
    rw [abs_of_nonneg]
    · exact hfrac.trans hlog
    · exact sub_nonneg.mpr (Real.log_le_log hrealOrder hleCenters)

/-- Every member of a short block is logarithmically close to its block
centre. -/
theorem shortBlock_log_offset_le
    {s : Finset ℕ} {A H : ℕ} (hA : 1 ≤ A) (hH : 0 < H)
    (hs : s ⊆ Finset.Ioc A (2 * A))
    (i : {i // i ∈ shortBlockIndices s A H})
    (n : ℕ) (hn : n ∈ shortBlock s A H i) :
    |Real.log n - shortBlockCenter A H i| ≤ (H : ℝ) / A := by
  have hnBlock := Finset.mem_Ioc.mp (shortBlock_subset_Ioc s A H hH hs i hn)
  let a : ℕ := shortBlockStart A H i + 1
  have haPos : (0 : ℝ) < a := by positivity
  have han : (a : ℝ) ≤ n := by exact_mod_cast (by dsimp [a]; omega)
  have hlogNonneg : 0 ≤ Real.log n - Real.log a :=
    sub_nonneg.mpr (Real.log_le_log haPos han)
  unfold shortBlockCenter
  rw [abs_of_nonneg (by simpa only [a] using hlogNonneg)]
  have hupper := log_sub_log_upper haPos han
  change Real.log n - Real.log a ≤ _
  calc
    Real.log n - Real.log a ≤ ((n : ℝ) - a) / a := hupper
    _ ≤ (H : ℝ) / A := by
      apply (div_le_div_iff₀ haPos (by exact_mod_cast (show 0 < A by omega))).2
      have hdiff : (n : ℝ) - a ≤ H := by
        have hnupper : n ≤ a + H := by
          have hraw : n ≤ shortBlockStart A H i + 1 + H := by omega
          simpa only [a] using hraw
        have hnupperReal : (n : ℝ) ≤ (a : ℝ) + H := by
          exact_mod_cast hnupper
        linarith
      have haA : (A : ℝ) ≤ a := by
        exact_mod_cast (show A ≤ a by dsimp [a, shortBlockStart]; omega)
      nlinarith

end

end Erdos48

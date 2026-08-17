import Mathlib

/-!
# Finite probability and the distortion step for Erdős Problem 586

This file contains the finite probability-space algebra used by the distortion
sieve.  A stage has an old coordinate `X` and a new, uniformly distributed
finite coordinate `Y`.  The set `B : Set (X × Y)` is the part removed at the
stage.  Its relative size in the fibre above `x` is `fiberFraction B x`.

The definition `distortWeight` deliberately has a separate zero-fibre branch.
Thus the quotient by `fiberFraction B x` in the covered-point multiplier is
never evaluated when that fraction is zero.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A probability distribution on a finite type, represented by its point
weights. -/
structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  sum_weight : ∑ ω, weight ω = 1

namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]

/-- The uniform probability distribution on a nonempty finite type. -/
def uniform [Nonempty Ω] : FiniteProbability Ω where
  weight := fun _ => 1 / Fintype.card Ω
  weight_nonneg := fun _ => by positivity
  sum_weight := by
    have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    field_simp

@[simp] lemma uniform_weight [Nonempty Ω] (ω : Ω) :
    (uniform : FiniteProbability Ω).weight ω = 1 / Fintype.card Ω := rfl

/-- The mass assigned to an event. -/
def mass (μ : FiniteProbability Ω) (S : Set Ω) : ℝ :=
  ∑ ω, if ω ∈ S then μ.weight ω else 0

/-- Expectation of a real-valued random variable. -/
def expectation (μ : FiniteProbability Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ.weight ω * f ω

@[simp] lemma mass_empty (μ : FiniteProbability Ω) : μ.mass ∅ = 0 := by
  simp [mass]

@[simp] lemma mass_univ (μ : FiniteProbability Ω) : μ.mass Set.univ = 1 := by
  simpa [mass] using μ.sum_weight

lemma mass_nonneg (μ : FiniteProbability Ω) (S : Set Ω) : 0 ≤ μ.mass S := by
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs
  · exact μ.weight_nonneg ω
  · exact le_rfl

lemma mass_mono (μ : FiniteProbability Ω) {S T : Set Ω} (hST : S ⊆ T) :
    μ.mass S ≤ μ.mass T := by
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hS : ω ∈ S
  · have hT : ω ∈ T := hST hS
    simp [mass, hS, hT]
  · by_cases hT : ω ∈ T
    · simp [mass, hS, hT, μ.weight_nonneg]
    · simp [mass, hS, hT]

lemma mass_le_one (μ : FiniteProbability Ω) (S : Set Ω) : μ.mass S ≤ 1 := by
  simpa using μ.mass_mono (Set.subset_univ S)

lemma expectation_nonneg (μ : FiniteProbability Ω) {f : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ μ.expectation f := by
  apply Finset.sum_nonneg
  intro ω hω
  exact mul_nonneg (μ.weight_nonneg ω) (hf ω)

lemma expectation_mono (μ : FiniteProbability Ω) {f g : Ω → ℝ}
    (hfg : ∀ ω, f ω ≤ g ω) : μ.expectation f ≤ μ.expectation g := by
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left (hfg ω) (μ.weight_nonneg ω)

lemma mass_eq_expectation_indicator (μ : FiniteProbability Ω) (S : Set Ω) :
    μ.mass S = μ.expectation (fun ω => if ω ∈ S then 1 else 0) := by
  simp only [mass, expectation]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hS : ω ∈ S <;> simp [hS]

/-- Transport a finite probability distribution along an equivalence.  This
is the change-of-coordinates operation used after each CRT distortion step. -/
def mapEquiv {Ω' : Type*} [Fintype Ω'] (μ : FiniteProbability Ω)
    (e : Ω ≃ Ω') : FiniteProbability Ω' where
  weight := fun ω' => μ.weight (e.symm ω')
  weight_nonneg := fun ω' => μ.weight_nonneg (e.symm ω')
  sum_weight := by
    rw [e.symm.sum_comp]
    exact μ.sum_weight

@[simp] lemma mapEquiv_weight {Ω' : Type*} [Fintype Ω']
    (μ : FiniteProbability Ω) (e : Ω ≃ Ω') (ω' : Ω') :
    (μ.mapEquiv e).weight ω' = μ.weight (e.symm ω') := rfl

/-- Event mass after a change of coordinates is the mass of its preimage. -/
lemma mapEquiv_mass {Ω' : Type*} [Fintype Ω']
    (μ : FiniteProbability Ω) (e : Ω ≃ Ω') (S : Set Ω') :
    (μ.mapEquiv e).mass S = μ.mass (e ⁻¹' S) := by
  classical
  simp only [mass, mapEquiv_weight, Set.mem_preimage]
  symm
  apply Fintype.sum_equiv e
  intro ω
  simp

/-- In the target coordinates, the event corresponding to a source event
has exactly its original mass.  This is the convenient CRT-stage form of
`mapEquiv_mass`. -/
lemma mapEquiv_mass_symm_preimage {Ω' : Type*} [Fintype Ω']
    (μ : FiniteProbability Ω) (e : Ω ≃ Ω') (S : Set Ω) :
    (μ.mapEquiv e).mass (e.symm ⁻¹' S) = μ.mass S := by
  rw [mapEquiv_mass]
  congr 1
  ext ω
  simp

/-- Expectations transport by composition with the coordinate equivalence. -/
lemma mapEquiv_expectation {Ω' : Type*} [Fintype Ω']
    (μ : FiniteProbability Ω) (e : Ω ≃ Ω') (f : Ω' → ℝ) :
    (μ.mapEquiv e).expectation f = μ.expectation (fun ω => f (e ω)) := by
  simp only [expectation, mapEquiv_weight]
  symm
  apply Fintype.sum_equiv e
  intro ω
  simp

end FiniteProbability

section Fibres

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The number of covered points in the fibre above `x`. -/
def fiberCount (B : Set (X × Y)) (x : X) : ℕ :=
  (Finset.univ.filter fun y => (x, y) ∈ B).card

/-- The fraction of the fibre above `x` which belongs to `B`. -/
def fiberFraction (B : Set (X × Y)) (x : X) : ℝ :=
  (fiberCount B x : ℝ) / Fintype.card Y

lemma fiberCount_le (B : Set (X × Y)) (x : X) : fiberCount B x ≤ Fintype.card Y := by
  simpa [fiberCount] using
    Finset.card_le_card
      (Finset.filter_subset (fun y => (x, y) ∈ B) (Finset.univ : Finset Y))

lemma card_pos_of_nonempty [Nonempty Y] : 0 < Fintype.card Y := Fintype.card_pos

lemma fiberFraction_nonneg [Nonempty Y] (B : Set (X × Y)) (x : X) :
    0 ≤ fiberFraction B x := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma fiberFraction_le_one [Nonempty Y] (B : Set (X × Y)) (x : X) :
    fiberFraction B x ≤ 1 := by
  rw [fiberFraction, div_le_one (by positivity : (0 : ℝ) < Fintype.card Y)]
  exact_mod_cast fiberCount_le B x

lemma fiberFraction_eq_zero_iff [Nonempty Y] (B : Set (X × Y)) (x : X) :
    fiberFraction B x = 0 ↔ ∀ y, (x, y) ∉ B := by
  constructor
  · intro hzero
    have hden : (Fintype.card Y : ℝ) ≠ 0 := by positivity
    have hcCast : (fiberCount B x : ℝ) = 0 :=
      (div_eq_zero_iff.mp (by simpa [fiberFraction] using hzero)).resolve_right hden
    have hc : fiberCount B x = 0 := by exact_mod_cast hcCast
    intro y hy
    have : y ∈ Finset.univ.filter (fun z => (x, z) ∈ B) := by simp [hy]
    have hpos : 0 < fiberCount B x := by
      rw [fiberCount]
      exact Finset.card_pos.mpr ⟨y, this⟩
    omega
  · intro h
    have hc : fiberCount B x = 0 := by
      simp only [fiberCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy
      exact h y
    simp [fiberFraction, hc]

/-- The old distribution, extended uniformly over the new coordinate. -/
def uniformLiftWeight (μ : FiniteProbability X) (z : X × Y) : ℝ :=
  μ.weight z.1 / Fintype.card Y

lemma uniformLiftWeight_nonneg [Nonempty Y] (μ : FiniteProbability X) (z : X × Y) :
    0 ≤ uniformLiftWeight μ z := by
  exact div_nonneg (μ.weight_nonneg z.1) (Nat.cast_nonneg _)

def uniformLift [Nonempty Y] (μ : FiniteProbability X) : FiniteProbability (X × Y) where
  weight := uniformLiftWeight μ
  weight_nonneg := uniformLiftWeight_nonneg μ
  sum_weight := by
    rw [Fintype.sum_prod_type]
    simp only [uniformLiftWeight]
    calc
      ∑ x, ∑ _y : Y, μ.weight x / Fintype.card Y
          = ∑ x, μ.weight x := by
              apply Finset.sum_congr rfl
              intro x hx
              have hcard : (Fintype.card Y : ℝ) ≠ 0 := by positivity
              simp only [Finset.sum_const, nsmul_eq_mul]
              field_simp
              simp only [Finset.card_univ]
              ring
      _ = 1 := μ.sum_weight

lemma uniformLift_fiber_sum [Nonempty Y] (μ : FiniteProbability X) (x : X) :
    ∑ y : Y, (uniformLift μ).weight (x, y) = μ.weight x := by
  have hcard : (Fintype.card Y : ℝ) ≠ 0 := by positivity
  simp only [uniformLift, uniformLiftWeight, Finset.sum_const, nsmul_eq_mul]
  field_simp
  simp only [Finset.card_univ]
  ring

lemma uniformLift_mass_fiber [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) (x : X) :
    ∑ y : Y, (if (x, y) ∈ B then (uniformLift μ).weight (x, y) else 0) =
      μ.weight x * fiberFraction B x := by
  classical
  simp only [uniformLift, uniformLiftWeight, fiberFraction, fiberCount]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp
  <;> ring

lemma uniformLift_mass_eq_expectation [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) :
    (uniformLift μ).mass B = μ.expectation (fiberFraction B) := by
  classical
  rw [FiniteProbability.mass, FiniteProbability.expectation, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  exact uniformLift_mass_fiber μ B x

/-- Point weight after a distortion step.  The first branch is intentionally
separate: when a fibre is empty, no quotient by `fiberFraction B x` is formed. -/
def distortWeight (μ : FiniteProbability X) (B : Set (X × Y)) (δ : ℝ)
    (z : X × Y) : ℝ :=
  let α := fiberFraction B z.1
  let w := uniformLiftWeight μ z
  if hzero : α = 0 then
    w
  else if α ≤ δ then
    if z ∈ B then 0 else (1 / (1 - α)) * w
  else
    if z ∈ B then
      ((α - δ) / (α * (1 - δ))) * w
    else
      (1 / (1 - δ)) * w

lemma distortWeight_of_fiberFraction_eq_zero (μ : FiniteProbability X)
    (B : Set (X × Y)) (δ : ℝ) {x : X} (hzero : fiberFraction B x = 0) (y : Y) :
    distortWeight μ B δ (x, y) = uniformLiftWeight μ (x, y) := by
  simp [distortWeight, hzero]

lemma distortWeight_nonneg [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (z : X × Y) :
    0 ≤ distortWeight μ B δ z := by
  classical
  unfold distortWeight
  dsimp only
  split_ifs with hzero hsmall hB hB
  · exact uniformLiftWeight_nonneg μ z
  · exact le_rfl
  · apply mul_nonneg
    · exact one_div_nonneg.mpr (sub_nonneg.mpr (fiberFraction_le_one B z.1))
    · exact uniformLiftWeight_nonneg μ z
  · apply mul_nonneg
    · exact div_nonneg (sub_nonneg.mpr (le_of_not_ge hsmall))
        (mul_nonneg (fiberFraction_nonneg B z.1) (sub_nonneg.mpr hδ))
    · exact uniformLiftWeight_nonneg μ z
  · apply mul_nonneg
    · exact one_div_nonneg.mpr (sub_nonneg.mpr hδ)
    · exact uniformLiftWeight_nonneg μ z

/-- Sum a function which is constant on the covered and uncovered parts of a
single fibre. -/
lemma sum_fiber_piecewise (B : Set (X × Y)) (x : X) (a b : ℝ) :
    (∑ y : Y, if (x, y) ∈ B then a else b) =
      (fiberCount B x : ℝ) * a +
        ((Fintype.card Y - fiberCount B x : ℕ) : ℝ) * b := by
  classical
  let p : Y → Prop := fun y => (x, y) ∈ B
  have hcard :
      (Finset.univ.filter fun y : Y => ¬p y).card =
        Fintype.card Y - (Finset.univ.filter p).card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Y)) p
    rw [← Finset.card_univ]
    omega
  calc
    (∑ y : Y, if (x, y) ∈ B then a else b) =
        (∑ y ∈ Finset.univ.filter p, a) +
          ∑ y ∈ Finset.univ.filter (fun y => ¬p y), b := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun y => (x, y) ∈ B) (fun y => if (x, y) ∈ B then a else b)]
          congr 1
          · apply Finset.sum_congr rfl
            intro y hy
            have hyB : (x, y) ∈ B := by simpa [p] using (Finset.mem_filter.mp hy).2
            simp [hyB]
          · apply Finset.sum_congr rfl
            intro y hy
            have hyB : (x, y) ∉ B := by simpa [p] using (Finset.mem_filter.mp hy).2
            simp [hyB]
    _ = (fiberCount B x : ℝ) * a +
        ((Fintype.card Y - fiberCount B x : ℕ) : ℝ) * b := by
          simp only [Finset.sum_const, nsmul_eq_mul, p, fiberCount]
          rw [hcard]

/-- Distortion preserves the total mass in every old-coordinate fibre. -/
lemma distort_fiber_sum [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (x : X) :
    ∑ y : Y, distortWeight μ B δ (x, y) = μ.weight x := by
  classical
  let α := fiberFraction B x
  have hα0 : 0 ≤ α := fiberFraction_nonneg B x
  have hα1 : α ≤ 1 := fiberFraction_le_one B x
  have hδ1 : δ < 1 := by linarith
  have hcount := fiberCount_le B x
  have hn : (Fintype.card Y : ℝ) ≠ 0 := by positivity
  by_cases hzero : α = 0
  · simpa only [distortWeight, α, hzero, ↓reduceDIte, uniformLift] using
      uniformLift_fiber_sum μ x
  by_cases hsmall : α ≤ δ
  · have hαlt : α < 1 := by linarith
    have hαden : 1 - α ≠ 0 := by linarith
    have hcountlt : fiberCount B x < Fintype.card Y := by
      change (fiberCount B x : ℝ) / Fintype.card Y < 1 at hαlt
      rw [div_lt_one (by positivity)] at hαlt
      exact_mod_cast hαlt
    have hsub : (Fintype.card Y : ℝ) - fiberCount B x ≠ 0 := by
      have hcountlt' : (fiberCount B x : ℝ) < Fintype.card Y := by exact_mod_cast hcountlt
      linarith
    simp only [distortWeight, Prod.fst, α, hzero, ↓reduceDIte, hsmall, ↓reduceIte,
      uniformLiftWeight]
    rw [sum_fiber_piecewise]
    rw [Nat.cast_sub hcount]
    dsimp [α, fiberFraction]
    field_simp [hn, hsub]
    ring
  · have hδden : 1 - δ ≠ 0 := by linarith
    have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hzero)
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have hcne : (fiberCount B x : ℝ) ≠ 0 := by
      intro hc
      apply hzero
      simp [α, fiberFraction, hc]
    simp only [distortWeight, Prod.fst, α, hzero, ↓reduceDIte, hsmall, ↓reduceIte,
      uniformLiftWeight]
    rw [sum_fiber_piecewise]
    rw [Nat.cast_sub hcount]
    dsimp [α, fiberFraction]
    field_simp [hn, hδden, hcne]
    ring

/-- The probability distribution produced by one distortion stage. -/
def distort [Nonempty Y] (μ : FiniteProbability X) (B : Set (X × Y)) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) : FiniteProbability (X × Y) where
  weight := distortWeight μ B δ
  weight_nonneg := distortWeight_nonneg μ B hδ0 (by linarith)
  sum_weight := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ x, ∑ y, distortWeight μ B δ (x, y) = ∑ x, μ.weight x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact distort_fiber_sum μ B hδ0 hδhalf x
      _ = 1 := μ.sum_weight

@[simp] lemma distort_weight [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (z : X × Y) :
    (distort μ B δ hδ0 hδhalf).weight z = distortWeight μ B δ z := rfl

lemma distort_fiber_conservation [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (x : X) :
    ∑ y : Y, (distort μ B δ hδ0 hδhalf).weight (x, y) = μ.weight x :=
  distort_fiber_sum μ B hδ0 hδhalf x

/-- Every point weight grows by at most `(1-δ)⁻¹`. -/
lemma distortWeight_le_uniform_div [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (z : X × Y) :
    distortWeight μ B δ z ≤ (1 / (1 - δ)) * uniformLiftWeight μ z := by
  classical
  let α := fiberFraction B z.1
  let w := uniformLiftWeight μ z
  have hw : 0 ≤ w := uniformLiftWeight_nonneg μ z
  have hα0 : 0 ≤ α := fiberFraction_nonneg B z.1
  have hα1 : α ≤ 1 := fiberFraction_le_one B z.1
  have hδpos : 0 < 1 - δ := by linarith
  have hfac : 1 ≤ 1 / (1 - δ) := by
    rw [le_div_iff₀ hδpos]
    linarith
  by_cases hzero : α = 0
  · simp only [distortWeight, α, hzero, ↓reduceDIte, w]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac hw
  by_cases hsmall : α ≤ δ
  · by_cases hB : z ∈ B
    · simp only [distortWeight, α, hzero, hsmall, hB, ↓reduceDIte, ↓reduceIte]
      exact mul_nonneg (one_div_nonneg.mpr hδpos.le) (uniformLiftWeight_nonneg μ z)
    · have hαposden : 0 < 1 - α := by linarith
      have hrecip : 1 / (1 - α) ≤ 1 / (1 - δ) :=
        one_div_le_one_div_of_le hδpos (by linarith)
      simp only [distortWeight, α, hzero, hsmall, hB, ↓reduceDIte, ↓reduceIte, w]
      exact mul_le_mul_of_nonneg_right hrecip hw
  · by_cases hB : z ∈ B
    · have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hzero)
      have hmulpos : 0 < α * (1 - δ) := mul_pos hαpos hδpos
      have hquot : (α - δ) / (α * (1 - δ)) ≤ 1 / (1 - δ) := by
        apply (div_le_iff₀ hmulpos).2
        field_simp
        nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hα1)]
      simp only [distortWeight, α, hzero, hsmall, hB, ↓reduceDIte, ↓reduceIte, w]
      exact mul_le_mul_of_nonneg_right hquot hw
    · simp [distortWeight, α, hzero, hsmall, hB, w]

/-- A covered point never gains mass. -/
lemma distortWeight_covered_le [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    {z : X × Y} (hz : z ∈ B) :
    distortWeight μ B δ z ≤ uniformLiftWeight μ z := by
  classical
  let α := fiberFraction B z.1
  let w := uniformLiftWeight μ z
  have hw : 0 ≤ w := uniformLiftWeight_nonneg μ z
  have hα0 : 0 ≤ α := fiberFraction_nonneg B z.1
  have hα1 : α ≤ 1 := fiberFraction_le_one B z.1
  have hδpos : 0 < 1 - δ := by linarith
  have hzero : α ≠ 0 := by
    intro h
    exact (fiberFraction_eq_zero_iff B z.1).mp h z.2 hz
  by_cases hsmall : α ≤ δ
  · simp [distortWeight, α, hzero, hsmall, hz, uniformLiftWeight_nonneg μ]
  · have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hzero)
    have hdenpos : 0 < α * (1 - δ) := mul_pos hαpos hδpos
    have hmul : (α - δ) / (α * (1 - δ)) ≤ 1 := by
      rw [div_le_one hdenpos]
      nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hα1)]
    simp only [distortWeight, α, hzero, hsmall, hz, ↓reduceDIte, ↓reduceIte, w]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hmul hw

/-- Pointwise domination implies the event form of the distortion bound. -/
lemma distort_event_le [Nonempty Y] (μ : FiniteProbability X)
    (B S : Set (X × Y)) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    (distort μ B δ hδ0 hδhalf).mass S ≤
      (1 / (1 - δ)) * (uniformLift μ).mass S := by
  classical
  rw [FiniteProbability.mass, FiniteProbability.mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  by_cases hS : z ∈ S
  · simp only [hS, ↓reduceIte, distort_weight, uniformLift]
    exact distortWeight_le_uniform_div μ B hδ0 hδhalf z
  · simp [hS]

/-- On an event contained in the newly covered set, distortion can only
decrease mass. -/
lemma distort_covered_le [Nonempty Y] (μ : FiniteProbability X)
    (B S : Set (X × Y)) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hSB : S ⊆ B) :
    (distort μ B δ hδ0 hδhalf).mass S ≤ (uniformLift μ).mass S := by
  classical
  rw [FiniteProbability.mass, FiniteProbability.mass]
  apply Finset.sum_le_sum
  intro z hz
  by_cases hS : z ∈ S
  · simp only [hS, ↓reduceIte, distort_weight, uniformLift]
    exact distortWeight_covered_le μ B hδ0 hδhalf (hSB hS)
  · simp [hS]

/-- The fraction of old fibre mass which remains on its covered part after
distortion. -/
def stageRemovedFraction (δ α : ℝ) : ℝ :=
  if α ≤ δ then 0 else (α - δ) / (1 - δ)

lemma distort_covered_fiber_sum [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (x : X) :
    (∑ y : Y, if (x, y) ∈ B then distortWeight μ B δ (x, y) else 0) =
      μ.weight x * stageRemovedFraction δ (fiberFraction B x) := by
  classical
  let α := fiberFraction B x
  have hcount := fiberCount_le B x
  have hδden : 1 - δ ≠ 0 := by linarith
  by_cases hzero : α = 0
  · have hnone := (fiberFraction_eq_zero_iff B x).mp hzero
    simp [hnone, stageRemovedFraction, α, hzero, hδ0]
  by_cases hsmall : α ≤ δ
  · have hsmall' : fiberFraction B x ≤ δ := by simpa [α] using hsmall
    have hzero' : fiberFraction B x ≠ 0 := by simpa [α] using hzero
    rw [stageRemovedFraction, if_pos hsmall']
    simp only [mul_zero]
    apply Finset.sum_eq_zero
    intro y hy
    by_cases hB : (x, y) ∈ B <;>
      simp [distortWeight, hzero', hsmall', hB]
  · have hαpos : 0 < α := lt_of_le_of_ne (fiberFraction_nonneg B x) (Ne.symm hzero)
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have hzero' : fiberFraction B x ≠ 0 := by simpa [α] using hzero
    have hn : (Fintype.card Y : ℝ) ≠ 0 := by positivity
    have hcne : (fiberCount B x : ℝ) ≠ 0 := by
      intro hc
      apply hzero'
      simp [fiberFraction, hc]
    have hlarge' : ¬fiberFraction B x ≤ δ := by simpa [α] using hsmall
    calc
      (∑ y : Y, if (x, y) ∈ B then distortWeight μ B δ (x, y) else 0) =
          ∑ y : Y, if (x, y) ∈ B then
            ((fiberFraction B x - δ) / (fiberFraction B x * (1 - δ))) *
              (μ.weight x / Fintype.card Y) else 0 := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hB : (x, y) ∈ B <;>
              simp [distortWeight, hzero', hlarge', hB, uniformLiftWeight]
      _ = μ.weight x * stageRemovedFraction δ (fiberFraction B x) := by
        rw [sum_fiber_piecewise]
        rw [Nat.cast_sub hcount]
        simp only [stageRemovedFraction, hlarge', ↓reduceIte]
        rw [fiberFraction]
        field_simp [hn, hcne, hδden]
        ring

/-- Exact stage cost as an expectation over old fibres. -/
lemma distort_stage_mass_eq_expectation [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    (distort μ B δ hδ0 hδhalf).mass B =
      μ.expectation (fun x => stageRemovedFraction δ (fiberFraction B x)) := by
  classical
  rw [FiniteProbability.mass, FiniteProbability.expectation, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  simpa [distort_weight] using distort_covered_fiber_sum μ B hδ0 hδhalf x

/-- First moment of the fibre density at a stage. -/
def firstMoment (μ : FiniteProbability X) (B : Set (X × Y)) : ℝ :=
  μ.expectation (fiberFraction B)

/-- Second moment of the fibre density at a stage. -/
def secondMoment (μ : FiniteProbability X) (B : Set (X × Y)) : ℝ :=
  μ.expectation (fun x => (fiberFraction B x) ^ 2)

/-- The elementary quadratic inequality behind the second-moment stage-cost
bound. -/
lemma max_sub_le_sq_div {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) :
    max (u - v) 0 ≤ u ^ 2 / (4 * v) := by
  rw [le_div_iff₀ (mul_pos (by norm_num) hv)]
  by_cases huv : u ≤ v
  · rw [max_eq_right (by linarith)]
    nlinarith [sq_nonneg u]
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (u - 2 * v)]

lemma stageRemovedFraction_le_sq {δ α : ℝ} (hα : 0 ≤ α)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    stageRemovedFraction δ α ≤ α ^ 2 / (4 * δ * (1 - δ)) := by
  have hden : 0 < 1 - δ := by linarith
  by_cases hsmall : α ≤ δ
  · rw [stageRemovedFraction, if_pos hsmall]
    positivity
  · rw [stageRemovedFraction, if_neg hsmall]
    have hmax : max (α - δ) 0 = α - δ := max_eq_left (by linarith)
    calc
      (α - δ) / (1 - δ) = max (α - δ) 0 / (1 - δ) := by rw [hmax]
      _ ≤ (α ^ 2 / (4 * δ)) / (1 - δ) :=
        div_le_div_of_nonneg_right (max_sub_le_sq_div hα hδ) hden.le
      _ = α ^ 2 / (4 * δ * (1 - δ)) := by
        field_simp

/-- First-moment form of the stage-cost estimate. -/
lemma stage_cost_first_le [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    (distort μ B δ hδ0 hδhalf).mass B ≤ firstMoment μ B := by
  calc
    (distort μ B δ hδ0 hδhalf).mass B ≤ (uniformLift μ).mass B :=
      distort_covered_le μ B B δ hδ0 hδhalf (fun _ h => h)
    _ = firstMoment μ B := by
      rw [uniformLift_mass_eq_expectation]
      rfl

/-- Second-moment form of the stage-cost estimate. -/
lemma stage_cost_second_le [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (distort μ B δ hδ.le hδhalf).mass B ≤
      secondMoment μ B / (4 * δ * (1 - δ)) := by
  rw [distort_stage_mass_eq_expectation]
  calc
    μ.expectation (fun x => stageRemovedFraction δ (fiberFraction B x)) ≤
        μ.expectation (fun x => (fiberFraction B x) ^ 2 / (4 * δ * (1 - δ))) :=
      μ.expectation_mono fun x =>
        stageRemovedFraction_le_sq (fiberFraction_nonneg B x) hδ hδhalf
    _ = secondMoment μ B / (4 * δ * (1 - δ)) := by
      rw [FiniteProbability.expectation, secondMoment, FiniteProbability.expectation,
        Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      ring

/-- The complete stage-cost estimate from the first and second moments. -/
lemma stage_cost_le [Nonempty Y] (μ : FiniteProbability X)
    (B : Set (X × Y)) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (distort μ B δ hδ.le hδhalf).mass B ≤
      min (firstMoment μ B) (secondMoment μ B / (4 * δ * (1 - δ))) := by
  exact le_min (stage_cost_first_le μ B δ hδ.le hδhalf)
    (stage_cost_second_le μ B hδ hδhalf)

end Fibres

end

end Erdos586

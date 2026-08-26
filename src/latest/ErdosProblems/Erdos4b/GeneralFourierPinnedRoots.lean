/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedEdges

/-!
# Exact roots of the two pinned affine families

At a rough prime the shift difference is invertible. The roots below
are precisely those of the pinned affine forms, and equality between
families is exactly the pinned cross-divisibility condition.
-/

namespace Erdos4b

noncomputable section

def pinnedIndexSlope {K : ℕ} (h : Fin K) (w p : ℕ) (i : PinnedShiftIndex h) : ZMod p :=
  (primorial w : ZMod p) * ((i.val.val : ZMod p) - h.val)

def pinnedFirstRoot {K : ℕ} (h : Fin K) (w p₀ p : ℕ) (i : PinnedShiftIndex h) : ZMod p :=
  -(p₀ : ZMod p) * (pinnedIndexSlope h w p i)⁻¹

def pinnedCompanionRoot {K : ℕ} (h : Fin K) (w m p₀ p : ℕ)
    (i : PinnedShiftIndex h) : ZMod p :=
  (1 - (m : ZMod p) * p₀) * ((m : ZMod p) * pinnedIndexSlope h w p i)⁻¹

theorem primorial_natCast_zmod_ne_zero {w p : ℕ} (hp : p.Prime) (hwp : w < p) :
    (primorial w : ZMod p) ≠ 0 := by
  intro hz
  exact (not_le_of_gt hwp) (hp.dvd_primorial_iff.mp
    ((ZMod.natCast_eq_zero_iff (primorial w) p).mp hz))

theorem pinnedIndexSlope_ne_zero
    {K w p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (i : PinnedShiftIndex h) : pinnedIndexSlope h w p i ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  apply mul_ne_zero (primorial_natCast_zmod_ne_zero hp hwp)
  intro hz
  exact i.property (fin_natCast_zmod_injective (hKw.trans hwp.le) (sub_eq_zero.mp hz))

theorem pinnedFirstRoot_iff_affine_zero
    {K w p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (i : PinnedShiftIndex h) (q : ZMod p) :
    q = pinnedFirstRoot h w p₀ p i ↔ (p₀ : ZMod p) + pinnedIndexSlope h w p i * q = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [pinnedFirstRoot, ← div_eq_mul_inv,
    eq_div_iff (pinnedIndexSlope_ne_zero h hp hKw hwp i)]
  constructor <;> intro he <;> linear_combination he

theorem pinnedCompanionRoot_iff_affine_one
    {K w m p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpm : ¬p ∣ m) (i : PinnedShiftIndex h) (q : ZMod p) :
    q = pinnedCompanionRoot h w m p₀ p i ↔
      (m : ZMod p) * ((p₀ : ZMod p) + pinnedIndexSlope h w p i * q) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := fun hz ↦ hpm ((ZMod.natCast_eq_zero_iff m p).mp hz)
  rw [pinnedCompanionRoot, ← div_eq_mul_inv,
    eq_div_iff (mul_ne_zero hm0 (pinnedIndexSlope_ne_zero h hp hKw hwp i))]
  constructor <;> intro he <;> linear_combination he

theorem pinnedIndexFourierEdge_iff_roots_eq
    {K w m p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpm : ¬p ∣ m) (i j : PinnedShiftIndex h) :
    (i, j) ∈ pinnedIndexFourierEdges h m p₀ p ↔
      pinnedFirstRoot h w p₀ p i = pinnedCompanionRoot h w m p₀ p j := by
  let : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := fun hz ↦ hpm ((ZMod.natCast_eq_zero_iff m p).mp hz)
  have hP0 := primorial_natCast_zmod_ne_zero hp hwp
  rw [mem_pinnedIndexFourierEdges_iff, pinnedFirstRoot, pinnedCompanionRoot,
    ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_eq_div_iff (pinnedIndexSlope_ne_zero h hp hKw hwp i)
      (mul_ne_zero hm0 (pinnedIndexSlope_ne_zero h hp hKw hwp j))]
  unfold pinnedIndexSlope
  constructor
  · intro he
    linear_combination (primorial w : ZMod p) * he
  · intro he
    apply mul_left_cancel₀ hP0
    rw [mul_zero]
    linear_combination he

theorem pinnedIndexSlope_injective
    {K w p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p) :
    Function.Injective (pinnedIndexSlope h w p) := by
  let : Fact p.Prime := ⟨hp⟩
  intro i j heq
  apply Subtype.ext
  apply fin_natCast_zmod_injective (hKw.trans hwp.le)
  exact sub_left_inj.mp (mul_left_cancel₀ (primorial_natCast_zmod_ne_zero hp hwp) heq)

theorem pinnedFirstRoot_injective
    {K w p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpp₀ : ¬p ∣ p₀) : Function.Injective (pinnedFirstRoot h w p₀ p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp₀0 : (p₀ : ZMod p) ≠ 0 := fun hz ↦ hpp₀ ((ZMod.natCast_eq_zero_iff p₀ p).mp hz)
  intro i j heq
  apply pinnedIndexSlope_injective h hp hKw hwp
  exact inv_injective (mul_left_cancel₀ (neg_ne_zero.mpr hp₀0) heq)

theorem pinnedCompanionRoot_injective
    {K w m p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpm : ¬p ∣ m) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    Function.Injective (pinnedCompanionRoot h w m p₀ p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := fun hz ↦ hpm ((ZMod.natCast_eq_zero_iff m p).mp hz)
  intro i j heq
  apply pinnedIndexSlope_injective h hp hKw hwp
  exact mul_left_cancel₀ hm0 (inv_injective (mul_left_cancel₀ hnum heq))

theorem pinnedFirstRoot_ne_zero
    {K w p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpp₀ : ¬p ∣ p₀) (i : PinnedShiftIndex h) : pinnedFirstRoot h w p₀ p i ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (fun hz ↦ hpp₀ ((ZMod.natCast_eq_zero_iff p₀ p).mp hz))
  · exact inv_ne_zero (pinnedIndexSlope_ne_zero h hp hKw hwp i)

theorem pinnedCompanionRoot_ne_zero
    {K w m p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpm : ¬p ∣ m) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0)
    (i : PinnedShiftIndex h) : pinnedCompanionRoot h w m p₀ p i ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := fun hz ↦ hpm ((ZMod.natCast_eq_zero_iff m p).mp hz)
  exact mul_ne_zero hnum (inv_ne_zero (mul_ne_zero hm0 (pinnedIndexSlope_ne_zero h hp hKw hwp i)))

end

end Erdos4b

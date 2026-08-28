import Wikipedia.HopfProblem.ToricTwists
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The number of coordinate boundary branches

Height-one monomial changes send each vanishing coordinate to a distinct
vanishing coordinate. Applying the inverse gives equality of their
numbers, including on the boundary. This defines an invariant branch
count on the glued toric space and for its twisted lattice action.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricCharts

def zeroCount (z : CoordinateSpace 3) : ℕ := Nat.card {j : Fin 3 // z j = 0}

def vanishingIndices (z : CoordinateSpace 3) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun j => z j = 0)

@[simp] theorem mem_vanishingIndices (z : CoordinateSpace 3) (j : Fin 3) :
    j ∈ vanishingIndices z ↔ z j = 0 := by
  classical
  simp [vanishingIndices]

theorem vanishingIndices_card (z : CoordinateSpace 3) :
    (vanishingIndices z).card = zeroCount z := by
  classical
  rw [zeroCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem vanishingIndices_nonempty (z : CoordinateSpace 3) :
    (vanishingIndices z).Nonempty ↔ ToricFan.Triangle.time z = 0 := by
  constructor
  · rintro ⟨j, hj⟩
    have hp : ∏ k, z k = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) ((mem_vanishingIndices z j).mp hj)
    simpa [ToricFan.Triangle.time, Fin.prod_univ_succ, mul_assoc] using hp
  · intro hz
    obtain h | h | h := (ToricFan.Triangle.central_fibre z).mp hz
    · exact ⟨0, (mem_vanishingIndices z 0).mpr h⟩
    · exact ⟨1, (mem_vanishingIndices z 1).mpr h⟩
    · exact ⟨2, (mem_vanishingIndices z 2).mpr h⟩

theorem zeroCount_pos_iff (z : CoordinateSpace 3) :
    0 < zeroCount z ↔ ToricFan.Triangle.time z = 0 := by
  rw [← vanishingIndices_card, Finset.card_pos, vanishingIndices_nonempty]

theorem zeroCount_le_three (z : CoordinateSpace 3) : zeroCount z ≤ 3 := by
  simpa only [zeroCount, Nat.card_fin] using
    Nat.card_le_card_of_injective
      (Subtype.val : {j : Fin 3 // z j = 0} → Fin 3) Subtype.val_injective

@[simp] theorem zeroCount_zero : zeroCount (0 : CoordinateSpace 3) = 3 := by
  classical
  simp [zeroCount, Nat.card_eq_fintype_card]

theorem zeroCount_eq_three (z : CoordinateSpace 3) : zeroCount z = 3 ↔ z = 0 := by
  constructor
  · intro hz
    have hc : Nat.card {j : Fin 3 // z j = 0} = Nat.card (Fin 3) := by
      simpa only [zeroCount, Nat.card_fin] using hz
    have hs := ((Nat.bijective_iff_injective_and_card
      (Subtype.val : {j : Fin 3 // z j = 0} → Fin 3)).mpr ⟨Subtype.val_injective, hc⟩).surjective
    ext i
    obtain ⟨j, rfl⟩ := hs i
    exact j.2
  · rintro rfl
    exact zeroCount_zero

theorem equal_columns_of_left_inverse {A B : Matrix (Fin 3) (Fin 3) ℤ} (hBA : B * A = 1)
    {j k : Fin 3} (hcol : ∀ i, A i j = A i k) : j = k := by
  have he : (B * A) j j = (B * A) j k := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun c => B j i * c) (hcol i))
  rw [hBA] at he
  by_contra hne
  simp [hne] at he

theorem zeroCount_le_monomial {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) (hBA : B * A = 1) {z : CoordinateSpace 3} (hz : z ∈ domain A) :
    zeroCount z ≤ zeroCount (monomial A z) := by
  have hcol (j : {j : Fin 3 // z j = 0}) :
      ∃ k : Fin 3, ∀ i, A i j = if i = k then 1 else 0 :=
    column_single_of_zero hA hz j.2
  choose f hf using hcol
  let g : {j : Fin 3 // z j = 0} → {k : Fin 3 // monomial A z k = 0} :=
    fun j => ⟨f j, monomial_zero_of_column_single j.2 (hf j)⟩
  apply Nat.card_le_card_of_injective g
  intro j k h
  have hfk : f j = f k := congrArg Subtype.val h
  apply Subtype.ext
  apply equal_columns_of_left_inverse hBA
  intro i
  rw [hf j i, hf k i, hfk]

theorem zeroCount_monomial {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) (hB : HeightOne B) (hAB : A * B = 1) (hBA : B * A = 1)
    {z : CoordinateSpace 3} (hz : z ∈ domain A) : zeroCount (monomial A z) = zeroCount z := by
  have hw := inverse_mapsTo_domain hA hBA hz
  have he : monomial B (monomial A z) = z :=
    monomial_inverse_on_overlap A B hBA ⟨hz, hw⟩
  have hle := zeroCount_le_monomial hB hAB hw
  rw [he] at hle
  exact le_antisymm hle (zeroCount_le_monomial hA hBA hz)

theorem zeroCount_mul (u z : CoordinateSpace 3) (hu : ∀ j, u j ≠ 0) :
    zeroCount (u * z) = zeroCount z := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun j => by simp only [Pi.mul_apply, mul_eq_zero, hu j, false_or])

end Wikipedia.HopfProblem.ToricCharts

namespace Wikipedia.HopfProblem.ToricFan.Triangle

open ToricCharts

theorem zeroCount_chartChange (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ (chartChange s t).source) : zeroCount (chartChange s t z) = zeroCount z := by
  apply zeroCount_monomial (transition_heightOne s t) (transition_heightOne t s)
    (by rw [transition_mul, transition_self]) (by rw [transition_mul, transition_self])
  simpa only [chartChange_source] using hz

theorem origin_mem_chartChange_source (s t : Triangle) :
    (0 : CoordinateSpace 3) ∈ (chartChange s t).source ↔ s = t := by
  constructor
  · intro hz
    rw [chartChange_source] at hz
    have hn (i j : Fin 3) : 0 ≤ transition s t i j := by
      by_contra h
      exact hz i j (lt_of_not_ge h) rfl
    have h00 := hn 0 0
    have h01 := hn 0 1
    have h02 := hn 0 2
    have h10 := hn 1 0
    have h11 := hn 1 1
    have h12 := hn 1 2
    have h20 := hn 2 0
    have h21 := hn 2 1
    have h22 := hn 2 2
    cases hs : s.upper <;> cases ht : t.upper
    all_goals
      simp [transition, dual, rays, hs, ht, Matrix.mul_apply, Fin.sum_univ_succ]
        at h00 h01 h02 h10 h11 h12 h20 h21 h22
    all_goals
      first
      | omega
      | apply Triangle.ext
        · omega
        · omega
        · simp [hs, ht]
  · rintro rfl
    rw [chartChange_self_source]
    exact Set.mem_univ _

end Wikipedia.HopfProblem.ToricFan.Triangle

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

def branchCount (x : Space) : ℕ :=
  zeroCount ((parametrization (preferredTriangle x)).symm x)

theorem branchCount_inclusion (s : Triangle) (z : CoordinateSpace 3) :
    branchCount (inclusion s z) = zeroCount z := by
  have he := parametrization_transition s (preferredTriangle (inclusion s z))
    (preferred_mem (inclusion s z))
  unfold branchCount
  rw [he.2]
  exact zeroCount_chartChange s _ he.1

theorem branchCount_le_three (x : Space) : branchCount x ≤ 3 := zeroCount_le_three _

theorem branchCount_pos_iff (x : Space) : 0 < branchCount x ↔ time x = 0 := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [branchCount_inclusion, zeroCount_pos_iff, time_inclusion]

theorem branchCount_eq_three (x : Space) :
    branchCount x = 3 ↔ ∃ s : Triangle, inclusion s 0 = x := by
  constructor
  · intro hx
    obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
    rw [branchCount_inclusion, zeroCount_eq_three] at hx
    exact ⟨s, by rw [hx]⟩
  · rintro ⟨s, rfl⟩
    rw [branchCount_inclusion, zeroCount_zero]

theorem inclusion_origin_injective (s t : Triangle) :
    inclusion s 0 = inclusion t 0 ↔ s = t := by
  constructor
  · intro he
    exact (origin_mem_chartChange_source s t).mp ((inclusion_eq_iff s t 0 0).mp he).1
  · rintro rfl
    rfl

theorem twistedTranslate_origin (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (s : Triangle) :
    twistedTranslate C v (inclusion s 0) = inclusion (s.shift (cuspVector v)) 0 := by
  simp [twistedTranslate, translate_inclusion, variableMultiplier, scale]

@[simp] theorem branchCount_translate (v : Fin 2 → ℤ) (x : Space) :
    branchCount (translate v x) = branchCount x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [translate_inclusion, branchCount_inclusion, branchCount_inclusion]

@[simp] theorem branchCount_torusAction (u : ActingTorus) (x : Space) :
    branchCount (torusAction u x) = branchCount x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [torusAction_inclusion, branchCount_inclusion, branchCount_inclusion]
  exact zeroCount_mul (factors s u) z (factors_nonzero s u)

@[simp] theorem branchCount_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : Space) : branchCount (twistedTranslate C v x) = branchCount x := by
  simp [twistedTranslate, variableMultiplier]

end Wikipedia.HopfProblem.ToricSpace

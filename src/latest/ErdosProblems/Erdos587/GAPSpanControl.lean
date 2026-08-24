import ErdosProblems.Erdos587.GAPMultiplierCover

/-! Span and translation control for progressions contained in actual subset sums. -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

def coefficientSpan (P : GeneralizedAP) : ℤ := ∑ i, (P.length i : ℤ) * |P.step i|

theorem coefficientSpan_nonneg (P : GeneralizedAP) : 0 ≤ P.coefficientSpan :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

theorem abs_sub_le_coefficientSpan (P : GeneralizedAP) {x y : ℤ}
    (hx : x ∈ P.carrier) (hy : y ∈ P.carrier) : |x - y| ≤ P.coefficientSpan := by
  obtain ⟨u, rfl⟩ := P.mem_carrier_iff.mp hx
  obtain ⟨v, rfl⟩ := P.mem_carrier_iff.mp hy
  have heq : P.eval u - P.eval v = ∑ i, ((u i : ℤ) - (v i : ℤ)) * P.step i := by
    simp only [eval, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hcoord : |(u i : ℤ) - (v i : ℤ)| ≤ (P.length i : ℤ) := by
    have hu := (u i).isLt
    have hv := (v i).isLt
    rw [abs_le]
    constructor <;> omega
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right hcoord (abs_nonneg _)

theorem le_coefficientSpan_of_zero_mem (P : GeneralizedAP)
    (hzero : (0 : ℤ) ∈ P.carrier) {x : ℤ} (hx : x ∈ P.carrier) :
    x ≤ P.coefficientSpan :=
  (le_abs_self x).trans (by simpa only [sub_zero] using P.abs_sub_le_coefficientSpan hx hzero)

def upperEndpoint (P : GeneralizedAP) : ℤ := P.positiveForm.base + P.coefficientSpan

theorem upperEndpoint_mem (P : GeneralizedAP) : P.upperEndpoint ∈ P.carrier := by
  rw [← P.carrier_positiveForm]
  apply P.positiveForm.mem_carrier_iff.mpr
  exact ⟨fun i => ⟨P.length i, Nat.lt_succ_self _⟩, rfl⟩

theorem upperEndpoint_le_subset_budget (P Q : GeneralizedAP) (W : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hWP : W ⊆ P.carrier)
    (hQW : Q.carrier ⊆ W.subsetSum) :
    Q.upperEndpoint ≤ (W.card : ℤ) * P.coefficientSpan := by
  obtain ⟨S, hSW, hsum⟩ := Finset.mem_subsetSum_iff.mp (hQW Q.upperEndpoint_mem)
  calc
    Q.upperEndpoint = ∑ x ∈ S, x := hsum.symm
    _ ≤ ∑ _x ∈ S, P.coefficientSpan := Finset.sum_le_sum
      (fun x hx => P.le_coefficientSpan_of_zero_mem hzero (hWP (hSW hx)))
    _ = (S.card : ℤ) * P.coefficientSpan := by simp
    _ ≤ (W.card : ℤ) * P.coefficientSpan := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card hSW) P.coefficientSpan_nonneg

theorem coefficientSpan_lower_of_multipliers
    (P Q : GeneralizedAP) (hrank : Q.rank = P.rank)
    (a : Fin P.rank → ℤ) (hane : ∀ i, a i ≠ 0) (H F : ℕ)
    (hstep : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      Q.step i = a j * P.step j)
    (hside : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      H * P.length j ≤ F * Q.length i) :
    (H : ℤ) * P.coefficientSpan ≤ (F : ℤ) * Q.coefficientSpan := by
  let e : Fin P.rank ≃ Fin Q.rank := finCongr hrank.symm
  have hterm (j : Fin P.rank) : (H : ℤ) * ((P.length j : ℤ) * |P.step j|) ≤
      (F : ℤ) * ((Q.length (e j) : ℤ) * |Q.step (e j)|) := by
    have hlen : (H : ℤ) * P.length j ≤ (F : ℤ) * Q.length (e j) := by
      exact_mod_cast hside (e j) j rfl
    have hsteps : |P.step j| ≤ |Q.step (e j)| := by
      rw [hstep (e j) j rfl, abs_mul]
      exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs (hane j))
    calc
      (H : ℤ) * ((P.length j : ℤ) * |P.step j|) =
          ((H : ℤ) * P.length j) * |P.step j| := by ring
      _ ≤ ((F : ℤ) * Q.length (e j)) * |Q.step (e j)| :=
        mul_le_mul hlen hsteps (abs_nonneg _) (by positivity)
      _ = (F : ℤ) * ((Q.length (e j) : ℤ) * |Q.step (e j)|) := by ring
  simp only [coefficientSpan, Finset.mul_sum]
  calc
    _ ≤ ∑ j : Fin P.rank, (F : ℤ) * ((Q.length (e j) : ℤ) * |Q.step (e j)|) :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = ∑ i : Fin Q.rank, (F : ℤ) * ((Q.length i : ℤ) * |Q.step i|) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Linear selection cost and a fixed dilation loss give the fixed
base-to-span ratio required by the square-location theorem. -/
theorem upperEndpoint_le_span_multiple
    (P Q : GeneralizedAP) (W : Finset ℤ) (H C F : ℕ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hWP : W ⊆ P.carrier)
    (hQW : Q.carrier ⊆ W.subsetSum) (hcard : W.card ≤ C * H)
    (hspan : (H : ℤ) * P.coefficientSpan ≤ (F : ℤ) * Q.coefficientSpan) :
    Q.upperEndpoint ≤ ((C * F : ℕ) : ℤ) * Q.coefficientSpan := by
  calc
    Q.upperEndpoint ≤ (W.card : ℤ) * P.coefficientSpan :=
      P.upperEndpoint_le_subset_budget Q W hzero hWP hQW
    _ ≤ ((C * H : ℕ) : ℤ) * P.coefficientSpan := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard) P.coefficientSpan_nonneg
    _ = (C : ℤ) * ((H : ℤ) * P.coefficientSpan) := by push_cast; ring
    _ ≤ (C : ℤ) * ((F : ℤ) * Q.coefficientSpan) :=
      mul_le_mul_of_nonneg_left hspan (Nat.cast_nonneg C)
    _ = ((C * F : ℕ) : ℤ) * Q.coefficientSpan := by push_cast; ring

end Erdos587.GeneralizedAP

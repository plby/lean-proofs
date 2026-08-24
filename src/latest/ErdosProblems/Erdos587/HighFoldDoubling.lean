import ErdosProblems.Erdos587.DenseHighFold
import ErdosProblems.Erdos587.GAPMultiplierCover

/-!
Propagate a constant-density selected-scale model to uniform doubling at
every larger high-fold scale. A standardized progression in a bounded
further sumset supplies the comparison from below; the translate cover is
valid even after its dilations lose properness.
-/

open scoped Pointwise
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem le_twice_quotient_mul {H k : ℕ} (hk : 0 < k) (hH : k ≤ H) :
    H ≤ 2 * (H / k) * k := by
  have hq : 0 < H / k := Nat.div_pos hH hk
  have hlt := Nat.lt_mul_div_succ H hk
  nlinarith

theorem standardized_dilate_side_bound {H h q F L S : ℕ}
    (hh : 0 < h) (hq : 0 < q) (hF : 0 < F) (hH : q * h ≤ H)
    (hside : h * L ≤ 2 * F * S) :
    (2 * H) * L < (8 * q * F) * ((H / (q * h)) * S + 1) := by
  have hH' := le_twice_quotient_mul (Nat.mul_pos hq hh) hH
  have hle : (2 * H) * L ≤ (8 * q * F) * ((H / (q * h)) * S) := by
    calc
      (2 * H) * L ≤ (2 * (2 * (H / (q * h)) * (q * h))) * L :=
        Nat.mul_le_mul_right L (Nat.mul_le_mul_left 2 hH')
      _ = (4 * (H / (q * h)) * q) * (h * L) := by ring
      _ ≤ (4 * (H / (q * h)) * q) * (2 * F * S) :=
        Nat.mul_le_mul_left _ hside
      _ = (8 * q * F) * ((H / (q * h)) * S) := by ring
  have hpos : 0 < 8 * q * F := by positivity
  nlinarith

/-- A single standardized high-fold progression gives a doubling bound
which is independent of the larger scale `H`. -/
theorem highFold_doubling_of_standardized
    (A : Finset ℤ) (P Q : GeneralizedAP) (hzero : (0 : ℤ) ∈ A)
    (hAP : A ⊆ P.carrier) (hrank : Q.rank = P.rank) (hQ : Q.Proper)
    (hpos : ∀ i, 0 < P.length i) (h q F B : ℕ)
    (hh : 0 < h) (hq : 0 < q) (hF : 0 < F) (hscale : F ≤ h)
    (hsub : Q.carrier ⊆ (q * h) • A)
    (hstep : Q.StepMultipliersBoundedByConstant P B)
    (hside : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      Q.length i = h * P.length j / F)
    (H : ℕ) (hH : q * h ≤ H) :
    (H • A + H • A).card ≤ ((8 * q * F) * B) ^ P.rank * (H • A).card := by
  let n := H / (q * h)
  have hQpos : ∀ i, 0 < Q.length i := by
    intro i
    rw [hside i (Fin.cast hrank i) rfl]
    exact standardized_side_pos (hpos _) hF hscale
  have hratio : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      (2 * H) * P.length j < (8 * q * F) * (n * Q.length i + 1) := by
    intro i j hij
    apply standardized_dilate_side_bound hh hq hF hH
    rw [hside i j hij]
    exact standardized_side_lower (hpos j) hF hscale
  have hcover := P.card_dilate_le_of_bounded_multipliers Q hrank hQ hQpos B
    (8 * q * F) (2 * H) n hstep hratio
  have hsub' : (Q.dilate n).carrier ⊆ H • A := by
    rw [← Q.nsmul_carrier]
    exact (Finset.nsmul_subset_nsmul_left hsub).trans (by
      rw [← mul_nsmul]
      apply Finset.nsmul_subset_nsmul_right hzero
      simpa only [n, Nat.mul_comm] using Nat.div_mul_le_self H (q * h))
  calc
    (H • A + H • A).card = ((2 * H) • A).card := by rw [two_mul, add_nsmul]
    _ ≤ (P.dilate (2 * H)).carrier.card :=
      Finset.card_le_card (highFold_subset_dilate_of_subset A P hAP _)
    _ ≤ ((8 * q * F) * B) ^ P.rank * (Q.dilate n).carrier.card := hcover
    _ ≤ ((8 * q * F) * B) ^ P.rank * (H • A).card :=
      Nat.mul_le_mul_left _ (Finset.card_le_card hsub')

/-- The doubling constant depends only on reciprocal density and rank, not
on either the original scale or the later prescribed scale. -/
def highFoldDoublingConstant (D d : ℕ) : ℕ :=
  let q := nvDenseCount D d
  let F := nvDenseProperFactor D d * (q + 1) ^ d
  ((8 * q * F) * (2 * q * F)) ^ d

theorem highFoldDoublingConstant_pos {D d : ℕ} (hD : 0 < D) (hd : 0 < d) :
    0 < highFoldDoublingConstant D d := by
  have hq : 0 < nvDenseCount D d := by rw [nvDenseCount_eq_mul]; positivity
  have hF : 0 < nvDenseProperFactor D d := nvDenseProperFactor_pos hD
  unfold highFoldDoublingConstant
  positivity

theorem highFold_doubling_of_dense_model
    (A : Finset ℤ) (P : GeneralizedAP) (hzero : (0 : ℤ) ∈ A)
    (hAP : A ⊆ P.carrier) (hpos : ∀ i, 0 < P.length i) (hrank : 0 < P.rank)
    (h D : ℕ) (hh : 0 < h) (hD : 0 < D) (hproper : P.TProper h)
    (hdense : (P.dilate h).boxCard ≤ D * (h • A).card)
    (hscale : nvDenseProperFactor D P.rank * (nvDenseCount D P.rank + 1) ^ P.rank ≤ h)
    (H : ℕ) (hH : nvDenseCount D P.rank * h ≤ H) :
    (H • A + H • A).card ≤ highFoldDoublingConstant D P.rank * (H • A).card := by
  let q := nvDenseCount D P.rank
  let F := nvDenseProperFactor D P.rank * (q + 1) ^ P.rank
  have hq : 0 < q := by dsimp [q]; rw [nvDenseCount_eq_mul]; positivity
  have hF : 0 < F := Nat.mul_pos (nvDenseProperFactor_pos hD) (by positivity)
  obtain ⟨Q, hQrank, hQproper, hQsub, hQstep, hQside⟩ :=
    exists_standardized_GAP_in_highFold_sumset A P h D hD hAP hproper hdense
  exact highFold_doubling_of_standardized A P Q hzero hAP hQrank hQproper hpos h q F
    (2 * q * F) hh hq hF hscale hQsub hQstep hQside H hH

/-- Upgrade a selected-scale model to a model at any sufficiently large
prescribed scale. No small-doubling hypothesis at the new scale is assumed. -/
theorem exists_prescribed_scale_highFold_model
    (A : Finset ℤ) (P : GeneralizedAP) (hzero : (0 : ℤ) ∈ A)
    (hAP : A ⊆ P.carrier) (hpos : ∀ i, 0 < P.length i) (hrank : 0 < P.rank)
    (h D : ℕ) (hh : 0 < h) (hD : 0 < D) (hproper : P.TProper h)
    (hdense : (P.dilate h).boxCard ≤ D * (h • A).card)
    (hscale : nvDenseProperFactor D P.rank * (nvDenseCount D P.rank + 1) ^ P.rank ≤ h)
    (H : ℕ) (hH : nvDenseCount D P.rank * h ≤ H) :
    ∃ Q : GeneralizedAP, Q.rank ≤ freimanRank (highFoldDoublingConstant D P.rank) ∧
      (∀ i, 0 < Q.length i) ∧ Q.TProper H ∧ (0 : ℤ) ∈ Q.carrier ∧
      A ⊆ Q.carrier ∧ (Q.dilate H).boxCard ≤
        freimanTSizeFactor (highFoldDoublingConstant D P.rank) 2 * (H • A).card := by
  have hq : 0 < nvDenseCount D P.rank := by rw [nvDenseCount_eq_mul]; positivity
  exact exists_noncollapsed_highFold_model_of_small_doubling A hzero H
    (highFoldDoublingConstant D P.rank) ((Nat.mul_pos hq hh).trans_le hH)
    (highFoldDoublingConstant_pos hD hrank)
    (highFold_doubling_of_dense_model A P hzero hAP hpos hrank h D hh hD hproper
      hdense hscale H hH)

end Erdos587.CFP

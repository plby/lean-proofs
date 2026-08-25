import ErdosProblems.Erdos964.AffineSemiprimeDecomposition
import ErdosProblems.Erdos964.PrimeSliceCounts

/-!
# The affine second-count main term and distribution errors

This is the exact-endpoint version of the initial arithmetic estimate in
Section 5 of GGPY. Its error consists of one semiprime discrepancy and
the prime discrepancies on the slices dividing the squarefree modulus.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

noncomputable def affineSemiprimeCountMain (A B : Fin 3 → ℕ) (j : Fin 3)
    (P Q : Finset ℕ) (x y u : ℕ) : ℝ :=
  (affineCoprimeProductRoots A B j u).card *
    ((∑ p ∈ P.filter (fun p => ¬ p ∣ u), ((primeSlice Q p x y).card : ℝ)) /
      (A j * u).totient) +
  ∑ p ∈ P.filter (fun p => p ∣ u),
    ((affineCoprimeProductRoots A B j (u / p)).card : ℝ) *
      ((primeSlice Q p x y).card / (A j * (u / p)).totient)

theorem prime_gt_coprime_of_le (r q L : ℕ) (hr : r.Prime)
    (hq : 0 < q) (hqL : q ≤ L) (hLr : L < r) : r.Coprime q := by
  apply hr.coprime_iff_not_dvd.mpr
  intro hrq
  exact (not_le_of_gt hLr) ((Nat.le_of_dvd hq hrq).trans hqL)

theorem prime_filter_not_dvd_mul (P : Finset ℕ) (a u : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPa : ∀ p ∈ P, p.Coprime a) :
    P.filter (fun p => ¬ p ∣ a * u) = P.filter (fun p => ¬ p ∣ u) := by
  apply Finset.filter_congr
  intro p hp
  rw [(hP p hp).dvd_mul]
  have hpa := (hP p hp).coprime_iff_not_dvd.mp (hPa p hp)
  simp only [hpa, false_or]

theorem affineSemiprimeCount_error_le (A B : Fin 3 → ℕ) (j : Fin 3)
    (N u L x y : ℕ) (hA : 0 < A j) (hBA : (B j).Coprime (A j))
    (hu : Squarefree u) (hmod : A j * u ≤ L)
    (hx : x ∈ Finset.Icc 1 (L ^ 2)) (hy : y ∈ Finset.Icc 1 (L ^ 2))
    (hxy : x ≤ y) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ L) (hPa : ∀ p ∈ P, p.Coprime (A j))
    (hlo : ∀ p ∈ P, p * L ≤ x)
    (hS : semiprimeScaleInterval P L x y ⊆
      Finset.Ico (A j * N + B j) (A j * (2 * N) + B j)) :
    let Q := (Finset.Ioc L (L ^ 2)).filter Nat.Prime
    |(affineDivisorValueCount A B j N u (semiprimeScaleInterval P L x y) : ℝ) -
      affineSemiprimeCountMain A B j P Q x y u| ≤
      (affineCoprimeProductRoots A B j u).card *
        (2 * semiprimeScaleCoprimeMaxDiscrepancy P L (A j * u)) +
      ∑ p ∈ P.filter (fun p => p ∣ u),
        (affineCoprimeProductRoots A B j (u / p)).card *
          (maxProgressionDiscrepancy (y / p) (A j * (u / p)) +
            maxProgressionDiscrepancy (x / p) (A j * (u / p))) := by
  let Q := (Finset.Ioc L (L ^ 2)).filter Nat.Prime
  have hu0 : 0 < u := Nat.pos_of_ne_zero hu.ne_zero
  have hau0 : 0 < A j * u := Nat.mul_pos hA hu0
  have hQ (r : ℕ) (hr : r ∈ Q) : r.Prime := (Finset.mem_filter.mp hr).2
  have hQr (r : ℕ) (hr : r ∈ Q) : L < r :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
  have hQcop (r : ℕ) (hr : r ∈ Q) : r.Coprime (A j * u) :=
    prime_gt_coprime_of_le r (A j * u) L (hQ r hr) hau0 hmod (hQr r hr)
  have hQnot (r : ℕ) (hr : r ∈ Q) : ¬ r ∣ A j * u :=
    (hQ r hr).coprime_iff_not_dvd.mp (hQcop r hr)
  have hQu (r : ℕ) (hr : r ∈ Q) : ¬ r ∣ u :=
    fun h => hQnot r hr (h.trans (dvd_mul_left u (A j)))
  have hsep (p : ℕ) (hp : p ∈ P) (r : ℕ) (hr : r ∈ Q) : p < r :=
    (hP p hp).2.trans_lt (hQr r hr)
  have hinterval : semiprimeScaleInterval P L x y = primeProductInterval P Q x y :=
    semiprimeScaleInterval_eq_primeProductInterval P L x y hxy
  have hcenter : (finiteCoprimeCount (semiprimeScaleInterval P L x y) (A j * u) : ℝ) =
      ∑ p ∈ P.filter (fun p => ¬ p ∣ u), ((primeSlice Q p x y).card : ℝ) := by
    rw [hinterval, finiteCoprimeCount_primeProductInterval P Q x y (A j * u)
      (fun p hp => (hP p hp).1) hQ hsep hQnot,
      prime_filter_not_dvd_mul P (A j) u (fun p hp => (hP p hp).1) hPa, Nat.cast_sum]
  have hcop := affineCoprimeValueCount_semiprime_error A B j N u hA hu0 hBA
    P L x y hx hy hxy hS
  rw [hcenter] at hcop
  have hslices (p : ℕ) (hp : p ∈ P.filter (fun p => p ∣ u)) :
      |(affineCoprimeValueCount A B j N (u / p)
          ((primeSlice Q p x y).image (fun r => p * r)) : ℝ) -
        (affineCoprimeProductRoots A B j (u / p)).card *
          ((primeSlice Q p x y).card / (A j * (u / p)).totient)| ≤
        (affineCoprimeProductRoots A B j (u / p)).card *
          (maxProgressionDiscrepancy (y / p) (A j * (u / p)) +
            maxProgressionDiscrepancy (x / p) (A j * (u / p))) := by
    have hp' := Finset.mem_filter.mp hp
    have hpprime := (hP p hp'.1).1
    have hquot : 0 < u / p := Nat.div_pos (Nat.le_of_dvd hu0 hp'.2) hpprime.pos
    have hpcop : p.Coprime (u / p) := by
      apply Nat.coprime_of_squarefree_mul
      rwa [Nat.mul_div_cancel' hp'.2]
    have hmodquot : A j * (u / p) ≤ L :=
      (Nat.mul_le_mul_left (A j) (Nat.div_le_self u p)).trans hmod
    have hsliceS : (primeSlice Q p x y).image (fun r => p * r) ⊆
        Finset.Ico (A j * N + B j) (A j * (2 * N) + B j) := by
      intro m hm
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hm
      have hr' := Finset.mem_filter.mp hr
      apply hS
      rw [hinterval, mem_primeProductInterval]
      exact ⟨p, hp'.1, r, hr'.1, hr'.2.1, hr'.2.2, rfl⟩
    have hcount := primeSlice_coprime_count_eq_card L (L ^ 2) p x y
      (A j * (u / p)) (Nat.mul_pos hA hquot) hmodquot
    have h := affineCoprimeValueCount_mul_image_error A B j N (u / p) p hA hquot hBA
      hpprime.pos ((hPa p hp'.1).mul_right hpcop) (primeSlice Q p x y) hsliceS
      (maxProgressionDiscrepancy (y / p) (A j * (u / p)) +
        maxProgressionDiscrepancy (x / p) (A j * (u / p)))
    rw [hcount] at h
    apply h
    intro a ha
    apply primeSlice_discrepancy_le L (L ^ 2) p x y (A j * (u / p)) a
      hpprime.pos hxy (hlo p hp'.1) _ (Nat.mul_pos hA hquot) ha
    exact (Finset.mem_Icc.mp hy).2.trans (Nat.le_mul_of_pos_left _ hpprime.pos)
  have hsplit := affineDivisorValueCount_semiprime_split A B j N u x y hu P Q
    (fun p hp => (hP p hp).1) hQ hsep hQu
  rw [← hinterval] at hsplit
  dsimp only [affineSemiprimeCountMain]
  rw [hsplit, Nat.cast_add, Nat.cast_sum]
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hslices)
  rw [Finset.sum_sub_distrib] at hsum
  have hbound := (abs_add_le _ _).trans (add_le_add hcop hsum)
  convert hbound using 1 <;> (congr 1 <;> ring)

end Erdos964

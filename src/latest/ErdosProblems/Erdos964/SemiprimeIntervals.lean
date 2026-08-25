import ErdosProblems.Erdos964.SemiprimeCoprimeCentering

/-!
# Actual semiprime interval counts

Prefix differences are the genuine semiprime sets in `(x,y]`. Their
reduced-residue errors are controlled by the coprime-centered endpoint
maximum, including fixed affine endpoint translations.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem cast_card_filter_sdiff (S T : Finset ℕ) (hST : S ⊆ T)
    (pred : ℕ → Prop) [DecidablePred pred] :
    (((T \ S).filter pred).card : ℝ) = ((T.filter pred).card : ℝ) - (S.filter pred).card := by
  have hfilter : (T \ S).filter pred = T.filter pred \ S.filter pred := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hsub := Finset.filter_subset_filter pred hST
  rw [hfilter, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]

theorem finiteResidueCount_sdiff_cast (S T : Finset ℕ) (hST : S ⊆ T) (q a : ℕ) :
    (finiteResidueCount (T \ S) q a : ℝ) =
      (finiteResidueCount T q a : ℝ) - finiteResidueCount S q a :=
  cast_card_filter_sdiff S T hST (fun n => n ≡ a [MOD q])

theorem finiteCoprimeCount_sdiff_cast (S T : Finset ℕ) (hST : S ⊆ T) (q : ℕ) :
    (finiteCoprimeCount (T \ S) q : ℝ) =
      (finiteCoprimeCount T q : ℝ) - finiteCoprimeCount S q :=
  cast_card_filter_sdiff S T hST (fun n => n.Coprime q)

theorem semiprimesAtScale_mono (P : Finset ℕ) (L x y : ℕ) (hxy : x ≤ y) :
    semiprimesAtScale P L x ⊆ semiprimesAtScale P L y := by
  intro n hn
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
  exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.trans hxy⟩, rfl⟩

theorem semiprimesAtScale_filter_le (P : Finset ℕ) (L x y : ℕ) (hxy : x ≤ y) :
    (semiprimesAtScale P L y).filter (fun n => n ≤ x) = semiprimesAtScale P L x := by
  ext n
  constructor
  · intro hn
    obtain ⟨hny, hnx⟩ := Finset.mem_filter.mp hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hny
    exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz).1, hnx⟩, rfl⟩
  · intro hn
    have hny := semiprimesAtScale_mono P L x y hxy hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr ⟨hny, (Finset.mem_filter.mp hz).2⟩

def semiprimeScaleInterval (P : Finset ℕ) (L x y : ℕ) : Finset ℕ :=
  semiprimesAtScale P L y \ semiprimesAtScale P L x

theorem semiprimeScaleInterval_eq_filter (P : Finset ℕ) (L x y : ℕ) (hxy : x ≤ y) :
    semiprimeScaleInterval P L x y = (semiprimesAtScale P L y).filter (fun n => x < n) := by
  unfold semiprimeScaleInterval
  rw [← semiprimesAtScale_filter_le P L x y hxy]
  ext n
  simp only [Finset.mem_sdiff, Finset.mem_filter, not_and, Nat.not_le]
  tauto

theorem semiprimeScaleInterval_discrepancy_le (P : Finset ℕ) (L x y q a : ℕ)
    (hx : x ∈ Finset.Icc 1 (L ^ 2)) (hy : y ∈ Finset.Icc 1 (L ^ 2)) (hxy : x ≤ y)
    (hq : 0 < q) (ha : a.Coprime q) :
    |(finiteResidueCount (semiprimeScaleInterval P L x y) q a : ℝ) -
      (finiteCoprimeCount (semiprimeScaleInterval P L x y) q : ℝ) / q.totient| ≤
        2 * semiprimeScaleCoprimeMaxDiscrepancy P L q := by
  rw [semiprimeScaleInterval,
    finiteResidueCount_sdiff_cast _ _ (semiprimesAtScale_mono P L x y hxy),
    finiteCoprimeCount_sdiff_cast _ _ (semiprimesAtScale_mono P L x y hxy)]
  exact semiprimeScale_coprime_interval_discrepancy_le P L q x y a hx hy hq ha

end Erdos964

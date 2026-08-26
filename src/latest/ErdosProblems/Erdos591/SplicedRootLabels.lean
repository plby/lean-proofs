import ErdosProblems.Erdos591.OrderedLabelRanks

/-!
# Two shared U root indices with all later upper bodies beyond the lower root

The first upper body is the lower critical body of rank j. The next
lower body has prescribed upper rank r. Earlier upper indices lie in
the gap between those two lower indices; later upper indices exceed
the largest lower index. This realizes both r=k+1 (last) and r=k
(nonlast with k≥2) in the strict triangle construction.
-/

namespace Erdos591.Positive.Game

structure SplicedRootLabels (H : Set ℕ) (B e d j r : ℕ) where
  lower : Finset ℕ
  upper : Finset ℕ
  first : ℕ
  anchor : ℕ
  last : ℕ
  marker : ℕ
  lower_card : lower.card = e
  upper_card : upper.card = d
  first_lower : first ∈ lower
  first_upper : first ∈ upper
  anchor_lower : anchor ∈ lower
  anchor_upper : anchor ∈ upper
  last_lower : last ∈ lower
  first_lt_anchor : first < anchor
  anchor_le_last : anchor ≤ last
  first_rank : (lower.filter (fun x => x ≤ first)).card = j
  anchor_lower_rank : (lower.filter (fun x => x ≤ anchor)).card = j + 1
  anchor_upper_rank : (upper.filter (fun x => x ≤ anchor)).card = r
  lower_sup : lower.sup id = last
  lower_gap : ∀ x ∈ lower, x ≤ first ∨ anchor ≤ x
  upper_first : ∀ x ∈ upper, first ≤ x
  upper_gap : ∀ x ∈ upper, x ≤ anchor ∨ last < x
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

namespace SplicedRootLabels

private def lowerIndex (j r i : ℕ) := if i < j then i else i + (r - 2)

private def upperIndex (e j r i : ℕ) :=
  if i = 0 then j - 1 else if i < r then j + i - 1 else e + i - 2

private theorem lowerIndex_strictMono (j r : ℕ) : StrictMono (lowerIndex j r) := by
  apply strictMono_nat_of_lt_succ
  intro i
  simp only [lowerIndex]
  split_ifs <;> omega

private theorem upperIndex_strictMono {e j r : ℕ} (hj : 0 < j) (hje : j < e) (hr : 2 ≤ r) :
    StrictMono (upperIndex e j r) := by
  apply strictMono_nat_of_lt_succ
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [upperIndex, ↓reduceIte, show 0 + 1 ≠ 0 by omega, show 0 + 1 < r by omega]
    omega
  · have hnext : i + 1 ≠ 0 := by omega
    simp only [upperIndex, hi, hnext, ↓reduceIte]
    split_ifs <;> omega

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B e d j r : ℕ)
    (hj : 0 < j) (hje : j < e) (hr : 2 ≤ r) (hrd : r < d) :
    Nonempty (SplicedRootLabels H B e d j r) := by
  classical
  obtain ⟨f, hf, hfH, hfB, _⟩ := FastSequence.exists_above_finite_bounds hH ∅ (fun _ => B)
  let lo := fun i => f (lowerIndex j r i)
  let up := fun i => f (upperIndex e j r i)
  have hlo : StrictMono lo := hf.comp (lowerIndex_strictMono j r)
  have hup : StrictMono up := hf.comp (upperIndex_strictMono hj hje hr)
  let lower := (Finset.range e).image lo
  let upper := (Finset.range d).image up
  have hfirst : lo (j - 1) = up 0 := by
    simp [lo, up, lowerIndex, upperIndex, show j - 1 < j by omega]
  have hanchor : lo j = up (r - 1) := by
    simp only [lo, up, lowerIndex, lt_self_iff_false, ↓reduceIte, upperIndex,
      show r - 1 ≠ 0 by omega, show r - 1 < r by omega]
    congr 1
    omega
  have hmemLo {i : ℕ} (hi : i < e) : lo i ∈ lower :=
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have hmemUp {i : ℕ} (hi : i < d) : up i ∈ upper :=
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have hlastIndex : lowerIndex j r (e - 1) = e + r - 3 := by
    simp only [lowerIndex, show ¬ e - 1 < j by omega, ↓reduceIte]
    omega
  have hsmallLo {i : ℕ} (hi : i < e) : lowerIndex j r i < e + d - 2 := by
    simp only [lowerIndex]
    split_ifs <;> omega
  have hsmallUp {i : ℕ} (hi : i < d) : upperIndex e j r i < e + d - 2 := by
    simp only [upperIndex]
    split_ifs <;> omega
  refine ⟨⟨lower, upper, lo (j - 1), lo j, lo (e - 1), f (e + d - 2), ?_, ?_,
    hmemLo (by omega), hfirst ▸ hmemUp (by omega), hmemLo hje,
    hanchor ▸ hmemUp (by omega), hmemLo (by omega), hlo (by omega),
    hlo.monotone (by omega), ?_, ?_, ?_, image_range_sup lo hlo (by omega), ?_, ?_, ?_,
    ?_, ?_, ⟨hfH _, hfB _⟩⟩⟩
  · simp [lower, Finset.card_image_of_injective _ hlo.injective]
  · simp [upper, Finset.card_image_of_injective _ hup.injective]
  · simpa only [Nat.sub_add_cancel hj] using image_range_rank lo hlo (show j - 1 < e by omega)
  · exact image_range_rank lo hlo hje
  · rw [hanchor]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using
      image_range_rank up hup (show r - 1 < d by omega)
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    by_cases hij : i < j
    · exact Or.inl (hlo.monotone (by omega))
    · exact Or.inr (hlo.monotone (by omega))
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    rw [hfirst]
    exact hup.monotone (Nat.zero_le _)
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    by_cases hir : i < r
    · exact Or.inl (by rw [hanchor]; exact hup.monotone (by omega))
    · apply Or.inr
      apply hf
      change lowerIndex j r (e - 1) < upperIndex e j r i
      rw [hlastIndex]
      simp only [upperIndex, show i ≠ 0 by omega, hir, ↓reduceIte]
      omega
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hfH _, hfB _, hf (hsmallLo (Finset.mem_range.mp hi))⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hfH _, hfB _, hf (hsmallUp (Finset.mem_range.mp hi))⟩

#print axioms exists_of_infinite

end SplicedRootLabels

end Erdos591.Positive.Game

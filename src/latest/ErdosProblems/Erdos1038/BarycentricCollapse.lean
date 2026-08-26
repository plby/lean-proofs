import ErdosProblems.Erdos1038.Definitions

/-!
# The local Jensen engine for barycentric collapse

This file treats a finite nonempty multiset of real roots as a local cluster.
Its barycenter is the arithmetic mean, with multiplicities retained.  For a
point outside an open interval containing the cluster, concavity of `log`
shows that replacing the cluster by its barycenter weakly raises its total
logarithmic-potential contribution.
-/

open scoped BigOperators
open Set

namespace Erdos1038

noncomputable section

/-- Arithmetic mean of a finite multiset, counting multiplicities.  The
nonempty hypothesis needed to use this as a genuine barycenter is supplied
to the lemmas below. -/
def multisetBarycenter (s : Multiset ℝ) : ℝ :=
  s.sum / (s.card : ℝ)

/-- The barycenter of a nonempty cluster contained in `(a, b)` is itself in
`(a, b)`. -/
lemma multisetBarycenter_mem_Ioo {s : Multiset ℝ} {a b : ℝ}
    (hs : s ≠ 0) (hmem : ∀ r ∈ s, r ∈ Set.Ioo a b) :
    multisetBarycenter s ∈ Set.Ioo a b := by
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast (Multiset.card_pos.mpr hs)
  have hlo := Multiset.sum_lt_sum_of_nonempty hs
    (fun r hr ↦ (hmem r hr).1 : ∀ r ∈ s, a < r)
  have hhi := Multiset.sum_lt_sum_of_nonempty hs
    (fun r hr ↦ (hmem r hr).2 : ∀ r ∈ s, r < b)
  have hlo' : (s.card : ℝ) * a < s.sum := by
    simpa [nsmul_eq_mul] using! hlo
  have hhi' : s.sum < (s.card : ℝ) * b := by
    simpa [nsmul_eq_mul] using! hhi
  constructor
  · rw [multisetBarycenter, lt_div_iff₀ hcard]
    nlinarith
  · rw [multisetBarycenter, div_lt_iff₀ hcard]
    simpa [mul_comm] using! hhi'

/-- Finite Jensen inequality for the logarithm, in unnormalized multiset
form.  Positivity is explicit because `Real.log` is used only on `(0, ∞)`. -/
lemma sum_log_le_card_mul_log_average {s : Multiset ℝ}
    (hs : s ≠ 0) (hpos : ∀ y ∈ s, 0 < y) :
    (s.map Real.log).sum ≤
      (s.card : ℝ) * Real.log (s.sum / (s.card : ℝ)) := by
  let l : List ℝ := s.toList
  let w : Fin l.length → ℝ := fun _ ↦ (l.length : ℝ)⁻¹
  let p : Fin l.length → ℝ := fun i ↦ l[i.1]
  have hlength : 0 < l.length := by
    simpa [l] using! Multiset.card_pos.mpr hs
  have hlength_real : 0 < (l.length : ℝ) := by exact_mod_cast hlength
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin l.length)), 0 ≤ w i := by
    intro i hi
    exact (inv_pos.mpr hlength_real).le
  have hwsum : ∑ i, w i = 1 := by
    simp [w, hlength.ne']
  have hp : ∀ i ∈ (Finset.univ : Finset (Fin l.length)), p i ∈ Set.Ioi (0 : ℝ) := by
    intro i hi
    change 0 < l[i.1]
    apply hpos
    rw [← Multiset.mem_toList]
    change l[i.1] ∈ l
    exact List.getElem_mem i.isLt
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := (Finset.univ : Finset (Fin l.length)))
    (w := w) (p := p) hw hwsum hp
  have hscaled :
      (s.map Real.log).sum / (s.card : ℝ) ≤
        Real.log (s.sum / (s.card : ℝ)) := by
    simpa [l, w, p, div_eq_mul_inv, ← Finset.mul_sum, mul_comm] using! hjensen
  have hcard_ne : (s.card : ℝ) ≠ 0 := ne_of_gt (by
    exact_mod_cast (Multiset.card_pos.mpr hs))
  calc
    (s.map Real.log).sum =
        (s.card : ℝ) * ((s.map Real.log).sum / (s.card : ℝ)) := by
      field_simp [hcard_ne]
    _ ≤ (s.card : ℝ) * Real.log (s.sum / (s.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hscaled (Nat.cast_nonneg _)

/-- Sum of `r - x` over a multiset. -/
private lemma sum_map_sub_const (s : Multiset ℝ) (x : ℝ) :
    (s.map fun r ↦ r - x).sum = s.sum - (s.card : ℝ) * x := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        Nat.cast_add, Nat.cast_one, ih]
      ring

/-- Sum of `x - r` over a multiset. -/
private lemma sum_map_const_sub (s : Multiset ℝ) (x : ℝ) :
    (s.map fun r ↦ x - r).sum = (s.card : ℝ) * x - s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        Nat.cast_add, Nat.cast_one, ih]
      ring

/-- To the left of the containing interval, the average root distance is the
distance to the barycenter. -/
lemma average_abs_sub_eq_abs_sub_barycenter_of_le {s : Multiset ℝ}
    {a b x : ℝ} (hs : s ≠ 0) (hmem : ∀ r ∈ s, r ∈ Set.Ioo a b)
    (hx : x ≤ a) :
    (s.map fun r ↦ |x - r|).sum / (s.card : ℝ) =
      |x - multisetBarycenter s| := by
  have hbary := multisetBarycenter_mem_Ioo hs hmem
  have hmap :
      (s.map fun r ↦ |x - r|) = s.map fun r ↦ r - x := by
    apply Multiset.map_congr rfl
    intro r hr
    calc
      |x - r| = -(x - r) := abs_of_nonpos (by linarith [(hmem r hr).1])
      _ = r - x := by ring
  have hcard_ne : (s.card : ℝ) ≠ 0 := ne_of_gt (by
    exact_mod_cast (Multiset.card_pos.mpr hs))
  rw [hmap, sum_map_sub_const, abs_of_nonpos]
  · rw [multisetBarycenter]
    field_simp [hcard_ne]
    ring
  · linarith [hbary.1]

/-- To the right of the containing interval, the average root distance is
the distance to the barycenter. -/
lemma average_abs_sub_eq_abs_sub_barycenter_of_ge {s : Multiset ℝ}
    {a b x : ℝ} (hs : s ≠ 0) (hmem : ∀ r ∈ s, r ∈ Set.Ioo a b)
    (hx : b ≤ x) :
    (s.map fun r ↦ |x - r|).sum / (s.card : ℝ) =
      |x - multisetBarycenter s| := by
  have hbary := multisetBarycenter_mem_Ioo hs hmem
  have hmap :
      (s.map fun r ↦ |x - r|) = s.map fun r ↦ x - r := by
    apply Multiset.map_congr rfl
    intro r hr
    exact abs_of_nonneg (by linarith [(hmem r hr).2])
  have hcard_ne : (s.card : ℝ) ≠ 0 := ne_of_gt (by
    exact_mod_cast (Multiset.card_pos.mpr hs))
  rw [hmap, sum_map_const_sub, abs_of_nonneg]
  · rw [multisetBarycenter]
    field_simp [hcard_ne]
  · linarith [hbary.2]

/-- **Left exterior barycentric collapse.**  Replacing a cluster in `(a, b)`
by its barycenter, with multiplicity `s.card`, weakly raises its total
logarithmic-potential contribution at every `x ≤ a`. -/
lemma sum_log_abs_sub_le_card_mul_log_abs_sub_barycenter_of_le
    {s : Multiset ℝ} {a b x : ℝ} (hs : s ≠ 0)
    (hmem : ∀ r ∈ s, r ∈ Set.Ioo a b) (hx : x ≤ a) :
    (s.map fun r ↦ Real.log |x - r|).sum ≤
      (s.card : ℝ) * Real.log |x - multisetBarycenter s| := by
  have hd_ne : (s.map fun r ↦ |x - r|) ≠ 0 := by
    simpa using! hs
  have hd_pos : ∀ y ∈ (s.map fun r ↦ |x - r|), 0 < y := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    rw [abs_pos]
    have : x < r := hx.trans_lt (hmem r hr).1
    exact sub_ne_zero.mpr this.ne
  have hjensen := sum_log_le_card_mul_log_average hd_ne hd_pos
  rw [Multiset.card_map,
    average_abs_sub_eq_abs_sub_barycenter_of_le hs hmem hx] at hjensen
  simpa only [Multiset.map_map, Function.comp_apply] using! hjensen

/-- **Right exterior barycentric collapse.**  Replacing a cluster in `(a,b)`
by its barycenter weakly raises its total logarithmic-potential contribution
at every `b ≤ x`. -/
lemma sum_log_abs_sub_le_card_mul_log_abs_sub_barycenter_of_ge
    {s : Multiset ℝ} {a b x : ℝ} (hs : s ≠ 0)
    (hmem : ∀ r ∈ s, r ∈ Set.Ioo a b) (hx : b ≤ x) :
    (s.map fun r ↦ Real.log |x - r|).sum ≤
      (s.card : ℝ) * Real.log |x - multisetBarycenter s| := by
  have hd_ne : (s.map fun r ↦ |x - r|) ≠ 0 := by
    simpa using! hs
  have hd_pos : ∀ y ∈ (s.map fun r ↦ |x - r|), 0 < y := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    rw [abs_pos]
    have : r < x := (hmem r hr).2.trans_le hx
    exact sub_ne_zero.mpr this.ne'
  have hjensen := sum_log_le_card_mul_log_average hd_ne hd_pos
  rw [Multiset.card_map,
    average_abs_sub_eq_abs_sub_barycenter_of_ge hs hmem hx] at hjensen
  simpa only [Multiset.map_map, Function.comp_apply] using! hjensen

/-- Exterior barycentric collapse, combining the left and right cases. -/
lemma sum_log_abs_sub_le_card_mul_log_abs_sub_barycenter
    {s : Multiset ℝ} {a b x : ℝ} (hs : s ≠ 0)
    (hmem : ∀ r ∈ s, r ∈ Set.Ioo a b)
    (hx : x ≤ a ∨ b ≤ x) :
    (s.map fun r ↦ Real.log |x - r|).sum ≤
      (s.card : ℝ) * Real.log |x - multisetBarycenter s| := by
  rcases hx with hx | hx
  · exact sum_log_abs_sub_le_card_mul_log_abs_sub_barycenter_of_le hs hmem hx
  · exact sum_log_abs_sub_le_card_mul_log_abs_sub_barycenter_of_ge hs hmem hx

/-- Normalized exterior contribution form of barycentric collapse. -/
lemma average_log_abs_sub_le_log_abs_sub_barycenter
    {s : Multiset ℝ} {a b x : ℝ} (hs : s ≠ 0)
    (hmem : ∀ r ∈ s, r ∈ Set.Ioo a b)
    (hx : x ≤ a ∨ b ≤ x) :
    (s.map fun r ↦ Real.log |x - r|).sum / (s.card : ℝ) ≤
      Real.log |x - multisetBarycenter s| := by
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast (Multiset.card_pos.mpr hs)
  rw [div_le_iff₀ hcard]
  simpa [mul_comm] using!
    sum_log_abs_sub_le_card_mul_log_abs_sub_barycenter hs hmem hx

end

end Erdos1038

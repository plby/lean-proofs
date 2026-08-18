/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.AnisotropicRounding

/-!
# Zonotope representations with bounded fractional support

A point of a `d`-dimensional zonotope has a coefficient representation in
which at most `d` coefficients are strictly between zero and one.  The proof
is the elementary basic-feasible-solution argument: if more coefficients are
fractional, move along a nontrivial linear dependence until one coefficient
reaches an endpoint.

Rounding the remaining fractional coefficients then costs at most `d` times
the coordinate width, independently of the number of generators.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Coefficients of `c` on `s` which are at neither endpoint of `[0,1]`. -/
def fractionalSupport {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ) : Finset ι :=
  s.filter fun a ↦ c a ≠ 0 ∧ c a ≠ 1

@[simp] theorem mem_fractionalSupport {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {c : ι → ℝ} {a : ι} :
    a ∈ fractionalSupport s c ↔ a ∈ s ∧ c a ≠ 0 ∧ c a ≠ 1 := by
  simp [fractionalSupport]

/-- A single basic-feasible pivot.  If more than `d` coefficients are
fractional, a dependence among their vectors permits a box-preserving move
which keeps the represented vector fixed and strictly decreases fractional
support. -/
theorem exists_fractionalSupport_reduction
    {d : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ) (v : ι → Fin d → ℝ)
    (hc : ∀ a ∈ s, 0 ≤ c a ∧ c a ≤ 1)
    (hcard : d < (fractionalSupport s c).card) :
    ∃ c' : ι → ℝ,
      (∀ a ∈ s, 0 ≤ c' a ∧ c' a ≤ 1) ∧
      (∀ i, ∑ a ∈ s, c' a * v a i = ∑ a ∈ s, c a * v a i) ∧
      (fractionalSupport s c').card < (fractionalSupport s c).card := by
  classical
  let F := fractionalSupport s c
  have hdep : ¬ LinearIndependent ℝ (fun a : ↥F ↦ v a) := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Module.finrank_fin_fun] at hle
    exact (not_le_of_gt hcard) (by simpa [F] using hle)
  obtain ⟨g, hg, ag, hag⟩ :=
    Fintype.not_linearIndependent_iff.mp hdep
  let G : Finset F := Finset.univ.filter fun a ↦ g a ≠ 0
  have hG : G.Nonempty := by
    exact ⟨ag, by simp [G, hag]⟩
  let step : F → ℝ := fun a ↦
    if 0 < g a then (1 - c a) / g a else -c a / g a
  have hstep_pos : ∀ a ∈ G, 0 < step a := by
    intro a ha
    have hga : g a ≠ 0 := by simpa [G] using ha
    have haF := (mem_fractionalSupport.mp a.property)
    have hca := hc a haF.1
    have hcpos : 0 < c a := by
      exact lt_of_le_of_ne hca.1 (Ne.symm haF.2.1)
    have hclt : c a < 1 := lt_of_le_of_ne hca.2 haF.2.2
    by_cases hgp : 0 < g a
    · simp only [step, if_pos hgp]
      exact div_pos (sub_pos.mpr hclt) hgp
    · have hgn : g a < 0 := lt_of_le_of_ne (not_lt.mp hgp) hga
      simp only [step, if_neg hgp]
      exact div_pos_of_neg_of_neg (neg_neg_of_pos hcpos) hgn
  let steps : Finset ℝ := G.image step
  have hsteps : steps.Nonempty := hG.image step
  let ε : ℝ := steps.min' hsteps
  have hεpos : 0 < ε := by
    apply (Finset.lt_min'_iff steps hsteps).2
    intro y hy
    obtain ⟨a, haG, rfl⟩ := Finset.mem_image.mp hy
    exact hstep_pos a haG
  have hεle : ∀ a ∈ G, ε ≤ step a := by
    intro a ha
    exact Finset.min'_le steps (step a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  let direction : ι → ℝ := fun a ↦
    if ha : a ∈ F then g ⟨a, ha⟩ else 0
  let c' : ι → ℝ := fun a ↦ c a + ε * direction a
  have hc' : ∀ a ∈ s, 0 ≤ c' a ∧ c' a ≤ 1 := by
    intro a haS
    by_cases haF : a ∈ F
    · have haFrac := mem_fractionalSupport.mp haF
      have hca := hc a haS
      have hcpos : 0 < c a :=
        lt_of_le_of_ne hca.1 (Ne.symm haFrac.2.1)
      have hclt : c a < 1 := lt_of_le_of_ne hca.2 haFrac.2.2
      let af : F := ⟨a, haF⟩
      by_cases hga : g af = 0
      · simpa [c', direction, haF, af, hga] using hca
      · have haG : af ∈ G := by simp [G, hga]
        have hle := hεle af haG
        by_cases hgp : 0 < g af
        · have hmul : ε * g af ≤ 1 - c a := by
            exact (le_div_iff₀ hgp).mp (by simpa [step, hgp, af] using hle)
          constructor
          · simp only [c', direction, dif_pos haF]
            exact add_nonneg hca.1
              (mul_nonneg hεpos.le (by simpa [af] using hgp.le))
          · simp only [c', direction, dif_pos haF]
            simpa [af] using (show c a + ε * g af ≤ 1 by linarith)
        · have hgn : g af < 0 := lt_of_le_of_ne (not_lt.mp hgp) hga
          have hmul : -c a ≤ ε * g af := by
            exact (le_div_iff_of_neg hgn).mp
              (by simpa [step, hgp, af] using hle)
          constructor
          · simp only [c', direction, dif_pos haF]
            simpa [af] using (show 0 ≤ c a + ε * g af by linarith)
          · simp only [c', direction, dif_pos haF]
            have hprod : ε * g af ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
              hεpos.le hgn.le
            simpa [af] using (show c a + ε * g af ≤ 1 by linarith)
    · simpa [c', direction, haF] using hc a haS
  have hsum : ∀ i,
      ∑ a ∈ s, c' a * v a i = ∑ a ∈ s, c a * v a i := by
    intro i
    have hrel : ∑ a : F, g a * v a i = 0 := by
      have hi := congrFun hg i
      simpa [smul_eq_mul] using hi
    have hdir : ∑ a ∈ s, direction a * v a i = 0 := by
      calc
        ∑ a ∈ s, direction a * v a i =
            ∑ a ∈ F, direction a * v a i := by
          symm
          apply Finset.sum_subset (by
            intro a ha
            exact (mem_fractionalSupport.mp ha).1)
          intro a haS haF
          simp only [direction, dif_neg haF, zero_mul]
        _ = ∑ a : F, g a * v a i := by
          rw [← F.sum_attach]
          apply Finset.sum_congr rfl
          intro a _ha
          simp only [direction, dif_pos a.property]
        _ = 0 := hrel
    calc
      ∑ a ∈ s, c' a * v a i =
          ∑ a ∈ s, (c a * v a i + ε * (direction a * v a i)) := by
        apply Finset.sum_congr rfl
        intro a _ha
        simp only [c']
        ring
      _ = (∑ a ∈ s, c a * v a i) +
          ε * ∑ a ∈ s, direction a * v a i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ a ∈ s, c a * v a i := by rw [hdir, mul_zero, add_zero]
  obtain ⟨a₀, ha₀G, hstep₀⟩ :=
    Finset.mem_image.mp (steps.min'_mem hsteps)
  have ha₀F : (a₀ : ι) ∈ F := a₀.property
  have hga₀ : g a₀ ≠ 0 := by simpa [G] using ha₀G
  have hendpoint : c' a₀ = 0 ∨ c' a₀ = 1 := by
    by_cases hgp : 0 < g a₀
    · right
      have hε : ε = (1 - c a₀) / g a₀ := by
        rw [show ε = step a₀ from hstep₀.symm]
        simp [step, hgp]
      simp only [c', direction, ha₀F, dif_pos]
      rw [hε]
      field_simp
      ring
    · left
      have hε : ε = -c a₀ / g a₀ := by
        rw [show ε = step a₀ from hstep₀.symm]
        simp [step, hgp]
      simp only [c', direction, ha₀F, dif_pos]
      rw [hε]
      field_simp
      ring
  have hsupport_subset : fractionalSupport s c' ⊆ F := by
    intro a ha
    have ha' := mem_fractionalSupport.mp ha
    by_contra haF
    have hc'eq : c' a = c a := by simp [c', direction, haF]
    have hn : ¬ (c a ≠ 0 ∧ c a ≠ 1) := by
      intro h
      exact haF (mem_fractionalSupport.mpr ⟨ha'.1, h⟩)
    rcases not_and_or.mp hn with h0 | h1
    · exact ha'.2.1 (hc'eq.trans (not_ne_iff.mp h0))
    · exact ha'.2.2 (hc'eq.trans (not_ne_iff.mp h1))
  have ha₀not : (a₀ : ι) ∉ fractionalSupport s c' := by
    intro ha
    have ha' := mem_fractionalSupport.mp ha
    rcases hendpoint with h0 | h1
    · exact ha'.2.1 h0
    · exact ha'.2.2 h1
  refine ⟨c', hc', hsum, Finset.card_lt_card ?_⟩
  exact (Finset.ssubset_iff_of_subset hsupport_subset).2
    ⟨a₀, ha₀F, ha₀not⟩

/-- Every box-constrained coefficient representation in dimension `d` can
be replaced by one with the same represented vector and at most `d`
fractional coefficients. -/
theorem exists_coefficients_fractionalSupport_card_le
    {d : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ) (v : ι → Fin d → ℝ)
    (hc : ∀ a ∈ s, 0 ≤ c a ∧ c a ≤ 1) :
    ∃ c' : ι → ℝ,
      (∀ a ∈ s, 0 ≤ c' a ∧ c' a ≤ 1) ∧
      (∀ i, ∑ a ∈ s, c' a * v a i = ∑ a ∈ s, c a * v a i) ∧
      (fractionalSupport s c').card ≤ d := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ c' : ι → ℝ,
    (∀ a ∈ s, 0 ≤ c' a ∧ c' a ≤ 1) ∧
    (∀ i, ∑ a ∈ s, c' a * v a i = ∑ a ∈ s, c a * v a i) ∧
    (fractionalSupport s c').card = n
  have hP : ∃ n, P n := by
    refine ⟨(fractionalSupport s c).card, c, hc, ?_, rfl⟩
    intro i
    rfl
  obtain ⟨c', hc', hsum, hcard⟩ := Nat.find_spec hP
  refine ⟨c', hc', hsum, ?_⟩
  by_contra hle
  have hlt : d < (fractionalSupport s c').card := Nat.lt_of_not_ge hle
  obtain ⟨c'', hc'', hsum'', hsmaller⟩ :=
    exists_fractionalSupport_reduction s c' v hc' hlt
  have hP'' : P (fractionalSupport s c'').card := by
    refine ⟨c'', hc'', ?_, rfl⟩
    intro i
    rw [hsum'' i, hsum i]
  have hminimal := Nat.find_min' hP hP''
  rw [hcard] at hsmaller
  exact (not_le_of_gt hsmaller) hminimal

/-- A zonotope point admits a coefficient representation with at most `d`
nonintegral coefficients. -/
theorem exists_zonotope_coefficients_fractionalSupport_card_le
    {d : ℕ} (A : Finset (Fin d → ℤ)) (x : Fin d → ℝ)
    (hx : Zonotope.IsZonotopePoint A x) :
    ∃ q : (Fin d → ℤ) → ℝ,
      (∀ a ∈ A, 0 ≤ q a ∧ q a ≤ 1) ∧
      (∀ i, x i = ∑ a ∈ A, q a * (a i : ℝ)) ∧
      (fractionalSupport A q).card ≤ d := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨q, hq, hsum, hcard⟩ :=
    exists_coefficients_fractionalSupport_card_le A c
      (fun a i ↦ (a i : ℝ)) hc
  refine ⟨q, hq, ?_, hcard⟩
  intro i
  rw [hsum i, ← hxc i]

/-- Cardinality-independent anisotropic rounding.  The error in coordinate
`i` is at most `d * width i`, regardless of the number of generators. -/
theorem exists_subset_sum_approximation_anisotropic_finrank
    {d : ℕ} {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (v : ι → Fin d → ℝ)
    (width : Fin d → ℝ)
    (hc : ∀ a ∈ s, 0 ≤ c a ∧ c a ≤ 1)
    (hwidth : ∀ i, 0 ≤ width i)
    (hv : ∀ a ∈ s, ∀ i, |v a i| ≤ width i) :
    ∃ t : Finset ι, t ⊆ s ∧ ∀ i,
      |(∑ a ∈ s, c a * v a i) - ∑ a ∈ t, v a i| ≤
        (d : ℝ) * width i := by
  classical
  obtain ⟨c', hc', hsum, hcard⟩ :=
    exists_coefficients_fractionalSupport_card_le s c v hc
  let F := fractionalSupport s c'
  let t := s.filter fun a ↦ c' a = 1
  refine ⟨t, Finset.filter_subset _ _, ?_⟩
  intro i
  have hdecomp :
      (∑ a ∈ s, c' a * v a i) - ∑ a ∈ t, v a i =
        ∑ a ∈ F, c' a * v a i := by
    rw [show (∑ a ∈ t, v a i) =
        ∑ a ∈ s, if c' a = 1 then v a i else 0 by
          simpa [t] using
            (Finset.sum_filter (s := s) (fun a ↦ c' a = 1)
              (fun a ↦ v a i))]
    rw [← Finset.sum_sub_distrib]
    calc
      ∑ a ∈ s, (c' a * v a i - if c' a = 1 then v a i else 0) =
          ∑ a ∈ s, if a ∈ F then c' a * v a i else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h1 : c' a = 1
        · simp [h1, F, fractionalSupport]
        · by_cases h0 : c' a = 0
          · simp [h0, F, fractionalSupport]
          · simp [h0, h1, F, fractionalSupport, ha]
      _ = ∑ a ∈ F, c' a * v a i := by
        rw [← Finset.sum_filter]
        congr 1
        ext a
        simp [F, fractionalSupport]
  rw [← hsum i, hdecomp]
  calc
    |∑ a ∈ F, c' a * v a i| ≤ ∑ a ∈ F, |c' a * v a i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ F, width i := by
      apply Finset.sum_le_sum
      intro a haF
      have haS : a ∈ s := (mem_fractionalSupport.mp haF).1
      have hca := hc' a haS
      rw [abs_mul, abs_of_nonneg hca.1]
      calc
        c' a * |v a i| ≤ 1 * |v a i| :=
          mul_le_mul_of_nonneg_right hca.2 (abs_nonneg _)
        _ ≤ width i := by simpa using hv a haS i
    _ = (F.card : ℝ) * width i := by simp
    _ ≤ (d : ℝ) * width i := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hwidth i)

/-- Zonotope-point specialization for integer generators. -/
theorem zonotope_rounding_anisotropic_finrank {d : ℕ}
    (A : Finset (Fin d → ℤ)) (x : Fin d → ℝ)
    (width : Fin d → ℝ) (hx : Zonotope.IsZonotopePoint A x)
    (hwidth : ∀ i, 0 ≤ width i)
    (hA : ∀ a ∈ A, ∀ i, |(a i : ℝ)| ≤ width i) :
    ∃ T : Finset (Fin d → ℤ), T ⊆ A ∧ ∀ i,
      |x i - ∑ a ∈ T, (a i : ℝ)| ≤ (d : ℝ) * width i := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨T, hTA, hT⟩ :=
    exists_subset_sum_approximation_anisotropic_finrank A c
      (fun a i ↦ (a i : ℝ)) width hc hwidth hA
  refine ⟨T, hTA, ?_⟩
  intro i
  rw [hxc i]
  exact hT i

end

end Erdos186.PZ.Intersection

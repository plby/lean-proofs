/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Coordinate and sum hyperplanes in general position

This file contains the elementary finite-dimensional linear algebra used by
the Subspace-Theorem part of the proof of Erdős Problem 407.  On `ℚ^n` we use
the `n` coordinate forms together with the form which is the sum of all
coordinates.  Deleting any one of these `n + 1` forms leaves a basis of the
dual space.
-/

namespace Erdos407.GeneralPosition

open scoped BigOperators

/-- The index set for the coordinate forms and the extra total-sum form.
`some i` denotes the `i`th coordinate and `none` denotes the total sum. -/
abbrev FormIndex (n : ℕ) := Option (Fin n)

/-- The `i`th coordinate linear form on `ℚ^n`. -/
def coordinateForm {n : ℕ} (i : Fin n) : (Fin n → ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.proj i

@[simp]
theorem coordinateForm_apply {n : ℕ} (i : Fin n) (x : Fin n → ℚ) :
    coordinateForm i x = x i :=
  rfl

/-- The linear form on `ℚ^n` obtained by summing all coordinates. -/
def totalForm (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] ℚ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

@[simp]
theorem totalForm_apply (n : ℕ) (x : Fin n → ℚ) :
    totalForm n x = ∑ i, x i :=
  rfl

/-- The `n + 1` forms consisting of all coordinate projections and their sum. -/
def coordSumForm (n : ℕ) : FormIndex n → ((Fin n → ℚ) →ₗ[ℚ] ℚ)
  | none => totalForm n
  | some i => coordinateForm i

@[simp]
theorem coordSumForm_none (n : ℕ) : coordSumForm n none = totalForm n :=
  rfl

@[simp]
theorem coordSumForm_some (n : ℕ) (i : Fin n) :
    coordSumForm n (some i) = coordinateForm i :=
  rfl

@[simp]
theorem coordSumForm_apply_none (n : ℕ) (x : Fin n → ℚ) :
    coordSumForm n none x = ∑ i, x i :=
  rfl

@[simp]
theorem coordSumForm_apply_some (n : ℕ) (i : Fin n) (x : Fin n → ℚ) :
    coordSumForm n (some i) x = x i :=
  rfl

private theorem coordinateForm_linearIndependent (n : ℕ) :
    LinearIndependent ℚ (fun i : Fin n => coordinateForm i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := LinearMap.congr_fun hc (Pi.single i 1)
  have hsum : ∑ j, c j * (Pi.single i (1 : ℚ) : Fin n → ℚ) j = c i := by
    calc
      ∑ j, c j * (Pi.single i (1 : ℚ) : Fin n → ℚ) j =
          c i * (Pi.single i (1 : ℚ) : Fin n → ℚ) i := by
        apply Fintype.sum_eq_single i
        intro j hji
        simp [hji]
      _ = c i := by simp
  simpa [hsum] using h

private def coordSumOmit (n : ℕ) (j : Fin n) :
    Option {i : Fin n // i ≠ j} → ((Fin n → ℚ) →ₗ[ℚ] ℚ)
  | none => totalForm n
  | some i => coordinateForm i.1

private theorem coordSumOmit_linearIndependent (n : ℕ) (j : Fin n) :
    LinearIndependent ℚ (coordSumOmit n j) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hc₀ : c none = 0 := by
    have h := LinearMap.congr_fun hc (Pi.single j 1)
    have hzero : ∑ k : {i : Fin n // i ≠ j},
        c (some k) * (Pi.single j (1 : ℚ) : Fin n → ℚ) k.1 = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      simp [k.2]
    simpa [coordSumOmit, Fintype.sum_option, hzero] using h
  cases i with
  | none => exact hc₀
  | some i =>
      have h := LinearMap.congr_fun hc (Pi.single i.1 1)
      have hsum : ∑ k : {k : Fin n // k ≠ j},
          c (some k) * (Pi.single i.1 (1 : ℚ) : Fin n → ℚ) k.1 = c (some i) := by
        calc
          ∑ k : {k : Fin n // k ≠ j},
              c (some k) * (Pi.single i.1 (1 : ℚ) : Fin n → ℚ) k.1 =
              c (some i) * (Pi.single i.1 (1 : ℚ) : Fin n → ℚ) i.1 := by
            apply Fintype.sum_eq_single i
            intro k hki
            have hv : k.1 ≠ i.1 := fun hv => hki (Subtype.ext hv)
            simp [hv]
          _ = c (some i) := by simp
      simpa [coordSumOmit, Fintype.sum_option, hc₀, hsum] using h

private def omitNoneEquiv (n : ℕ) :
    {i : FormIndex n // i ≠ none} ≃ Fin n where
  toFun i := Option.get i.1 (Option.ne_none_iff_isSome.mp i.2)
  invFun i := ⟨some i, by simp⟩
  left_inv i := Subtype.ext (Option.some_get _)
  right_inv i := Option.get_some _ _

private def omitSomeEquiv (n : ℕ) (j : Fin n) :
    {i : FormIndex n // i ≠ some j} ≃ Option {i : Fin n // i ≠ j} where
  toFun i := by
    cases hi : i.1 with
    | none => exact none
    | some k =>
        exact some ⟨k, fun hkj => i.2 (by simp [hi, hkj])⟩
  invFun i := by
    cases i with
    | none => exact ⟨none, by simp⟩
    | some k => exact ⟨some k.1, by simp [k.2]⟩
  left_inv i := by
    rcases i with ⟨i, hi⟩
    apply Subtype.ext
    cases i with
    | none => rfl
    | some k => rfl
  right_inv i := by
    cases i with
    | none => rfl
    | some k => rfl

/-- Deleting any one of the coordinate-and-sum forms leaves a linearly
independent family. -/
theorem coordSumForm_omit_linearIndependent (n : ℕ) (k : FormIndex n) :
    LinearIndependent ℚ
      (fun i : {i : FormIndex n // i ≠ k} => coordSumForm n i.1) := by
  classical
  cases k with
  | none =>
      apply (linearIndependent_equiv' (omitNoneEquiv n) ?_).mpr
        (coordinateForm_linearIndependent n)
      funext i
      cases hi : i.1 with
      | none => exact False.elim (i.2 hi)
      | some j => simp [omitNoneEquiv, coordSumForm, hi]
  | some j₀ =>
      apply (linearIndependent_equiv' (omitSomeEquiv n j₀) ?_).mpr
        (coordSumOmit_linearIndependent n j₀)
      funext i
      rcases i with ⟨i, hi⟩
      cases i with
      | none => rfl
      | some j => rfl

/-- Every subfamily of at most `n` coordinate-and-sum forms is linearly
independent.  In particular, every dimension-sized subfamily is independent. -/
theorem coordSumForm_subfamily_linearIndependent (n : ℕ)
    (s : Finset (FormIndex n)) (hs : s.card ≤ n) :
    LinearIndependent ℚ (fun i : s => coordSumForm n i.1) := by
  classical
  have hcard : s.card < Fintype.card (FormIndex n) := by
    simpa using Nat.lt_succ_of_le hs
  have hsne : s ≠ Finset.univ := (Finset.card_lt_iff_ne_univ s).mp hcard
  obtain ⟨k, hk⟩ : ∃ k : FormIndex n, k ∉ s := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hsne (Finset.eq_univ_iff_forall.mpr h)
  let e : s → {i : FormIndex n // i ≠ k} := fun i => ⟨i.1, by
    intro hik
    exact hk (hik ▸ i.2)⟩
  exact (coordSumForm_omit_linearIndependent n k).comp e fun i j hij => by
    apply Subtype.ext
    simpa [e] using congrArg Subtype.val hij

/-- The precise dimension-sized formulation of general position. -/
theorem coordSumForm_generalPosition (n : ℕ)
    (s : Finset (FormIndex n)) (hs : s.card = n) :
    LinearIndependent ℚ (fun i : s => coordSumForm n i.1) :=
  coordSumForm_subfamily_linearIndependent n s hs.le

/-- The hyperplane belonging to one of the coordinate-and-sum forms. -/
def coordSumHyperplane (n : ℕ) (i : FormIndex n) : Submodule ℚ (Fin n → ℚ) :=
  LinearMap.ker (coordSumForm n i)

@[simp]
theorem mem_coordSumHyperplane_none {n : ℕ} (x : Fin n → ℚ) :
    x ∈ coordSumHyperplane n none ↔ ∑ i, x i = 0 := by
  rfl

@[simp]
theorem mem_coordSumHyperplane_some {n : ℕ} (i : Fin n) (x : Fin n → ℚ) :
    x ∈ coordSumHyperplane n (some i) ↔ x i = 0 := by
  rfl

/-- Any `n` of the `n + 1` coordinate-and-sum hyperplanes have trivial
intersection.  This is the hyperplane formulation of general position. -/
theorem iInf_coordSumHyperplane_eq_bot (n : ℕ)
    (s : Finset (FormIndex n)) (hs : s.card = n) :
    (⨅ i : s, coordSumHyperplane n i.1) = ⊥ := by
  classical
  let L : s → ((Fin n → ℚ) →ₗ[ℚ] ℚ) := fun i => coordSumForm n i.1
  have hli : LinearIndependent ℚ L := coordSumForm_generalPosition n s hs
  have hcard : Fintype.card s = Module.finrank ℚ ((Fin n → ℚ) →ₗ[ℚ] ℚ) := by
    rw [Fintype.card_coe, hs, Subspace.dual_finrank_eq,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hspan : Submodule.span ℚ (Set.range L) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    apply funext
    intro j
    have hvanish {f : (Fin n → ℚ) →ₗ[ℚ] ℚ}
        (hf : f ∈ Submodule.span ℚ (Set.range L)) : f x = 0 := by
      induction hf using Submodule.span_induction with
      | mem f hf =>
          obtain ⟨i, rfl⟩ := hf
          have hxi : x ∈ coordSumHyperplane n i.1 :=
            (Submodule.mem_iInf _).mp hx i
          exact hxi
      | zero => simp
      | add f g _ _ hf hg => simp [hf, hg]
      | smul a f _ hf => simp [hf]
    have hj : coordinateForm j ∈ Submodule.span ℚ (Set.range L) := by
      rw [hspan]
      exact Submodule.mem_top
    simpa using hvanish hj
  · exact bot_le

/-- Each coordinate-and-sum hyperplane is proper. -/
theorem coordSumHyperplane_ne_top {n : ℕ} (hn : 0 < n) (i : FormIndex n) :
    coordSumHyperplane n i ≠ ⊤ := by
  cases i with
  | none =>
      obtain ⟨j⟩ := Fin.pos_iff_nonempty.mp hn
      intro htop
      have hmem : (Pi.single j 1 : Fin n → ℚ) ∈ coordSumHyperplane n none := htop.symm ▸ Submodule.mem_top
      simp at hmem
  | some j =>
      intro htop
      have hmem : (Pi.single j 1 : Fin n → ℚ) ∈ coordSumHyperplane n (some j) :=
        htop.symm ▸ Submodule.mem_top
      simp at hmem

/-- Every proper rational subspace is contained in a rational hyperplane,
presented as the kernel of a nonzero rational linear form. -/
theorem properSubspace_le_kernel {n : ℕ} (W : Submodule ℚ (Fin n → ℚ))
    (hW : W < ⊤) :
    ∃ f : (Fin n → ℚ) →ₗ[ℚ] ℚ,
      f ≠ 0 ∧ W ≤ LinearMap.ker f ∧ LinearMap.ker f < ⊤ := by
  obtain ⟨f, hf, hle⟩ := W.exists_le_ker_of_lt_top hW
  refine ⟨f, hf, hle, lt_top_iff_ne_top.mpr ?_⟩
  intro hker
  apply hf
  rw [← LinearMap.ker_eq_top]
  exact hker

/-- A finite family of proper rational subspaces cannot cover `ℚ^n`.
This is the finite-cover induction principle needed downstream. -/
theorem exists_not_mem_finite_proper_subspaces {n : ℕ} {ι : Type*} [Finite ι]
    (W : ι → Submodule ℚ (Fin n → ℚ)) (hW : ∀ i, W i ≠ ⊤) :
    ∃ x : Fin n → ℚ, ∀ i, x ∉ W i :=
  Submodule.exists_forall_notMem_of_forall_ne_top W hW

/-- Finset-indexed version of `exists_not_mem_finite_proper_subspaces`. -/
theorem exists_not_mem_finset_proper_subspaces {n : ℕ} {ι : Type*}
    (s : Finset ι) (W : ι → Submodule ℚ (Fin n → ℚ))
    (hW : ∀ i ∈ s, W i ≠ ⊤) :
    ∃ x : Fin n → ℚ, ∀ i ∈ s, x ∉ W i := by
  let W' : s → Submodule ℚ (Fin n → ℚ) := fun i => W i.1
  obtain ⟨x, hx⟩ := exists_not_mem_finite_proper_subspaces W' fun i => hW i.1 i.2
  exact ⟨x, fun i hi => hx ⟨i, hi⟩⟩

end Erdos407.GeneralPosition

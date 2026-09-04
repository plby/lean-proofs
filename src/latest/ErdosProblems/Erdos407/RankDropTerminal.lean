/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.RankDrop

/-!
# Terminal scale selection for the rational rank-drop argument

The generalized Roth lemma needs successive logarithmic scales to be
separated by a fixed factor.  On the original natural scales this is a
power-growth condition, not merely a fixed multiplicative-growth condition.
This file records the proper-height selection lemma with an arbitrary next
threshold and specializes it to the nonexceptional codimension-one
approximation spaces.

The module imports `RankDrop` and is intentionally acyclic: the final
rank-stabilization theorem can import this file after all algebraic estimates
have been assembled.
-/

namespace Erdos407.RankDrop

open scoped BigOperators

/-! ## Arbitrary-threshold proper-height selection -/

/-- An infinite set on which a natural-valued height is proper contains a
finite list whose later entries dominate any prescribed function of every
earlier height. -/
theorem exists_growingBy_list {α : Type*} {X : Set α} {h : α → ℕ}
    (hproper : HeightBoxes.IsProperHeight X h) (hX : X.Infinite)
    (H₀ : ℕ) (next : ℕ → ℕ) (m : ℕ) :
    ∃ xs : List X, xs.length = m ∧
      (∀ x ∈ xs, H₀ < h x.1) ∧
      xs.Pairwise (fun (x y : X) => next (h x.1) < h y.1) := by
  induction m generalizing H₀ with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ m ih =>
      obtain ⟨x, hxX, hxH⟩ := hproper.unbounded hX H₀
      let xX : X := ⟨x, hxX⟩
      obtain ⟨xs, hlen, hH, hgrow⟩ := ih (max H₀ (next (h x)))
      refine ⟨xX :: xs, by simp [hlen], ?_, ?_⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨hxH, fun y hy => (le_max_left _ _).trans_lt (hH y hy)⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hgrow⟩
        intro y hy
        exact (le_max_right H₀ (next (h x))).trans_lt (hH y hy)

/-- If the requested next threshold is at least the current height, the
arbitrary-threshold list has no repetitions. -/
theorem exists_growingBy_list_nodup {α : Type*} {X : Set α} {h : α → ℕ}
    (hproper : HeightBoxes.IsProperHeight X h) (hX : X.Infinite)
    (H₀ : ℕ) (next : ℕ → ℕ) (m : ℕ)
    (hnext : ∀ H, H ≤ next H) :
    ∃ xs : List X, xs.length = m ∧ xs.Nodup ∧
      (∀ x ∈ xs, H₀ < h x.1) ∧
      xs.Pairwise (fun (x y : X) => next (h x.1) < h y.1) := by
  obtain ⟨xs, hlen, hH, hgrow⟩ :=
    exists_growingBy_list hproper hX H₀ next m
  refine ⟨xs, hlen, ?_, hH, hgrow⟩
  apply (List.nodup_iff_injective_get).2
  intro i j hij
  rcases lt_trichotomy i j with hijlt | hijeq | hjilt
  · have hg : next (h (xs.get i).1) < h (xs.get j).1 :=
      (List.pairwise_iff_get.mp hgrow) i j hijlt
    have heq : h (xs.get i).1 = h (xs.get j).1 :=
      congrArg (fun z : X => h z.1) hij
    have : next (h (xs.get i).1) < h (xs.get i).1 := by
      rwa [← heq] at hg
    exact (not_lt_of_ge (hnext _) this).elim
  · exact hijeq
  · have hg : next (h (xs.get j).1) < h (xs.get i).1 :=
      (List.pairwise_iff_get.mp hgrow) j i hjilt
    have heq : h (xs.get i).1 = h (xs.get j).1 :=
      congrArg (fun z : X => h z.1) hij
    have : next (h (xs.get j).1) < h (xs.get j).1 := by
      rwa [heq] at hg
    exact (not_lt_of_ge (hnext _) this).elim

/-- `Fin`-indexed arbitrary-threshold selection.  The sequence has `m+1`
entries, making every consecutive gap available without an empty-index
side condition. -/
theorem exists_growingBy {α : Type*} {X : Set α} {h : α → ℕ}
    (hproper : HeightBoxes.IsProperHeight X h) (hX : X.Infinite)
    (H₀ : ℕ) (next : ℕ → ℕ) (m : ℕ)
    (hnext : ∀ H, H ≤ next H) :
    ∃ x : Fin (m + 1) → X,
      H₀ < h (x 0).1 ∧
      (∀ i : Fin m, next (h (x i.castSucc).1) < h (x i.succ).1) ∧
      Function.Injective x := by
  obtain ⟨xs, hlen, hnodup, hH, hgrow⟩ :=
    exists_growingBy_list_nodup hproper hX H₀ next (m + 1) hnext
  let e : Fin (m + 1) → Fin xs.length := fun i => Fin.cast hlen.symm i
  let x : Fin (m + 1) → X := fun i => xs.get (e i)
  refine ⟨x, ?_, ?_, ?_⟩
  · exact hH _ (List.get_mem xs (e 0))
  · intro i
    have hi : e i.castSucc < e i.succ := by
      change i.castSucc.val < i.succ.val
      simp
    exact (List.pairwise_iff_get.mp hgrow) (e i.castSucc) (e i.succ) hi
  · exact (List.nodup_iff_injective_get.mp hnodup).comp
      (Fin.cast_injective hlen.symm)

/-- Exact-cardinality version retaining the cutoff bound for every selected
point and the growth condition for every ordered pair. -/
theorem exists_growingBy_all {α : Type*} {X : Set α} {h : α → ℕ}
    (hproper : HeightBoxes.IsProperHeight X h) (hX : X.Infinite)
    (H₀ : ℕ) (next : ℕ → ℕ) (m : ℕ)
    (hnext : ∀ H, H ≤ next H) :
    ∃ x : Fin m → X,
      (∀ i, H₀ < h (x i).1) ∧
      (∀ i j, i < j → next (h (x i).1) < h (x j).1) ∧
      Function.Injective x := by
  obtain ⟨xs, hlen, hnodup, hH, hgrow⟩ :=
    exists_growingBy_list_nodup hproper hX H₀ next m hnext
  let e : Fin m → Fin xs.length := fun i => Fin.cast hlen.symm i
  let x : Fin m → X := fun i => xs.get (e i)
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i
    exact hH _ (List.get_mem xs (e i))
  · intro i j hij
    exact (List.pairwise_iff_get.mp hgrow) (e i) (e j) (by
      change i.val < j.val
      exact hij)
  · exact (List.nodup_iff_injective_get.mp hnodup).comp
      (Fin.cast_injective hlen.symm)

/-! ## Nonexceptional codimension-one specialization -/

/-- Arbitrary-threshold selection after removing the finite family of
support-pattern exceptional spaces. -/
theorem exists_growingBy_nonexceptional_sCodimOneSpaces
    {n : ℕ} {L : LocalForms n} {c : HeightBoxes.LocalConstants n}
    (hinfinite : (sCodimOneApproximationSpaces L c).Infinite)
    (Q₀ : ℕ) (next : ℕ → ℕ) (m : ℕ)
    (hnext : ∀ Q, Q ≤ next Q) :
    ∃ W : Fin (m + 1) → sCodimOneApproximationSpaces L c,
      (∀ j, (W j).1 ∉ Set.range (exceptionalSpace L)) ∧
      Q₀ < sCodimOneScale (W 0) ∧
      (∀ i : Fin m,
        next (sCodimOneScale (W i.castSucc)) <
          sCodimOneScale (W i.succ)) ∧
      Function.Injective W := by
  let E : Set (sCodimOneApproximationSpaces L c) :=
    {W | W.1 ∈ Set.range (exceptionalSpace L)}
  have hE : E.Finite := by
    exact (finite_exceptionalSpaces L).preimage
      (f := fun W : sCodimOneApproximationSpaces L c => W.1)
      Subtype.val_injective.injOn
  let : Infinite (sCodimOneApproximationSpaces L c) := hinfinite.to_subtype
  have hnonexceptional :
      ((Set.univ : Set (sCodimOneApproximationSpaces L c)) \ E).Infinite :=
    Set.infinite_univ.sdiff hE
  have hproper : HeightBoxes.IsProperHeight
      ((Set.univ : Set (sCodimOneApproximationSpaces L c)) \ E)
      sCodimOneScale := by
    intro H
    apply (sCodimOneScale_isProper (L := L) (c := c) H).subset
    intro W hW
    exact ⟨Set.mem_univ W, hW.2⟩
  obtain ⟨x, hx₀, hxgrow, hxinj⟩ :=
    exists_growingBy hproper hnonexceptional Q₀ next m hnext
  let W : Fin (m + 1) → sCodimOneApproximationSpaces L c := fun j => (x j).1
  refine ⟨W, ?_, hx₀, hxgrow, ?_⟩
  · intro j hj
    exact (x j).2.2 hj
  · intro i j hij
    apply hxinj
    exact Subtype.ext hij

/-- Power-separated nonexceptional spaces.  This is the natural-scale form
of the logarithmic separation used to compare consecutive block degrees. -/
theorem exists_powerSeparated_nonexceptional_sCodimOneSpaces
    {n : ℕ} {L : LocalForms n} {c : HeightBoxes.LocalConstants n}
    (hinfinite : (sCodimOneApproximationSpaces L c).Infinite)
    (Q₀ K m : ℕ) :
    ∃ W : Fin (m + 1) → sCodimOneApproximationSpaces L c,
      (∀ j, (W j).1 ∉ Set.range (exceptionalSpace L)) ∧
      Q₀ < sCodimOneScale (W 0) ∧
      (∀ i : Fin m,
        sCodimOneScale (W i.castSucc) ^ K <
          sCodimOneScale (W i.succ)) ∧
      Function.Injective W := by
  obtain ⟨W, hWexceptional, hW₀, hWgrow, hWinj⟩ :=
    exists_growingBy_nonexceptional_sCodimOneSpaces
      hinfinite Q₀ (fun Q => max Q (Q ^ K)) m (fun Q => le_max_left _ _)
  refine ⟨W, hWexceptional, hW₀, ?_, hWinj⟩
  intro i
  exact (le_max_right
      (sCodimOneScale (W i.castSucc))
      (sCodimOneScale (W i.castSucc) ^ K)).trans_lt (hWgrow i)

/-- Taking logarithms turns the preceding power separation into the exact
linear logarithmic separation needed in the floor-degree argument. -/
theorem exists_logSeparated_nonexceptional_sCodimOneSpaces
    {n : ℕ} {L : LocalForms n} {c : HeightBoxes.LocalConstants n}
    (hinfinite : (sCodimOneApproximationSpaces L c).Infinite)
    (Q₀ K m : ℕ) :
    ∃ W : Fin (m + 1) → sCodimOneApproximationSpaces L c,
      (∀ j, (W j).1 ∉ Set.range (exceptionalSpace L)) ∧
      Q₀ < sCodimOneScale (W 0) ∧
      (∀ i : Fin m,
        (K : ℝ) * Real.log (sCodimOneScale (W i.castSucc) : ℝ) <
          Real.log (sCodimOneScale (W i.succ) : ℝ)) ∧
      Function.Injective W := by
  obtain ⟨W, hWexceptional, hW₀, hWgrow, hWinj⟩ :=
    exists_powerSeparated_nonexceptional_sCodimOneSpaces
      hinfinite Q₀ K m
  refine ⟨W, hWexceptional, hW₀, ?_, hWinj⟩
  intro i
  have hQ : 0 < (sCodimOneScale (W i.castSucc) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (sCodimOneScale_ge_two (W i.castSucc)))
  have hR : 0 < (sCodimOneScale (W i.succ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (sCodimOneScale_ge_two (W i.succ)))
  have hpow :
      ((sCodimOneScale (W i.castSucc) : ℝ) ^ K) <
        (sCodimOneScale (W i.succ) : ℝ) := by
    exact_mod_cast hWgrow i
  have hlog := Real.strictMonoOn_log (pow_pos hQ K) hR hpow
  simpa [Real.log_pow] using hlog

/-- Exact-cardinality form of logarithmic separation. -/
theorem exists_logSeparated_nonexceptional_sCodimOneSpaces_of_pos
    {n : ℕ} {L : LocalForms n} {c : HeightBoxes.LocalConstants n}
    (hinfinite : (sCodimOneApproximationSpaces L c).Infinite)
    (Q₀ K blocks : ℕ) (hblocks : 0 < blocks) :
    ∃ W : Fin blocks → sCodimOneApproximationSpaces L c,
      (∀ j, (W j).1 ∉ Set.range (exceptionalSpace L)) ∧
      Q₀ < sCodimOneScale (W ⟨0, hblocks⟩) ∧
      (∀ i : Fin (blocks - 1),
        (K : ℝ) * Real.log
            (sCodimOneScale (W ⟨i.val, by omega⟩) : ℝ) <
          Real.log (sCodimOneScale (W ⟨i.val + 1, by omega⟩) : ℝ)) ∧
      Function.Injective W := by
  have hb : blocks - 1 + 1 = blocks := Nat.sub_add_cancel hblocks
  obtain ⟨W, hWexceptional, hW₀, hWgrow, hWinj⟩ :=
    exists_logSeparated_nonexceptional_sCodimOneSpaces
      hinfinite Q₀ K (blocks - 1)
  let e : Fin blocks → Fin (blocks - 1 + 1) := Fin.cast hb.symm
  let W' : Fin blocks → sCodimOneApproximationSpaces L c := fun j ↦ W (e j)
  refine ⟨W', ?_, ?_, ?_, hWinj.comp (Fin.cast_injective hb.symm)⟩
  · intro j
    exact hWexceptional (e j)
  · simpa [W', e] using hW₀
  · intro i
    let i0 : Fin blocks := ⟨i.val, by omega⟩
    let i1 : Fin blocks := ⟨i.val + 1, by omega⟩
    have hcastSucc : e i0 = i.castSucc := by
      apply Fin.ext
      rfl
    have hsucc : e i1 = i.succ := by
      apply Fin.ext
      rfl
    simpa [W', i0, i1, hcastSucc, hsucc] using hWgrow i

/-- Exact-cardinality logarithmic selection which retains the initial
cutoff for every chosen space.  This is the form used to apply a uniform
normal-height theorem blockwise. -/
theorem exists_logSeparated_nonexceptional_sCodimOneSpaces_all
    {n : ℕ} {L : LocalForms n} {c : HeightBoxes.LocalConstants n}
    (hinfinite : (sCodimOneApproximationSpaces L c).Infinite)
    (Q₀ K blocks : ℕ) :
    ∃ W : Fin blocks → sCodimOneApproximationSpaces L c,
      (∀ j, (W j).1 ∉ Set.range (exceptionalSpace L)) ∧
      (∀ j, Q₀ < sCodimOneScale (W j)) ∧
      (∀ i : Fin (blocks - 1),
        (K : ℝ) * Real.log
            (sCodimOneScale (W ⟨i.val, by omega⟩) : ℝ) <
          Real.log (sCodimOneScale (W ⟨i.val + 1, by omega⟩) : ℝ)) ∧
      Function.Injective W := by
  let E : Set (sCodimOneApproximationSpaces L c) :=
    {W | W.1 ∈ Set.range (exceptionalSpace L)}
  have hE : E.Finite := by
    exact (finite_exceptionalSpaces L).preimage
      (f := fun W : sCodimOneApproximationSpaces L c => W.1)
      Subtype.val_injective.injOn
  let : Infinite (sCodimOneApproximationSpaces L c) := hinfinite.to_subtype
  have hnonexceptional :
      ((Set.univ : Set (sCodimOneApproximationSpaces L c)) \ E).Infinite :=
    Set.infinite_univ.sdiff hE
  have hproper : HeightBoxes.IsProperHeight
      ((Set.univ : Set (sCodimOneApproximationSpaces L c)) \ E)
      sCodimOneScale := by
    intro H
    apply (sCodimOneScale_isProper (L := L) (c := c) H).subset
    intro W hW
    exact ⟨Set.mem_univ W, hW.2⟩
  obtain ⟨x, hxlarge, hxgrow, hxinj⟩ :=
    exists_growingBy_all hproper hnonexceptional Q₀
      (fun Q => max Q (Q ^ K)) blocks (fun Q => le_max_left _ _)
  let W : Fin blocks → sCodimOneApproximationSpaces L c := fun j => (x j).1
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact (x j).2.2 hj
  · intro j
    exact hxlarge j
  · intro i
    let i0 : Fin blocks := ⟨i.val, by omega⟩
    let i1 : Fin blocks := ⟨i.val + 1, by omega⟩
    have hi : i0 < i1 := by simp [i0, i1]
    have hgrow := hxgrow i0 i1 hi
    have hpow : sCodimOneScale (W i0) ^ K <
        sCodimOneScale (W i1) :=
      (le_max_right (sCodimOneScale (W i0))
        (sCodimOneScale (W i0) ^ K)).trans_lt hgrow
    have hQ : 0 < (sCodimOneScale (W i0) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
        (sCodimOneScale_ge_two (W i0)))
    have hR : 0 < (sCodimOneScale (W i1) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
        (sCodimOneScale_ge_two (W i1)))
    have hpowR : ((sCodimOneScale (W i0) : ℝ) ^ K) <
        (sCodimOneScale (W i1) : ℝ) := by
      exact_mod_cast hpow
    have hlog := Real.strictMonoOn_log (pow_pos hQ K) hR hpowR
    simpa [i0, i1, Real.log_pow] using hlog
  · intro i j hij
    apply hxinj
    exact Subtype.ext hij

/-- Simultaneous block selection and the repaired codimension-one normal
height estimate.  Every selected space receives a primitive integral normal
whose projective form height has the same positive logarithmic slope. -/
theorem exists_logSeparated_primitiveNormals
    {m : ℕ} (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants (m + 1))
    {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ v, ∑ i, c v i) ≤ -delta)
    (hinfinite : (sCodimOneApproximationSpaces L c).Infinite)
    (Q₀ K blocks : ℕ) :
    ∃ (W : Fin blocks → sCodimOneApproximationSpaces L c)
        (z : Fin blocks → IntVector (m + 1)),
      (∀ j, (W j).1 ∉ Set.range (exceptionalSpace L)) ∧
      (∀ j, Q₀ < sCodimOneScale (W j)) ∧
      (∀ i : Fin (blocks - 1),
        (K : ℝ) * Real.log
            (sCodimOneScale (W ⟨i.val, by omega⟩) : ℝ) <
          Real.log (sCodimOneScale (W ⟨i.val + 1, by omega⟩) : ℝ)) ∧
      Function.Injective W ∧
      (∀ j, z j ≠ 0 ∧ Primitive.IsPrimitive (z j) ∧
        (∀ y ∈ (W j).1,
          y ⬝ᵥ PadicSubspace.intCastVec (z j) = 0) ∧
        delta / (12 * (m + 1)) *
            Real.log (sCodimOneScale (W j) : ℝ) ≤
          GeneralizedRoth.formHeight (primitiveNormalForm (z j))) := by
  classical
  obtain ⟨Qnormal, hQnormal⟩ :=
    exists_sCodimOne_primitiveNormal_formHeight_ge
      L hL c hdelta hc
  obtain ⟨W, hWexceptional, hWlarge, hWgap, hWinj⟩ :=
    exists_logSeparated_nonexceptional_sCodimOneSpaces_all
      hinfinite (max Q₀ Qnormal) K blocks
  have hnormal : ∀ j, ∃ z : IntVector (m + 1),
      z ≠ 0 ∧ Primitive.IsPrimitive z ∧
      (∀ y ∈ (W j).1, y ⬝ᵥ PadicSubspace.intCastVec z = 0) ∧
      delta / (12 * (m + 1)) *
          Real.log (sCodimOneScale (W j) : ℝ) ≤
        GeneralizedRoth.formHeight (primitiveNormalForm z) := by
    intro j
    exact hQnormal (W j)
      ((le_max_right Q₀ Qnormal).trans (hWlarge j).le)
      (hWexceptional j)
  choose z hz using hnormal
  refine ⟨W, z, hWexceptional, ?_, hWgap, hWinj, hz⟩
  intro j
  exact (le_max_left Q₀ Qnormal).trans_lt (hWlarge j)

/-! ## Generalized-Roth extraction at the adaptive parameters -/

/-- Apply the generalized Roth lemma with the adaptive GLR separation
parameter and extract a nonzero restriction derivative.  The special choice
of `rankDropSigmaAt` turns the Roth-root bound into exactly half of the
central-band derivative budget. -/
theorem exists_rankDrop_restrictedDerivative
    {blocks n : ℕ} (hblocks : 0 < blocks) (hn : 0 < n)
    {eta : ℚ} (heta : 0 < eta) (hetaOne : eta ≤ 1)
    {degree : Fin blocks → ℕ} (hdegree : ∀ h, 0 < degree h)
    (coeff : AuxiliaryPolynomial.MonomialIndex
      blocks (n + 1) degree → ℤ)
    (hcoeff : AuxiliaryPolynomial.ofCoefficients coeff ≠ 0)
    (hhom : GLRAuxiliary.IsMultihomogeneous degree
      (AuxiliaryPolynomial.ofCoefficients coeff))
    (M : GeneralizedRoth.FormFamily blocks n) (hM : ∀ h, M h ≠ 0)
    (hratio : ∀ j : Fin (blocks - 1),
      (degree ⟨j.val + 1, by omega⟩ : ℝ) /
        (degree ⟨j.val, by omega⟩ : ℝ) ≤
          rankDropSigmaAt blocks eta)
    (hheight : ∀ j,
      (n : ℝ) * (rankDropSigmaAt blocks eta)⁻¹ *
          (PolynomialHeights.projectiveCoeffHeight
              (rationalAuxiliaryPolynomial coeff) +
            4 * (blocks : ℝ) *
              (degree ⟨0, hblocks⟩ : ℝ)) ≤
        (degree j : ℝ) * GeneralizedRoth.formHeight (M j)) :
    ∃ N : RestrictionIndex.NormalOrder blocks,
      RestrictionIndex.normalWeight degree N ≤
          (blocks : ℚ) * eta / 2 ∧
      RestrictionIndex.restrictedDividedDerivative M hM
          (rationalAuxiliaryPolynomial coeff) N ≠ 0 := by
  have hindexR := GeneralizedRoth.generalizedRothLemma
    hblocks hn (rationalAuxiliaryPolynomial_ne_zero hcoeff)
    degree hdegree
    (rationalAuxiliaryPolynomial_isMultiHomogeneous coeff hhom)
    M hM (rankDropSigmaAt_pos heta)
    (rankDropSigmaAt_le_half heta hetaOne) hratio hheight
  rw [twice_blocks_mul_rothRoot_rankDropSigmaAt heta] at hindexR
  have hindexQ : GeneralizedRoth.formIndex M hM
      (rationalAuxiliaryPolynomial coeff) degree ≤
        (blocks : ℚ) * eta / 2 := by
    exact_mod_cast hindexR
  exact RestrictionIndex.exists_restrictedDividedDerivative_of_formIndex_le
    M hM (rationalAuxiliaryPolynomial_ne_zero hcoeff) degree hindexQ

end Erdos407.RankDrop

#print axioms Erdos407.RankDrop.exists_growingBy_nonexceptional_sCodimOneSpaces

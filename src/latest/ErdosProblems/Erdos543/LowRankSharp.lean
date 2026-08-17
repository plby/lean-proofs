import ErdosProblems.Erdos543.Hypercube
import ErdosProblems.Erdos543.LowRankCount

/-!
# The sharp low-rank Boolean-matrix count

This file supplies the missing three-quarters cube-intersection input for the
low-rank count in `LowRankCount.lean` and applies it to ordered matrices with
distinct nonzero rows.
-/

open scoped BigOperators
open Finset

namespace Erdos543

attribute [local instance] Classical.propDecidable

theorem boolRat_injective : Function.Injective boolRat := by
  intro x y h
  cases x <;> cases y <;> simp_all

/-! ## Splitting off Boolean coordinates -/

/-- The indices left after first deleting `p`, then deleting `q`.  The nested
subtype is chosen so that `Fintype.sum_eq_add_sum_subtype_ne` applies twice
without any reindexing. -/
abbrev RemoveTwo {α : Type*} (p q : α) [DecidableEq α] (hpq : p ≠ q) :=
  {i : {j : α // j ≠ p} // i ≠ ⟨q, hpq.symm⟩}

/-- Split a Boolean function into all coordinates except `p,q`, followed by
the two distinguished bits. -/
def cubeRemoveTwoEquiv {α : Type*} [DecidableEq α] (p q : α) (hpq : p ≠ q) :
    (α → Bool) ≃ (RemoveTwo p q hpq → Bool) × (Bool × Bool) where
  toFun x := (fun i ↦ x i, (x p, x q))
  invFun z i :=
    if hip : i = p then z.2.1
    else if hiq : i = q then z.2.2
    else z.1 ⟨⟨i, hip⟩, fun h ↦ hiq (congrArg Subtype.val h)⟩
  left_inv x := by
    funext i
    by_cases hip : i = p
    · subst i
      simp
    · by_cases hiq : i = q
      · subst i
        simp [hip]
      · simp [hip, hiq]
  right_inv z := by
    apply Prod.ext
    · funext i
      have hiq : (i.1 : α) ≠ q := fun h ↦ i.2 (Subtype.ext h)
      simp [i.1.2, hiq]
    · apply Prod.ext <;> simp [hpq.symm]

lemma card_removeTwo {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α) (hpq : p ≠ q) :
    Fintype.card (RemoveTwo p q hpq) = Fintype.card α - 2 := by
  calc
    Fintype.card (RemoveTwo p q hpq) =
        Fintype.card {j : α // j ≠ p} - 1 := by
      rw [Fintype.card_subtype]
      rw [show ({x : {j : α // j ≠ p} | x ≠ ⟨q, hpq.symm⟩} :
          Finset {j : α // j ≠ p}) = Finset.univ.erase ⟨q, hpq.symm⟩ by
        ext x
        simp]
      simp [Finset.card_erase_of_mem]
    _ = (Fintype.card α - 1) - 1 := by
      congr 1
      rw [Fintype.card_subtype]
      rw [show ({x : α | x ≠ p} : Finset α) = Finset.univ.erase p by ext; simp]
      simp [Finset.card_erase_of_mem]
    _ = Fintype.card α - 2 := by omega

lemma sum_eq_removeTwo_add (α : Type*) [Fintype α] [DecidableEq α]
    (p q : α) (hpq : p ≠ q) (f : α → ℚ) :
    ∑ i, f i =
      (∑ i : RemoveTwo p q hpq, f i) + f p + f q := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f p]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun i : {j : α // j ≠ p} ↦ f i) ⟨q, hpq.symm⟩]
  ac_rfl

/-- A linear form with two specified nonzero coefficients is accepted on at
most three quarters of an arbitrary finite Boolean cube. -/
theorem card_linear_form_two_nonzero_le {α : Type*} [Fintype α] [DecidableEq α]
    (coeff : α → ℚ) (p q : α) (hpq : p ≠ q)
    (hp : coeff p ≠ 0) (hq : coeff q ≠ 0) :
    Fintype.card {x : α → Bool //
      IsZeroOrOne (∑ i, coeff i * boolRat (x i))} ≤
      3 * 2 ^ (Fintype.card α - 2) := by
  let e := cubeRemoveTwoEquiv p q hpq
  let offset : (RemoveTwo p q hpq → Bool) → ℚ := fun x ↦
    ∑ i : RemoveTwo p q hpq, coeff i * boolRat (x i)
  have hL : ∀ x : α → Bool,
      (∑ i, coeff i * boolRat (x i)) =
        offset (e x).1 + coeff p * boolRat (e x).2.1 +
          coeff q * boolRat (e x).2.2 := by
    intro x
    exact sum_eq_removeTwo_add α p q hpq
      (fun i ↦ coeff i * boolRat (x i))
  have h := card_accepted_of_equiv_two_bits e
    (fun x : α → Bool ↦ ∑ i, coeff i * boolRat (x i))
    offset (coeff p) (coeff q) hp hq hL
  simpa [Fintype.card_fun, Fintype.card_bool, card_removeTwo p q hpq] using h

/-- The indices left after deleting one distinguished coordinate. -/
abbrev RemoveOne {α : Type*} (p : α) [DecidableEq α] := {i : α // i ≠ p}

lemma card_removeOne {α : Type*} [Fintype α] [DecidableEq α] (p : α) :
    Fintype.card (RemoveOne p) = Fintype.card α - 1 := by
  rw [Fintype.card_subtype]
  rw [show ({x : α | x ≠ p} : Finset α) = Finset.univ.erase p by ext; simp]
  simp [Finset.card_erase_of_mem]

lemma accepted_single_bit_forces_false (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (b : Bool) (hb : IsZeroOrOne (a * boolRat b)) : b = false := by
  cases b
  · rfl
  · simp only [boolRat_true, mul_one, IsZeroOrOne] at hb
    exact (hb.elim ha0 ha1).elim

/-- If a one-coordinate form has coefficient different from both `0` and
`1`, exactly one of the two values of that coordinate can be accepted. -/
theorem card_single_coefficient_form_le {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    Fintype.card {x : α → Bool // IsZeroOrOne (a * boolRat (x p))} ≤
      2 ^ (Fintype.card α - 1) := by
  let forget : {x : α → Bool // IsZeroOrOne (a * boolRat (x p))} ↪
      (RemoveOne p → Bool) :=
    { toFun := fun x i ↦ (x : α → Bool) i
      inj' := by
        intro x y hxy
        apply Subtype.ext
        funext i
        by_cases hip : i = p
        · subst i
          rw [accepted_single_bit_forces_false a ha0 ha1 (x.val p) x.property,
            accepted_single_bit_forces_false a ha0 ha1 (y.val p) y.property]
        · exact congrFun hxy ⟨i, hip⟩ }
  calc
    Fintype.card {x : α → Bool // IsZeroOrOne (a * boolRat (x p))} ≤
        Fintype.card (RemoveOne p → Bool) := Fintype.card_le_of_embedding forget
    _ = 2 ^ (Fintype.card α - 1) := by
      rw [Fintype.card_fun, Fintype.card_bool, card_removeOne]

/-- A nonzero linear form which is not any coordinate projection is accepted
on at most three quarters of the Boolean cube. -/
theorem card_linear_form_noncoordinate_le {α : Type*} [Fintype α] [DecidableEq α]
    (coeff : α → ℚ) (hcard : 2 ≤ Fintype.card α)
    (hne : coeff ≠ 0)
    (hcoord : ∀ p, coeff ≠ fun i ↦ if p = i then 1 else 0) :
    Fintype.card {x : α → Bool //
      IsZeroOrOne (∑ i, coeff i * boolRat (x i))} ≤
      3 * 2 ^ (Fintype.card α - 2) := by
  have hex : ∃ p, coeff p ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    funext p
    exact h p
  obtain ⟨p, hp⟩ := hex
  by_cases htwo : ∃ q, q ≠ p ∧ coeff q ≠ 0
  · obtain ⟨q, hqp, hq⟩ := htwo
    exact card_linear_form_two_nonzero_le coeff p q hqp.symm hp hq
  · push Not at htwo
    have hz : ∀ q, q ≠ p → coeff q = 0 := htwo
    have hp1 : coeff p ≠ 1 := by
      intro hpone
      apply hcoord p
      funext i
      by_cases hpi : p = i
      · subst i
        simp [hpone]
      · simp [hpi, hz i (fun hip ↦ hpi hip.symm)]
    have hform : ∀ x : α → Bool,
        (∑ i, coeff i * boolRat (x i)) = coeff p * boolRat (x p) := by
      intro x
      rw [Fintype.sum_eq_add_sum_subtype_ne
        (fun i ↦ coeff i * boolRat (x i)) p]
      have hzero : (∑ i : {j : α // j ≠ p},
          coeff i * boolRat (x i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [hz i i.property]
      rw [hzero, add_zero]
    have hcardSingle := card_single_coefficient_form_le p (coeff p) hp hp1
    have heq :
        Fintype.card {x : α → Bool //
          IsZeroOrOne (∑ i, coeff i * boolRat (x i))} =
        Fintype.card {x : α → Bool // IsZeroOrOne (coeff p * boolRat (x p))} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight fun x ↦ by rw [hform x]
    rw [heq]
    refine hcardSingle.trans ?_
    have hsub : Fintype.card α - 1 = (Fintype.card α - 2) + 1 := by omega
    have hpow : 2 ^ (Fintype.card α - 1) =
        2 * 2 ^ (Fintype.card α - 2) := by
      rw [hsub, pow_succ]
      ac_rfl
    rw [hpow]
    exact Nat.mul_le_mul_right _ (by decide : 2 ≤ 3)

/-! ## Independent coordinate rows -/

/-- The rows of the `r × d` matrix whose columns are the vectors `b`. -/
def generatorRow {r d : ℕ} (b : Fin d → Fin r → ℚ) (i : Fin r) : Fin d → ℚ :=
  fun j ↦ b j i

/-- Nonzero, pairwise distinct coordinate functionals on the span generated
by `b`, expressed directly as a property of the generator matrix. -/
def GeneratorRowsDistinctNonzero {r d : ℕ} (b : Fin d → Fin r → ℚ) : Prop :=
  (∀ i, generatorRow b i ≠ 0) ∧ Function.Injective (generatorRow b)

/-- A linearly independent family of `d` columns has `d` linearly
independent coordinate rows. -/
theorem exists_independent_generator_rows {r d : ℕ}
    (b : Fin d → Fin r → ℚ) (hli : LinearIndependent ℚ b) :
    ∃ s : Fin d → Fin r, Function.Injective s ∧
      LinearIndependent ℚ (fun i ↦ generatorRow b (s i)) := by
  let A : Matrix (Fin r) (Fin d) ℚ := fun i j ↦ b j i
  have hcol : LinearIndependent ℚ A.col := by
    have heq : A.col = b := by
      funext j i
      rfl
    rw [heq]
    exact hli
  have hrowT : LinearIndependent ℚ A.transpose.row := by
    have heq : A.transpose.row = A.col := by
      funext j i
      rfl
    rw [heq]
    exact hcol
  have hrank : A.rank = d := by
    have h := hrowT.rank_matrix
    simpa using h
  have hfin : Module.finrank ℚ
      (Submodule.span ℚ (Set.range A.row)) = d := by
    rw [← A.rank_eq_finrank_span_row, hrank]
  have hex := Submodule.exists_fun_fin_finrank_span_eq
    ℚ (Set.range A.row)
  rw [hfin] at hex
  obtain ⟨f, hfmem, _hfspan, hfli⟩ := hex
  choose s hs using hfmem
  have hsf : (fun i ↦ generatorRow b (s i)) = f := by
    funext i j
    have hij := congrFun (hs i) j
    simpa [A, Matrix.row, generatorRow] using hij
  refine ⟨s, ?_, hsf.symm ▸ hfli⟩
  intro i j hij
  apply hfli.injective
  rw [← hs i, ← hs j, hij]

lemma exists_index_outside_injective_range {r d : ℕ}
    (s : Fin d → Fin r) (_hs : Function.Injective s) (hdr : d < r) :
    ∃ q : Fin r, ∀ i, s i ≠ q := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective s := fun q ↦ h q
  have hle := Fintype.card_le_of_surjective s hsurj
  have hle' : r ≤ d := by simpa using hle
  exact (Nat.not_le_of_gt hdr) hle'

/-! ## Coefficients of the extra coordinate functional -/

/-- Dot product with a fixed rational row, bundled as a linear map. -/
def rowLinear {d : ℕ} (a : Fin d → ℚ) : (Fin d → ℚ) →ₗ[ℚ] ℚ where
  toFun x := ∑ i, a i * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul]
    change (∑ i, a i * (c * x i)) = c * ∑ i, a i * x i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

@[simp] theorem rowLinear_apply {d : ℕ} (a x : Fin d → ℚ) :
    rowLinear a x = ∑ i, a i * x i := rfl

theorem rowLinear_injective {d : ℕ} : Function.Injective (@rowLinear d) := by
  intro a b hab
  funext i
  have h := LinearMap.congr_fun hab (fun j ↦ if i = j then 1 else 0)
  simpa [rowLinear] using h

/-- The `i`th coordinate projection as a rational linear map. -/
def coordinateLinear {d : ℕ} (i : Fin d) : (Fin d → ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.proj i

@[simp] theorem coordinateLinear_apply {d : ℕ} (i : Fin d) (x : Fin d → ℚ) :
    coordinateLinear i x = x i := rfl

/-- Coefficients of a functional in the standard basis. -/
def linearCoefficients {d : ℕ} (ell : (Fin d → ℚ) →ₗ[ℚ] ℚ) : Fin d → ℚ :=
  fun i ↦ ell (fun j ↦ if i = j then 1 else 0)

theorem linear_eq_sum_coefficients {d : ℕ}
    (ell : (Fin d → ℚ) →ₗ[ℚ] ℚ) (x : Fin d → ℚ) :
    ell x = ∑ i, linearCoefficients ell i * x i := by
  rw [LinearMap.pi_apply_eq_sum_univ]
  apply Finset.sum_congr rfl
  intro i hi
  simp [linearCoefficients, smul_eq_mul, mul_comm]

theorem linearCoefficients_injective {d : ℕ} :
    Function.Injective (@linearCoefficients d) := by
  intro ell psi h
  apply LinearMap.ext
  intro x
  rw [linear_eq_sum_coefficients, linear_eq_sum_coefficients, h]

@[simp] theorem linearCoefficients_coordinate {d : ℕ} (p : Fin d) :
    linearCoefficients (coordinateLinear p) =
      fun i ↦ if p = i then 1 else 0 := by
  funext i
  simp [linearCoefficients, coordinateLinear, eq_comm]

/-! ## Boolean points in a separating column span -/

/-- A Boolean vector regarded as a rational zero-one vector. -/
def ratVector {r : ℕ} (x : Fin r → Bool) : Fin r → ℚ := fun i ↦ boolRat (x i)

theorem ratVector_injective {r : ℕ} : Function.Injective (@ratVector r) := by
  intro x y h
  funext i
  exact boolRat_injective (congrFun h i)

/-- The two rational values `0,1` are equivalent to Boolean digits. -/
def boolRatEquiv : Bool ≃ {x : ℚ // IsZeroOrOne x} where
  toFun b := ⟨boolRat b, by cases b <;> simp [IsZeroOrOne]⟩
  invFun x := if x.1 = 1 then true else false
  left_inv b := by cases b <;> simp
  right_inv x := by
    apply Subtype.ext
    rcases x.2 with hx | hx
    · simp [hx]
    · simp [hx]

/-- Boolean encodings of the rational Boolean points in a generated span. -/
noncomputable def cubeSpanEquiv {r d : ℕ} (b : Fin d → Fin r → ℚ) :
    {x : Fin r → Bool // ratVector x ∈ Submodule.span ℚ (Set.range b)} ≃
      ↥((booleanVectors r).filter
        (fun v ↦ v ∈ Submodule.span ℚ (Set.range b))) where
  toFun x := ⟨ratVector x, by
    rw [Finset.mem_filter]
    exact ⟨mem_booleanVectors.mpr (fun i ↦ by
      cases hxi : x.val i <;> simp [ratVector, hxi]), x.property⟩⟩
  invFun v := ⟨fun i ↦ boolRatEquiv.symm
      ⟨v.val i, mem_booleanVectors.mp (Finset.mem_filter.mp v.property).1 i⟩, by
    have hv : ratVector (fun i ↦ boolRatEquiv.symm
        ⟨v.val i, mem_booleanVectors.mp (Finset.mem_filter.mp v.property).1 i⟩) = v.val := by
      funext i
      exact congrArg Subtype.val (boolRatEquiv.apply_symm_apply
        ⟨v.val i, mem_booleanVectors.mp (Finset.mem_filter.mp v.property).1 i⟩)
    rw [hv]
    exact (Finset.mem_filter.mp v.property).2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact boolRatEquiv.symm_apply_apply (x.val i)
  right_inv v := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (boolRatEquiv.apply_symm_apply
      ⟨v.val i, mem_booleanVectors.mp (Finset.mem_filter.mp v.property).1 i⟩)

lemma card_cubeSpan_eq_filter {r d : ℕ} (b : Fin d → Fin r → ℚ) :
    Fintype.card {x : Fin r → Bool //
      ratVector x ∈ Submodule.span ℚ (Set.range b)} =
      ((booleanVectors r).filter
        (fun v ↦ v ∈ Submodule.span ℚ (Set.range b))).card := by
  simpa using Fintype.card_congr (cubeSpanEquiv b)

/-- The sharp cube-intersection estimate for a span with nonzero distinct
coordinate rows. -/
theorem card_boolean_span_intersection_le {r d : ℕ}
    (hdr : d < r) (hd : 2 ≤ d)
    (b : Fin d → Fin r → ℚ) (hli : LinearIndependent ℚ b)
    (hrows : GeneratorRowsDistinctNonzero b) :
    ((booleanVectors r).filter
      (fun v ↦ v ∈ Submodule.span ℚ (Set.range b))).card ≤
      3 * 2 ^ (d - 2) := by
  obtain ⟨s, hs, hsli⟩ := exists_independent_generator_rows b hli
  obtain ⟨q, hq⟩ := exists_index_outside_injective_range s hs hdr
  let A : Matrix (Fin r) (Fin d) ℚ := fun i j ↦ b j i
  let B : Matrix (Fin d) (Fin d) ℚ := fun i j ↦ b j (s i)
  have hBrow : LinearIndependent ℚ B.row := by
    have heq : B.row = fun i ↦ generatorRow b (s i) := by
      funext i j
      rfl
    rw [heq]
    exact hsli
  have hBcol : LinearIndependent ℚ B.col := by
    rw [Matrix.linearIndependent_col_iff_row]
    exact hBrow
  have hBinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff.mpr hBcol
  let E : (Fin d → ℚ) ≃ₗ[ℚ] (Fin d → ℚ) :=
    LinearEquiv.ofInjectiveEndo B.mulVecLin hBinj
  let ell : (Fin d → ℚ) →ₗ[ℚ] ℚ :=
    (rowLinear (generatorRow b q)).comp E.symm.toLinearMap
  let coeff : Fin d → ℚ := linearCoefficients ell
  have hell_ne : ell ≠ 0 := by
    intro hell
    apply hrows.1 q
    apply rowLinear_injective
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hell (E x)
    simpa [ell, E] using hx
  have hcoeff_ne : coeff ≠ 0 := by
    intro hc
    apply hell_ne
    apply linearCoefficients_injective
    change coeff = linearCoefficients 0
    rw [hc]
    funext i
    simp [linearCoefficients]
  have hcoeff_coord : ∀ p, coeff ≠ fun i ↦ if p = i then 1 else 0 := by
    intro p hcp
    have hellp : ell = coordinateLinear p := by
      apply linearCoefficients_injective
      simpa [coeff] using hcp
    have hroweq : generatorRow b q = generatorRow b (s p) := by
      apply rowLinear_injective
      apply LinearMap.ext
      intro x
      calc
        rowLinear (generatorRow b q) x = ell (E x) := by simp [ell]
        _ = coordinateLinear p (E x) := LinearMap.congr_fun hellp (E x)
        _ = (E x) p := rfl
        _ = B.mulVec x p := rfl
        _ = rowLinear (generatorRow b (s p)) x := by
          rfl
    exact hq p (hrows.2 hroweq).symm
  have haccepted := card_linear_form_noncoordinate_le coeff
    (by simpa using hd) hcoeff_ne hcoeff_coord
  have hAcol : A.col = b := by
    funext j i
    rfl
  have selected_injective : Set.InjOn
      (fun x : Fin r → Bool ↦ fun i ↦ x (s i))
      {x | ratVector x ∈ Submodule.span ℚ (Set.range b)} := by
    intro x hx y hy hxy
    have hxrange : ratVector x ∈ LinearMap.range A.mulVecLin := by
      rw [Matrix.range_mulVecLin, hAcol]
      exact hx
    have hyrange : ratVector y ∈ LinearMap.range A.mulVecLin := by
      rw [Matrix.range_mulVecLin, hAcol]
      exact hy
    obtain ⟨cx, hcx⟩ := hxrange
    obtain ⟨cy, hcy⟩ := hyrange
    have hB : B.mulVec cx = B.mulVec cy := by
      funext i
      have hx_i := congrFun hcx (s i)
      have hy_i := congrFun hcy (s i)
      simp only [Matrix.mulVecLin_apply] at hx_i hy_i
      have hbit := congrFun hxy i
      calc
        B.mulVec cx i = ratVector x (s i) := by
          simpa [A, B, Matrix.mulVec] using hx_i
        _ = ratVector y (s i) := by simp [ratVector, hbit]
        _ = B.mulVec cy i := by
          simpa [A, B, Matrix.mulVec] using hy_i.symm
    have hc : cx = cy := hBinj hB
    apply ratVector_injective
    rw [← hcx, ← hcy, hc]
  let inclusion : {x : Fin r → Bool //
      ratVector x ∈ Submodule.span ℚ (Set.range b)} ↪
      {y : Fin d → Bool //
        IsZeroOrOne (∑ i, coeff i * boolRat (y i))} :=
    {
    toFun x := ⟨fun i ↦ x.val (s i), by
      have hxrange : ratVector x.val ∈ LinearMap.range A.mulVecLin := by
        rw [Matrix.range_mulVecLin, hAcol]
        exact x.property
      obtain ⟨c, hc⟩ := hxrange
      let yq : Fin d → ℚ := fun i ↦ boolRat (x.val (s i))
      have hEy : E c = yq := by
        have hEc : E c = B.mulVec c := rfl
        rw [hEc]
        funext i
        have hi := congrFun hc (s i)
        simp only [Matrix.mulVecLin_apply] at hi
        simpa [A, B, Matrix.mulVec, ratVector, yq] using hi
      have hell : ell yq = boolRat (x.val q) := by
        calc
          ell yq = rowLinear (generatorRow b q) c := by
            rw [← hEy]
            simp [ell]
          _ = A.mulVec c q := by rfl
          _ = ratVector x.val q := congrFun hc q
          _ = boolRat (x.val q) := rfl
      rw [← linear_eq_sum_coefficients ell yq]
      change IsZeroOrOne (ell yq)
      rw [hell]
      cases (x.val q) <;> simp [IsZeroOrOne]
      ⟩
    inj' := by
      intro x y hxy
      apply Subtype.ext
      exact selected_injective x.property y.property
        (congrArg Subtype.val hxy) }
  rw [← card_cubeSpan_eq_filter b]
  simpa using (Fintype.card_le_of_embedding inclusion).trans haccepted

/-! ## The refined finite union -/

lemma coordinate_zero_on_span_of_generatorRow_eq_zero {r d : ℕ}
    (b : Fin d → Fin r → ℚ) (i : Fin r)
    (hi : generatorRow b i = 0) {v : Fin r → ℚ}
    (hv : v ∈ Submodule.span ℚ (Set.range b)) : v i = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact congrFun hi j
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma coordinates_equal_on_span_of_generatorRows_eq {r d : ℕ}
    (b : Fin d → Fin r → ℚ) (i j : Fin r)
    (hij : generatorRow b i = generatorRow b j) {v : Fin r → ℚ}
    (hv : v ∈ Submodule.span ℚ (Set.range b)) : v i = v j := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨t, rfl⟩ := hv
      exact congrFun hij t
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/-- Ordered Boolean generator tuples which are linearly independent and
whose coordinate rows are nonzero and pairwise distinct. -/
noncomputable def sharpGenerators (r d : ℕ) :
    Finset (Fin d → Fin r → ℚ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin d ↦ booleanVectors r)).filter
    (fun b ↦ LinearIndependent ℚ b ∧ GeneratorRowsDistinctNonzero b)

@[simp] lemma mem_sharpGenerators {r d : ℕ} {b : Fin d → Fin r → ℚ} :
    b ∈ sharpGenerators r d ↔
      (∀ j, b j ∈ booleanVectors r) ∧ LinearIndependent ℚ b ∧
        GeneratorRowsDistinctNonzero b := by
  classical
  simp [sharpGenerators]

lemma card_sharpGenerators_le (r d : ℕ) :
    (sharpGenerators r d).card ≤ 2 ^ (r * d) := by
  classical
  refine (Finset.card_filter_le _ _).trans ?_
  simp [pow_mul]

/-- Boolean column families lying in the span of one sharp generator tuple. -/
noncomputable def sharpColumnFamilies (r d k : ℕ) :
    Finset (Fin k → Fin r → ℚ) := by
  classical
  exact (sharpGenerators r d).biUnion fun b ↦
    Fintype.piFinset (fun _ : Fin k ↦
      (booleanVectors r).filter
        (fun v ↦ v ∈ Submodule.span ℚ (Set.range b)))

@[simp] lemma mem_sharpColumnFamilies {r d k : ℕ}
    {c : Fin k → Fin r → ℚ} :
    c ∈ sharpColumnFamilies r d k ↔
      ∃ b ∈ sharpGenerators r d,
        ∀ j, c j ∈ booleanVectors r ∧
          c j ∈ Submodule.span ℚ (Set.range b) := by
  classical
  simp [sharpColumnFamilies]

lemma card_sharpColumnFamilies_le (r d k : ℕ) (hdr : d < r) (hd : 2 ≤ d) :
    (sharpColumnFamilies r d k).card ≤
      2 ^ (r * d) * (3 * 2 ^ (d - 2)) ^ k := by
  classical
  refine (Finset.card_biUnion_le_card_mul
    (sharpGenerators r d)
    (fun b ↦ Fintype.piFinset (fun _ : Fin k ↦
      (booleanVectors r).filter
        (fun v ↦ v ∈ Submodule.span ℚ (Set.range b))))
    ((3 * 2 ^ (d - 2)) ^ k) ?_).trans ?_
  · intro b hb
    rw [mem_sharpGenerators] at hb
    simpa using Nat.pow_le_pow_left
      (card_boolean_span_intersection_le hdr hd b hb.2.1 hb.2.2) k
  · exact Nat.mul_le_mul_right _ (card_sharpGenerators_le r d)

/-- Matrix version of `sharpColumnFamilies`. -/
noncomputable def sharpLowRankMatrices (r d k : ℕ) :
    Finset (Matrix (Fin r) (Fin k) ℚ) := by
  classical
  exact (sharpColumnFamilies r d k).map matrixColumnsEquiv.symm.toEmbedding

@[simp] lemma mem_sharpLowRankMatrices {r d k : ℕ}
    {M : Matrix (Fin r) (Fin k) ℚ} :
    M ∈ sharpLowRankMatrices r d k ↔
      (fun j i ↦ M i j) ∈ sharpColumnFamilies r d k := by
  classical
  rw [sharpLowRankMatrices, Finset.mem_map]
  constructor
  · rintro ⟨c, hc, hcm⟩
    have hmc : matrixColumnsEquiv M = c := by
      apply matrixColumnsEquiv.symm.injective
      simpa using hcm.symm
    change matrixColumnsEquiv M ∈ sharpColumnFamilies r d k
    rw [hmc]
    exact hc
  · intro hc
    refine ⟨matrixColumnsEquiv M, ?_, ?_⟩
    · exact hc
    · exact matrixColumnsEquiv.symm_apply_apply M

@[simp] lemma card_sharpLowRankMatrices (r d k : ℕ) :
    (sharpLowRankMatrices r d k).card = (sharpColumnFamilies r d k).card := by
  classical
  simp [sharpLowRankMatrices]

/-- Every ordered distinct/nonzero-row rank-`d` Boolean matrix is captured by
the refined union: choose a Boolean basis from its columns. -/
lemma orderedDistinctRowLowRankMatrices_subset_sharp (r d k : ℕ) :
    orderedDistinctRowLowRankMatrices r d k ⊆ sharpLowRankMatrices r d k := by
  classical
  intro M hM
  rw [orderedDistinctRowLowRankMatrices, Finset.mem_filter,
    mem_booleanMatricesOfRank] at hM
  let c : Fin k → Fin r → ℚ := fun j i ↦ M i j
  have hrank : Module.finrank ℚ (Submodule.span ℚ (Set.range c)) = d := by
    have h := hM.1.2
    change Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun j i ↦ M i j))) = d at h
    simpa only [c] using h
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range c)
  rw [hrank] at hex
  obtain ⟨b, hbmem, hspan, hbli⟩ := hex
  have hbbool : ∀ i, b i ∈ booleanVectors r := by
    intro i
    obtain ⟨j, hj⟩ := hbmem i
    rw [← hj]
    exact hM.1.1 j
  have hbrows : GeneratorRowsDistinctNonzero b := by
    constructor
    · intro i hi
      obtain ⟨j, hne⟩ := hM.2.1 i
      apply hne
      apply coordinate_zero_on_span_of_generatorRow_eq_zero b i hi
      rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self j)
    · intro i j hij
      apply hM.2.2
      funext t
      apply coordinates_equal_on_span_of_generatorRows_eq b i j hij
      rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self t)
  rw [mem_sharpLowRankMatrices, mem_sharpColumnFamilies]
  refine ⟨b, ?_, ?_⟩
  · rw [mem_sharpGenerators]
    exact ⟨hbbool, hbli, hbrows⟩
  · intro j
    exact ⟨hM.1.1 j, hspan ▸ Submodule.subset_span (Set.mem_range_self j)⟩

/-- Sharp count in the substantive range `2 ≤ d < r`. -/
theorem card_orderedDistinctRowLowRankMatrices_le_sharp_of_two_le
    (r d k : ℕ) (hdr : d < r) (hd : 2 ≤ d) :
    (orderedDistinctRowLowRankMatrices r d k).card ≤
      2 ^ (r * r) * (3 * 2 ^ (d - 2)) ^ k := by
  calc
    (orderedDistinctRowLowRankMatrices r d k).card ≤
        (sharpLowRankMatrices r d k).card :=
      Finset.card_le_card (orderedDistinctRowLowRankMatrices_subset_sharp r d k)
    _ = (sharpColumnFamilies r d k).card := card_sharpLowRankMatrices r d k
    _ ≤ 2 ^ (r * d) * (3 * 2 ^ (d - 2)) ^ k :=
      card_sharpColumnFamilies_le r d k hdr hd
    _ ≤ 2 ^ (r * r) * (3 * 2 ^ (d - 2)) ^ k := by
      exact Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by decide : 0 < 2)
          (Nat.mul_le_mul_left r (Nat.le_of_lt hdr)))

/-- In ranks zero and one, fewer rows than ambient coordinates cannot be
simultaneously nonzero and pairwise distinct. -/
lemma sharpGenerators_eq_empty_of_lt_two
    (r d : ℕ) (hdr : d < r) (hd : d < 2) :
    sharpGenerators r d = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  rw [mem_sharpGenerators] at hb
  have hd_cases : d = 0 ∨ d = 1 := by omega
  rcases hd_cases with rfl | rfl
  · let i : Fin r := ⟨0, by omega⟩
    apply hb.2.2.1 i
    funext j
    exact Fin.elim0 j
  · let i0 : Fin r := ⟨0, by omega⟩
    let i1 : Fin r := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [i0, i1] at hv
    have hvalue (i : Fin r) : b (0 : Fin 1) i = 1 := by
      have hbit := mem_booleanVectors.mp (hb.1 (0 : Fin 1)) i
      rcases hbit with hzero | hone
      · exfalso
        apply hb.2.2.1 i
        funext j
        have hj : j = 0 := Fin.eq_zero j
        subst j
        exact hzero
      · exact hone
    have hrow : generatorRow b i0 = generatorRow b i1 := by
      funext j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rw [generatorRow, generatorRow, hvalue i0, hvalue i1]
    exact hi01 (hb.2.2.2 hrow)

/-- The requested sharp bound, including the vacuous ranks `d = 0,1`. -/
theorem card_orderedDistinctRowLowRankMatrices_le_sharp
    (r d k : ℕ) (hdr : d < r) :
    (orderedDistinctRowLowRankMatrices r d k).card ≤
      2 ^ (r * r) * (3 * 2 ^ (d - 2)) ^ k := by
  by_cases hd : 2 ≤ d
  · exact card_orderedDistinctRowLowRankMatrices_le_sharp_of_two_le r d k hdr hd
  · have hdlt : d < 2 := by omega
    have hgen := sharpGenerators_eq_empty_of_lt_two r d hdr hdlt
    have hcol : sharpColumnFamilies r d k = ∅ := by
      simp [sharpColumnFamilies, hgen]
    have hmat : sharpLowRankMatrices r d k = ∅ := by
      simp [sharpLowRankMatrices, hcol]
    have hzero : (orderedDistinctRowLowRankMatrices r d k).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro M hM
      have hs := orderedDistinctRowLowRankMatrices_subset_sharp r d k hM
      rw [hmat] at hs
      exact Finset.notMem_empty M hs
    rw [hzero]
    exact Nat.zero_le _

end Erdos543

import Mathlib
import ErdosProblems.Erdos697.Erdos697FiniteModel
import ErdosProblems.Erdos697.Erdos697Bernoulli

/-!
# CRT product model for Erdős 697

The zero coordinates of a uniformly sampled product of residue rings have
the same product law as independent divisibility indicators.  The exact
fiber count below is the finite combinatorial identity used for the moment
and conditional-distribution estimates.
-/

open scoped BigOperators

namespace Erdos697.CRTModel

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (a : ι → ℕ) [(i : ι) → NeZero (a i)]

def zeroSet (x : (i : ι) → ZMod (a i)) : Finset ι :=
  Finset.univ.filter fun i => x i = 0

@[simp] theorem mem_zeroSet (x : (i : ι) → ZMod (a i)) (i : ι) :
    i ∈ zeroSet a x ↔ x i = 0 := by
  simp [zeroSet]

private abbrev exactZeroFiber (S : Finset ι) :=
  {x : (i : ι) → ZMod (a i) // ∀ i, x i = 0 ↔ i ∈ S}

private abbrev nonzeroCoordinates (S : Finset ι) :=
  (i : {i : ι // i ∉ S}) → {z : ZMod (a i.1) // z ≠ 0}

private def exactZeroFiberEquiv (S : Finset ι) :
    exactZeroFiber a S ≃ nonzeroCoordinates a S where
  toFun x i := ⟨x.1 i.1, by
    intro hzero
    exact i.2 ((x.2 i.1).mp hzero)⟩
  invFun y := ⟨fun i => if hi : i ∈ S then 0 else y ⟨i, hi⟩, by
    intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp only [hi, ↓reduceDIte, iff_false]
      exact (y ⟨i, hi⟩).2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · simp [hi, (x.2 i).mpr hi]
    · simp [hi]
  right_inv y := by
    funext i
    simp [i.2]

private theorem card_nonzero_zmod (n : ℕ) [NeZero n] :
    Fintype.card {z : ZMod n // z ≠ 0} = n - 1 := by
  rw [Fintype.card_subtype_compl (fun z : ZMod n => z = 0)]
  simp [ZMod.card]

private theorem card_nonzeroCoordinates (S : Finset ι) :
    Fintype.card (nonzeroCoordinates a S) =
      ∏ i : {i : ι // i ∉ S}, (a i.1 - 1) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact card_nonzero_zmod (a i.1)

private theorem card_exactZeroFiber (S : Finset ι) :
    Fintype.card (exactZeroFiber a S) =
      ∏ i : {i : ι // i ∉ S}, (a i.1 - 1) := by
  rw [Fintype.card_congr (exactZeroFiberEquiv a S)]
  exact card_nonzeroCoordinates a S

private def zeroSetFiberEquiv (S : Finset ι) :
    {x : (i : ι) → ZMod (a i) // zeroSet a x = S} ≃ exactZeroFiber a S where
  toFun x := ⟨x.1, fun i => by
    rw [← mem_zeroSet a x.1 i, x.2]⟩
  invFun x := ⟨x.1, by
    ext i
    rw [mem_zeroSet]
    exact x.2 i⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

/-- Exact count of coordinate vectors with a prescribed zero set. -/
theorem card_filter_zeroSet_eq (S : Finset ι) :
    ((Finset.univ : Finset ((i : ι) → ZMod (a i))).filter
      (fun x => zeroSet a x = S)).card =
      ∏ i : {i : ι // i ∉ S}, (a i.1 - 1) := by
  rw [← Fintype.card_subtype (fun x : (i : ι) → ZMod (a i) =>
    zeroSet a x = S)]
  rw [Fintype.card_congr (zeroSetFiberEquiv a S)]
  exact card_exactZeroFiber a S

/-- Exact law of the zero-coordinate set under the uniform product model. -/
theorem card_filter_zeroSet_good (Good : Finset ι → Prop)
    [DecidablePred Good] :
    ((Finset.univ : Finset ((i : ι) → ZMod (a i))).filter
      (fun x => Good (zeroSet a x))).card =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        ∏ i : {i : ι // i ∉ S}, (a i.1 - 1) := by
  classical
  let s := (Finset.univ : Finset ((i : ι) → ZMod (a i))).filter
    (fun x => Good (zeroSet a x))
  let t := (Finset.univ : Finset (Finset ι)).filter Good
  have hmap : (s : Set ((i : ι) → ZMod (a i))).MapsTo (zeroSet a) t := by
    intro x hx
    simpa [s, t] using hx
  change s.card = ∑ S ∈ t, _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro S hS
  have hGood : Good S := (Finset.mem_filter.mp hS).2
  have hfiber :
      (s.filter fun x => zeroSet a x = S) =
        (Finset.univ.filter fun x => zeroSet a x = S) := by
    ext x
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hx => hx.2
    · intro hx
      exact ⟨hx ▸ hGood, hx⟩
  rw [hfiber]
  exact card_filter_zeroSet_eq a S

private theorem normalized_exactZeroFiber_eq_weight (S : Finset ι) :
    (∏ i : {i : ι // i ∉ S}, ((a i.1 - 1 : ℕ) : ℝ)) /
        (∏ i, (a i : ℝ)) =
      Bernoulli.weight (Finset.univ : Finset ι)
        (fun i => 1 / (a i : ℝ)) S := by
  classical
  unfold Bernoulli.weight
  have hsubprod :
      (∏ i : {i : ι // i ∉ S}, ((a i.1 - 1 : ℕ) : ℝ)) =
        ∏ i ∈ (Finset.univ : Finset ι) \ S, ((a i : ℝ) - 1) := by
    rw [Finset.prod_subtype (s := (Finset.univ : Finset ι) \ S)]
    · apply Finset.prod_congr rfl
      intro i _
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (a i)))]
      norm_num
    · intro i
      simp
  rw [hsubprod]
  have hSsubset : S ⊆ (Finset.univ : Finset ι) :=
    fun _ _ => Finset.mem_univ _
  have hdisj : Disjoint S ((Finset.univ : Finset ι) \ S) :=
    Finset.disjoint_sdiff
  have hunion : S ∪ ((Finset.univ : Finset ι) \ S) = Finset.univ :=
    Finset.union_sdiff_of_subset hSsubset
  have hden_split :
      (∏ i, (a i : ℝ)) =
        (∏ i ∈ S, (a i : ℝ)) *
          ∏ i ∈ (Finset.univ : Finset ι) \ S, (a i : ℝ) := by
    rw [← Finset.prod_union hdisj, hunion]
  have hfirst :
      (∏ i ∈ S, 1 / (a i : ℝ)) =
        1 / (∏ i ∈ S, (a i : ℝ)) := by
    simp only [one_div, Finset.prod_inv_distrib]
  have hsecond :
      (∏ i ∈ (Finset.univ : Finset ι) \ S,
          (1 - 1 / (a i : ℝ))) =
        (∏ i ∈ (Finset.univ : Finset ι) \ S, ((a i : ℝ) - 1)) /
          (∏ i ∈ (Finset.univ : Finset ι) \ S, (a i : ℝ)) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hai : (a i : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne (a i))
    field_simp
  rw [hfirst, hsecond, hden_split]
  have hAS : (∏ i ∈ S, (a i : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast (NeZero.ne (a i))
  have hAC :
      (∏ i ∈ (Finset.univ : Finset ι) \ S, (a i : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast (NeZero.ne (a i))
  field_simp

/-- The exact zero-coordinate count, divided by the size of the product
ring, is the independent Bernoulli law with success probabilities `1/aᵢ`. -/
theorem card_filter_zeroSet_good_div_eq_bernoulli
    (Good : Finset ι → Prop) [DecidablePred Good] :
    (((Finset.univ : Finset ((i : ι) → ZMod (a i))).filter
        (fun x => Good (zeroSet a x))).card : ℝ) /
        (∏ i, (a i : ℝ)) =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        Bernoulli.weight (Finset.univ : Finset ι)
          (fun i => 1 / (a i : ℝ)) S := by
  rw [card_filter_zeroSet_good]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  exact normalized_exactZeroFiber_eq_weight a S

private theorem card_filter_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : α → Prop) [DecidablePred P] :
    ((Finset.univ : Finset α).filter P).card =
      ((Finset.univ : Finset β).filter (fun y => P (e.symm y))).card := by
  let E : {x : α // P x} ≃ {y : β // P (e.symm y)} :=
    { toFun := fun x => ⟨e x.1, by simpa using x.2⟩
      invFun := fun y => ⟨e.symm y.1, y.2⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp }
  rw [← Fintype.card_subtype P,
    ← Fintype.card_subtype (fun y : β => P (e.symm y))]
  exact Fintype.card_congr E

/-- The same exact law, expressed on the single CRT residue ring. -/
theorem card_filter_crt_zeroSet_good
    [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (Good : Finset ι → Prop) [DecidablePred Good] :
    ((Finset.univ : Finset (ZMod (∏ i, a i))).filter
      (fun z => Good (zeroSet a (ZMod.prodEquivPi a hcoprime z)))).card =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        ∏ i : {i : ι // i ∉ S}, (a i.1 - 1) := by
  let e := (ZMod.prodEquivPi a hcoprime).toEquiv
  calc
    ((Finset.univ : Finset (ZMod (∏ i, a i))).filter
        (fun z => Good (zeroSet a (e z)))).card =
      ((Finset.univ : Finset ((i : ι) → ZMod (a i))).filter
        (fun x => Good (zeroSet a x))).card := by
          simpa [e] using card_filter_equiv e
            (fun z => Good (zeroSet a (e z)))
    _ = _ := card_filter_zeroSet_good a Good

/-- Natural-number sampling of a CRT zero-pattern has exactly the same
density as the corresponding independent Bernoulli event. -/
theorem crt_zeroSet_good_hasDensity
    [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (Good : Finset ι → Prop) [DecidablePred Good] :
    {n : ℕ | Good
        (zeroSet a
          (ZMod.prodEquivPi a hcoprime (n : ZMod (∏ i, a i))))}.HasDensity
      (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter Good,
        Bernoulli.weight (Finset.univ : Finset ι)
          (fun i => 1 / (a i : ℝ)) S) := by
  let q := ∏ i, a i
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hbase := FiniteModel.zmodPredicate_hasDensity hq
    (fun z : ZMod q => Good
      (zeroSet a (ZMod.prodEquivPi a hcoprime z)))
  convert hbase using 1
  rw [card_filter_crt_zeroSet_good a hcoprime]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  simpa [q] using (normalized_exactZeroFiber_eq_weight a S).symm

end

end Erdos697.CRTModel

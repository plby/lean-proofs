import ErdosProblems.Erdos965.Countability
import ErdosProblems.Erdos965.CriticalPair

open Function Set

universe u

namespace Erdos965

variable {ι : Type u}

/-! ## Countable exceptional prefix fibres -/

/-- The first `n` bits of the rational-cut code of a Hamel index. -/
noncomputable def codePrefix (n : ℕ) (x : HamelIndex) : Fin n → Bool :=
  fun i ↦ binaryCode x i

/-- Points which belong to a countable relative prefix fibre at some finite
depth.  There are only countably many depths and finitely many prefixes at
each depth, so this is a countable exceptional set. -/
def badPrefixPoints (p : ι → HamelIndex) (I : Set ι) : Set ι :=
  {x ∈ I | ∃ n, {y ∈ I | codePrefix n (p y) = codePrefix n (p x)}.Countable}

theorem badPrefixPoints_countable (p : ι → HamelIndex) (I : Set ι) :
    (badPrefixPoints p I).Countable := by
  classical
  refine (Set.countable_iUnion fun n ↦
    countable_union_of_countable_fibers
      (fun x ↦ codePrefix n (p x)) I).mono ?_
  rintro x ⟨hxI, n, hn⟩
  exact Set.mem_iUnion.2 ⟨n, hxI, hn⟩

/-- A point outside `badPrefixPoints` has an uncountable relative prefix
fibre at every finite depth. -/
theorem prefix_fiber_uncountable_of_not_bad (p : ι → HamelIndex) (I : Set ι)
    {x : ι} (hxI : x ∈ I) (hx : x ∉ badPrefixPoints p I) (n : ℕ) :
    ¬ {y ∈ I | codePrefix n (p y) = codePrefix n (p x)}.Countable := by
  intro h
  exact hx ⟨hxI, n, h⟩

/-! ## Prefixes determine the split level and ordinary orientation -/

/-- If `x` and `y` have the same length-`N+1` prefixes as two distinct
points `a` and `b`, where `N` is the first difference of `a` and `b`, then
`N` is also the first difference of `x` and `y`. -/
theorem firstDiff_eq_of_codePrefix_succ_eq {x y a b : HamelIndex}
    (hab : a ≠ b)
    (hx : codePrefix (firstDiff a b + 1) x = codePrefix (firstDiff a b + 1) a)
    (hy : codePrefix (firstDiff a b + 1) y = codePrefix (firstDiff a b + 1) b) :
    firstDiff x y = firstDiff a b := by
  let N := firstDiff a b
  have hxN : binaryCode x N = binaryCode a N :=
    congrFun hx ⟨N, by omega⟩
  have hyN : binaryCode y N = binaryCode b N :=
    congrFun hy ⟨N, by omega⟩
  have habN : binaryCode a N ≠ binaryCode b N := by
    simpa only [N] using binaryCode_apply_firstDiff_ne hab
  have hxyN : binaryCode x N ≠ binaryCode y N := by
    intro h
    exact habN (hxN.symm.trans (h.trans hyN))
  have hcodeNe : binaryCode x ≠ binaryCode y := by
    intro h
    exact hxyN (congrFun h N)
  have hge : N ≤ firstDiff x y := by
    rw [firstDiff]
    refine (PiNat.mem_cylinder_iff_le_firstDiff hcodeNe N).1 ?_
    intro i hi
    have hxi : binaryCode x i = binaryCode a i :=
      congrFun hx ⟨i, by omega⟩
    have hyi : binaryCode y i = binaryCode b i :=
      congrFun hy ⟨i, by omega⟩
    calc
      binaryCode x i = binaryCode a i := hxi
      _ = binaryCode b i := binaryCode_apply_eq_of_lt_firstDiff hi
      _ = binaryCode y i := hyi.symm
  have hle : firstDiff x y ≤ N := by
    by_contra h
    exact hxyN (binaryCode_apply_eq_of_lt_firstDiff (Nat.lt_of_not_ge h))
  exact le_antisymm hle hge

/-- The same prefix hypotheses also preserve ordinary orientation. -/
theorem lt_of_codePrefix_succ_eq_of_lt {x y a b : HamelIndex} (hab : a < b)
    (hx : codePrefix (firstDiff a b + 1) x = codePrefix (firstDiff a b + 1) a)
    (hy : codePrefix (firstDiff a b + 1) y = codePrefix (firstDiff a b + 1) b) :
    x < y := by
  let N := firstDiff a b
  have hxN : binaryCode x N = binaryCode a N :=
    congrFun hx ⟨N, by omega⟩
  have hyN : binaryCode y N = binaryCode b N :=
    congrFun hy ⟨N, by omega⟩
  have habBits : binaryCode a N = false ∧ binaryCode b N = true := by
    simpa only [N] using binaryCode_firstDiff_of_lt hab
  have hxBit : binaryCode x N = false := hxN.trans habBits.1
  have hyBit : binaryCode y N = true := hyN.trans habBits.2
  have hxLe : (x : ℝ) ≤ ((ratEnum N : ℚ) : ℝ) := by
    have : ¬ (((ratEnum N : ℚ) : ℝ) < (x : ℝ)) := by
      change decide (((ratEnum N : ℚ) : ℝ) < (x : ℝ)) = false at hxBit
      exact of_decide_eq_false hxBit
    exact le_of_not_gt this
  have hyLt : (((ratEnum N : ℚ) : ℝ) < (y : ℝ)) := by
    change decide (((ratEnum N : ℚ) : ℝ) < (y : ℝ)) = true at hyBit
    exact of_decide_eq_true hyBit
  exact hxLe.trans_lt hyLt

/-! ## The uncountable binary-cylinder split -/

/-- Two uncountable subfamilies on which `p` is injective can be thinned to
uncountable subfamilies separated by one fixed binary split.  Across the two
subfamilies the first-difference level is constant and the ordinary order has
one fixed orientation.

This is the form needed when identifying the critical pair in a structured
union of finite supports. -/
theorem uncountable_cylinder_split (p : ι → HamelIndex) {D U V : Set ι}
    (hp : InjOn p D) (hUD : U ⊆ D) (hVD : V ⊆ D)
    (hU : ¬ U.Countable) (hV : ¬ V.Countable) :
    ∃ (U' V' : Set ι) (N : ℕ),
      U' ⊆ U ∧ V' ⊆ V ∧ ¬ U'.Countable ∧ ¬ V'.Countable ∧
        (∀ u ∈ U', ∀ v ∈ V', firstDiff (p u) (p v) = N) ∧
        ((∀ u ∈ U', ∀ v ∈ V', p u < p v) ∨
          ∀ u ∈ U', ∀ v ∈ V', p v < p u) := by
  classical
  let BU := badPrefixPoints p U
  let BV := badPrefixPoints p V
  have hBU : BU.Countable := badPrefixPoints_countable p U
  have hBV : BV.Countable := badPrefixPoints_countable p V
  obtain ⟨u₀, hu₀U, hu₀good⟩ :=
    exists_mem_not_mem_of_uncountable_of_countable hU hBU
  obtain ⟨v₀, hv₀V, hv₀good⟩ :=
    exists_mem_not_mem_of_uncountable_of_countable hV
      (hBV.union (Set.countable_singleton u₀))
  have hv₀BV : v₀ ∉ BV := by
    intro hv
    exact hv₀good (Or.inl hv)
  have hv₀ne : v₀ ≠ u₀ := by
    intro h
    exact hv₀good (Or.inr h)
  have hpne : p u₀ ≠ p v₀ := by
    intro h
    exact hv₀ne (hp (hVD hv₀V) (hUD hu₀U) h.symm)
  let N := firstDiff (p u₀) (p v₀)
  let U' : Set ι :=
    {u ∈ U | codePrefix (N + 1) (p u) = codePrefix (N + 1) (p u₀)}
  let V' : Set ι :=
    {v ∈ V | codePrefix (N + 1) (p v) = codePrefix (N + 1) (p v₀)}
  have hU'sub : U' ⊆ U := fun _ h ↦ h.1
  have hV'sub : V' ⊆ V := fun _ h ↦ h.1
  have hU' : ¬ U'.Countable := by
    simpa only [U', N, BU] using
      prefix_fiber_uncountable_of_not_bad p U hu₀U hu₀good (N + 1)
  have hV' : ¬ V'.Countable := by
    simpa only [V', N, BV] using
      prefix_fiber_uncountable_of_not_bad p V hv₀V hv₀BV (N + 1)
  have hdiff : ∀ u ∈ U', ∀ v ∈ V', firstDiff (p u) (p v) = N := by
    intro u hu v hv
    simpa only [N] using
      firstDiff_eq_of_codePrefix_succ_eq hpne hu.2 hv.2
  refine ⟨U', V', N, hU'sub, hV'sub, hU', hV', hdiff, ?_⟩
  rcases lt_or_gt_of_ne hpne with huv | hvu
  · exact Or.inl fun u hu v hv ↦ by
      exact lt_of_codePrefix_succ_eq_of_lt huv hu.2 hv.2
  · exact Or.inr fun u hu v hv ↦ by
      have hvPrefix :
          codePrefix (firstDiff (p v₀) (p u₀) + 1) (p v) =
            codePrefix (firstDiff (p v₀) (p u₀) + 1) (p v₀) := by
        rw [firstDiff_comm (p v₀) (p u₀)]
        simpa only [N] using hv.2
      have huPrefix :
          codePrefix (firstDiff (p v₀) (p u₀) + 1) (p u) =
            codePrefix (firstDiff (p v₀) (p u₀) + 1) (p u₀) := by
        rw [firstDiff_comm (p v₀) (p u₀)]
        simpa only [N] using hu.2
      exact lt_of_codePrefix_succ_eq_of_lt hvu hvPrefix huPrefix

end Erdos965

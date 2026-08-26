import ErdosProblems.Erdos591.ExactLevels
import ErdosProblems.Erdos591.LexFiberBound

open Set Ordinal

namespace Erdos591.Negative.Exact.Levels

open LexFiberBound

/-!
Large-level extraction with an explicit ordinal margin.  The argument
bounds thinnings by their ordered child sets and does not claim that a
leading ordinal term must survive the removal of all smaller fibers.
-/

theorem exists_child_of_proper_prefix
    {W : Set G} {p : List (List ℕ)} {m : ℕ}
    (hroot : ∀ x ∈ W, x.1.length = m) (hp : p.length < m)
    {x : G} (hx : x ∈ Fiber W p) :
    ∃ a : InnerLevels.OrderedSL, x ∈ Child W p a := by
  rcases hx.2 with ⟨s, hs⟩
  cases s with
  | nil =>
      have hlen := hroot x hx.1
      have hpEq : p = x.1 := by simpa using hs
      rw [← hpEq] at hlen
      omega
  | cons a s =>
      refine ⟨a, hx.1, s, ?_⟩
      simpa only [List.append_assoc, List.singleton_append] using hs

theorem thin_union_compl
    (W : Set G) (p : List (List ℕ)) (A : Set InnerLevels.OrderedSL)
    {m : ℕ} (hroot : ∀ x ∈ W, x.1.length = m) (hp : p.length < m) :
    Thin W p A ∪ Thin W p Aᶜ = Fiber W p := by
  ext x
  constructor
  · rintro (hx | hx) <;> exact hx.1
  · intro hx
    obtain ⟨a, ha⟩ := exists_child_of_proper_prefix hroot hp hx
    by_cases hA : a ∈ A
    · exact Or.inl ⟨hx, a, hA, ha.2⟩
    · exact Or.inr ⟨hx, a, hA, ha.2⟩

/-- Bound a thinning by a uniform bound on its continuation fibers times
the order type of the selected children. -/
theorem type_thin_le_mul
    (W : Set G) (p : List (List ℕ))
    (hroot : ∀ x ∈ W, ∀ y ∈ W, x.1.length = y.1.length)
    (A : Set InnerLevels.OrderedSL) (eta : Ordinal.{0})
    (hchildren : ∀ a ∈ A, typeLT (Child W p a) ≤ eta) :
    typeLT (Thin W p A) ≤ eta * typeLT A := by
  classical
  let f : Thin W p A → A := fun x ↦
    ⟨Classical.choose x.2.2, (Classical.choose_spec x.2.2).1⟩
  have spec (x : Thin W p A) : x.1 ∈ Child W p (f x).1 :=
    ⟨x.2.1.1, (Classical.choose_spec x.2.2).2⟩
  have hf : Monotone f := by
    intro x y hxy
    apply le_of_not_gt
    intro hlt
    have hrev : y < x :=
      child_separated W p hroot hlt y.1 (spec y) x.1 (spec x)
    exact (not_lt_of_ge hxy) hrev
  apply type_le_mul_of_monotone f hf eta
  intro a
  let e : {x : Thin W p A | f x = a} ↪o Child W p a.1 :=
    OrderEmbedding.ofStrictMono
      (fun x ↦ ⟨x.1.1, by
        have hx := spec x.1
        have hfa : (f x.1).1 = a.1 := congrArg Subtype.val x.2
        rwa [hfa] at hx⟩)
      (fun _ _ hxy ↦ hxy)
  exact e.ltEmbedding.ordinal_type_le.trans (hchildren a.1 a.2)

/-- Children whose continuation has at least the specified order type. -/
def LargeChildren (W : Set G) (p : List (List ℕ))
    (gamma : Ordinal.{0}) : Set InnerLevels.OrderedSL :=
  {a | gamma ≤ typeLT (Child W p a)}

theorem type_orderedSL : typeLT InnerLevels.OrderedSL = ω ^ ω :=
  WeakPigeon.rawShortlex_type

open Erdos591.Schipperus.K4Core

/-- The finite-depth induction behind extraction.  The ordinal bounds
are parameters here, so every use of the available margin is explicit. -/
theorem type_fiber_lt_of_largeChildren_small
    (W : Set G) {m : ℕ} (hroot : ∀ x ∈ W, x.1.length = m)
    (gamma delta : Ordinal.{0}) (rho : ℕ → Ordinal.{0})
    (hbase : 1 < rho 0)
    (hsmall : ∀ k, gamma * (ω ^ ω) < rho (k + 1))
    (hstep : ∀ k, rho k * delta < rho (k + 1))
    (hind : ∀ k, FinitelyIndivisible (rho (k + 1)).ToType)
    (hlevels : ∀ p, typeLT (LargeChildren W p gamma) ≤ delta)
    (k : ℕ) (p : List (List ℕ)) (hp : p.length + k = m) :
    typeLT (Fiber W p) < rho k := by
  induction k generalizing p with
  | zero =>
      have hlen : p.length = m := by omega
      have : Subsingleton (Fiber W p) := by
        refine ⟨fun x y ↦ ?_⟩
        have hx : p = x.1.1 := x.2.2.eq_of_length
          (hlen.trans (hroot x.1 x.2.1).symm)
        have hy : p = y.1.1 := y.2.2.eq_of_length
          (hlen.trans (hroot y.1 y.2.1).symm)
        exact Subtype.ext (Subtype.ext (hx.symm.trans hy))
      exact (LexPrefix.typeLT_le_one_of_subsingleton (Fiber W p)).trans_lt hbase
  | succ k ih =>
      have hp' : p.length < m := by omega
      have hsame : ∀ x ∈ W, ∀ y ∈ W, x.1.length = y.1.length :=
        fun x hx y hy ↦ (hroot x hx).trans (hroot y hy).symm
      let A := LargeChildren W p gamma
      have hS : typeLT (Thin W p Aᶜ) < rho (k + 1) := by
        have hchild : ∀ a ∈ Aᶜ, typeLT (Child W p a) ≤ gamma := by
          intro a ha
          change ¬ gamma ≤ typeLT (Child W p a) at ha
          exact (lt_of_not_ge ha).le
        have htype : typeLT (Aᶜ : Set InnerLevels.OrderedSL) ≤ ω ^ ω :=
          (Ordinal.type_set_le _).trans_eq type_orderedSL
        exact (type_thin_le_mul W p hsame Aᶜ gamma hchild).trans_lt
          ((mul_le_mul_right htype gamma).trans_lt (hsmall k))
      have hT : typeLT (Thin W p A) < rho (k + 1) := by
        have hchild : ∀ a ∈ A, typeLT (Child W p a) ≤ rho k := by
          intro a _
          have hpa : (p ++ [show List ℕ from a]).length + k = m := by
            rw [List.length_append]
            change p.length + 1 + k = m
            omega
          exact (ih (p ++ [show List ℕ from a]) hpa).le
        exact (type_thin_le_mul W p hsame A (rho k) hchild).trans_lt
          ((mul_le_mul_right (hlevels p) (rho k)).trans_lt (hstep k))
      rw [← thin_union_compl W p A hroot hp']
      exact type_union_lt (rho (k + 1)) (hind k) _ _ hT hS

end Erdos591.Negative.Exact.Levels

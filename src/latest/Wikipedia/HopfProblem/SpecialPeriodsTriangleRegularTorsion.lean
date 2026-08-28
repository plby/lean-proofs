import Wikipedia.HopfProblem.SpecialPeriodsTrianglePresentation
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularTorsionWords

/-!
# Torsion in the actual triangle group

The torsion classification is proved from the reduced words of an indexed
free product.  A nonsingleton word whose endpoint indices agree has a strictly
shorter cyclic conjugate.  A word with distinct endpoint indices has no positive
power equal to the identity.  Minimizing length in a conjugacy class
therefore places every nonidentity torsion element in a conjugate factor.

The last results specialize this argument to the actual free product
`TriangleGroup`, rather than to a group equipped with an assumed normal form.
-/

noncomputable section

universe u

namespace Wikipedia.HopfProblem.SpecialPeriods.CoprodTorsion

open Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- Cyclically moving the first letter to the end shortens a reduced word
when its two endpoint letters come from the same factor. -/
theorem exists_shorter_conjugate (w : Word G) (a b : Σ i, G i)
    (l : List (Σ i, G i)) (hw : w.toList = a :: (l ++ [b]))
    (hab : a.1 = b.1) :
    ∃ v : Word G, v.toList.length < w.toList.length ∧ IsConj v.prod w.prod := by
  classical
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  dsimp only at hab
  subst j
  have hchain : (l ++ [Sigma.mk i b]).IsChain
      (fun x y : Σ i, G i => x.1 ≠ y.1) := by
    have hc := w.chain_ne
    rw [hw] at hc
    exact hc.tail
  have hletters : ∀ x ∈ l, Sigma.snd x ≠ 1 := by
    intro x hx
    apply w.ne_one x
    rw [hw]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
  let middle : Word G := ⟨l, hletters, hchain.left_of_append⟩
  have hp : w.prod = of a * (middle.prod * of b) := by
    simp [Word.prod, hw, middle]
  by_cases hba : b * a = 1
  · refine ⟨middle, ?_, ?_⟩
    · simp only [middle, hw, List.length_cons, List.length_append]
      omega
    · apply isConj_iff.mpr
      refine ⟨of a, ?_⟩
      have hb : of b = (of a : Monoid.CoprodI G)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, hba, map_one]
      rw [hp, hb, mul_assoc]
  · let v : Word G :=
      { toList := l ++ [⟨i, b * a⟩]
        ne_one := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hletters x hx
          · have hx' : x = ⟨i, b * a⟩ := List.mem_singleton.mp hx
            subst x
            exact hba
        chain_ne := by
          apply List.IsChain.append hchain.left_of_append (List.isChain_singleton _)
          intro x hx y hy
          have hy' : y = ⟨i, b * a⟩ := by simpa using hy.symm
          subst y
          exact (List.isChain_append.mp hchain).2.2 x hx ⟨i, b⟩ (by simp) }
    refine ⟨v, ?_, ?_⟩
    · simp only [v, hw, List.length_cons, List.length_append]
      omega
    · apply isConj_iff.mpr
      refine ⟨of a, ?_⟩
      have hv : v.prod = middle.prod * of (b * a) := by
        simp only [Word.prod, v, middle, List.map_append, List.map_singleton,
          List.prod_append, List.prod_singleton]
      rw [hv, hp, map_mul]
      simp only [mul_assoc, mul_inv_cancel, mul_one]

private theorem list_cases_endpoints {α : Type*} (l : List α) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a m b, l = a :: (m ++ [b]) := by
  induction l using List.bidirectionalRec with
  | nil => exact Or.inl rfl
  | singleton a => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | cons_append a l b _ => exact Or.inr (Or.inr ⟨a, l, b, rfl⟩)

/-- The torsion theorem for an arbitrary indexed free product: a finite-order
element is the identity or is conjugate to an element of one factor. -/
theorem coprodI_isOfFinOrder_conjugate_factor (x : Monoid.CoprodI G)
    (hx : IsOfFinOrder x) :
    x = 1 ∨ ∃ (i : ι) (a : G i), IsConj (of a) x := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ w : Word G, w.toList.length = n ∧ IsConj w.prod x
  have hP : ∃ n, P n := by
    refine ⟨(Word.equiv x).toList.length, Word.equiv x, rfl, ?_⟩
    have hp : (Word.equiv x).prod = x := (Word.equiv (M := G)).symm_apply_apply x
    rw [hp]
  obtain ⟨w, hwlen, hwconj⟩ := Nat.find_spec hP
  have hmin (v : Word G) (hv : IsConj v.prod x) :
      w.toList.length ≤ v.toList.length := by
    rw [hwlen]
    exact Nat.find_min' hP ⟨v, rfl, hv⟩
  have hwfin : IsOfFinOrder w.prod := hwconj.symm.isOfFinOrder hx
  rcases list_cases_endpoints w.toList with hnil | ⟨a, hsingle⟩ | ⟨a, l, b, hw⟩
  · left
    have hp : w.prod = 1 := by simp [Word.prod, hnil]
    simpa only [hp, isConj_one_right] using hwconj
  · right
    refine ⟨a.1, a.2, ?_⟩
    have hp : w.prod = of a.2 := by simp [Word.prod, hsingle]
    simpa only [hp] using hwconj
  · by_cases hab : a.1 = b.1
    · obtain ⟨v, hvlen, hvconj⟩ := exists_shorter_conjugate w a b l hw hab
      exact (Nat.not_lt_of_ge (hmin v (hvconj.trans hwconj)) hvlen).elim
    · exfalso
      apply word_not_isOfFinOrder_of_head_getLast w a b (by simp [hw])
        (by rw [hw, ← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp)]; rfl)
        hab hwfin

/-- The nonidentity form of the free-product torsion theorem, with a
nonidentity element of the factor. -/
theorem coprodI_nontrivial_isOfFinOrder_conjugate_factor (x : Monoid.CoprodI G)
    (hx : IsOfFinOrder x) (hne : x ≠ 1) :
    ∃ (i : ι) (a : G i), a ≠ 1 ∧ IsConj (of a) x := by
  obtain hx | ⟨i, a, ha⟩ := coprodI_isOfFinOrder_conjugate_factor x hx
  · exact (hne hx).elim
  · refine ⟨i, a, ?_, ha⟩
    rintro rfl
    exact hne (by simpa using ha.symm)

/-- The same classification for the binary coproduct used by the triangle
group.  The comparison with indexed coproducts follows from their universal
properties. -/
theorem coprod_nontrivial_isOfFinOrder_conjugate_factor
    {A B : Type u} [Group A] [Group B] (x : Monoid.Coprod A B)
    (hx : IsOfFinOrder x) (hne : x ≠ 1) :
    (∃ a : A, a ≠ 1 ∧ IsConj (Monoid.Coprod.inl a) x) ∨
      ∃ b : B, b ≠ 1 ∧ IsConj (Monoid.Coprod.inr b) x := by
  let H : Bool → Type _ := fun b => cond b B A
  let : ∀ b, Group (H b) :=
    Bool.rec (inferInstance : Group A) (inferInstance : Group B)
  let toI : Monoid.Coprod A B →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := false))
      (Monoid.CoprodI.of (M := H) (i := true))
  let fromI : Monoid.CoprodI H →* Monoid.Coprod A B :=
    Monoid.CoprodI.lift fun b => match b with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id (Monoid.Coprod A B) := by
    apply Monoid.Coprod.hom_ext
    · ext a
      simp [toI, fromI]
    · ext b
      simp [toI, fromI]
  have hleft_apply (y : Monoid.Coprod A B) : fromI (toI y) = y :=
    DFunLike.congr_fun hleft y
  have hto_ne : toI x ≠ 1 := by
    intro he
    apply hne
    have hh := congrArg fromI he
    simpa only [hleft_apply, map_one] using hh
  obtain ⟨b, a, hane, ha⟩ :=
    coprodI_nontrivial_isOfFinOrder_conjugate_factor (toI x) (toI.isOfFinOrder hx) hto_ne
  have ha' := fromI.map_isConj ha
  rw [hleft_apply] at ha'
  cases b with
  | false => exact Or.inl ⟨a, hane, by simpa [fromI] using ha'⟩
  | true => exact Or.inr ⟨a, hane, by simpa [fromI] using ha'⟩

end Wikipedia.HopfProblem.SpecialPeriods.CoprodTorsion

namespace Wikipedia.HopfProblem.SpecialPeriods

private theorem cyclic_eq_positive_generator_pow {n : ℕ} [NeZero n]
    (a : Multiplicative (ZMod n)) (ha : a ≠ 1) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ a = Multiplicative.ofAdd (1 : ZMod n) ^ k := by
  refine ⟨a.toAdd.val, ZMod.val_pos.mpr ?_, ZMod.val_lt _, ?_⟩
  · exact ha
  · change a.toAdd = a.toAdd.val • (1 : ZMod n)
    simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

/-- Every nonidentity finite-order element of the actual triangle group is
conjugate to a nonidentity power of one of its two distinguished generators. -/
theorem triangle_nontrivial_isOfFinOrder_conjugate_generator_power
    (g : TriangleGroup) (hg : IsOfFinOrder g) (hne : g ≠ 1) :
    (∃ n : ℕ, 0 < n ∧ n < 3 ∧ IsConj (triangleGenerator₁ ^ n) g) ∨
      ∃ n : ℕ, 0 < n ∧ n < 4 ∧ IsConj (triangleGenerator₂ ^ n) g := by
  obtain ⟨a, hane, ha⟩ | ⟨a, hane, ha⟩ :=
    CoprodTorsion.coprod_nontrivial_isOfFinOrder_conjugate_factor g hg hne
  · obtain ⟨n, hn0, hn3, rfl⟩ := cyclic_eq_positive_generator_pow a hane
    exact Or.inl ⟨n, hn0, hn3, by simpa only [map_pow, triangleGenerator₁] using ha⟩
  · obtain ⟨n, hn0, hn4, rfl⟩ := cyclic_eq_positive_generator_pow a hane
    exact Or.inr ⟨n, hn0, hn4, by simpa only [map_pow, triangleGenerator₂] using ha⟩

/-- An explicit-conjugator form of the triangle torsion classification. -/
theorem triangle_nontrivial_isOfFinOrder_eq_conjugate_generator_power
    (g : TriangleGroup) (hg : IsOfFinOrder g) (hne : g ≠ 1) :
    (∃ (h : TriangleGroup) (n : ℕ), 0 < n ∧ n < 3 ∧
      g = h * triangleGenerator₁ ^ n * h⁻¹) ∨
    (∃ (h : TriangleGroup) (n : ℕ), 0 < n ∧ n < 4 ∧
      g = h * triangleGenerator₂ ^ n * h⁻¹) := by
  obtain ⟨n, hn0, hn3, hn⟩ | ⟨n, hn0, hn4, hn⟩ :=
    triangle_nontrivial_isOfFinOrder_conjugate_generator_power g hg hne
  · obtain ⟨h, hh⟩ := isConj_iff.mp hn
    exact Or.inl ⟨h, n, hn0, hn3, hh.symm⟩
  · obtain ⟨h, hh⟩ := isConj_iff.mp hn
    exact Or.inr ⟨h, n, hn0, hn4, hh.symm⟩

end Wikipedia.HopfProblem.SpecialPeriods

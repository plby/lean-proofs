import Wikipedia.HopfProblem.SpecialPeriodsTrianglePresentation
import Mathlib.GroupTheory.CoprodI

/-!
# Reduced words and boundary identifications of a closed triangle domain

Nontrivial elements of either cyclic factor send the closed candidate
domain into a weak sector.  Crossing from the opposite weak sector puts
a point in the strict sector.  Consequently a reduced word with at least
two syllables cannot return a domain point to the domain.  A returning
element of the actual free product therefore lies in one cyclic factor.
Faithfulness of the chosen representation is not an assumption.
-/

noncomputable section

open Function Set
open scoped Pointwise

namespace Wikipedia.HopfProblem.SpecialPeriods

private theorem lift_neWord_weak_to_strict
    {ι G α : Type*} [Group G] [MulAction G α]
    {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G)
    (X W : ι → Set α) (hXW : ∀ i, X i ⊆ W i)
    (hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ X i)
    {i j k : ι} (w : Monoid.CoprodI.NeWord H i j) (hk : j ≠ k) :
    Monoid.CoprodI.lift f w.prod • W k ⊆ X i := by
  induction w generalizing k with
  | singleton x hx => simpa using hcross hk x hx
  | @append i j m l w₁ hne w₂ ih₁ ih₂ =>
      rw [Monoid.CoprodI.NeWord.append_prod, map_mul, mul_smul]
      exact (smul_set_subset_smul_set_iff.mpr ((ih₂ hk).trans (hXW m))).trans (ih₁ hne)

private theorem lift_neWord_closed_domain_subset
    {ι G α : Type*} [Group G] [MulAction G α]
    {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G)
    (X W : ι → Set α) (D : Set α) (hXW : ∀ i, X i ⊆ W i)
    (hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ X i)
    (hD : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ W i)
    {i j : ι} (w : Monoid.CoprodI.NeWord H i j) :
    Monoid.CoprodI.lift f w.prod • D ⊆ W i := by
  induction w with
  | singleton x hx => simpa using hD _ x hx
  | @append i j k l w₁ hne w₂ _ih₁ ih₂ =>
      rw [Monoid.CoprodI.NeWord.append_prod, map_mul, mul_smul]
      exact (smul_set_subset_smul_set_iff.mpr ih₂).trans
        ((lift_neWord_weak_to_strict f X W hXW hcross w₁ hne).trans (hXW i))

private theorem lift_neWord_factor_or_strict
    {ι G α : Type*} [Group G] [MulAction G α]
    {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G)
    (X W : ι → Set α) (D : Set α) (hXW : ∀ i, X i ⊆ W i)
    (hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ X i)
    (hD : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ W i)
    {i j : ι} (w : Monoid.CoprodI.NeWord H i j) :
    (∃ x : H i, w.prod = Monoid.CoprodI.of x) ∨
      Monoid.CoprodI.lift f w.prod • D ⊆ X i := by
  cases w with
  | singleton x hx => exact Or.inl ⟨x, Monoid.CoprodI.NeWord.prod_singleton x hx⟩
  | @append i j k l w₁ hne w₂ =>
      right
      rw [Monoid.CoprodI.NeWord.append_prod, map_mul, mul_smul]
      exact (smul_set_subset_smul_set_iff.mpr
        (lift_neWord_closed_domain_subset f X W D hXW hcross hD w₂)).trans
        (lift_neWord_weak_to_strict f X W hXW hcross w₁ hne)

private theorem gluing_cyclicPowerHom_two {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (2 : ℤ)

private theorem gluing_cyclicPowerHom_three {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (3 : ℤ)

private theorem cyclicThree_closed_subset {G α : Type*} [Group G] [MulAction G α]
    (a : G) (ha : a ^ 3 = 1) (S T : Set α)
    (h₁ : MapsTo (fun z => a • z) S T)
    (h₂ : MapsTo (fun z => a ^ 2 • z) S T)
    (g : Multiplicative (ZMod 3)) (hg : g ≠ 1) : cyclicPowerHom 3 a ha g • S ⊆ T := by
  have hc : g = Multiplicative.ofAdd (1 : ZMod 3) ∨
      g = Multiplicative.ofAdd (2 : ZMod 3) :=
    (by decide : ∀ x : Multiplicative (ZMod 3), x ≠ 1 →
      x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2) g hg
  rcases hc with rfl | rfl
  · rw [cyclicPowerHom_one]
    exact Set.smul_set_subset_iff.mpr h₁
  · rw [gluing_cyclicPowerHom_two]
    exact Set.smul_set_subset_iff.mpr h₂

private theorem cyclicFour_closed_subset {G α : Type*} [Group G] [MulAction G α]
    (b : G) (hb : b ^ 4 = 1) (S T : Set α)
    (h₁ : MapsTo (fun z => b • z) S T)
    (h₂ : MapsTo (fun z => b ^ 2 • z) S T)
    (h₃ : MapsTo (fun z => b ^ 3 • z) S T)
    (g : Multiplicative (ZMod 4)) (hg : g ≠ 1) : cyclicPowerHom 4 b hb g • S ⊆ T := by
  have hc : g = Multiplicative.ofAdd (1 : ZMod 4) ∨
      g = Multiplicative.ofAdd (2 : ZMod 4) ∨
      g = Multiplicative.ofAdd (3 : ZMod 4) :=
    (by decide : ∀ x : Multiplicative (ZMod 4), x ≠ 1 →
      x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2 ∨
      x = Multiplicative.ofAdd 3) g hg
  rcases hc with rfl | rfl | rfl
  · rw [cyclicPowerHom_one]
    exact Set.smul_set_subset_iff.mpr h₁
  · rw [gluing_cyclicPowerHom_two]
    exact Set.smul_set_subset_iff.mpr h₂
  · rw [gluing_cyclicPowerHom_three]
    exact Set.smul_set_subset_iff.mpr h₃

private theorem cyclic_eq_generator_pow_val {n : ℕ} [NeZero n]
    (x : Multiplicative (ZMod n)) :
    x = Multiplicative.ofAdd (1 : ZMod n) ^ x.toAdd.val := by
  change x.toAdd = x.toAdd.val • (1 : ZMod n)
  simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

variable {G α : Type*} [Group G] [MulAction G α]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y XB YB D : Set α)
    (hXXB : X ⊆ XB) (hYYB : Y ⊆ YB)
    (ha₁ : MapsTo (fun z => a • z) YB X)
    (ha₂ : MapsTo (fun z => a ^ 2 • z) YB X)
    (hb₁ : MapsTo (fun z => b • z) XB Y)
    (hb₂ : MapsTo (fun z => b ^ 2 • z) XB Y)
    (hb₃ : MapsTo (fun z => b ^ 3 • z) XB Y)
    (hDa₁ : MapsTo (fun z => a • z) D XB)
    (hDa₂ : MapsTo (fun z => a ^ 2 • z) D XB)
    (hDb₁ : MapsTo (fun z => b • z) D YB)
    (hDb₂ : MapsTo (fun z => b ^ 2 • z) D YB)
    (hDb₃ : MapsTo (fun z => b ^ 3 • z) D YB)
    (hDX : Disjoint D X) (hDY : Disjoint D Y)

include hXXB hYYB ha₁ ha₂ hb₁ hb₂ hb₃ hDa₁ hDa₂ hDb₁ hDb₂ hDb₃ hDX hDY

/-- A return to the closed domain is one of the explicitly bounded
powers of the two generators of the actual triangle group. -/
theorem triangleLift_eq_generator_pow_of_closed_domain_mem (g : TriangleGroup)
    {z : α} (hz : z ∈ D) (hgz : triangleLift a b ha hb g • z ∈ D) :
    (∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n) ∨
      (∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n) := by
  classical
  by_cases hg : g = 1
  · exact Or.inl ⟨0, by decide, by simpa using hg⟩
  let H : Bool → Type := fun i => cond i
    (Multiplicative (ZMod 4)) (Multiplicative (ZMod 3))
  let : ∀ i, Group (H i) :=
    Bool.rec (inferInstance : Group (Multiplicative (ZMod 3)))
      (inferInstance : Group (Multiplicative (ZMod 4)))
  let f : ∀ i, H i →* G := fun i => match i with
    | false => cyclicPowerHom 3 a ha
    | true => cyclicPowerHom 4 b hb
  let toI : TriangleGroup →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := false))
      (Monoid.CoprodI.of (M := H) (i := true))
  let fromI : Monoid.CoprodI H →* TriangleGroup :=
    Monoid.CoprodI.lift fun i => match i with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id TriangleGroup := by
    apply triangle_hom_ext
    · simp [toI, fromI, triangleGenerator₁]
    · simp [toI, fromI, triangleGenerator₂]
  have hto_ne : toI g ≠ 1 := by
    intro h
    apply hg
    calc
      g = fromI (toI g) := (DFunLike.congr_fun hleft g).symm
      _ = 1 := by rw [h, map_one]
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  let U : Bool → Set α := fun i => cond i Y X
  let W : Bool → Set α := fun i => cond i YB XB
  have hUW : ∀ i, U i ⊆ W i := by
    intro i
    cases i
    · exact hXXB
    · exact hYYB
  have hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ U i := by
    intro i j hij h hh
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact cyclicThree_closed_subset a ha YB X ha₁ ha₂ h hh
    · exact cyclicFour_closed_subset b hb XB Y hb₁ hb₂ hb₃ h hh
    · exact (hij rfl).elim
  have hstart : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ W i := by
    intro i h hh
    cases i
    · exact cyclicThree_closed_subset a ha D XB hDa₁ hDa₂ h hh
    · exact cyclicFour_closed_subset b hb D YB hDb₁ hDb₂ hDb₃ h hh
  let r := Monoid.CoprodI.Word.equiv (M := H) (toI g)
  have hr : r.prod = toI g := (Monoid.CoprodI.Word.equiv (M := H)).symm_apply_apply (toI g)
  have hr_ne : r ≠ Monoid.CoprodI.Word.empty := by
    intro h
    apply hto_ne
    rw [← hr, h, Monoid.CoprodI.Word.prod_empty]
  obtain ⟨i, j, w, hw⟩ := Monoid.CoprodI.NeWord.of_word r hr_ne
  have hwprod : w.prod = toI g := by
    change w.toWord.prod = toI g
    rw [hw]
    exact hr
  rcases lift_neWord_factor_or_strict f U W D hUW hcross hstart w with ⟨x, hx⟩ | himage
  · have hfrom : fromI (Monoid.CoprodI.of x) = g := by
      rw [← hx, hwprod]
      exact DFunLike.congr_fun hleft g
    cases i
    · left
      refine ⟨x.toAdd.val, ZMod.val_lt x.toAdd, ?_⟩
      calc
        g = Monoid.Coprod.inl x := by simpa [fromI] using hfrom.symm
        _ = triangleGenerator₁ ^ x.toAdd.val := by
          rw [triangleGenerator₁, ← map_pow]
          exact congrArg Monoid.Coprod.inl (cyclic_eq_generator_pow_val x)
    · right
      refine ⟨x.toAdd.val, ZMod.val_lt x.toAdd, ?_⟩
      calc
        g = Monoid.Coprod.inr x := by simpa [fromI] using hfrom.symm
        _ = triangleGenerator₂ ^ x.toAdd.val := by
          rw [triangleGenerator₂, ← map_pow]
          exact congrArg Monoid.Coprod.inr (cyclic_eq_generator_pow_val x)
  · have heval : triangleLift a b ha hb g = Monoid.CoprodI.lift f (toI g) :=
      DFunLike.congr_fun hrepresentation g
    have hstrict : triangleLift a b ha hb g • z ∈ U i := by
      rw [heval, ← hwprod]
      exact Set.smul_set_subset_iff.mp himage hz
    cases i
    · exact (hDX.le_bot ⟨hgz, hstrict⟩).elim
    · exact (hDY.le_bot ⟨hgz, hstrict⟩).elim

/-- Every return to the closed domain lies in one of the two actual
cyclic factors, without a faithfulness assumption on the representation. -/
theorem triangleLift_mem_factor_of_closed_domain_mem (g : TriangleGroup)
    {z : α} (hz : z ∈ D) (hgz : triangleLift a b ha hb g • z ∈ D) :
    g ∈ Subgroup.zpowers triangleGenerator₁ ∨ g ∈ Subgroup.zpowers triangleGenerator₂ := by
  rcases triangleLift_eq_generator_pow_of_closed_domain_mem a b ha hb X Y XB YB D hXXB hYYB
    ha₁ ha₂ hb₁ hb₂ hb₃ hDa₁ hDa₂ hDb₁ hDb₂ hDb₃ hDX hDY g hz hgz with
    ⟨n, _, rfl⟩ | ⟨n, _, rfl⟩
  · exact Or.inl (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) n)
  · exact Or.inr (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) n)

end Wikipedia.HopfProblem.SpecialPeriods

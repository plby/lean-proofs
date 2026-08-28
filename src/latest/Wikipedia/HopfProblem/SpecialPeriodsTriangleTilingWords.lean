import Wikipedia.HopfProblem.SpecialPeriodsTrianglePresentation
import Mathlib.GroupTheory.CoprodI

/-!
# Reduced-word separation of a triangle fundamental-domain candidate

Every nonempty reduced word sends the candidate domain into the
ping-pong set determined by its first factor.  Thus a domain disjoint
from the two ping-pong sets has disjoint nonidentity translates.  The
conclusion detects the identity in the actual abstract free product;
faithfulness of its chosen representation is not an assumption.
-/

noncomputable section

open Function Set
open scoped Pointwise

namespace Wikipedia.HopfProblem.SpecialPeriods

private theorem lift_neWord_domain_subset
    {ι G α : Type*} [Group G] [MulAction G α]
    {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G)
    (X : ι → Set α) (D : Set α)
    (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i)
    (hD : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ X i)
    {i j : ι} (w : Monoid.CoprodI.NeWord H i j) :
    Monoid.CoprodI.lift f w.prod • D ⊆ X i := by
  induction w with
  | singleton x hx => simpa using hD _ x hx
  | @append i j k l w₁ hne w₂ _ih₁ ih₂ =>
      calc
        Monoid.CoprodI.lift f (Monoid.CoprodI.NeWord.append w₁ hne w₂).prod • D =
            Monoid.CoprodI.lift f w₁.prod • Monoid.CoprodI.lift f w₂.prod • D := by
          simp [mul_smul]
        _ ⊆ Monoid.CoprodI.lift f w₁.prod • X k := smul_set_subset_smul_set_iff.mpr ih₂
        _ ⊆ X i := Monoid.CoprodI.lift_word_ping_pong f X hpp w₁ hne

private theorem tiling_cyclicPowerHom_two {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (2 : ℤ)

private theorem tiling_cyclicPowerHom_three {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (3 : ℤ)

private theorem cyclicThree_domain_subset {G α : Type*} [Group G] [MulAction G α]
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
  · rw [tiling_cyclicPowerHom_two]
    exact Set.smul_set_subset_iff.mpr h₂

private theorem cyclicFour_domain_subset {G α : Type*} [Group G] [MulAction G α]
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
  · rw [tiling_cyclicPowerHom_two]
    exact Set.smul_set_subset_iff.mpr h₂
  · rw [tiling_cyclicPowerHom_three]
    exact Set.smul_set_subset_iff.mpr h₃

variable {G α : Type*} [Group G] [MulAction G α]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y D : Set α)
    (ha₁ : MapsTo (fun z => a • z) Y X)
    (ha₂ : MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : MapsTo (fun z => b • z) X Y)
    (hb₂ : MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : MapsTo (fun z => b ^ 3 • z) X Y)
    (hDa₁ : MapsTo (fun z => a • z) D X)
    (hDa₂ : MapsTo (fun z => a ^ 2 • z) D X)
    (hDb₁ : MapsTo (fun z => b • z) D Y)
    (hDb₂ : MapsTo (fun z => b ^ 2 • z) D Y)
    (hDb₃ : MapsTo (fun z => b ^ 3 • z) D Y)

include ha₁ ha₂ hb₁ hb₂ hb₃ hDa₁ hDa₂ hDb₁ hDb₂ hDb₃

/-- Every nonidentity abstract triangle word sends the candidate domain
into one of the two ping-pong sets.  No representation-faithfulness or
nonemptiness assumption is needed. -/
theorem triangleLift_mapsTo_pingPongUnion (g : TriangleGroup) (hg : g ≠ 1) :
    MapsTo (fun z => triangleLift a b ha hb g • z) D (X ∪ Y) := by
  classical
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
  have hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i := by
    intro i j hij h hh
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact cyclicThree_domain_subset a ha Y X ha₁ ha₂ h hh
    · exact cyclicFour_domain_subset b hb X Y hb₁ hb₂ hb₃ h hh
    · exact (hij rfl).elim
  have hstart : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ U i := by
    intro i h hh
    cases i
    · exact cyclicThree_domain_subset a ha D X hDa₁ hDa₂ h hh
    · exact cyclicFour_domain_subset b hb D Y hDb₁ hDb₂ hDb₃ h hh
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
  have himage := lift_neWord_domain_subset f U D hpp hstart w
  have hUi : U i ⊆ X ∪ Y := by
    cases i
    · exact subset_union_left
    · exact subset_union_right
  have heval : triangleLift a b ha hb g = Monoid.CoprodI.lift f (toI g) :=
    DFunLike.congr_fun hrepresentation g
  intro z hz
  rw [heval, ← hwprod]
  exact hUi (Set.smul_set_subset_iff.mp himage hz)

variable (hDX : Disjoint D X) (hDY : Disjoint D Y)

include hDX hDY

/-- A candidate domain outside the two ping-pong sets is disjoint from
every translate by a nonidentity abstract triangle word. -/
theorem triangleLift_disjoint_domain_translate (g : TriangleGroup) (hg : g ≠ 1) :
    Disjoint D (triangleLift a b ha hb g • D) := by
  apply (hDX.sup_right hDY).mono_right
  exact Set.smul_set_subset_iff.mpr
    (triangleLift_mapsTo_pingPongUnion a b ha hb X Y D ha₁ ha₂ hb₁ hb₂ hb₃
      hDa₁ hDa₂ hDb₁ hDb₂ hDb₃ g hg)

/-- An actual image of a domain point can return to the domain only for
the identity of the abstract triangle group. -/
theorem triangleLift_eq_one_of_domain_mem (g : TriangleGroup) {z : α} (hz : z ∈ D)
    (hgz : triangleLift a b ha hb g • z ∈ D) : g = 1 := by
  by_contra hg
  have hd := triangleLift_disjoint_domain_translate a b ha hb X Y D
    ha₁ ha₂ hb₁ hb₂ hb₃ hDa₁ hDa₂ hDb₁ hDb₂ hDb₃ hDX hDY g hg
  exact hd.le_bot ⟨hgz, ⟨z, hz, rfl⟩⟩

/-- Two points of the domain are related by the chosen representation
only when the relating abstract triangle element is the identity. -/
theorem triangleLift_eq_one_of_domain_eq (g : TriangleGroup) {z w : α}
    (hz : z ∈ D) (hw : w ∈ D) (hzw : triangleLift a b ha hb g • z = w) : g = 1 := by
  apply triangleLift_eq_one_of_domain_mem a b ha hb X Y D
    ha₁ ha₂ hb₁ hb₂ hb₃ hDa₁ hDa₂ hDb₁ hDb₂ hDb₃ hDX hDY g hz
  rwa [hzw]

end Wikipedia.HopfProblem.SpecialPeriods

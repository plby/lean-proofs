import ErdosProblems.Erdos336.KneserConsequences
import ErdosProblems.Erdos336.RectifiedLift
import ErdosProblems.Erdos336.DenseCosetAddition

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise BigOperators

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Embedding of the finite coordinate as the vertical subgroup. -/
def verticalHom : H →+ ℤ × H where
  toFun h := (0, h)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem verticalHom_apply (h : H) : verticalHom h = (0, h) := rfl

/-- The vertical copy of a finite subgroup, represented as a finset. -/
noncomputable def verticalSubgroupFinset (K : AddSubgroup H) : Finset (ℤ × H) :=
  (addSubgroupFinset K).image verticalHom

@[simp] theorem mem_verticalSubgroupFinset {K : AddSubgroup H} {x : ℤ × H} :
    x ∈ verticalSubgroupFinset K ↔ x.1 = 0 ∧ x.2 ∈ K := by
  constructor
  · intro hx
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx
    rw [← hkx]
    exact ⟨rfl, by simpa using hk⟩
  · rintro ⟨hx0, hxK⟩
    apply Finset.mem_image.mpr
    refine ⟨x.2, by simpa using hxK, ?_⟩
    apply Prod.ext
    · simpa using hx0.symm
    · rfl

@[simp] theorem card_verticalSubgroupFinset (K : AddSubgroup H) :
    (verticalSubgroupFinset K).card = (addSubgroupFinset K).card := by
  apply Finset.card_image_of_injective
  intro x y h
  exact congrArg Prod.snd h

/-- Every period of a finite nonempty subset of `ℤ × H` is vertical. -/
theorem fst_eq_zero_of_mem_addStab
    (S : Finset (ℤ × H)) (hS : S.Nonempty) {v : ℤ × H}
    (hv : v ∈ S.addStab) : v.1 = 0 := by
  have heq : v +ᵥ S = S := (Finset.mem_addStab hS).mp hv
  have hsum := congrArg (fun U : Finset (ℤ × H) => ∑ x ∈ U, x.1) heq
  rw [Finset.vadd_finset_def, Finset.sum_image] at hsum
  · simp only [vadd_eq_add, Prod.fst_add, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul] at hsum
    have hc : (S.card : ℤ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
    apply (mul_eq_zero.mp ?_).resolve_left hc
    linarith
  · intro x _hx y _hy hxy
    exact add_left_cancel hxy

/-- The vertical subgroup corresponding to the stabilizer of `S`. -/
def verticalStabilizer (S : Finset (ℤ × H)) : AddSubgroup H :=
  (AddAction.stabilizer (ℤ × H) (S : Set (ℤ × H))).comap verticalHom

@[simp] theorem mem_verticalStabilizer
    {S : Finset (ℤ × H)} (hS : S.Nonempty) {k : H} :
    k ∈ verticalStabilizer S ↔ (0, k) ∈ S.addStab := by
  rw [verticalStabilizer, AddSubgroup.mem_comap,
    AddAction.mem_stabilizer_iff, Finset.mem_addStab hS]
  constructor
  · intro h
    apply Finset.coe_inj.mp
    simpa using h
  · intro h
    have hc := congrArg (fun U : Finset (ℤ × H) => (U : Set (ℤ × H))) h
    simpa using hc

/-- The stabilizer finset is exactly the vertical copy of its finite-coordinate
subgroup. -/
theorem addStab_eq_verticalSubgroupFinset
    (S : Finset (ℤ × H)) (hS : S.Nonempty) :
    S.addStab = verticalSubgroupFinset (verticalStabilizer S) := by
  ext x
  constructor
  · intro hx
    have hx0 := fst_eq_zero_of_mem_addStab S hS hx
    apply mem_verticalSubgroupFinset.mpr
    refine ⟨hx0, ?_⟩
    rw [mem_verticalStabilizer hS]
    have heq : (0, x.2) = x := Prod.ext hx0.symm rfl
    simpa only [heq] using hx
  · intro hx
    obtain ⟨hx0, hxK⟩ := mem_verticalSubgroupFinset.mp hx
    rw [mem_verticalStabilizer hS] at hxK
    have heq : (0, x.2) = x := Prod.ext hx0.symm rfl
    simpa only [heq] using hxK

/-- In particular, the stabilizer cardinal is the cardinal of its vertical
subgroup. -/
theorem card_addStab_eq_card_verticalStabilizer
    (S : Finset (ℤ × H)) (hS : S.Nonempty) :
    S.addStab.card = (addSubgroupFinset (verticalStabilizer S)).card := by
  rw [addStab_eq_verticalSubgroupFinset S hS,
    card_verticalSubgroupFinset]

section Rectified

variable {N m : ℕ} [NeZero N] [NeZero m]

/-- Saturating by a subgroup killed by the rectifying homomorphism commutes
exactly with the rectified lift. -/
theorem rectifiedLift_add_vertical
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m)
    (houter : ∀ x ∈ A,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m))
    (K : AddSubgroup (ZMod N)) (hK : K ≤ π.ker) :
    rectifiedLift A π α + verticalSubgroupFinset K =
      rectifiedLift (A + addSubgroupFinset K) π α := by
  have houterSat : ∀ x ∈ A + addSubgroupFinset K,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m) := by
    intro x hx
    obtain ⟨a, ha, k, hk, hak⟩ := Finset.mem_add.mp hx
    obtain ⟨q, hq, hπa⟩ := houter a ha
    refine ⟨q, hq, ?_⟩
    rw [← hak, map_add, show π k = 0 from hK (by simpa using hk), add_zero, hπa]
  have hlabel (a : ZMod N) (ha : a ∈ A) (k : ZMod N)
      (hk : k ∈ K) :
      halfIntervalLabel π α (a + k) = halfIntervalLabel π α a := by
    have haS := halfIntervalLabel_spec π α a (houter a ha)
    have hakmem : a + k ∈ A + addSubgroupFinset K :=
      Finset.mem_add.mpr ⟨a, ha, k, by simpa using hk, rfl⟩
    have hakS := halfIntervalLabel_spec π α (a + k)
      (houterSat (a + k) hakmem)
    apply short_zmod_cast_injective (m := m) hakS.1 haS.1
    apply add_left_cancel (a := α)
    rw [← hakS.2, ← haS.2, map_add,
      show π k = 0 from hK (by simpa using hk), add_zero]
  ext y
  constructor
  · intro hy
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hy
    obtain ⟨a, ha, hua⟩ := mem_rectifiedLift.mp hu
    obtain ⟨hv0, hvK⟩ := mem_verticalSubgroupFinset.mp hv
    apply mem_rectifiedLift.mpr
    refine ⟨a + v.2,
      Finset.mem_add.mpr ⟨a, ha, v.2, by simpa using hvK, rfl⟩, ?_⟩
    rw [← huv, hua]
    apply Prod.ext
    · simp [hv0, hlabel a ha v.2 hvK]
    · rfl
  · intro hy
    obtain ⟨x, hx, hyx⟩ := mem_rectifiedLift.mp hy
    obtain ⟨a, ha, k, hk, hak⟩ := Finset.mem_add.mp hx
    apply Finset.mem_add.mpr
    let u : ℤ × ZMod N :=
      (Int.ofNat (halfIntervalLabel π α a), a)
    let v : ℤ × ZMod N := (0, k)
    refine ⟨u, mem_rectifiedLift.mpr ⟨a, ha, rfl⟩,
      v, mem_verticalSubgroupFinset.mpr ⟨rfl, by simpa using hk⟩, ?_⟩
    rw [hyx, ← hak]
    apply Prod.ext
    · dsimp [u, v]
      rw [hlabel a ha k (by simpa using hk)]
      simp
    · rfl

/-- Hence kernel saturation has exactly the same defect before and after
strict-half rectification. -/
theorem card_rectifiedLift_add_vertical
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m)
    (houter : ∀ x ∈ A,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m))
    (K : AddSubgroup (ZMod N)) (hK : K ≤ π.ker) :
    (rectifiedLift A π α + verticalSubgroupFinset K).card =
      (A + addSubgroupFinset K).card := by
  rw [rectifiedLift_add_vertical A π α houter K hK,
    card_rectifiedLift]

end Rectified

end Erdos336

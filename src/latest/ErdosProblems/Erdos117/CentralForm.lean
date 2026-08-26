import ErdosProblems.Erdos117.Spread
import ErdosProblems.Erdos117.Basic
import ErdosProblems.Erdos117.ScalarCliques
import Mathlib.Algebra.Module.ZMod

/-!
# Scalar forms from alternating group pairings

The row space of an alternating bicharacter realizes its quotient by the
radical as a vector space. The construction derives both the vector-space
structure and nondegeneracy from the group pairing.
-/

namespace Erdos117

variable (G : Type*) [Group G] (p : ℕ)

structure AlternatingBicharacter where
  toFun : G → G → ZMod p
  mul_left : ∀ x y z, toFun (x * y) z = toFun x z + toFun y z
  mul_right : ∀ x y z, toFun x (y * z) = toFun x y + toFun x z
  self : ∀ x, toFun x x = 0

namespace AlternatingBicharacter

variable {G p} (β : AlternatingBicharacter G p)

theorem one_left (x : G) : β.toFun 1 x = 0 := by
  have h := β.mul_left 1 1 x
  simpa using h

theorem one_right (x : G) : β.toFun x 1 = 0 := by
  have h := β.mul_right x 1 1
  simpa using h

theorem neg_swap (x y : G) : -β.toFun x y = β.toFun y x := by
  have h := β.self (x * y)
  rw [β.mul_left, β.mul_right, β.mul_right, β.self, β.self, zero_add, add_zero] at h
  exact (eq_neg_of_add_eq_zero_right h).symm

def rowHom : Additive G →+ (G → ZMod p) where
  toFun x := β.toFun x.toMul
  map_zero' := funext β.one_left
  map_add' x y := funext (β.mul_left x.toMul y.toMul)

def rowSpace : Submodule (ZMod p) (G → ZMod p) :=
  AddSubgroup.toZModSubmodule p β.rowHom.range

def row (x : G) : β.rowSpace := ⟨β.toFun x, ⟨Additive.ofMul x, rfl⟩⟩

theorem row_surjective : Function.Surjective β.row := by
  intro v
  obtain ⟨x, hx⟩ := v.2
  exact ⟨x.toMul, Subtype.ext hx⟩

@[simp] theorem row_apply (x y : G) : (β.row x).val y = β.toFun x y := rfl

@[simp] theorem row_one : β.row 1 = 0 := Subtype.ext (funext β.one_left)

@[simp] theorem row_mul (x y : G) : β.row (x * y) = β.row x + β.row y :=
  Subtype.ext (funext (β.mul_left x y))

noncomputable def representative (v : β.rowSpace) : G := (β.row_surjective v).choose

@[simp] theorem row_representative (v : β.rowSpace) : β.row (β.representative v) = v :=
  (β.row_surjective v).choose_spec

noncomputable def pairing (v w : β.rowSpace) : ZMod p := v.val (β.representative w)

theorem pairing_row_right (v : β.rowSpace) (x : G) : β.pairing v (β.row x) = v.val x := by
  obtain ⟨a, rfl⟩ := β.row_surjective v
  have h := congrArg (fun v : β.rowSpace => v.val a) (β.row_representative (β.row x))
  change β.toFun (β.representative (β.row x)) a = β.toFun x a at h
  change β.toFun a (β.representative (β.row x)) = β.toFun a x
  rw [← β.neg_swap a (β.representative (β.row x)), ← β.neg_swap a x] at h
  exact neg_injective h

@[simp] theorem pairing_row (x y : G) :
    β.pairing (β.row x) (β.row y) = β.toFun x y := β.pairing_row_right _ _

theorem pairing_neg_swap (v w : β.rowSpace) : -β.pairing v w = β.pairing w v := by
  obtain ⟨x, rfl⟩ := β.row_surjective v
  obtain ⟨y, rfl⟩ := β.row_surjective w
  simpa only [pairing_row] using β.neg_swap x y

noncomputable def pairingAddHom (v : β.rowSpace) : β.rowSpace →+ ZMod p where
  toFun := β.pairing v
  map_zero' := by
    rw [← β.row_one, β.pairing_row_right]
    obtain ⟨x, rfl⟩ := β.row_surjective v
    exact β.one_right x
  map_add' w z := by
    rw [← β.pairing_neg_swap, ← β.pairing_neg_swap w v, ← β.pairing_neg_swap z v]
    exact neg_add _ _

noncomputable def form : LinearMap.BilinForm (ZMod p) β.rowSpace where
  toFun v := (β.pairingAddHom v).toZModLinearMap p
  map_add' _ _ := LinearMap.ext (fun _ => rfl)
  map_smul' _ _ := LinearMap.ext (fun _ => rfl)

@[simp] theorem form_apply (v w : β.rowSpace) : β.form v w = β.pairing v w := rfl

theorem form_isAlt : β.form.IsAlt := by
  intro v
  obtain ⟨x, rfl⟩ := β.row_surjective v
  simpa only [form_apply, pairing_row] using β.self x

theorem form_nondegenerate : β.form.Nondegenerate := by
  apply β.form_isAlt.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro v hv
  apply Subtype.ext
  funext x
  exact (β.pairing_row_right v x).symm.trans (hv (β.row x))

def rowMonoidHom : G →* Multiplicative β.rowSpace where
  toFun x := Multiplicative.ofAdd (β.row x)
  map_one' := β.row_one
  map_mul' := β.row_mul

def subgroupOfSubspace (W : Submodule (ZMod p) β.rowSpace) : Subgroup G :=
  W.toAddSubgroup.toSubgroup.comap β.rowMonoidHom

@[simp] theorem mem_subgroupOfSubspace (W : Submodule (ZMod p) β.rowSpace) (x : G) :
    x ∈ β.subgroupOfSubspace W ↔ β.row x ∈ W := Iff.rfl

theorem form_rank [Finite G] [Fact p.Prime] :
    Module.finrank (ZMod p) β.form.range = Module.finrank (ZMod p) β.rowSpace := by
  classical
  let := Fintype.ofFinite G
  have h := β.form.finrank_range_add_finrank_ker
  rw [β.form_nondegenerate.ker_eq_bot] at h
  simpa using h

/-- Pulling a spread back along the row homomorphism gives subgroups on which
the scalar commutator pairing vanishes. -/
theorem exists_subgroup_cover [Finite G] [Fact p.Prime] :
    ∃ A : Fin (p ^ (Module.finrank (ZMod p) β.rowSpace / 2) + 1) → Subgroup G,
      (∀ x, ∃ i, x ∈ A i) ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, β.toFun x y = 0 := by
  classical
  let := Fintype.ofFinite G
  have hcover := exists_isotropic_cover β.form β.form_isAlt
  rw [β.form_rank] at hcover
  obtain ⟨W, hW⟩ := hcover
  refine ⟨fun i => β.subgroupOfSubspace (W i), ?_, ?_⟩
  · intro x
    exact hW.2 (β.row x)
  · intro i x hx y hy
    rw [← β.pairing_row, ← β.form_apply]
    exact hW.1 i (β.row x) hx (β.row y) hy

/-- Cliques in the scalar form lift to noncommuting families whenever
commuting elements have zero scalar pairing. -/
theorem clique_card_le [Fact p.Prime] {n : ℕ} (hn : NoncommutingBound G n)
    (hcomm : ∀ x y, Commute x y → β.toFun x y = 0)
    {ι : Type*} [Fintype ι] {f : ι → β.rowSpace} (hf : NonorthogonalFamily β.form f) :
    Fintype.card ι ≤ n := by
  classical
  let a : ι → G := fun i => β.representative (f i)
  have ha : ∀ i j, i ≠ j → ¬Commute (a i) (a j) := by
    intro i j hij hc
    apply hf i j hij
    have heq := hcomm (a i) (a j) hc
    rw [← β.pairing_row, β.row_representative, β.row_representative] at heq
    exact heq
  have hinj : Function.Injective a := by
    intro i j h
    by_contra hij
    exact ha i j hij (h ▸ Commute.refl _)
  have h := hn (Finset.univ.image a) (by
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact ha i j (fun h => hxy (congrArg a h)))
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ] at h

theorem scalar_rank_bound [Finite G] [Fact p.Prime]
    {n : ℕ} (hn : NoncommutingBound G n)
    (hcomm : ∀ x y, Commute x y → β.toFun x y = 0) :
    p * (Module.finrank (ZMod p) β.rowSpace / 2) + 1 ≤ n := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨m, hm⟩ := even_finrank_of_nondegenerate_alt β.form β.form_isAlt β.form_nondegenerate
  obtain ⟨f, hf⟩ := exists_scalar_clique_nondegenerate β.form β.form_isAlt
    β.form_nondegenerate (m := Module.finrank (ZMod p) β.rowSpace / 2) (by omega)
  have h := β.clique_card_le hn hcomm hf
  rw [Fintype.card_fin, ZMod.card] at h
  exact h

theorem kernel_index [Finite G] [Fact p.Prime] :
    β.rowMonoidHom.ker.index = p ^ Module.finrank (ZMod p) β.rowSpace := by
  classical
  let := Fintype.ofFinite G
  have hsurj : Function.Surjective β.rowMonoidHom := β.row_surjective
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
    Nat.card_congr Subgroup.topEquiv.toEquiv]
  change Nat.card β.rowSpace = p ^ Module.finrank (ZMod p) β.rowSpace
  let := Fintype.ofFinite β.rowSpace
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

theorem binary_rank_bound [Finite G] (β : AlternatingBicharacter G 2)
    {n : ℕ} (hn : NoncommutingBound G n)
    (hcomm : ∀ x y, Commute x y → β.toFun x y = 0) :
    Module.finrank (ZMod 2) β.rowSpace + 1 ≤ n := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨m, hm⟩ := even_finrank_of_nondegenerate_alt β.form β.form_isAlt β.form_nondegenerate
  have h := β.scalar_rank_bound hn hcomm
  omega

theorem ternary_rank_bound [Finite G] (β : AlternatingBicharacter G 3)
    {n : ℕ} (hn : NoncommutingBound G n)
    (hcomm : ∀ x y, Commute x y → β.toFun x y = 0) :
    2 * Module.finrank (ZMod 3) β.rowSpace ≤ n + 1 := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨c, f, hf, hrank⟩ := exists_ternary_clique_of_rank β.form β.form_isAlt
  have h := β.clique_card_le hn hcomm hf
  rw [Fintype.card_fin] at h
  rw [β.form_rank] at hrank
  omega

theorem scalar_credit_bound [Finite G] [Fact p.Prime]
    {n : ℕ} (hn : NoncommutingBound G n)
    (hcomm : ∀ x y, Commute x y → β.toFun x y = 0) :
    scalarCreditRate p * (Module.finrank (ZMod p) β.rowSpace / 2) ≤ n - 1 + scalarDefect p := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨c, f, hf, hcredit⟩ := exists_scalar_credit β.form β.form_isAlt
  have hc := β.clique_card_le hn hcomm hf
  rw [Fintype.card_fin] at hc
  rw [β.form_rank] at hcredit
  omega

end AlternatingBicharacter

open scoped commutatorElement

variable {G p}

def centralCommutator (N : Subgroup G) (hD : commutator G ≤ N) (x y : G) : N :=
  ⟨⁅x, y⁆, hD (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _))⟩

theorem centralCommutator_mul_left (N : Subgroup G) (hD : commutator G ≤ N)
    (hN : N ≤ Subgroup.center G) (x y z : G) :
    centralCommutator N hD (x * y) z =
      centralCommutator N hD x z * centralCommutator N hD y z := by
  have hc (a b c : G) : c * ⁅a, b⁆ = ⁅a, b⁆ * c :=
    Subgroup.mem_center_iff.mp (hN (centralCommutator N hD a b).2) c
  apply Subtype.ext
  change ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆
  rw [commutatorElement_mul_left_eq_conj_mul, hc y z x, mul_inv_cancel_right]
  exact (hc y z ⁅x, z⁆).symm

theorem centralCommutator_mul_right (N : Subgroup G) (hD : commutator G ≤ N)
    (hN : N ≤ Subgroup.center G) (x y z : G) :
    centralCommutator N hD x (y * z) =
      centralCommutator N hD x y * centralCommutator N hD x z := by
  have hc : y * ⁅x, z⁆ = ⁅x, z⁆ * y :=
    Subgroup.mem_center_iff.mp (hN (centralCommutator N hD x z).2) y
  apply Subtype.ext
  change ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆
  calc
    ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      group
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [hc, mul_inv_cancel_right]

/-- The scalar pairing associated to a character of a central subgroup
containing the derived subgroup. Bilinearity follows from commutator calculus. -/
def centralCommutatorBicharacter (N : Subgroup G) (hD : commutator G ≤ N)
    (hN : N ≤ Subgroup.center G) (χ : N →* Multiplicative (ZMod p)) :
    AlternatingBicharacter G p where
  toFun x y := (χ (centralCommutator N hD x y)).toAdd
  mul_left x y z := by rw [centralCommutator_mul_left N hD hN, map_mul]; rfl
  mul_right x y z := by rw [centralCommutator_mul_right N hD hN, map_mul]; rfl
  self x := by
    have h : centralCommutator N hD x x = 1 :=
      Subtype.ext (commutatorElement_self x)
    rw [h, map_one]
    rfl

theorem centralCommutatorBicharacter_eq_zero_iff (N : Subgroup G)
    (hD : commutator G ≤ N) (hN : N ≤ Subgroup.center G)
    (χ : N →* Multiplicative (ZMod p)) (x y : G) :
    (centralCommutatorBicharacter N hD hN χ).toFun x y = 0 ↔
      centralCommutator N hD x y ∈ χ.ker := Iff.rfl

theorem centralCommutatorBicharacter_commute (N : Subgroup G)
    (hD : commutator G ≤ N) (hN : N ≤ Subgroup.center G)
    (χ : N →* Multiplicative (ZMod p)) (x y : G) (hxy : Commute x y) :
    (centralCommutatorBicharacter N hD hN χ).toFun x y = 0 := by
  have h : centralCommutator N hD x y = 1 := Subtype.ext hxy.commutator_eq
  change (χ (centralCommutator N hD x y)).toAdd = 0
  rw [h, map_one]
  rfl

/-- The central-factor descent needed inside the class-two subgroup used in
the global reduction. Every child has its derived subgroup in the character
kernel, and the children cover the entire parent group. -/
theorem central_factor_descent [Finite G] [Fact p.Prime]
    (N : Subgroup G) (hD : commutator G ≤ N) (hN : N ≤ Subgroup.center G)
    (χ : N →* Multiplicative (ZMod p)) :
    let β := centralCommutatorBicharacter N hD hN χ
    ∃ A : Fin (p ^ (Module.finrank (ZMod p) β.rowSpace / 2) + 1) → Subgroup G,
      (∀ x, ∃ i, x ∈ A i) ∧ ∀ i, ⁅A i, A i⁆ ≤ χ.ker.map N.subtype := by
  let β := centralCommutatorBicharacter N hD hN χ
  obtain ⟨A, hcover, hzero⟩ := β.exists_subgroup_cover
  refine ⟨A, hcover, fun i => Subgroup.commutator_le.mpr ?_⟩
  intro x hx y hy
  refine Subgroup.mem_map.mpr ⟨centralCommutator N hD x y, ?_, rfl⟩
  exact hzero i x hx y hy

end Erdos117

import Wikipedia.HomotopyGroupsOfSpheres.Samelson
import Mathlib.Algebra.Group.Hom.Instances

/-! # Bilinearity of the native cubical Samelson product -/

noncomputable section

open scoped Topology unitInterval commutatorElement

namespace Wikipedia.HomotopyGroupsOfSpheres.Samelson

variable {M N G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable [DecidableEq M] [DecidableEq N]

private theorem update_inl_comp_inl (t : (M ⊕ N) → I) (i : M) (s : I) :
    Function.update t (Sum.inl i) s ∘ Sum.inl = Function.update (t ∘ Sum.inl) i s := by
  funext j
  by_cases h : j = i <;> simp [h]

private theorem update_inl_comp_inr (t : (M ⊕ N) → I) (i : M) (s : I) :
    Function.update t (Sum.inl i) s ∘ Sum.inr = t ∘ Sum.inr := by
  funext j
  simp

private theorem update_inr_comp_inl (t : (M ⊕ N) → I) (i : N) (s : I) :
    Function.update t (Sum.inr i) s ∘ Sum.inl = t ∘ Sum.inl := by
  funext j
  simp

private theorem update_inr_comp_inr (t : (M ⊕ N) → I) (i : N) (s : I) :
    Function.update t (Sum.inr i) s ∘ Sum.inr = Function.update (t ∘ Sum.inr) i s := by
  funext j
  by_cases h : j = i <;> simp [h]

omit [IsTopologicalGroup G] in
private theorem transAt_apply {K : Type*} [DecidableEq K] (i : K)
    (p q : GenLoop K G 1) (t : K → I) :
    GenLoop.transAt i p q t =
      if (t i : ℝ) ≤ 1 / 2 then
        p (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i)))
      else q (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i - 1))) := rfl

/-- Concatenation in the first input uses its own block of output coordinates. -/
theorem loop_transAt_left (i : M) (p p' : GenLoop M G 1) (q : GenLoop N G 1) :
    loop (GenLoop.transAt i p p') q =
      GenLoop.transAt (Sum.inl i) (loop p q) (loop p' q) := by
  apply GenLoop.ext
  intro t
  simp only [loop_apply, transAt_apply, Function.comp_apply]
  split_ifs <;> simp only [update_inl_comp_inl, update_inl_comp_inr]

/-- Concatenation in the second input uses its own block of output coordinates. -/
theorem loop_transAt_right (i : N) (p : GenLoop M G 1) (q q' : GenLoop N G 1) :
    loop p (GenLoop.transAt i q q') =
      GenLoop.transAt (Sum.inr i) (loop p q) (loop p q') := by
  apply GenLoop.ext
  intro t
  simp only [loop_apply, transAt_apply, Function.comp_apply]
  split_ifs <;> simp only [update_inr_comp_inl, update_inr_comp_inr]

variable [Nonempty M] [Nonempty N]

local instance : Nontrivial (M ⊕ N) :=
  ⟨⟨Sum.inl (Classical.arbitrary M), Sum.inr (Classical.arbitrary N), Sum.inl_ne_inr⟩⟩

@[simp] theorem product_one_left (b : HomotopyGroup N G 1) :
    product (1 : HomotopyGroup M G 1) b = 1 := by
  induction b using Quotient.inductionOn with
  | h q =>
    change (⟦loop (GenLoop.const : GenLoop M G 1) q⟧ : HomotopyGroup (M ⊕ N) G 1) =
      ⟦GenLoop.const⟧
    rw [loop_const_left]

@[simp] theorem product_one_right (a : HomotopyGroup M G 1) :
    product a (1 : HomotopyGroup N G 1) = 1 := by
  induction a using Quotient.inductionOn with
  | h p =>
    change (⟦loop p (GenLoop.const : GenLoop N G 1)⟧ : HomotopyGroup (M ⊕ N) G 1) =
      ⟦GenLoop.const⟧
    rw [loop_const_right]

theorem product_mul_left (a a' : HomotopyGroup M G 1) (b : HomotopyGroup N G 1) :
    product (a * a') b = product a b * product a' b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction a' using Quotient.inductionOn with
    | h p' =>
      induction b using Quotient.inductionOn with
      | h q =>
        let i : M := Classical.arbitrary M
        exact (congrArg (fun a => product a (⟦q⟧ : HomotopyGroup N G 1))
          (HomotopyGroup.mul_spec (i := i) (p := p) (q := p'))).trans
          ((congrArg (fun s : GenLoop (M ⊕ N) G 1 => (⟦s⟧ : HomotopyGroup (M ⊕ N) G 1))
            (loop_transAt_left i p' p q)).trans
            (HomotopyGroup.mul_spec (i := Sum.inl i) (p := loop p q) (q := loop p' q)).symm)

omit [Nonempty M] in
theorem product_mul_right (a : HomotopyGroup M G 1) (b b' : HomotopyGroup N G 1) :
    product a (b * b') = product a b * product a b' := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      induction b' using Quotient.inductionOn with
      | h q' =>
        let i : N := Classical.arbitrary N
        exact (congrArg (product (⟦p⟧ : HomotopyGroup M G 1))
          (HomotopyGroup.mul_spec (i := i) (p := q) (q := q'))).trans
          ((congrArg (fun s : GenLoop (M ⊕ N) G 1 => (⟦s⟧ : HomotopyGroup (M ⊕ N) G 1))
            (loop_transAt_right i p q' q)).trans
            (HomotopyGroup.mul_spec (i := Sum.inr i) (p := loop p q) (q := loop p q')).symm)

/-- The commutator pairing is a homomorphism in both variables. -/
def bilinear : HomotopyGroup M G 1 →*
    (HomotopyGroup N G 1 →* HomotopyGroup (M ⊕ N) G 1) where
  toFun a := {
    toFun := product a
    map_one' := product_one_right a
    map_mul' := product_mul_right a }
  map_one' := by ext b; exact product_one_left b
  map_mul' a a' := by ext b; exact product_mul_left a a' b

@[simp] theorem bilinear_apply (a : HomotopyGroup M G 1) (b : HomotopyGroup N G 1) :
    bilinear a b = product a b := rfl

theorem product_pow_left (a : HomotopyGroup M G 1) (b : HomotopyGroup N G 1) (k : ℕ) :
    product (a ^ k) b = product a b ^ k :=
  DFunLike.congr_fun (map_pow (bilinear (M := M) (N := N) (G := G)) a k) b

theorem product_pow_right (a : HomotopyGroup M G 1) (b : HomotopyGroup N G 1) (k : ℕ) :
    product a (b ^ k) = product a b ^ k := map_pow (bilinear a) b k

theorem product_zpow_left (a : HomotopyGroup M G 1) (b : HomotopyGroup N G 1) (k : ℤ) :
    product (a ^ k) b = product a b ^ k :=
  DFunLike.congr_fun (map_zpow (bilinear (M := M) (N := N) (G := G)) a k) b

theorem product_zpow_right (a : HomotopyGroup M G 1) (b : HomotopyGroup N G 1) (k : ℤ) :
    product a (b ^ k) = product a b ^ k := map_zpow (bilinear a) b k

theorem product_zpow_zpow (a : HomotopyGroup M G 1) (b : HomotopyGroup N G 1) (k l : ℤ) :
    product (a ^ k) (b ^ l) = product a b ^ (k * l) := by
  rw [product_zpow_left, product_zpow_right, ← zpow_mul, mul_comm l k]

end Wikipedia.HomotopyGroupsOfSpheres.Samelson

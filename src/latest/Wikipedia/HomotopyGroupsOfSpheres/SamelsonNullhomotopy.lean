import Wikipedia.HomotopyGroupsOfSpheres.Samelson
import Wikipedia.HopfProblem.HomotopyGroupPowerMap

/-!
# Turning a commutator null-homotopy into an exponent bound

A homotopy on a product need not initially fix its wedge. An explicit
normalization fixes the wedge throughout. Consequently a null-homotopy
of the pointwise `k`th power of a group's commutator kills every Samelson
product in the native homotopy group.

No such null-homotopy is assumed to have been constructed for `k = 12`.
-/

noncomputable section

open scoped Topology unitInterval commutatorElement

namespace Wikipedia.HomotopyGroupsOfSpheres.Samelson

variable {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- The two coordinate axes of a pointed product. -/
def wedge (x : X) (y : Y) : Set (X × Y) := {z | z.1 = x ∨ z.2 = y}

/-- Normalize a homotopy in a topological group so that it fixes both coordinate axes. -/
def fixWedge (x : X) (y : Y) {f g : C(X × Y, G)} (H : f.Homotopy g)
    (hf : ∀ z ∈ wedge x y, f z = 1) (hg : ∀ z ∈ wedge x y, g z = 1) :
    f.HomotopyRel g (wedge x y) where
  toFun tz := (H (tz.1, (tz.2.1, y)))⁻¹ * H (tz.1, tz.2) *
    (H (tz.1, (x, tz.2.2)))⁻¹ * H (tz.1, (x, y))
  continuous_toFun := by
    have hH := H.continuous
    fun_prop
  map_zero_left z := by
    simp only [ContinuousMap.Homotopy.apply_zero, hf (z.1, y) (Or.inr rfl),
      hf (x, z.2) (Or.inl rfl), hf (x, y) (Or.inl rfl), inv_one, one_mul, mul_one]
  map_one_left z := by
    simp only [ContinuousMap.Homotopy.apply_one, hg (z.1, y) (Or.inr rfl),
      hg (x, z.2) (Or.inl rfl), hg (x, y) (Or.inl rfl), inv_one, one_mul, mul_one]
  prop' t z hz := by
    rw [hf z hz]
    rcases z with ⟨a, b⟩
    rcases hz with rfl | rfl <;> simp [mul_assoc]

/-- The ordinary commutator map of a topological group. -/
def commutatorMap : C(G × G, G) :=
  ⟨fun z => ⁅z.1, z.2⁆, by simp only [commutatorElement_def]; fun_prop⟩

theorem commutatorMap_wedge (z : G × G) (hz : z ∈ wedge (1 : G) 1) :
    commutatorMap z = 1 := by
  rcases z with ⟨a, b⟩
  rcases hz with rfl | rfl <;> simp [commutatorMap]

/-- An actual global null-homotopy of a commutator power, corrected to fix the wedge. -/
def commutatorPowerHomotopy (k : ℕ)
    (H : (commutatorMap (G := G) ^ k).Homotopy (ContinuousMap.const _ 1)) :
    (commutatorMap (G := G) ^ k).HomotopyRel (ContinuousMap.const _ 1) (wedge (1 : G) 1) :=
  fixWedge 1 1 H
    (fun z hz => by simp only [ContinuousMap.pow_apply, commutatorMap_wedge z hz, one_pow])
    (fun _ _ => rfl)

variable {M N : Type*}

/-- Compose a wedge-fixed commutator contraction with arbitrary two cubical representatives. -/
def loopPowerHomotopy (k : ℕ)
    (H : (commutatorMap (G := G) ^ k).Homotopy (ContinuousMap.const _ 1))
    (p : GenLoop M G 1) (q : GenLoop N G 1) :
    (HopfProblem.HomotopyGroupPowerMap.powLoop (loop p q) k).val.HomotopyRel
      (GenLoop.const : GenLoop (M ⊕ N) G 1).val (Cube.boundary (M ⊕ N)) where
  toFun tu := commutatorPowerHomotopy k H (tu.1, (p (tu.2 ∘ Sum.inl), q (tu.2 ∘ Sum.inr)))
  continuous_toFun := by fun_prop
  map_zero_left t := (commutatorPowerHomotopy k H).map_zero_left _
  map_one_left t := (commutatorPowerHomotopy k H).map_one_left _
  prop' s t ht := by
    apply (commutatorPowerHomotopy k H).eq_fst s
    rcases Cube.boundary_sum_iff.mp ht with hp | hq
    · exact Or.inl (p.property _ hp)
    · exact Or.inr (q.property _ hq)

variable [DecidableEq M] [DecidableEq N] [Nonempty M]

/-- A proved global commutator contraction gives an exponent bound on every Samelson product. -/
theorem product_pow_eq_one_of_nullhomotopy (k : ℕ)
    (h : (commutatorMap (G := G) ^ k).Homotopic (ContinuousMap.const _ 1))
    (a : HomotopyGroup M G 1) (b : HomotopyGroup N G 1) : product a b ^ k = 1 := by
  obtain ⟨H⟩ := h
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      exact (HopfProblem.HomotopyGroupPowerMap.class_powLoop (loop p q) k).symm.trans
        (Quotient.sound ⟨loopPowerHomotopy k H p q⟩)

end Wikipedia.HomotopyGroupsOfSpheres.Samelson

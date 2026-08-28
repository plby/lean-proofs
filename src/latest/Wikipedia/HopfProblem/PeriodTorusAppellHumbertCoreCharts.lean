import Wikipedia.HopfProblem.PeriodTorusAppellHumbertData
import Wikipedia.HopfProblem.CoveringManifold

/-!
# Local lifts in the existing period-torus atlas

The charts are exactly the `DiscreteQuotient` charts already used for the
period torus. Their differences on overlaps are lattice elements, locally
constant by uniqueness of lifts through a local homeomorphism.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core

variable (p : PeriodDomain)

/-- The existing local quotient lift; no new base atlas is installed. -/
def lift (i : p.Torus) : OpenPartialHomeomorph p.Torus ComplexPlane₂ :=
  DiscreteQuotient.chart p.lattice i

def baseSet (i : p.Torus) : Set p.Torus := (lift p i).source

theorem isOpen_baseSet (i : p.Torus) : IsOpen (baseSet p i) :=
  (lift p i).open_source

theorem mem_baseSet (i : p.Torus) : i ∈ baseSet p i :=
  mem_chart_source ComplexPlane₂ i

theorem lift_project (i : p.Torus) {x : p.Torus} (hx : x ∈ baseSet p i) :
    p.lattice.mkQ (lift p i x) = x :=
  DiscreteQuotient.mkQ_chart p.lattice i x hx

@[simp] theorem lift_symm (i : p.Torus) :
    (lift p i).symm = (p.lattice.mkQ : ComplexPlane₂ → p.Torus) :=
  DiscreteQuotient.chart_symm p.lattice i

@[simp] theorem mkQ_lattice (l : p.lattice) : p.lattice.mkQ l = 0 :=
  (Submodule.Quotient.mk_eq_zero p.lattice).mpr l.property

theorem lift_sub_lift_mem (i j : p.Torus) {x : p.Torus}
    (hx : x ∈ baseSet p i ∩ baseSet p j) : lift p j x - lift p i x ∈ p.lattice := by
  apply (Submodule.Quotient.eq p.lattice).mp
  exact (lift_project p j hx.2).trans (lift_project p i hx.1).symm

/-- The translation from the first lift to the second, extended by zero
off their overlap. -/
def deck (i j x : p.Torus) : p.lattice := by
  classical
  exact if hx : x ∈ baseSet p i ∩ baseSet p j then
    ⟨lift p j x - lift p i x, lift_sub_lift_mem p i j hx⟩ else 0

theorem deck_coe (i j : p.Torus) {x : p.Torus}
    (hx : x ∈ baseSet p i ∩ baseSet p j) :
    (deck p i j x : ComplexPlane₂) = lift p j x - lift p i x := by
  classical
  simp only [deck, dif_pos hx]

theorem deck_spec (i j : p.Torus) {x : p.Torus}
    (hx : x ∈ baseSet p i ∩ baseSet p j) :
    lift p i x + deck p i j x = lift p j x := by
  rw [deck_coe p i j hx]
  abel

theorem deck_eq_of_add (i j : p.Torus) {x : p.Torus}
    (hx : x ∈ baseSet p i ∩ baseSet p j) (l : p.lattice)
    (hl : lift p i x + l = lift p j x) : deck p i j x = l := by
  apply Subtype.ext
  exact add_left_cancel ((deck_spec p i j hx).trans hl.symm)

theorem deck_self (i : p.Torus) {x : p.Torus} (hx : x ∈ baseSet p i) :
    deck p i i x = 0 :=
  deck_eq_of_add p i i ⟨hx, hx⟩ 0 (add_zero _)

theorem deck_comp (i j k : p.Torus) {x : p.Torus}
    (hx : x ∈ baseSet p i ∩ baseSet p j ∩ baseSet p k) :
    deck p j k x + deck p i j x = deck p i k x := by
  apply Subtype.ext
  rw [Submodule.coe_add, deck_coe p j k ⟨hx.1.2, hx.2⟩,
    deck_coe p i j hx.1, deck_coe p i k ⟨hx.1.1, hx.2⟩]
  abel

/-- The deck translation is locally fixed on every overlap. -/
theorem deck_locally_constant (i j : p.Torus) {x : p.Torus}
    (hx : x ∈ baseSet p i ∩ baseSet p j) :
    deck p i j =ᶠ[𝓝 x] fun _ => deck p i j x := by
  have hU : ∀ᶠ y in 𝓝 x, y ∈ baseSet p i ∩ baseSet p j :=
    ((isOpen_baseSet p i).inter (isOpen_baseSet p j)).mem_nhds hx
  have he : (lift p j : p.Torus → ComplexPlane₂) =ᶠ[𝓝 x]
      fun y => lift p i y + deck p i j x := by
    apply eventuallyEq_of_localHomeomorph_comp_eq
      (DiscreteQuotient.quotient_localHomeomorph p.lattice)
      ((lift p j).continuousAt hx.2)
      (((lift p i).continuousAt hx.1).add continuousAt_const)
      (deck_spec p i j hx).symm
    filter_upwards [hU] with y hy
    change p.lattice.mkQ (lift p j y) =
      p.lattice.mkQ (lift p i y + deck p i j x)
    rw [map_add, mkQ_lattice, add_zero, lift_project p i hy.1, lift_project p j hy.2]
  filter_upwards [hU, he] with y hy hey
  exact deck_eq_of_add p i j hy (deck p i j x) hey.symm

/-- Each chosen lift is holomorphic for the original quotient atlas. -/
theorem lift_holomorphic (i : p.Torus) :
    ContMDiffOn (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (lift p i) (baseSet p i) :=
  contMDiffOn_chart

/-- Pulling a local lift back to the covering space is locally translation
by an actual lattice vector. -/
theorem lift_comp_mkQ_locally_add (i : p.Torus) (a : ComplexPlane₂)
    (ha : p.lattice.mkQ a ∈ baseSet p i) :
    ∃ l : p.lattice, (fun b => lift p i (p.lattice.mkQ b)) =ᶠ[𝓝 a]
      (fun b => b + l) := by
  let l : p.lattice := ⟨lift p i (p.lattice.mkQ a) - a,
    (Submodule.Quotient.eq p.lattice).mp (lift_project p i ha)⟩
  refine ⟨l, ?_⟩
  apply eventuallyEq_of_localHomeomorph_comp_eq
    (DiscreteQuotient.quotient_localHomeomorph p.lattice)
    (((lift p i).continuousAt ha).comp p.lattice.continuous_mkQ.continuousAt)
    (continuousAt_id.add continuousAt_const)
  · dsimp [l]
    abel
  · have hU : ∀ᶠ b in 𝓝 a, p.lattice.mkQ b ∈ baseSet p i :=
      p.lattice.continuous_mkQ.continuousAt ((isOpen_baseSet p i).mem_nhds ha)
    filter_upwards [hU] with b hb
    change p.lattice.mkQ (lift p i (p.lattice.mkQ b)) = p.lattice.mkQ (b + l)
    rw [map_add, mkQ_lattice, add_zero, lift_project p i hb]

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core

import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupGenerationCore
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupPathInduction
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Actual loop generation by overlap components

For a two-set simply connected open cover, loops going out through the
first set and returning through the second generate the actual fundamental
group. One representative in each path component of the overlap suffices.
The proof subdivides paths into the given open sets.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroup

variable {X : Type*} [TopologicalSpace X]

open Path.Homotopic.Quotient

namespace TwoSimplyConnectedCover

variable (D : TwoSimplyConnectedCover X)

theorem memV_of_not_memU {x : X} (hx : x ∉ D.U) : x ∈ D.V := by
  have h : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact h.resolve_left hx

/-- A path-class section chosen from one of the two actual open sets. -/
def basedSection (x : X) : Path.Homotopic.Quotient D.base x := by
  classical
  exact if hx : x ∈ D.U then Path.Homotopic.Quotient.mk (D.pathU x hx)
    else Path.Homotopic.Quotient.mk (D.pathV x (D.memV_of_not_memU hx))

theorem basedSection_eq_U {x : X} (hx : x ∈ D.U) :
    D.basedSection x = Path.Homotopic.Quotient.mk (D.pathU x hx) := by
  simp only [basedSection, dif_pos hx]

theorem basedSection_eq_V {x : X} (hxU : x ∉ D.U) (hxV : x ∈ D.V) :
    D.basedSection x = Path.Homotopic.Quotient.mk (D.pathV x hxV) := by
  simp only [basedSection, dif_neg hxU]

@[simp] theorem basedSection_base : D.basedSection D.base =
    Path.Homotopic.Quotient.refl D.base := by
  rw [D.basedSection_eq_U D.baseU]
  apply Path.Homotopic.Quotient.eq.mpr
  exact SimplyConnectedCover.homotopic_of_mem D.simplyU _ _
    (D.pathU_mem _ _) (fun _ => D.baseU)

theorem comparisonU_mem (H : Subgroup (FundamentalGroup X D.base))
    {x : X} (hx : x ∈ D.U) :
    pathDifference (D.basedSection x) (Path.Homotopic.Quotient.mk (D.pathU x hx)) ∈ H := by
  rw [D.basedSection_eq_U hx]
  simpa only [pathDifference, trans_symm, FundamentalGroup.one_def] using H.one_mem

theorem comparisonV_mem (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H)
    {x : X} (hx : x ∈ D.V) :
    pathDifference (D.basedSection x) (Path.Homotopic.Quotient.mk (D.pathV x hx)) ∈ H := by
  by_cases hxU : x ∈ D.U
  · rw [D.basedSection_eq_U hxU]
    exact hH x hxU hx
  · rw [D.basedSection_eq_V hxU hx]
    simpa only [pathDifference, trans_symm, FundamentalGroup.one_def] using H.one_mem

theorem basedLoop_mem_of_path_in_U (H : Subgroup (FundamentalGroup X D.base))
    {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.U) :
    basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) ∈ H := by
  have hx : x ∈ D.U := by simpa using hp 0
  have hy : y ∈ D.U := by simpa using hp 1
  rw [basedLoop_comparison D.basedSection
    (Path.Homotopic.Quotient.mk (D.pathU x hx))
    (Path.Homotopic.Quotient.mk (D.pathU y hy))
    (Path.Homotopic.Quotient.mk p) (D.pathU_trans hx hy p hp)]
  exact H.mul_mem (H.inv_mem (D.comparisonU_mem H hy)) (D.comparisonU_mem H hx)

theorem basedLoop_mem_of_path_in_V (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H)
    {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.V) :
    basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) ∈ H := by
  have hx : x ∈ D.V := by simpa using hp 0
  have hy : y ∈ D.V := by simpa using hp 1
  rw [basedLoop_comparison D.basedSection
    (Path.Homotopic.Quotient.mk (D.pathV x hx))
    (Path.Homotopic.Quotient.mk (D.pathV y hy))
    (Path.Homotopic.Quotient.mk p) (D.pathV_trans hx hy p hp)]
  exact H.mul_mem (H.inv_mem (D.comparisonV_mem H hH hy)) (D.comparisonV_mem H hH hx)

/-- Any subgroup containing the actual two-chart switch loops is the whole
fundamental group. -/
theorem subgroup_eq_top_of_switchClass_mem (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H) :
    H = ⊤ := by
  let W : Bool → Set X := fun b => if b then D.V else D.U
  have hopen : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact D.U.isOpen
    · exact D.V.isOpen
  have hcover : ⋃ b, W b = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨false, hx⟩
    · exact mem_iUnion.mpr ⟨true, hx⟩
  have hall : ∀ {x y : X} (q : Path.Homotopic.Quotient x y),
      basedLoop D.basedSection q ∈ H := by
    apply pathClass_induction_of_open_cover W hopen hcover
      (fun q => basedLoop D.basedSection q ∈ H)
    · intro x
      rw [basedLoop_refl]
      exact H.one_mem
    · intro x y z p q hp hq
      rw [basedLoop_trans]
      exact H.mul_mem hq hp
    · intro b x y p hp
      cases b
      · exact D.basedLoop_mem_of_path_in_U H p (fun t => hp ⟨t, rfl⟩)
      · exact D.basedLoop_mem_of_path_in_V H hH p (fun t => hp ⟨t, rfl⟩)
  apply top_unique
  intro q _
  have hq := hall q
  have hrefl : (Path.Homotopic.Quotient.refl D.base).symm =
      Path.Homotopic.Quotient.refl D.base := by
    change (1 : FundamentalGroup X D.base)⁻¹ = 1
    exact inv_one
  simpa only [basedLoop, D.basedSection_base, refl_trans, hrefl, trans_refl] using hq

/-- A representative of every path component of the overlap yields generators. -/
theorem closure_switchClasses_eq_top {ι : Type*} (r : ι → X)
    (hrU : ∀ i, r i ∈ D.U) (hrV : ∀ i, r i ∈ D.V)
    (hr : ∀ x, x ∈ D.U → x ∈ D.V →
      ∃ i, JoinedIn ((D.U : Set X) ∩ D.V) (r i) x) :
    Subgroup.closure (range (fun i => D.switchClass (r i) (hrU i) (hrV i))) = ⊤ := by
  apply D.subgroup_eq_top_of_switchClass_mem
  intro x hxU hxV
  obtain ⟨i, hi⟩ := hr x hxU hxV
  rw [← D.switchClass_eq_of_joinedIn (hrU i) (hrV i) hxU hxV hi]
  exact Subgroup.subset_closure ⟨i, rfl⟩

/-- The choice of paths inside each simply connected set can be replaced
by any explicitly supplied paths, without changing the loop class. -/
theorem switchClass_eq_of_paths {x : X} (hxU : x ∈ D.U) (hxV : x ∈ D.V)
    (p q : Path D.base x) (hp : ∀ t, p t ∈ D.U) (hq : ∀ t, q t ∈ D.V) :
    D.switchClass x hxU hxV =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.trans q.symm)) := by
  have hU : Path.Homotopic.Quotient.mk (D.pathU x hxU) =
      Path.Homotopic.Quotient.mk p :=
    Path.Homotopic.Quotient.eq.mpr
      (SimplyConnectedCover.homotopic_of_mem D.simplyU _ _ (D.pathU_mem x hxU) hp)
  have hV : Path.Homotopic.Quotient.mk (D.pathV x hxV) =
      Path.Homotopic.Quotient.mk q :=
    Path.Homotopic.Quotient.eq.mpr
      (SimplyConnectedCover.homotopic_of_mem D.simplyV _ _ (D.pathV_mem x hxV) hq)
  simp only [switchClass, hU, hV, FundamentalGroup.fromPath, FundamentalGroup.fromArrow,
    mk_trans, mk_symm]

end TwoSimplyConnectedCover

end Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroup

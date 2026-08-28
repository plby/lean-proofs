import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupGenerationCore
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupPathInduction
import Wikipedia.HopfProblem.FundamentalGroupVanKampenPathSubtypes
import Mathlib.GroupTheory.Finiteness

/-!

# Old loops and switch loops generate a simply connected patch attachment

The old open set is only path connected. Its actual fundamental-group
image must be retained, together with loops going to an overlap point
through the old set and returning through the simply connected patch.
The overlap is allowed to be disconnected. The proof uses the existing
open-cover induction on actual path-homotopy classes.
-/

noncomputable section

open Set Function ContinuousMap Path.Homotopic.Quotient
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.PatchLoopGeneration

open TriangleRegularBaseFundamentalGroup FundamentalGroupVanKampen

structure Cover (X : Type*) [TopologicalSpace X] where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ V = univ
  pathConnectedU : IsPathConnected (U : Set X)
  simplyV : IsSimplyConnected (V : Set X)
  base : X
  baseU : base ∈ U
  baseV : base ∈ V

namespace Cover

variable {X : Type*} [TopologicalSpace X] (D : Cover X)

def pathU (x : X) (hx : x ∈ D.U) : Path D.base x := by
  classical
  exact if h : x = D.base then (Path.refl D.base).cast rfl h else
    (D.pathConnectedU.joinedIn D.base D.baseU x hx).somePath

theorem pathU_mem (x : X) (hx : x ∈ D.U) (t : unitInterval) :
    D.pathU x hx t ∈ D.U := by
  classical
  unfold pathU
  split_ifs with h
  · exact D.baseU
  · exact JoinedIn.somePath_mem _ t

@[simp] theorem pathU_base : D.pathU D.base D.baseU = Path.refl D.base := by
  classical
  simp [pathU]

def pathV (x : X) (hx : x ∈ D.V) : Path D.base x :=
  (D.simplyV.isPathConnected.joinedIn D.base D.baseV x hx).somePath

theorem pathV_mem (x : X) (hx : x ∈ D.V) (t : unitInterval) :
    D.pathV x hx t ∈ D.V := JoinedIn.somePath_mem _ t

theorem pathV_trans {x y : X} (hx : x ∈ D.V) (hy : y ∈ D.V)
    (p : Path x y) (hp : ∀ t, p t ∈ D.V) :
    (Path.Homotopic.Quotient.mk (D.pathV x hx)).trans (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (D.pathV y hy) := by
  rw [← mk_trans, eq]
  exact SimplyConnectedCover.homotopic_of_mem D.simplyV _ _
    (SimplyConnectedCover.trans_mem _ _ (D.pathV_mem x hx) hp) (D.pathV_mem y hy)

theorem memV_of_not_memU {x : X} (hx : x ∉ D.U) : x ∈ D.V := by
  have h : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact h.resolve_left hx

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

@[simp] theorem basedSection_base :
    D.basedSection D.base = Path.Homotopic.Quotient.refl D.base := by
  rw [D.basedSection_eq_U D.baseU, D.pathU_base, mk_refl]

def inclusionHomU : FundamentalGroup D.U (⟨D.base, D.baseU⟩ : D.U) →*
    FundamentalGroup X D.base :=
  FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(D.U, X)) ⟨D.base, D.baseU⟩

def switchClass (x : X) (hxU : x ∈ D.U) (hxV : x ∈ D.V) :
    FundamentalGroup X D.base :=
  pathDifference (Path.Homotopic.Quotient.mk (D.pathU x hxU))
    (Path.Homotopic.Quotient.mk (D.pathV x hxV))

theorem basedLoop_mem_of_path_in_U (K : Subgroup (FundamentalGroup X D.base))
    (hK : D.inclusionHomU.range ≤ K) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.U) :
    basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) ∈ K := by
  have hx : x ∈ D.U := by simpa using hp 0
  have hy : y ∈ D.U := by simpa using hp 1
  let px := pathIn (D.pathU x hx) D.baseU hx (D.pathU_mem x hx)
  let py := pathIn (D.pathU y hy) D.baseU hy (D.pathU_mem y hy)
  let pp := pathIn p hx hy hp
  let q := (px.trans pp).trans py.symm
  have he : D.inclusionHomU (Path.Homotopic.Quotient.mk q) =
      basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) := by
    rw [basedLoop, D.basedSection_eq_U hx, D.basedSection_eq_U hy]
    change Path.Homotopic.Quotient.mk (q.map continuous_subtype_val) =
      Path.Homotopic.Quotient.mk (((D.pathU x hx).trans p).trans (D.pathU y hy).symm)
    rw [show q = (px.trans pp).trans py.symm from rfl,
      Path.map_trans, Path.map_trans, ← Path.map_symm]
    rw [pathIn_map, pathIn_map, pathIn_map]
  rw [← he]
  exact hK ⟨Path.Homotopic.Quotient.mk q, rfl⟩

theorem comparisonV_mem (K : Subgroup (FundamentalGroup X D.base))
    (hK : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ K)
    {x : X} (hx : x ∈ D.V) :
    pathDifference (D.basedSection x) (Path.Homotopic.Quotient.mk (D.pathV x hx)) ∈ K := by
  by_cases hxU : x ∈ D.U
  · rw [D.basedSection_eq_U hxU]
    exact hK x hxU hx
  · rw [D.basedSection_eq_V hxU hx]
    simpa only [pathDifference, trans_symm, FundamentalGroup.one_def] using K.one_mem

theorem basedLoop_mem_of_path_in_V (K : Subgroup (FundamentalGroup X D.base))
    (hK : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ K)
    {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.V) :
    basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) ∈ K := by
  have hx : x ∈ D.V := by simpa using hp 0
  have hy : y ∈ D.V := by simpa using hp 1
  rw [basedLoop_comparison D.basedSection (Path.Homotopic.Quotient.mk (D.pathV x hx))
    (Path.Homotopic.Quotient.mk (D.pathV y hy))
    (Path.Homotopic.Quotient.mk p) (D.pathV_trans hx hy p hp)]
  exact K.mul_mem (K.inv_mem (D.comparisonV_mem K hK hy)) (D.comparisonV_mem K hK hx)

theorem subgroup_eq_top_of_old_and_switch_mem (K : Subgroup (FundamentalGroup X D.base))
    (hU : D.inclusionHomU.range ≤ K)
    (hK : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ K) : K = ⊤ := by
  let W : Bool → Set X := fun b ↦ if b then D.V else D.U
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
      basedLoop D.basedSection q ∈ K := by
    apply pathClass_induction_of_open_cover W hopen hcover
      (fun q ↦ basedLoop D.basedSection q ∈ K)
    · intro x
      rw [basedLoop_refl]
      exact K.one_mem
    · intro x y z p q hp hq
      rw [basedLoop_trans]
      exact K.mul_mem hq hp
    · intro b x y p hp
      cases b
      · exact D.basedLoop_mem_of_path_in_U K hU p (fun t ↦ hp ⟨t, rfl⟩)
      · exact D.basedLoop_mem_of_path_in_V K hK p (fun t ↦ hp ⟨t, rfl⟩)
  apply top_unique
  intro q _
  have hq := hall q
  have hrefl : (Path.Homotopic.Quotient.refl D.base).symm =
      Path.Homotopic.Quotient.refl D.base := by
    change (1 : FundamentalGroup X D.base)⁻¹ = 1
    exact inv_one
  simpa only [basedLoop, D.basedSection_base, refl_trans, hrefl, trans_refl] using hq

theorem switchClass_mem_of_joinedIn (K : Subgroup (FundamentalGroup X D.base))
    (hU : D.inclusionHomU.range ≤ K) {x y : X}
    (hxU : x ∈ D.U) (hxV : x ∈ D.V) (hyU : y ∈ D.U) (hyV : y ∈ D.V)
    (hxy : JoinedIn ((D.U : Set X) ∩ D.V) x y) (hx : D.switchClass x hxU hxV ∈ K) :
    D.switchClass y hyU hyV ∈ K := by
  let p := hxy.somePath
  have hV := D.pathV_trans hxV hyV p (fun t ↦ (hxy.somePath_mem t).2)
  have hloop := D.basedLoop_mem_of_path_in_U K hU p (fun t ↦ (hxy.somePath_mem t).1)
  have heq : D.switchClass y hyU hyV = D.switchClass x hxU hxV *
      (basedLoop D.basedSection (Path.Homotopic.Quotient.mk p))⁻¹ := by
    change (Path.Homotopic.Quotient.mk (D.pathU y hyU)).trans
        (Path.Homotopic.Quotient.mk (D.pathV y hyV)).symm =
      (basedLoop D.basedSection (Path.Homotopic.Quotient.mk p)).symm.trans
        ((Path.Homotopic.Quotient.mk (D.pathU x hxU)).trans
          (Path.Homotopic.Quotient.mk (D.pathV x hxV)).symm)
    rw [basedLoop, D.basedSection_eq_U hxU, D.basedSection_eq_U hyU, ← hV]
    simp only [← mk_trans, ← mk_symm, Path.trans_symm, Path.symm_symm]
    simp only [mk_trans, mk_symm, trans_assoc, quotient_symm_trans_cancel]
  rw [heq]
  exact K.mul_mem hx (K.inv_mem hloop)

/-- Finitely many overlap components and a finitely generated old group suffice. -/
theorem fg_of_finite_overlap
    [Group.FG (FundamentalGroup D.U (⟨D.base, D.baseU⟩ : D.U))]
    {ι : Type*} [Finite ι] (r : ι → X) (hrU : ∀ i, r i ∈ D.U) (hrV : ∀ i, r i ∈ D.V)
    (hr : ∀ x, x ∈ D.U → x ∈ D.V →
      ∃ i, JoinedIn ((D.U : Set X) ∩ D.V) (r i) x) :
    Group.FG (FundamentalGroup X D.base) := by
  let s : ι → FundamentalGroup X D.base := fun i ↦ D.switchClass (r i) (hrU i) (hrV i)
  let K : Subgroup (FundamentalGroup X D.base) :=
    D.inclusionHomU.range ⊔ Subgroup.closure (range s)
  have hswitch : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ K := by
    intro x hxU hxV
    obtain ⟨i, hi⟩ := hr x hxU hxV
    apply D.switchClass_mem_of_joinedIn K le_sup_left (hrU i) (hrV i) hxU hxV hi
    have hi : s i ∈ Subgroup.closure (range s) := Subgroup.subset_closure (mem_range_self i)
    exact (show Subgroup.closure (range s) ≤ K from le_sup_right) hi
  have htop : K = ⊤ := D.subgroup_eq_top_of_old_and_switch_mem K le_sup_left hswitch
  have hOld : D.inclusionHomU.range.FG := (Group.fg_iff_subgroup_fg _).mp inferInstance
  have hSwitch : (Subgroup.closure (range s)).FG :=
    (Subgroup.fg_iff _).mpr ⟨range s, rfl, Set.finite_range s⟩
  have hK : K.FG := hOld.sup hSwitch
  exact ⟨htop ▸ hK⟩

end Cover
end Wikipedia.HopfProblem.DegreeCollapse.PatchLoopGeneration

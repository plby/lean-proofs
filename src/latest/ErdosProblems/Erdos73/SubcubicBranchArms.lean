/- A supported arm system inside every branch of a subcubic minor model. -/
import ErdosProblems.Erdos73.SubdivisionEdges
import ErdosProblems.Erdos73.MinorModels
import ErdosProblems.Erdos73.JoinPathEdge

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

structure SubcubicBranchArms (M : MinorModel H G) where
  center : W → V
  center_mem : ∀ w, center w ∈ M.branchSet w
  arm : ∀ w, IncidentOrientedEdge H w → GraphPath G
  source_eq : ∀ w e, (arm w e).source = center w
  stays : ∀ w e, (arm w e).vertexSet ⊆ M.branchSet w
  intersection : ∀ w, ∀ ⦃e f : IncidentOrientedEdge H w⦄, e ≠ f →
    ∀ v, v ∈ (arm w e).vertexSet → v ∈ (arm w f).vertexSet → v = center w
  link : ∀ e : OrientedEdge H,
    G.Adj (arm e.lo e.incidentLo).target (arm e.hi e.incidentHi).target

theorem exists_subcubicBranchArms (M : MinorModel H G) (hdeg : ∀ w, H.degree w ≤ 3) :
    Nonempty (SubcubicBranchArms M) := by
  choose a ha b hb hab using fun e : OrientedEdge H => M.adjacent e.adj
  let terminal (w : W) (e : IncidentOrientedEdge H w) :=
    if e.val.lo = w then a e.val else b e.val
  have hterminal (w : W) (e : IncidentOrientedEdge H w) : terminal w e ∈ M.branchSet w := by
    dsimp only [terminal]
    split
    next he => exact (congrArg (fun z => a e.val ∈ M.branchSet z) he).mp (ha e.val)
    next he => exact (congrArg (fun z => b e.val ∈ M.branchSet z)
      (e.property.resolve_left he)).mp (hb e.val)
  have hex (w : W) := exists_disjointArms_of_card_le_three
    (M.branchSet w) (M.branch_connected w) (terminal w) (hterminal w)
    ((card_incidentOrientedEdge_le_degree w).trans (hdeg w))
  choose A hA hAS using hex
  refine ⟨{
    center := fun w => (A w).center
    center_mem := hA
    arm := fun w => (A w).arm
    source_eq := fun w => (A w).source_eq
    stays := hAS
    intersection := fun w => (A w).intersection
    link := ?_ }⟩
  intro e
  rw [(A e.lo).target_eq, (A e.hi).target_eq]
  change G.Adj (if e.lo = e.lo then a e else b e) (if e.lo = e.hi then a e else b e)
  rw [if_pos rfl, if_neg e.lo_lt_hi.ne]
  exact hab e

namespace SubcubicBranchArms
variable {M : MinorModel H G} (A : SubcubicBranchArms M)

theorem center_injective : Function.Injective A.center := by
  intro u v huv
  by_contra hne
  exact Finset.disjoint_left.mp (M.branch_disjoint hne) (A.center_mem u)
    (huv ▸ A.center_mem v)

def edgePath (e : OrientedEdge H) : GraphPath G :=
  (A.arm e.lo e.incidentLo).joinViaEdge (A.arm e.hi e.incidentHi).reverse (A.link e)

theorem edgePath_source (e : OrientedEdge H) : (A.edgePath e).source = A.center e.lo :=
  A.source_eq _ _

theorem edgePath_target (e : OrientedEdge H) : (A.edgePath e).target = A.center e.hi :=
  A.source_eq _ _

theorem edgePath_subset_arms (e : OrientedEdge H) :
    (A.edgePath e).vertexSet ⊆ (A.arm e.lo e.incidentLo).vertexSet ∪
      (A.arm e.hi e.incidentHi).vertexSet := by
  have hs := GraphPath.joinViaEdge_vertexSet_subset (A.arm e.lo e.incidentLo)
    (A.arm e.hi e.incidentHi).reverse (A.link e)
  rw [GraphPath.reverse_vertexSet] at hs
  exact hs

theorem edgePath_subset_branches (e : OrientedEdge H) :
    (A.edgePath e).vertexSet ⊆ M.branchSet e.lo ∪ M.branchSet e.hi :=
  (A.edgePath_subset_arms e).trans (Finset.union_subset_union (A.stays _ _) (A.stays _ _))

/-- An arm cannot contain the centre of a different minor branch. -/
theorem eq_of_center_mem_arm {w z : W} {e : IncidentOrientedEdge H w}
    (hz : A.center z ∈ (A.arm w e).vertexSet) : z = w := by
  by_contra hne
  exact Finset.disjoint_left.mp (M.branch_disjoint hne) (A.center_mem z) (A.stays w e hz)

theorem branchVertex_on_edgePath {e : OrientedEdge H} {w : W}
    (hw : A.center w ∈ (A.edgePath e).vertexSet) : w = e.lo ∨ w = e.hi := by
  rcases Finset.mem_union.mp (A.edgePath_subset_arms e hw) with hlo | hhi
  · exact Or.inl (A.eq_of_center_mem_arm hlo)
  · exact Or.inr (A.eq_of_center_mem_arm hhi)

theorem arms_intersection_of_distinct_edges {u w : W}
    {e : IncidentOrientedEdge H u} {f : IncidentOrientedEdge H w}
    (hef : e.val ≠ f.val) {v : V}
    (hve : v ∈ (A.arm u e).vertexSet) (hvf : v ∈ (A.arm w f).vertexSet) :
    u = w ∧ v = A.center u := by
  have huw : u = w := by
    by_contra hne
    exact Finset.disjoint_left.mp (M.branch_disjoint hne) (A.stays _ _ hve) (A.stays _ _ hvf)
  subst w
  exact ⟨rfl, A.intersection u (fun h => hef (congrArg Subtype.val h)) v hve hvf⟩

theorem edgePaths_intersection {e f : OrientedEdge H} (hef : e ≠ f) {v : V}
    (hve : v ∈ (A.edgePath e).vertexSet) (hvf : v ∈ (A.edgePath f).vertexSet) :
    ∃ w, v = A.center w ∧ (w = e.lo ∨ w = e.hi) ∧ (w = f.lo ∨ w = f.hi) := by
  rcases Finset.mem_union.mp (A.edgePath_subset_arms e hve) with he | he <;>
    rcases Finset.mem_union.mp (A.edgePath_subset_arms f hvf) with hf | hf
  · obtain ⟨hw, hv⟩ := A.arms_intersection_of_distinct_edges hef he hf
    exact ⟨e.lo, hv, Or.inl rfl, Or.inl hw⟩
  · obtain ⟨hw, hv⟩ := A.arms_intersection_of_distinct_edges hef he hf
    exact ⟨e.lo, hv, Or.inl rfl, Or.inr hw⟩
  · obtain ⟨hw, hv⟩ := A.arms_intersection_of_distinct_edges hef he hf
    exact ⟨e.hi, hv, Or.inr rfl, Or.inl hw⟩
  · obtain ⟨hw, hv⟩ := A.arms_intersection_of_distinct_edges hef he hf
    exact ⟨e.hi, hv, Or.inr rfl, Or.inr hw⟩

end SubcubicBranchArms
end
end Erdos73

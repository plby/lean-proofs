import Wikipedia.NoExoticSixSphere.JamesSphereCellCharts
import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# The genuine CW structure on the James space of a positive-dimensional sphere

The length-`k` stratum is a cell of dimension `k * n`. The characteristic
maps, inverse continuity, closure finiteness, and weak topology are proved
for the original reduced-word space and its original final topology.
This is Mathlib's classical `CWComplex` structure, not a replacement type.
-/

noncomputable section

open Set Metric Topology

namespace NoExoticSixSphere.JamesSphere.CW

abbrev CellIndex (n d : ℕ) := {k : ℕ // k * n = d}

theorem cellIndex_subsingleton (n : ℕ) (hn : 0 < n) (d : ℕ) :
    Subsingleton (CellIndex n d) := by
  constructor
  intro i j
  exact Subtype.ext (Nat.mul_right_cancel hn (i.property.trans j.property.symm))

theorem cellIndex_finite (n : ℕ) (hn : 0 < n) (d : ℕ) : Finite (CellIndex n d) := by
  let := cellIndex_subsingleton n hn d
  infer_instance

def attachingMap (n d : ℕ) (i : CellIndex n d) :
    PartialEquiv (Fin d → ℝ) (James.Space (Sphere n) (spherePole n)) := by
  rcases i with ⟨k, rfl⟩
  exact Cell.chart n k

theorem attachingMap_mk (n k : ℕ) : attachingMap n (k * n) ⟨k, rfl⟩ = Cell.chart n k := rfl

theorem attachingMap_source (n d : ℕ) (i : CellIndex n d) :
    (attachingMap n d i).source = ball 0 1 := by
  rcases i with ⟨k, rfl⟩
  exact Cell.chart_source n k

theorem attachingMap_continuousOn (n d : ℕ) (i : CellIndex n d) :
    ContinuousOn (attachingMap n d i) (closedBall 0 1) := by
  rcases i with ⟨k, rfl⟩
  exact Cell.chart_continuousOn n k

theorem attachingMap_continuousOn_symm (n : ℕ) (hn : 0 < n) (d : ℕ) (i : CellIndex n d) :
    ContinuousOn (attachingMap n d i).symm (attachingMap n d i).target := by
  rcases i with ⟨k, rfl⟩
  exact Cell.chart_continuousOn_symm n k hn

theorem attachingMap_image_ball (n : ℕ) (hn : 0 < n) (d : ℕ) (i : CellIndex n d) :
    attachingMap n d i '' ball 0 1 = {w | James.size (spherePole n) w = i.val} := by
  rcases i with ⟨k, rfl⟩
  exact Cell.image_ball n k hn

theorem attachingMap_image_closedBall (n : ℕ) (hn : 0 < n) (d : ℕ) (i : CellIndex n d) :
    attachingMap n d i '' closedBall 0 1 = James.stage (spherePole n) i.val := by
  rcases i with ⟨k, rfl⟩
  exact Cell.image_closedBall n k hn

theorem cells_pairwiseDisjoint (n : ℕ) (hn : 0 < n) :
    (univ : Set (Σ d, CellIndex n d)).PairwiseDisjoint
      (fun di ↦ attachingMap n di.1 di.2 '' ball 0 1) := by
  rintro ⟨d, ⟨k, rfl⟩⟩ _ ⟨e, ⟨l, rfl⟩⟩ _ hne
  change Disjoint (Cell.characteristic n k '' ball 0 1) (Cell.characteristic n l '' ball 0 1)
  rw [Cell.image_ball n k hn, Cell.image_ball n l hn]
  apply Set.disjoint_left.mpr
  intro w hwk hwl
  have hkl : k = l := hwk.symm.trans hwl
  exact hne (congrArg (fun j : ℕ ↦ (⟨j * n, ⟨j, rfl⟩⟩ : Σ d, CellIndex n d)) hkl)

theorem attachingMap_boundary (n : ℕ) (hn : 0 < n) (d : ℕ) (i : CellIndex n d) :
    MapsTo (attachingMap n d i) (sphere 0 1)
      (⋃ (e < d) (j : CellIndex n e), attachingMap n e j '' closedBall 0 1) := by
  rcases i with ⟨k, rfl⟩
  intro x hx
  let l := James.size (spherePole n) (Cell.characteristic n k x)
  have hl : l < k := Cell.boundary_size_lt n k hx
  have hdim : l * n < k * n := Nat.mul_lt_mul_of_pos_right hl hn
  refine mem_iUnion.mpr ⟨l * n, mem_iUnion.mpr ⟨hdim, mem_iUnion.mpr ⟨⟨l, rfl⟩, ?_⟩⟩⟩
  change Cell.characteristic n k x ∈ Cell.characteristic n l '' closedBall 0 1
  rw [Cell.image_closedBall n l hn]
  exact James.mem_stage_size (spherePole n) (Cell.characteristic n k x)

theorem isClosed_of_closed_stage_intersections (n : ℕ)
    (A : Set (James.Space (Sphere n) (spherePole n)))
    (hA : ∀ k, IsClosed (A ∩ James.stage (spherePole n) k)) : IsClosed A := by
  apply (James.isClosed_iff_on_words (spherePole n) A).mpr
  intro k
  have he : ((fun v : Fin k → Sphere n ↦ James.word (spherePole n) (List.ofFn v)) ⁻¹' A) =
      ((fun v : Fin k → Sphere n ↦ James.word (spherePole n) (List.ofFn v)) ⁻¹'
        (A ∩ James.stage (spherePole n) k)) := by
    ext v
    simp only [mem_preimage, mem_inter_iff]
    have hv : James.word (spherePole n) (List.ofFn v) ∈ James.stage (spherePole n) k := by
      rw [← James.range_word_array]
      exact mem_range_self v
    exact ⟨fun h ↦ ⟨h, hv⟩, And.left⟩
  rw [he]
  exact (hA k).preimage (James.continuous_word_array (spherePole n) k)

theorem weak_topology (n : ℕ) (hn : 0 < n)
    (A : Set (James.Space (Sphere n) (spherePole n)))
    (hA : ∀ d (i : CellIndex n d), IsClosed (A ∩ attachingMap n d i '' closedBall 0 1)) :
    IsClosed A := by
  apply isClosed_of_closed_stage_intersections n A
  intro k
  have h := hA (k * n) ⟨k, rfl⟩
  change IsClosed (A ∩ Cell.characteristic n k '' closedBall 0 1) at h
  rwa [Cell.image_closedBall n k hn] at h

theorem union_closed_cells (n : ℕ) (hn : 0 < n) :
    (⋃ (d : ℕ) (i : CellIndex n d), attachingMap n d i '' closedBall 0 1) = univ := by
  apply Set.eq_univ_of_forall
  intro w
  let k := James.size (spherePole n) w
  refine mem_iUnion.mpr ⟨k * n, mem_iUnion.mpr ⟨⟨k, rfl⟩, ?_⟩⟩
  change w ∈ Cell.characteristic n k '' closedBall 0 1
  rw [Cell.image_closedBall n k hn]
  exact James.mem_stage_size (spherePole n) w

@[instance_reducible]
def cwComplex (n : ℕ) (hn : 0 < n) :
    Topology.CWComplex (univ : Set (James.Space (Sphere n) (spherePole n))) :=
  Topology.CWComplex.mkFiniteType _ (CellIndex n) (attachingMap n)
    (cellIndex_finite n hn) (attachingMap_source n) (attachingMap_continuousOn n)
    (attachingMap_continuousOn_symm n hn) (cells_pairwiseDisjoint n hn)
    (attachingMap_boundary n hn) (fun A _ hA ↦ weak_topology n hn A hA)
    (union_closed_cells n hn)

instance (n : ℕ) [Fact (0 < n)] :
    Topology.CWComplex (univ : Set (James.Space (Sphere n) (spherePole n))) :=
  cwComplex n Fact.out

instance (n : ℕ) [Fact (0 < n)] :
    Topology.CWComplex.FiniteType (univ : Set (James.Space (Sphere n) (spherePole n))) where
  finite_cell d := cellIndex_finite n Fact.out d

end NoExoticSixSphere.JamesSphere.CW

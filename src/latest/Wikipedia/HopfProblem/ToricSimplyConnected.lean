import Wikipedia.HopfProblem.ToricSpace
import Wikipedia.HopfProblem.SimplyConnectedCover
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Topology of the actual toric chart cover

The toric space used in §4 of `tex/s6.tex` is covered by affine spaces. This
file verifies that their actual intersections are path-connected, using the
dense torus and local path connectedness, rather than assuming a presentation
for the fundamental group of the glued space.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ToricCharts

/-- The componentwise complex exponential parametrizes the coordinate torus. -/
def coordinateExp {d : ℕ} (z : CoordinateSpace d) : CoordinateSpace d :=
  fun j => Complex.exp (z j)

theorem coordinateExp_continuous {d : ℕ} :
    Continuous (@coordinateExp d) :=
  continuous_pi fun j => Complex.continuous_exp.comp (continuous_apply j)

theorem range_coordinateExp {d : ℕ} :
    range (@coordinateExp d) = (torus : Set (CoordinateSpace d)) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩ j
    exact Complex.exp_ne_zero (w j)
  · intro hz
    refine ⟨fun j => Complex.log (z j), ?_⟩
    funext j
    exact Complex.exp_log (hz j)

theorem torus_isPathConnected {d : ℕ} :
    IsPathConnected (torus : Set (CoordinateSpace d)) := by
  rw [← range_coordinateExp]
  exact isPathConnected_range coordinateExp_continuous

theorem domain_isPathConnected {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) :
    IsPathConnected (domain A) := by
  apply (domain_open A).isConnected_iff_isPathConnected.mp
  exact torus_isPathConnected.isConnected.subset_closure
    (torus_subset_domain A) (fun z _ => torus_dense z)

end Wikipedia.HopfProblem.ToricCharts

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan ToricFan.Triangle

/-- The intersection of two affine charts is their genuine monomial overlap. -/
theorem inclusion_ranges_inter (s t : Triangle) :
    range (inclusion s) ∩ range (inclusion t) =
      inclusion s '' domain (transition s t) := by
  ext x
  constructor
  · rintro ⟨⟨z, rfl⟩, ⟨w, hw⟩⟩
    refine ⟨z, ?_, rfl⟩
    simpa only [chartChange_source] using ((inclusion_eq_iff s t z w).mp hw.symm).1
  · rintro ⟨z, hz, rfl⟩
    refine ⟨mem_range_self z, chartChange s t z, ?_⟩
    exact ((inclusion_eq_iff s t z _).mpr
      ⟨by simpa only [chartChange_source] using hz, rfl⟩).symm

theorem inclusion_ranges_inter_isPathConnected (s t : Triangle) :
    IsPathConnected (range (inclusion s) ∩ range (inclusion t)) := by
  rw [inclusion_ranges_inter]
  exact (domain_isPathConnected (transition s t)).image
    (inclusion_openEmbedding s).continuous

theorem inclusion_range_isSimplyConnected (s : Triangle) :
    IsSimplyConnected (range (inclusion s)) := by
  rw [← image_univ]
  apply (inclusion_openEmbedding s).isEmbedding.isSimplyConnected_image.mpr
  change SimplyConnectedSpace (univ : Set (CoordinateSpace 3))
  let := (convex_univ : Convex ℝ (univ : Set (CoordinateSpace 3))).contractibleSpace
    univ_nonempty
  infer_instance

/-- The actual infinite toric gluing in §4 is simply connected. -/
theorem simplyConnectedSpace : SimplyConnectedSpace Space := by
  apply simplyConnectedSpace_of_open_cover (fun s : Triangle => range (inclusion s))
    (fun s => (inclusion_openEmbedding s).isOpen_range)
    ?_ inclusion_range_isSimplyConnected
    (inclusion referenceTriangle (fun _ => 1)) ?_
    inclusion_ranges_inter_isPathConnected
  · ext x
    simp only [mem_iUnion, mem_range, mem_univ, iff_true]
    exact inclusion_jointly_surjective x
  · intro s
    exact ⟨fun _ => 1, inclusion_one s referenceTriangle⟩

end Wikipedia.HopfProblem.ToricSpace

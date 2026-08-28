import Wikipedia.SmoothSixDPoincare.SmoothConnectingCurve
import Wikipedia.SmoothSixDPoincare.GlobalImageAvoidance
import Wikipedia.SmoothSixDPoincare.PathPointMoving

/-!
# Paths and point transport avoiding finite sets in dimension at least two

A finite obstacle is a genuine zero-dimensional manifold. Relative smooth
general position on the closed interval avoids it while fixing both
endpoints. Supported point transport along that path then gives an actual
global diffeomorphism fixing every obstacle point.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold J ∞ N] [T2Space N]

/-- Finite-point avoidance for paths needs only dimension two, not curve general position. -/
theorem exists_smooth_path_avoiding_finite {x y : N} (γ : Path x y)
    (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite)
    (hx : x ∉ S) (hy : y ∉ S) :
    ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, η t ∉ S := by
  let : Fintype S := hS.fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z S := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ S := IsManifold.of_discreteTopology _
  let g : C(S, N) := ⟨Subtype.val, continuous_subtype_val⟩
  have hg : ContMDiff 𝓘(ℝ, Z) J ∞ g := contMDiff_of_discreteTopology
  have hrange : range g = S := by ext z; simp [g]
  obtain ⟨f, hf, hf0, hf1⟩ := exists_smooth_connecting_curve (J := J) γ
  let fI : C(unitInterval, N) := ⟨fun t => f t, f.continuous.comp continuous_subtype_val⟩
  have hfI : ContMDiff (𝓡∂ 1) J ∞ fI := hf.comp contMDiff_subtypeVal_Icc
  have hdim' : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) + Module.finrank ℝ Z <
      Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin]
    omega
  have hfixed : ∀ t ∈ ({0, 1} : Set unitInterval), fI t ∉ range g := by
    intro t ht
    rw [hrange]
    rcases ht with rfl | ht
    · change f 0 ∉ S
      rw [hf0]
      exact hx
    · have ht1 : t = 1 := ht
      subst t
      change f 1 ∉ S
      rw [hf1]
      exact hy
  obtain ⟨f', hf', hrel, hdisjoint⟩ :=
    GeneralPosition.exists_disjoint_smooth_map_homotopicRel fI g hfI hg hdim'
      ((finite_singleton (1 : unitInterval)).insert 0).isClosed hfixed
  have hf'0 : f' 0 = x := (hrel.fst_eq_snd (by simp)).symm.trans hf0
  have hf'1 : f' 1 = y := (hrel.fst_eq_snd (by simp)).symm.trans hf1
  let η : Path x y := { toContinuousMap := f', source' := hf'0, target' := hf'1 }
  refine ⟨η, hf', ?_⟩
  intro t ht
  rw [hrange] at hdisjoint
  exact Set.disjoint_left.mp hdisjoint ⟨t, rfl⟩ ht

/-- A path between points outside a finite set gives a diffeomorphism fixing that set. -/
theorem exists_pointMoving_fixing_finite {x y : N} (γ : Path x y)
    (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite)
    (hx : x ∉ S) (hy : y ∉ S) :
    ∃ d : Diffeomorph J J N N ∞, d x = y ∧ ∀ z ∈ S, d z = z := by
  obtain ⟨η, _, hη⟩ := exists_smooth_path_avoiding_finite (J := J) γ hdim hS hx hy
  obtain ⟨d, hd, hfix⟩ := SupportedDiffeomorph.exists_pointMoving_of_path (J := J)
    hS.isClosed.isOpen_compl η hη
  exact ⟨d, hd, fun z hz => hfix z (fun hn => hn hz)⟩

end Wikipedia.SmoothSixDPoincare

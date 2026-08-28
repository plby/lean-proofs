import Wikipedia.HopfProblem.DegreeCollapseIntegralConvexSupport
import Wikipedia.NoExoticSixSphere.SupportedHomologyNeighborhoodLift
import Wikipedia.NoExoticSixSphere.SupportedLocalZeroNeighborhood

/-!
# Integral detection and uniqueness on every compact Euclidean support

Actual relative classes lift to a sufficiently small neighborhood of the
support. Finite unions of closed balls give neighborhoods with the proved
integral dimension bound and local detection. The original boundary
witnesses make zero local values persist near the compact support, so
restriction from a smaller such neighborhood proves detection on the
original support. The previously constructed integral class is then unique.
-/

noncomputable section

open Set Metric
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupport

open NoExoticSixSphere SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]

theorem exists_neighborhood (K U : Set E) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set E, Properties (n + 2) L ∧ K ⊆ interior L ∧ L ⊆ U := by
  classical
  have hradius : ∀ x : K, ∃ r : ℝ, 0 < r ∧ closedBall (x : E) r ⊆ U := by
    intro x
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU x.property))
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans hball⟩
  choose r hr hsub using hradius
  have hcover : K ⊆ ⋃ x : K, ball (x : E) (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : E) (r x))
    (fun _ => isOpen_ball) hcover
  let L : Set E := ⋃ x ∈ s, closedBall (x : E) (r x)
  have hinner : (⋃ x ∈ s, ball (x : E) (r x)) ⊆ L := by
    intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.mp hy
    obtain ⟨hx, hy⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, ball_subset_closedBall hy⟩⟩
  have hopen : IsOpen (⋃ x ∈ s, ball (x : E) (r x)) :=
    isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_ball))
  refine ⟨L, finiteUnion_compactConvex n s (fun x : K => closedBall (x : E) (r x))
    (fun x _ => isCompact_closedBall (x : E) (r x))
    (fun x _ => convex_closedBall (x : E) (r x)), hs.trans (interior_maximal hinner hopen), ?_⟩
  intro y hy
  obtain ⟨x, hx⟩ := mem_iUnion.mp hy
  obtain ⟨_, hy⟩ := mem_iUnion.mp hx
  exact hsub x hy

theorem compactEuclidean_above_subsingleton (K : Set E) (hK : IsCompact K)
    (k : ℕ) (hk : n + 2 < k) : Subsingleton (Homology (ModuleCat.of ℤ ℤ) K k) := by
  have hz : ∀ a : Homology (ModuleCat.of ℤ ℤ) K k, a = 0 := by
    intro a
    obtain ⟨U, hU, hKU, hlift⟩ := exists_lift_neighborhood (ModuleCat.of ℤ ℤ) K k a
    obtain ⟨L, hL, hKL, hLU⟩ := exists_neighborhood n K U hK hU hKU
    have h : K ⊆ L := hKL.trans interior_subset
    obtain ⟨b, hb⟩ := hlift L hLU h
    have hb0 : b = 0 := (hL.above k hk).elim b 0
    exact hb.symm.trans ((congrArg (restrict (ModuleCat.of ℤ ℤ) h k) hb0).trans (map_zero _))
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Actual zero localizations force the original compactly supported integral class to vanish. -/
theorem compactEuclidean_eq_zero (K : Set E) (hK : IsCompact K)
    (a : Homology (ModuleCat.of ℤ ℤ) K (n + 2))
    (ha : ∀ (x : E) (hx : x ∈ K), evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) a = 0) :
    a = 0 := by
  let A := ModuleCat.of ℤ ℤ
  obtain ⟨U, hU, hKU, hlift⟩ := exists_lift_neighborhood A K (n + 2) a
  obtain ⟨L, _, hKintL, hLU⟩ := exists_neighborhood n K U hK hU hKU
  have hKL : K ⊆ L := hKintL.trans interior_subset
  obtain ⟨b, hb⟩ := hlift L hLU hKL
  have hbzero : ∀ (x : E) (hx : x ∈ K), evaluate A L x (hKL hx) (n + 2) b = 0 := by
    intro x hx
    have he := LinearMap.congr_fun (evaluate_restrict A hKL x hx (n + 2)) b
    exact he.symm.trans ((congrArg (evaluate A K x hx (n + 2)) hb).trans (ha x hx))
  obtain ⟨V, hV, hKV, hVzero⟩ := exists_open_zero_evaluations A hKL (n + 2) b hbzero
  obtain ⟨N, hN, hKintN, hNVL⟩ := exists_neighborhood n K (V ∩ interior L) hK
    (hV.inter isOpen_interior) (fun x hx => ⟨hKV hx, hKintL hx⟩)
  have hKN : K ⊆ N := hKintN.trans interior_subset
  have hNL : N ⊆ L := fun x hx => interior_subset (hNVL hx).2
  have hNzero : restrict A hNL (n + 2) b = 0 := by
    apply hN.detected
    intro x hx
    have he := LinearMap.congr_fun (evaluate_restrict A hNL x hx (n + 2)) b
    exact (he.trans (hVzero x (hNL hx) (hNVL hx).1)).trans (map_zero _).symm
  have he : restrict A hKN (n + 2) (restrict A hNL (n + 2) b) = a :=
    (LinearMap.congr_fun (restrict_trans A hKN hNL (n + 2)) b).symm.trans hb
  exact he.symm.trans ((congrArg (restrict A hKN (n + 2)) hNzero).trans (map_zero _))

theorem compactEuclidean_detected (K : Set E) (hK : IsCompact K)
    (a b : Homology (ModuleCat.of ℤ ℤ) K (n + 2))
    (hab : ∀ (x : E) (hx : x ∈ K), evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) a =
      evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) b) : a = b := by
  apply sub_eq_zero.mp
  apply compactEuclidean_eq_zero n K hK (a - b)
  intro x hx
  rw [map_sub, hab x hx, sub_self]

theorem compactEuclidean_properties (K : Set E) (hK : IsCompact K) : Properties (n + 2) K where
  compact := hK
  above k hk := compactEuclidean_above_subsingleton n K hK k hk
  detected a b hab := compactEuclidean_detected n K hK a b hab

/-- The constructed class is now unique on every original compact Euclidean support. -/
theorem compactEuclidean_existsUnique_fundamentalClass (K : Set E) (hK : IsCompact K) :
    ∃! a : Homology (ModuleCat.of ℤ ℤ) K (n + 2), ∀ (x : E) (hx : x ∈ K),
      evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) a = IntegralBallOrientation.pointClass E n x := by
  refine ⟨IntegralEuclideanOrientation.fundamentalClass E n K hK.isBounded,
    IntegralEuclideanOrientation.fundamentalClass_evaluate E n K hK.isBounded, ?_⟩
  intro a ha
  apply compactEuclidean_detected n K hK
  intro x hx
  exact (ha x hx).trans
    (IntegralEuclideanOrientation.fundamentalClass_evaluate E n K hK.isBounded x hx).symm

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupport

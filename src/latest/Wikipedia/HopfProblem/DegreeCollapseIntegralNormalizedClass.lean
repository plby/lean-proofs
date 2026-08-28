import Wikipedia.HopfProblem.DegreeCollapseIntegralLocalNormalization

/-!
# Assembling the normalized integral top class

The marking-independent primitive-direction field has an actual signed
chart-class representative on a compact neighborhood of every point.
The proved compact assembly theorem therefore constructs its unique
supported representatives. On a compact manifold, the original
whole-support equivalence gives an actual absolute class with those
exact localizations. If the input localizations are nonzero, the new
localizations generate the original integral local homology groups.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralLocalNormalization

open SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

theorem exists_local_representative (a : SingularHomology M (n + 2)) (x : M) :
    ∃ B : Set M, IsCompact B ∧ x ∈ interior B ∧
      ∃ b : Homology (ModuleCat.of ℤ ℤ) B (n + 2),
        IntegralLocalAssembly.Represents (direction (E := E) n a) B b := by
  obtain ⟨e, U, hU, hxU, hUs, k, hk⟩ := exists_local_coefficient (E := E) n a x
  have hx : x ∈ e.source := hUs hxU
  obtain ⟨R, hR, hRtarget, hBU⟩ :=
    ChartClosedBall.exists_support_subset e x hx U (hU.mem_nhds hxU)
  let B := ChartClosedBall.support e (e x) R
  have hB : IsCompact B := ChartClosedBall.support_isCompact e (e x) R hRtarget
  have hBs : B ⊆ e.source := hBU.trans hUs
  have hxint : x ∈ interior B := mem_interior_iff_mem_nhds.mpr
    (ChartClosedBall.support_mem_nhds e x hx R hR hRtarget)
  let b := IntegralChartOrientation.fundamentalClass n e B hB hBs
  refine ⟨B, hB, hxint, Int.sign k • b, ?_⟩
  intro y hy
  have hby : evaluate (ModuleCat.of ℤ ℤ) B y hy (n + 2) b =
      (chartMark n e y (hUs (hBU hy))).symm 1 :=
    IntegralChartOrientation.fundamentalClass_evaluate n e B hB hBs y hy
  rw [map_zsmul, hby, direction_in_chart n a e y (hUs (hBU hy)), hk y (hBU hy)]
  exact (IntegralPrimitiveDirection.normalize_smul_generator
    (chartMark n e y (hUs (hBU hy))) k).symm

theorem existsUnique_supportedClass (a : SingularHomology M (n + 2))
    (K : Set M) (hK : IsCompact K) :
    ∃! b : Homology (ModuleCat.of ℤ ℤ) K (n + 2),
      IntegralLocalAssembly.Represents (direction (E := E) n a) K b :=
  IntegralLocalAssembly.existsUnique_of_local_representatives (E := E) n
    (direction (E := E) n a) K hK (fun x _ => exists_local_representative (E := E) n a x)

def supportedClass (a : SingularHomology M (n + 2)) (K : Set M) (hK : IsCompact K) :
    Homology (ModuleCat.of ℤ ℤ) K (n + 2) :=
  Classical.choose (existsUnique_supportedClass (E := E) n a K hK)

theorem supportedClass_represents (a : SingularHomology M (n + 2))
    (K : Set M) (hK : IsCompact K) :
    IntegralLocalAssembly.Represents (direction (E := E) n a) K
      (supportedClass (E := E) n a K hK) :=
  (Classical.choose_spec (existsUnique_supportedClass (E := E) n a K hK)).1

/-- The assembled classes retain the original restriction maps on every pair of compact supports. -/
theorem supportedClass_restrict (a : SingularHomology M (n + 2))
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) :
    restrict (ModuleCat.of ℤ ℤ) hKL (n + 2) (supportedClass (E := E) n a L hL) =
      supportedClass (E := E) n a K hK := by
  apply (Classical.choose_spec (existsUnique_supportedClass (E := E) n a K hK)).2
  exact (supportedClass_represents (E := E) n a L hL).restrict hKL

variable [CompactSpace M]

/-- The original whole-support projection constructs an absolute integral class. -/
def absoluteClass (a : SingularHomology M (n + 2)) : SingularHomology M (n + 2) :=
  (absoluteEquiv (X := M) (ModuleCat.of ℤ ℤ) (n + 2)).symm
    (supportedClass (E := E) n a univ isCompact_univ)

theorem fromAbsolute_absoluteClass (a : SingularHomology M (n + 2)) :
    fromAbsolute (ModuleCat.of ℤ ℤ) (univ : Set M) (n + 2) (absoluteClass (E := E) n a) =
      supportedClass (E := E) n a univ isCompact_univ :=
  (absoluteEquiv (X := M) (ModuleCat.of ℤ ℤ) (n + 2)).apply_symm_apply _

/-- Every original localization is exactly the normalized value of the input class. -/
theorem absoluteClass_localize (a : SingularHomology M (n + 2)) (x : M) :
    fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 2) (absoluteClass (E := E) n a) =
      direction (E := E) n a x :=
  (evaluate_fromAbsolute univ x (mem_univ x) (n + 2) (absoluteClass (E := E) n a)).symm.trans
    ((congrArg (evaluate (ModuleCat.of ℤ ℤ) univ x (mem_univ x) (n + 2))
      (fromAbsolute_absoluteClass (E := E) n a)).trans
        (supportedClass_represents (E := E) n a univ isCompact_univ x (mem_univ x)))

/-- Nonzero localizations normalize to actual primitive integral generators everywhere. -/
theorem absoluteClass_localize_generates (a : SingularHomology M (n + 2))
    (ha : ∀ x : M, fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 2) a ≠ 0)
    (x : M) (c : Homology (ModuleCat.of ℤ ℤ) {x} (n + 2)) :
    ∃ k : ℤ, k • fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 2) (absoluteClass (E := E) n a) = c := by
  obtain ⟨k, hk⟩ := IntegralPrimitiveDirection.normalize_generates
    (chartMark n (chartAt E x) x (mem_chart_source E x))
    (fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 2) a) (ha x) c
  exact ⟨k, (congrArg (fun z => k • z) (absoluteClass_localize (E := E) n a x)).trans hk⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralLocalNormalization

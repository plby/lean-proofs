import Wikipedia.HopfProblem.CuspCentralHomologyTopDegreesRegions
import Wikipedia.HopfProblem.CuspCentralHomologyTopDegreesMayerVietoris
import Wikipedia.HopfProblem.CuspCentralHomologyTopDegreesRadius

/-!
# The actual central cusp has one top class and no homology above degree four

The genuine radial open cover and the actual singular Mayer–Vietoris
sequence identify degree four with degree three of the overlap. That
overlap is the actual three-circle torus up to the constructed homotopy
equivalence. Higher homology vanishes by the same exact sequence.

The final statements concern the original central fibre at any positive
ambient radius. Analytic data supply a smaller admissible radius, and
the actual level-zero radius homeomorphism transports the result back.
No model equivalence or low-degree attaching-map computation is assumed.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

section Admissible

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

local notation "U" => outerRegion C ε hε (1 / 2)
local notation "V" => innerRegion C ε hε

/-- The top class is computed by the actual connecting homomorphism of
the actual half-radius collar and inner-region cover. -/
def centralSingularH4Equiv_of_admissible :
    SingularHomology (QuotientCentralFibre C ε) 4 ≃ₗ[ℤ] ℤ := by
  letI := outerRegion_homology_subsingleton C ε hε hε1 hC hR
    (1 / 2) (by norm_num) (by norm_num) 1
  letI := innerRegion_homology_subsingleton C ε hε hε1 hC hR 1
  letI := outerRegion_homology_subsingleton C ε hε hε1 hC hR
    (1 / 2) (by norm_num) (by norm_num) 0
  letI := innerRegion_homology_subsingleton C ε hε hε1 hC hR 0
  exact (coverConnectingEquivOfVanishing U V
    (outerRegion_isOpen C ε hε hε1 hC hR (1 / 2))
    (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)) 3).trans
      (overlapRegionHomologyThreeEquiv C ε hε hε1 hC hR
        (1 / 2) (by norm_num) (by norm_num))

include hε hε1 hC hR in
/-- Actual integral singular homology vanishes in every degree above
four, without any assertion about the lower attaching maps. -/
theorem centralSingularHomology_subsingleton_of_admissible (n : ℕ) :
    Subsingleton (SingularHomology (QuotientCentralFibre C ε) (n + 5)) := by
  let := outerRegion_homology_subsingleton C ε hε hε1 hC hR
    (1 / 2) (by norm_num) (by norm_num) (n + 2)
  let := innerRegion_homology_subsingleton C ε hε hε1 hC hR (n + 2)
  let : Subsingleton
      (SingularHomology (U ∩ V : Set (QuotientCentralFibre C ε)) (n + 4)) :=
    overlapRegion_homology_subsingleton C ε hε hε1 hC hR
      (1 / 2) (by norm_num) (by norm_num) n
  exact coverHomology_subsingleton_of_vanishing U V
    (outerRegion_isOpen C ε hε hε1 hC hR (1 / 2))
    (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)) (n + 4)

end Admissible

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- Degree four of the literal central fibre at the original ambient
radius is the integral coefficient module. All radius bounds needed for
the geometric computation are derived from the analytic data. -/
def centralSingularH4Equiv :
    SingularHomology (QuotientCentralFibre C r) 4 ≃ₗ[ℤ] ℤ := by
  let δ : ℝ := Classical.choose (CuspQuotient.exists_admissible_radius C hr hC)
  have hs : 0 < δ ∧ δ < r ∧ δ < 1 ∧ SmallDrift C δ ∧
      ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    Classical.choose_spec (CuspQuotient.exists_admissible_radius C hr hC)
  exact (homeomorphHomologyEquiv
    (centralRadiusHomeomorph C r δ hs.2.1.le hC hs.1).symm 4).trans
      (centralSingularH4Equiv_of_admissible C δ hs.1 hs.2.2.1 hs.2.2.2.2 hs.2.2.2.1)

include hr hC

theorem centralSingularHomology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology (QuotientCentralFibre C r) (n + 5)) := by
  obtain ⟨δ, hδ, hδr, hδ1, hR, hCδ⟩ := CuspQuotient.exists_admissible_radius C hr hC
  let := centralSingularHomology_subsingleton_of_admissible C δ hδ hδ1 hCδ hR n
  exact (homeomorphHomologyEquiv
    (centralRadiusHomeomorph C r δ hδr.le hC hδ).symm (n + 5)).injective.subsingleton

theorem centralSingularHomology_subsingleton_of_four_lt {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology (QuotientCentralFibre C r) n) := by
  have he : (n - 5) + 5 = n := Nat.sub_add_cancel (by omega)
  rw [← he]
  exact centralSingularHomology_subsingleton C r hr hC (n - 5)

/-- The actual higher homology groups are equivalent to the zero free module. -/
def centralSingularHomologyHigherEquivZero (n : ℕ) :
    SingularHomology (QuotientCentralFibre C r) (n + 5) ≃ₗ[ℤ] (Fin 0 → ℤ) := by
  letI := centralSingularHomology_subsingleton C r hr hC n
  exact LinearEquiv.ofSubsingleton _ _

theorem centralSingularH4_free :
    Module.Free ℤ (SingularHomology (QuotientCentralFibre C r) 4) :=
  Module.Free.of_equiv (centralSingularH4Equiv C r hr hC).symm

theorem centralSingularH4_finite :
    Module.Finite ℤ (SingularHomology (QuotientCentralFibre C r) 4) :=
  Module.Finite.of_surjective (centralSingularH4Equiv C r hr hC).symm.toLinearMap
    (centralSingularH4Equiv C r hr hC).symm.surjective

theorem centralSingularH4_finrank :
    Module.finrank ℤ (SingularHomology (QuotientCentralFibre C r) 4) = 1 := by
  rw [(centralSingularH4Equiv C r hr hC).finrank_eq]
  simp

theorem centralSingularH4_torsionFree :
    Module.IsTorsionFree ℤ (SingularHomology (QuotientCentralFibre C r) 4) := by
  let := centralSingularH4_free C r hr hC
  infer_instance

theorem centralSingularHomologyHigher_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology (QuotientCentralFibre C r) (n + 5)) = 0 := by
  rw [(centralSingularHomologyHigherEquivZero C r hr hC n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

end Wikipedia.HopfProblem.CuspCentralHomology

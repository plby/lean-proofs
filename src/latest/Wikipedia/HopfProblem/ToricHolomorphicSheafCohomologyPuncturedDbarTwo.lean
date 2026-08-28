import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarTwoSequence
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinDifferential

/-!
# Genuine global top-degree solvability on `ℂ × ℂ*`

The actual adjusted Cauchy--Green primitives agree exactly on exhausting
disc--annulus regions. Their stabilized values therefore give genuine
smooth coefficients on the actual punctured product, satisfying the
prescribed top-degree antiholomorphic equation everywhere there.

Only smoothness of the input on the actual open domain is assumed.
There is no extension, compact-support, Stein, or cohomology premise.
-/

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarTwo

open PeriodTorusLineBundleClassification PeriodTorusLineBundleClassificationCousin

def openRegion (n : ℕ) : Set (ℂ × ℂ) := PuncturedDbarOne.annularOpen (radius n)

theorem isOpen_openRegion (n : ℕ) : IsOpen (openRegion n) :=
  PuncturedDbarOne.isOpen_annularOpen _

theorem openRegion_subset_closedRegion (n : ℕ) : openRegion n ⊆ closedRegion n :=
  PuncturedDbarOne.annularOpen_subset_closed _

theorem openRegion_subset_domain (n : ℕ) : openRegion n ⊆ domain :=
  (openRegion_subset_closedRegion n).trans
    (PuncturedDbarOne.annularClosed_subset_domain (radius_pos n))

theorem exists_mem_openRegion (q : ℂ × ℂ) (hq : q ∈ domain) :
    ∃ n : ℕ, q ∈ openRegion n := by
  simpa only [openRegion, radius_eq, PuncturedDbarOne.exhaustionDomain] using
    PuncturedDbarOne.cover_exhaustionDomain q hq

def coveringIndex (q : domain) : ℕ := Classical.choose (exists_mem_openRegion q q.property)

theorem mem_coveringIndex (q : domain) : (q : ℂ × ℂ) ∈ openRegion (coveringIndex q) :=
  Classical.choose_spec (exists_mem_openRegion q q.property)

/-- Stabilized values on the actual punctured domain, extended by an
irrelevant zero value outside it. -/
def primitive {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (q : ℂ × ℂ) : ℂ × ℂ := by
  classical
  exact if hq : q ∈ domain then stage hw (coveringIndex ⟨q, hq⟩) q else 0

theorem primitive_eq_stage {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q ∈ openRegion n) :
    primitive hw q = stage hw n q := by
  have hd := openRegion_subset_domain n hq
  have hm := openRegion_subset_closedRegion _ (mem_coveringIndex ⟨q, hd⟩)
  have hn := openRegion_subset_closedRegion n hq
  rw [primitive, dif_pos hd]
  exact (stage_compatible hw (le_max_left (coveringIndex ⟨q, hd⟩) n) q hm).symm.trans
    (stage_compatible hw (le_max_right (coveringIndex ⟨q, hd⟩) n) q hn)

theorem primitive_eventuallyEq_stage {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) {q : ℂ × ℂ} (hq : q ∈ openRegion n) :
    primitive hw =ᶠ[𝓝 q] stage hw n := by
  filter_upwards [(isOpen_openRegion n).mem_nhds hq] with x hx
  exact primitive_eq_stage hw n x hx

theorem primitive_smoothOn {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) :
    ContDiffOn ℝ ∞ (primitive hw) domain := by
  intro q hq
  obtain ⟨n, hn⟩ := exists_mem_openRegion q hq
  exact ((stage_smooth hw n).contDiffAt.congr_of_eventuallyEq
    (primitive_eventuallyEq_stage hw n hn)).contDiffWithinAt

def primitiveFirst {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (q : ℂ × ℂ) : ℂ :=
  (primitive hw q).1

def primitiveSecond {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (q : ℂ × ℂ) : ℂ :=
  (primitive hw q).2

theorem primitiveFirst_smoothOn {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) :
    ContDiffOn ℝ ∞ (primitiveFirst hw) domain :=
  contDiff_fst.comp_contDiffOn (primitive_smoothOn hw)

theorem primitiveSecond_smoothOn {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) :
    ContDiffOn ℝ ∞ (primitiveSecond hw) domain :=
  contDiff_snd.comp_contDiffOn (primitive_smoothOn hw)

theorem primitive_equation {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (q : ℂ × ℂ) (hq : q ∈ domain) :
    dbarFirst (primitiveSecond hw) q - dbarSecond (primitiveFirst hw) q = w q := by
  obtain ⟨n, hn⟩ := exists_mem_openRegion q hq
  have he := primitive_eventuallyEq_stage hw n hn
  have hfirst : primitiveFirst hw =ᶠ[𝓝 q] firstStage hw n :=
    he.mono fun x hx => congrArg Prod.fst hx
  have hsecond : primitiveSecond hw =ᶠ[𝓝 q] secondStage hw n :=
    he.mono fun x hx => congrArg Prod.snd hx
  rw [dbarFirst_congr hsecond, dbarSecond_congr hfirst]
  exact stage_equation hw n q (openRegion_subset_closedRegion n hn).2

/-- Every actual smooth top-degree coefficient on `ℂ × ℂ*` has an
actual smooth global primitive on that domain. -/
theorem exists_smooth_top_primitive {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) :
    ∃ a b : ℂ × ℂ → ℂ, ContDiffOn ℝ ∞ a domain ∧ ContDiffOn ℝ ∞ b domain ∧
      ∀ q ∈ domain, dbarFirst b q - dbarSecond a q = w q :=
  ⟨primitiveFirst hw, primitiveSecond hw, primitiveFirst_smoothOn hw,
    primitiveSecond_smoothOn hw, primitive_equation hw⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarTwo

import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersNegativePairing
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleSections
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFunctions

/-!
# Vanishing of all positive powers of the actual negative pulled-back line

Pairing with the genuine positive dual section gives a global holomorphic
function on the constructed compact connected threefold.  It vanishes on
the nonempty cusp fibre, so is zero everywhere.  The dual section is
nonzero off that fibre, hence the original section vanishes on the actual
dense finite open.  Continuity in a native local trivialization then
forces it to vanish at every remaining point.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersNegative

open HolomorphicCharacterBundle

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The positive dual section has exactly the actual cusp fibre as its zero set. -/
theorem positiveSection_eq_zero_iff (n : ℕ) (hn : 0 < n) (x : Threefold.Space) :
    positiveSection n x = 0 ↔ Threefold.projectionSphere x = (∞ : RiemannSphere) := by
  change dualCoefficient (data.indexAt x) x ^ n = 0 ↔ _
  exact (pow_eq_zero_iff (Nat.ne_of_gt hn)).trans
    (dualCoefficient_eq_zero_iff _ x (data.mem_baseSet_at x))

theorem positiveSection_ne_zero_on_genericSet (n : ℕ) (x : Threefold.Space)
    (hx : x ∈ GlobalBasePullback.cartier.genericSet) : positiveSection n x ≠ 0 :=
  pow_ne_zero n (dualCoefficient_ne_zero _ x (data.mem_baseSet_at x) hx)

/-- The genuine dual evaluation vanishes on the full actual cusp fibre. -/
theorem pairing_eq_zero_of_projection_infty (n : ℕ) (hn : 0 < n) (s : Section n)
    (x : Threefold.Space) (hx : Threefold.projectionSphere x = (∞ : RiemannSphere)) :
    pairing n s x = 0 := by
  rw [pairing_apply,
    dualCoefficient_eq_zero_of_projection_infty _ x (data.mem_baseSet_at x) hx,
    zero_pow (Nat.ne_of_gt hn), zero_mul]

/-- The original sphere projection supplies an actual point of the cusp fibre;
compactness forces the holomorphic pairing to have its zero value everywhere. -/
theorem pairing_eq_zero (n : ℕ) (hn : 0 < n) (s : Section n) (x : Threefold.Space) :
    pairing n s x = 0 := by
  obtain ⟨a, ha⟩ := Threefold.projectionSphere_surjective (∞ : RiemannSphere)
  exact (Threefold.holomorphic_apply_eq (pairing_holomorphic n s) x a).trans
    (pairing_eq_zero_of_projection_infty n hn s a ha)

/-- Cancellation uses nonvanishing of the actual positive dual section,
on the original finite open and with no section-descent hypothesis. -/
theorem section_apply_eq_zero_on_genericSet (n : ℕ) (hn : 0 < n) (s : Section n)
    (x : Threefold.Space) (hx : x ∈ GlobalBasePullback.cartier.genericSet) : s x = 0 := by
  have hp := pairing_eq_zero n hn s x
  rw [pairing_apply] at hp
  exact (mul_eq_zero.mp hp).resolve_left
    (pow_ne_zero n (dualCoefficient_ne_zero _ x (data.mem_baseSet_at x) hx))

/-- Every positive native tensor power of the actual pulled-back ideal line
has zero entire holomorphic section space. -/
theorem section_eq_zero (n : ℕ) (hn : 0 < n) (s : Section n) : s = 0 := by
  classical
  apply ContMDiffSection.ext
  intro x
  change s x = 0
  by_contra hx
  let i := data.indexAt x
  have hc : (powerData n).localCoefficient s i x ≠ 0 := by
    intro h
    exact hx (((powerData n).localCoefficient_indexAt s x).symm.trans h)
  have hi : data.baseSet i ∈ 𝓝 x :=
    (data.isOpen_baseSet i).mem_nhds (data.mem_baseSet_at x)
  have hhol := ((powerData n).localCoefficient_holomorphic IF s s.contMDiff i).contMDiffAt hi
  have hne : {y : Threefold.Space | (powerData n).localCoefficient s i y ≠ 0} ∈ 𝓝 x :=
    hhol.continuousAt.eventually_ne hc
  obtain ⟨y, hy, hyG⟩ :=
    (mem_closure_iff_nhds.mp (GlobalBasePullback.cartier.genericSet_dense x)) _ hne
  apply hy
  have hzero : id (α := ℂ) (s y) = 0 :=
    section_apply_eq_zero_on_genericSet n hn s y hyG
  exact ((powerData n).localCoefficient_eq s i y).trans
    ((congrArg (fun c : ℂ =>
      ((powerData n).transition ((powerData n).indexAt y) i y : ℂ) * c) hzero).trans
        (mul_zero _))

/-- This is vanishing of the genuine native section type, not just of selected candidates. -/
theorem section_subsingleton (n : ℕ) (hn : 0 < n) : Subsingleton (Section n) :=
  ⟨fun s t => (section_eq_zero n hn s).trans (section_eq_zero n hn t).symm⟩

theorem section_finrank_zero (n : ℕ) (hn : 0 < n) : Module.finrank ℂ (Section n) = 0 := by
  let := section_subsingleton n hn
  exact Module.finrank_zero_of_subsingleton

/-- The original first-power bundle itself has no holomorphic sections;
the transfer uses the genuine holomorphic section-power map. -/
theorem base_section_eq_zero
    (s : ContMDiffSection IF ℂ ω GlobalBasePullback.bundle.Fiber) : s = 0 :=
  (CanonicalGlobalLineBundle.Powers.holomorphicSectionPower_eq_zero_iff
    data 1 IF (by decide) s).mp
      (section_eq_zero 1 (by decide)
        (CanonicalGlobalLineBundle.Powers.holomorphicSectionPower data 1 IF s))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersNegative

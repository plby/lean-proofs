import ErdosProblems.Erdos520.HarperBlockLaw
import Mathlib.Probability.Independence.InfinitePi

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Measure ProbabilityTheory
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Independence of disjoint scheduled blocks

The tilted cube is a product over prime coordinates.  We first record the
general fact that an independent family remains independent after its
coordinates are grouped into dependent-indexed tuples.  Scheduled prime
blocks are disjoint, so their centered sums are then mutually independent,
not merely pairwise independent.
-/

/-- Curry an independent family into independent groups.  This is the
reverse direction to Mathlib's `iIndepFun_uncurry` and follows by transporting
the joint product law through `MeasurableEquiv.piCurry`. -/
theorem iIndepFun_piCurry_of_iIndepFun
    {Ω ι : Type*} {β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω}
    [IsProbabilityMeasure P] {κ : ι → Type*}
    (Z : (p : (i : ι) × κ i) → Ω → β)
    (hZmeas : ∀ p, Measurable (Z p))
    (hZ : iIndepFun Z P) :
    iIndepFun (fun i omega j ↦ Z ⟨i, j⟩ omega) P := by
  let jointZ : Ω → ((p : (i : ι) × κ i) → β) :=
    fun omega p ↦ Z p omega
  let groupedZ : (i : ι) → Ω → (κ i → β) :=
    fun i omega j ↦ Z ⟨i, j⟩ omega
  let jointGroupedZ : Ω → ((i : ι) → κ i → β) :=
    fun omega i j ↦ Z ⟨i, j⟩ omega
  let B : (i : ι) → κ i → Type := fun _i _j ↦ β
  let e := MeasurableEquiv.piCurry B
  let marginal : (p : (i : ι) × κ i) → Measure β :=
    fun p ↦ P.map (Z p)
  have hjointMeas : Measurable jointZ := by
    exact measurable_pi_iff.mpr hZmeas
  have hgroupMeas : ∀ i, Measurable (groupedZ i) := by
    intro i
    exact measurable_pi_iff.mpr fun j ↦ hZmeas ⟨i, j⟩
  have hmarginal : ∀ p, IsProbabilityMeasure (marginal p) := by
    intro p
    exact Measure.isProbabilityMeasure_map (hZmeas p).aemeasurable
  letI (p : (i : ι) × κ i) : IsProbabilityMeasure (marginal p) :=
    hmarginal p
  have hjointLaw : P.map jointZ = infinitePi marginal := by
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map hZmeas).mp hZ
  have hgroupLaw (i : ι) :
      P.map (groupedZ i) =
        infinitePi (fun j : κ i ↦ marginal (Sigma.mk i j)) := by
    have hinj : Function.Injective (fun j : κ i ↦ Sigma.mk i j) := by
      intro a b hab
      exact eq_of_heq (Sigma.mk.inj_iff.mp hab).2
    have hi : iIndepFun (fun j : κ i ↦ Z (Sigma.mk i j)) P :=
      iIndepFun.precomp hinj hZ
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun j ↦ hZmeas (Sigma.mk i j))).mp hi
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hgroupMeas]
  change P.map jointGroupedZ = infinitePi (fun i ↦ P.map (groupedZ i))
  calc
    P.map jointGroupedZ = (P.map jointZ).map
        e := by
      rw [Measure.map_map e.measurable hjointMeas]
      apply Measure.map_congr
      exact ae_of_all P fun omega ↦ by
        ext i j
        rfl
    _ = (infinitePi marginal).map
        e := by
      rw [hjointLaw]
    _ = infinitePi (fun i ↦
          infinitePi (fun j : κ i ↦ marginal (Sigma.mk i j))) := by
      exact infinitePi_map_piCurry
        (X := B) (fun i j ↦ marginal (Sigma.mk i j))
    _ = infinitePi (fun i ↦ P.map (groupedZ i)) := by
      congr 1
      funext i
      exact (hgroupLaw i).symm

/-- Sums over pairwise-disjoint finite sets of an independent real family
are mutually independent.  This packages the coordinate grouping needed by
the scheduled prime blocks. -/
theorem iIndepFun_finset_sum_of_pairwise_disjoint
    {Ω α ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Z : α → Ω → ℝ) (hZmeas : ∀ a, Measurable (Z a))
    (hZ : iIndepFun Z P) (S : ι → Finset α)
    (hS : Pairwise fun i j ↦ Disjoint (S i) (S j)) :
    iIndepFun (fun i omega ↦ ∑ a ∈ S i, Z a omega) P := by
  let κ : ι → Type _ := fun i ↦ {a : α // a ∈ S i}
  let embed : (p : (i : ι) × κ i) → α := fun p ↦ p.2.1
  have hembed : Function.Injective embed := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    change a.1 = b.1 at hab
    by_cases hij : i = j
    · subst j
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hab))
    · exfalso
      apply (Finset.disjoint_left.mp (hS hij)) a.2
      rw [hab]
      exact b.2
  have hflat : iIndepFun (fun p ↦ Z (embed p)) P :=
    iIndepFun.precomp hembed hZ
  have hgroup : iIndepFun
      (fun i omega (a : κ i) ↦ Z a.1 omega) P := by
    exact iIndepFun_piCurry_of_iIndepFun
      (fun p ↦ Z (embed p)) (fun p ↦ hZmeas (embed p)) hflat
  have hsum := hgroup.comp
    (fun i (z : κ i → ℝ) ↦ ∑ a, z a)
    (fun i ↦ by fun_prop)
  apply hsum.congr
  intro i
  exact ae_of_all P fun omega ↦ by
    change (∑ a : κ i, Z a.1 omega) = ∑ a ∈ S i, Z a omega
    exact Finset.sum_coe_sort (S i) (fun a ↦ Z a omega)

/-- Any finite consecutive family of Harper's scheduled centered prime-block
sums is mutually independent under the tilted cube law. -/
theorem iIndepFun_harperScheduledCenteredBlockSums
    (y start n : ℕ) (t u : ℝ) :
    iIndepFun
      (fun j : Fin n ↦
        harperCenteredLinearPrimeBlockSum y
          (harperScheduledPrimeBlock y (start + (j : ℕ))) t u)
      (harperTiltedCubeLaw y t) := by
  let X : HarperPrimeIndex y → HarperPrimeCube y → ℝ :=
    fun p eta ↦ harperCenteredLinearPrimeIncrement p.1 t u (eta p)
  have hXmeas : ∀ p, Measurable (X p) := fun _p ↦ measurable_of_finite _
  have hX : iIndepFun X (harperTiltedCubeLaw y t) := by
    have hcoord := iIndepFun_harperTiltedCube_coordinates y t
    simpa only [X, Function.comp_apply] using! hcoord.comp
      (fun p b ↦ harperCenteredLinearPrimeIncrement p.1 t u b)
      (fun _p ↦ measurable_of_finite _)
  have hblocks : Pairwise fun i j : Fin n ↦
      Disjoint
        (harperScheduledPrimeBlock y (start + (i : ℕ)))
        (harperScheduledPrimeBlock y (start + (j : ℕ))) := by
    intro i j hij
    apply disjoint_harperScheduledPrimeBlock y
    intro hs
    apply hij
    apply Fin.ext
    omega
  simpa only [X, harperCenteredLinearPrimeBlockSum] using!
    iIndepFun_finset_sum_of_pairwise_disjoint X hXmeas hX
      (fun j : Fin n ↦
        harperScheduledPrimeBlock y (start + (j : ℕ))) hblocks

/-- Joint-law form of scheduled block independence.  The entire vector of
centered block sums has the finite product of the individual block laws. -/
theorem map_harperScheduledCenteredBlockSums_eq_pi
    (y start n : ℕ) (t u : ℝ) :
    Measure.map
        (fun eta : HarperPrimeCube y ↦ fun j : Fin n ↦
          harperCenteredLinearPrimeBlockSum y
            (harperScheduledPrimeBlock y (start + (j : ℕ))) t u eta)
        (harperTiltedCubeLaw y t) =
      Measure.pi (fun j : Fin n ↦
        harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y (start + (j : ℕ))) t u) := by
  have hmeas : ∀ j : Fin n, Measurable
      (harperCenteredLinearPrimeBlockSum y
        (harperScheduledPrimeBlock y (start + (j : ℕ))) t u) :=
    fun _j ↦ measurable_of_finite _
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j ↦ (hmeas j).aemeasurable)).mp
    (iIndepFun_harperScheduledCenteredBlockSums y start n t u)
  simpa only [harperCenteredLinearBlockLaw] using! h

end Problem520
end Erdos

import ErdosProblems.Erdos1166.Erdos1166HLOZActualStoppedLaw
import ErdosProblems.Erdos1166.Erdos1166HLOZIncompleteStoppedBlocks
import ErdosProblems.Erdos1166.Erdos1166HLOZProp45SourceInterval
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace Erdos1166.HLOZSourceInstantiation

open Erdos1166 HLOZDecomposition HLOZActualStopped
  HLOZIncompleteStoppedBlocks HLOZProp45SourceClock HLOZProp45SourceInterval

theorem simpleRandomWalk_injective : Function.Injective simpleRandomWalk := by
  intro ω η h
  funext n
  apply directionStep_injective
  have hsucc := congrFun h (n + 1)
  have hn := congrFun h n
  rw [simpleRandomWalk_succ' ω n, simpleRandomWalk_succ' η n, hn] at hsucc
  exact add_left_cancel hsucc

theorem measurableEmbedding_simpleRandomWalk :
    MeasurableEmbedding simpleRandomWalk :=
  measurable_simpleRandomWalk.measurableEmbedding simpleRandomWalk_injective

/-! ### The genuine path-space support

The abstract path space also contains functions which do not begin at the
origin (and functions whose successive differences are not walk steps).
They have zero `simpleRandomWalkLaw` mass and must not be demanded of a
literal source atom, since every such atom is an image of increment space.
-/

/-- The set of full paths which are actually produced by increment
sequences. -/
def simpleRandomWalkSupport : Set (ℕ → Site) := Set.range simpleRandomWalk

theorem measurableSet_simpleRandomWalkSupport :
    MeasurableSet simpleRandomWalkSupport :=
  measurableEmbedding_simpleRandomWalk.measurableSet_range

/-- The random-walk law is concentrated on its literal increment-image
support. -/
theorem ae_mem_simpleRandomWalkSupport :
    ∀ᵐ s ∂simpleRandomWalkLaw, s ∈ simpleRandomWalkSupport := by
  rw [simpleRandomWalkLaw]
  apply (ae_map_iff measurable_simpleRandomWalk.aemeasurable
    measurableSet_simpleRandomWalkSupport).2
  exact Filter.Eventually.of_forall (fun omega ↦ ⟨omega, rfl⟩)

/-- Intersecting any event with the genuine walk support does not change
its probability.  No measurability hypothesis on the event is needed. -/
theorem simpleRandomWalkLaw_inter_support (A : Set (ℕ → Site)) :
    simpleRandomWalkLaw (simpleRandomWalkSupport ∩ A) =
      simpleRandomWalkLaw A :=
  Measure.measure_inter_eq_of_ae ae_mem_simpleRandomWalkSupport

def externalPathWalkAtom (labels : List IncrementPair) : Set (ℕ → Site) :=
  simpleRandomWalk ''
    firstPairExternalPathEqFrom 0 (externalPathFromLabels labels)

theorem measurableSet_externalPathWalkAtom (labels : List IncrementPair) :
    MeasurableSet (externalPathWalkAtom labels) := by
  exact measurableEmbedding_simpleRandomWalk.measurableSet_image.2
    (measurableSet_externalPathAtom 0 labels)

theorem preimage_externalPathWalkAtom (labels : List IncrementPair) :
    simpleRandomWalk ⁻¹' externalPathWalkAtom labels =
      firstPairExternalPathEqFrom 0 (externalPathFromLabels labels) := by
  exact simpleRandomWalk_injective.preimage_image _

theorem cond_map_image {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : MeasurableEmbedding f) (μ : Measure X)
    (A : Set X) (hA : MeasurableSet A) :
    (μ.map f)[|f '' A] = (μ[|A]).map f := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_apply hf.measurable (hf.measurableSet_image.2 hA),
    hf.injective.preimage_image]
  rw [Measure.restrict_map hf.measurable (hf.measurableSet_image.2 hA)]
  rw [hf.injective.preimage_image]
  exact (Measure.map_smul _ _ _).symm

theorem HasLaw.cond_map_image
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [Nonempty Z]
    {f : X → Y} (hf : MeasurableEmbedding f)
    {μ : Measure X} {A : Set X} (hA : MeasurableSet A)
    {U : X → Z} {V : Y → Z} {ν : Measure Z}
    (hUmeas : Measurable U)
    (hUV : ∀ x ∈ A, V (f x) = U x)
    (hU : HasLaw U ν μ[|A]) :
    HasLaw V ν (μ.map f)[|f '' A] := by
  let g : Y → Z := Function.extend f U fun _ ↦ Classical.choice inferInstance
  have hg : Measurable g := hf.measurable_extend hUmeas
    (measurable_const' fun _ _ ↦ rfl)
  have hgf : g ∘ f = U := by
    funext x
    change Function.extend f U
      (fun _ ↦ Classical.choice inferInstance) (f x) = U x
    exact hf.injective.extend_apply U _ x
  have hgLaw : HasLaw g ν ((μ[|A]).map f) := by
    constructor
    · exact hg.aemeasurable
    · rw [Measure.map_map hg hf.measurable, hgf, hU.map_eq]
  rw [HLOZSourceInstantiation.cond_map_image (f := f) hf μ A hA]
  apply hgLaw.congr
  apply hf.ae_map_iff.2
  filter_upwards [ae_cond_mem hA] with x hx
  rw [hUV x hx]
  exact (congrFun hgf x).symm

theorem terminalPairLabelsThrough_length_mono
    (ω : ℕ → Direction) {N R : ℕ} (hNR : N ≤ R) :
    (terminalPairLabelsThrough ω N).length ≤
      (terminalPairLabelsThrough ω R).length := by
  rw [terminalPairLabelsThrough_length, terminalPairLabelsThrough_length]
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_filter] at hr ⊢
  exact ⟨Finset.mem_range.mpr
    ((Finset.mem_range.mp hr.1).trans_le hNR), hr.2⟩

theorem excursionEndSet_subset_even_horizon
    (ω : ℕ → Direction) (N i : ℕ)
    (hi : i < (terminalPairLabelsThrough ω N).length) :
    excursionEndSet (simpleRandomWalk ω) (2 * i) ⊆ Set.Iic (2 * N) := by
  intro k hk
  rcases hk.1.2.1 with ⟨a, ha⟩
  have hk2 : 2 ≤ k := hk.1.1
  have ha1 : 1 ≤ a := by omega
  let r := a - 1
  have hkform : k = 2 * r + 2 := by
    dsimp only [r]
    omega
  have hclock :
      2 * (terminalPairLabelsThrough ω r).length = 2 * i := by
    have hc := paperExternalClock_even_eq_external_length ω r
    rw [externalDirectionsFromLabels_length] at hc
    have hkm2 : k - 2 = 2 * r := by omega
    have hkclock : paperExternalClock (simpleRandomWalk ω) (k - 2) =
        2 * i := hk.2
    rw [hkm2] at hkclock
    omega
  have hlen : (terminalPairLabelsThrough ω r).length = i := by omega
  by_contra hkN
  have hNr : N ≤ r := by
    rw [Set.mem_Iic, hkform] at hkN
    omega
  have hmono := terminalPairLabelsThrough_length_mono ω hNr
  rw [hlen] at hmono
  omega

theorem excursionEndSet_eq_stopped_even
    (ω : ℕ → Direction) (N i : ℕ)
    (hi : i < (terminalPairLabelsThrough ω N).length) :
    excursionEndSet (simpleRandomWalk ω) (2 * i) =
      (stoppedExcursionEnds (simpleRandomWalk ω) (2 * N) (2 * i) : Set ℕ) := by
  rw [coe_stoppedExcursionEnds]
  exact (Set.inter_eq_left.2
    (excursionEndSet_subset_even_horizon ω N i hi)).symm

theorem paperHoldingNat_even_eq_stoppedExcursionBlock
    (ω : ℕ → Direction) (N i : ℕ)
    (hi : i < (terminalPairLabelsThrough ω N).length) :
    paperHoldingNat (simpleRandomWalk ω) (2 * i) =
      stoppedExcursionBlock (simpleRandomWalk ω) (2 * N) (2 * i) := by
  unfold paperHoldingNat paperHoldingTime stoppedExcursionBlock
  rw [excursionEndSet_eq_stopped_even ω N i hi,
    Set.encard_coe_eq_coe_finsetCard]
  simp

def runSubvector {n k : ℕ} (e : Fin k → Fin n)
    (v : Fin n → ℕ) : Fin k → ℕ :=
  fun i ↦ v (e i)

theorem runSubvector_hasLaw {n k : ℕ} (e : Fin k → Fin n)
    (he : Function.Injective e) :
    HasLaw (runSubvector e) (HLOZUrn.runVectorMeasure k)
      (HLOZUrn.runVectorMeasure n) := by
  constructor
  · exact (measurable_of_countable (runSubvector e)).aemeasurable
  · unfold HLOZUrn.runVectorMeasure runSubvector
    rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
    exact Measure.map_infinitePi_infinitePi_of_inj he

theorem runSubvectorSum_hasLaw {n k : ℕ} (e : Fin k → Fin n)
    (he : Function.Injective e) :
    HasLaw (fun v ↦ ∑ i, v (e i)) (HLOZUrn.negBinMeasure k)
      (HLOZUrn.runVectorMeasure n) := by
  have hsub := runSubvector_hasLaw e he
  simpa [HLOZUrn.runSum, runSubvector] using
    HLOZUrn.runSum_hasLaw.fun_comp hsub

abbrev CompletedExternalIndex {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) :=
  {i : Fin q //
    stoppedExternalBaseAt (0, 0) labels i.castSucc = x}

noncomputable def completedExternalEmbedding {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) :
    Fin (Fintype.card (CompletedExternalIndex labels x)) → Fin q :=
  fun i ↦ ((Fintype.equivFin (CompletedExternalIndex labels x)).symm i).1

theorem completedExternalEmbedding_injective {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) :
    Function.Injective (completedExternalEmbedding labels x) := by
  intro i j hij
  apply (Fintype.equivFin (CompletedExternalIndex labels x)).symm.injective
  apply Subtype.ext
  exact hij

noncomputable def decodedHoldingBlock {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (v : Fin q → ℕ) : ℕ :=
  ∑ i : Fin (Fintype.card (CompletedExternalIndex labels x)),
    v (completedExternalEmbedding labels x i)

theorem decodedHoldingBlock_hasLaw {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) :
    HasLaw (decodedHoldingBlock labels x)
      (HLOZUrn.negBinMeasure
        (Fintype.card (CompletedExternalIndex labels x)))
      (HLOZUrn.runVectorMeasure q) := by
  exact runSubvectorSum_hasLaw (completedExternalEmbedding labels x)
    (completedExternalEmbedding_injective labels x)

def listVectorToFin {q : ℕ} (labels : Fin q → IncrementPair)
    (v : Fin (List.ofFn labels).length → ℕ) : Fin q → ℕ :=
  fun i ↦ v (Fin.cast (by simp) i)

theorem listVectorToFin_hasLaw {q : ℕ}
    (labels : Fin q → IncrementPair) :
    HasLaw (listVectorToFin labels) (HLOZUrn.runVectorMeasure q)
      (HLOZUrn.runVectorMeasure (List.ofFn labels).length) := by
  unfold listVectorToFin
  apply runSubvector_hasLaw
  exact Fin.cast_injective _

theorem conditional_decodedHoldingBlock_hasLaw {q : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site) :
    HasLaw
      (fun ω ↦ decodedHoldingBlock labels x
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels) ω)))
      (HLOZUrn.negBinMeasure
        (Fintype.card (CompletedExternalIndex labels x)))
      incrementLaw[|firstPairExternalPathEqFrom 0
        (externalPathFromLabels (List.ofFn labels))] := by
  have hvec := conditionalPairRunVector_hasLaw 0 (List.ofFn labels) (by
    intro p hp
    rw [List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩
    exact hnondist i)
  have hblock := decodedHoldingBlock_hasLaw labels x
  have hcast := (listVectorToFin_hasLaw labels).fun_comp hvec
  exact hblock.fun_comp hcast

theorem measurable_conditionalDecodedHoldingBlock {q : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site) :
    Measurable
      (fun ω ↦ decodedHoldingBlock labels x
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels) ω))) := by
  have hruns : Measurable
      (conditionalPairRunVector 0 (List.ofFn labels)) :=
    measurable_conditionalPairRunVector 0 (List.ofFn labels) (by
      intro p hp
      rw [List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact hnondist i)
  exact (measurable_of_countable
    (fun v : Fin q → ℕ ↦ decodedHoldingBlock labels x v)).comp
      ((measurable_of_countable (listVectorToFin labels)).comp hruns)

noncomputable def pathDecodedHoldingBlock {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) :
    (ℕ → Site) → ℕ :=
  Function.extend simpleRandomWalk
    (fun ω ↦ decodedHoldingBlock labels x
      (listVectorToFin labels
        (conditionalPairRunVector 0 (List.ofFn labels) ω))) 0

theorem measurable_pathDecodedHoldingBlock {q : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site) :
    Measurable (pathDecodedHoldingBlock labels x) := by
  apply measurableEmbedding_simpleRandomWalk.measurable_extend
  · exact measurable_conditionalDecodedHoldingBlock labels hnondist x
  · exact measurable_const

theorem pathDecodedHoldingBlock_simpleRandomWalk {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) (ω : ℕ → Direction) :
    pathDecodedHoldingBlock labels x (simpleRandomWalk ω) =
      decodedHoldingBlock labels x
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels) ω)) := by
  unfold pathDecodedHoldingBlock
  exact simpleRandomWalk_injective.extend_apply _ _ ω

theorem externalPathWalkAtom_pos {q : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair) :
    simpleRandomWalkLaw
      (externalPathWalkAtom (List.ofFn labels)) ≠ 0 := by
  rw [simpleRandomWalkLaw,
    Measure.map_apply measurable_simpleRandomWalk
      (measurableSet_externalPathWalkAtom (List.ofFn labels)),
    preimage_externalPathWalkAtom]
  apply externalPathAtom_pos 0 (List.ofFn labels)
  intro p hp
  rw [List.mem_ofFn] at hp
  rcases hp with ⟨i, rfl⟩
  exact hnondist i

theorem pathDecodedHoldingBlock_hasLaw {q : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site) :
    HasLaw (pathDecodedHoldingBlock labels x)
      (HLOZUrn.negBinMeasure
        (Fintype.card (CompletedExternalIndex labels x)))
      simpleRandomWalkLaw[|externalPathWalkAtom (List.ofFn labels)] := by
  rw [simpleRandomWalkLaw]
  apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk
    (measurableSet_externalPathAtom 0 (List.ofFn labels))
  · exact measurable_conditionalDecodedHoldingBlock labels hnondist x
  · intro ω _
    exact pathDecodedHoldingBlock_simpleRandomWalk labels x ω
  · exact conditional_decodedHoldingBlock_hasLaw labels hnondist x

end Erdos1166.HLOZSourceInstantiation

import Wikipedia.NoExoticSixSphere.OperatorRankCoordinates
import Wikipedia.NoExoticSixSphere.CorankOneChart
import Mathlib.Topology.Compactness.Lindelof

/-!
# A countable coordinate cover of the entire corank-one stratum

Rank-adapted linear coordinates put every corank-one operator into an
invertible leading-block chart. The original finite-dimensional operator
space is second countable, so a countable subfamily covers the whole stratum.
The coordinate changes act on the actual operator by conjugating its source
and target; the smooth structure is not replaced.
-/

noncomputable section

open Set Function Module TopologicalSpace

namespace NoExoticSixSphere.CorankOneCoordinates

open CorankOne

variable {V W E F : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

abbrev Coordinates (V W E F : Type)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  (V ≃L[ℝ] E × ℝ) × (W ≃L[ℝ] E × F)

def operatorEquiv (c : Coordinates V W E F) : (V →L[ℝ] W) ≃L[ℝ] BlockMap E F :=
  c.1.arrowCongr c.2

def domain (c : Coordinates V W E F) : Opens (V →L[ℝ] W) :=
  ⟨operatorEquiv c ⁻¹' (chart (E := E) (F := F) : Set (BlockMap E F)),
    (chart (E := E) (F := F)).isOpen.preimage (operatorEquiv c).continuous⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem injective_operatorEquiv_iff (c : Coordinates V W E F) (L : V →L[ℝ] W) :
    Injective (operatorEquiv c L) ↔ Injective L := by
  constructor
  · intro h x y hxy
    apply c.1.injective
    apply h
    change c.2 (L (c.1.symm (c.1 x))) = c.2 (L (c.1.symm (c.1 y)))
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using congrArg c.2 hxy
  · intro h
    exact c.2.injective.comp (h.comp c.1.symm.injective)

theorem exists_chart (L : V →L[ℝ] W) (hr : finrank ℝ L.range = finrank ℝ E)
    (hv : finrank ℝ V = finrank ℝ E + 1)
    (hw : finrank ℝ W = finrank ℝ E + finrank ℝ F) :
    ∃ c : Coordinates V W E F, L ∈ domain c := by
  obtain ⟨u, v, huv⟩ := OperatorRank.exists_coordinates (N := ℝ) L hr
    (by simpa only [finrank_self] using hv) hw
  refine ⟨(u, v), ?_⟩
  change Injective (leading (operatorEquiv (u, v) L))
  have he : leading (operatorEquiv (u, v) L) = ContinuousLinearMap.id ℝ E := by
    ext x
    change (v (L (u.symm (x, 0)))).1 = x
    rw [huv]
  rw [he]
  exact Function.injective_id

theorem exists_countable_cover (hv : finrank ℝ V = finrank ℝ E + 1)
    (hw : finrank ℝ W = finrank ℝ E + finrank ℝ F) :
    ∃ C : Set (Coordinates V W E F), C.Countable ∧
      ∀ L : V →L[ℝ] W, finrank ℝ L.range = finrank ℝ E →
        ∃ c ∈ C, L ∈ domain c := by
  let e : (V →L[ℝ] W) ≃L[ℝ] (Fin (finrank ℝ (V →L[ℝ] W)) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun ℝ).symm
  let : SecondCountableTopology (V →L[ℝ] W) := e.toHomeomorph.secondCountableTopology
  let S : Set (V →L[ℝ] W) := {L | finrank ℝ L.range = finrank ℝ E}
  have hcov : S ⊆ ⋃ c : Coordinates V W E F, (domain c : Set (V →L[ℝ] W)) := by
    intro L hL
    obtain ⟨c, hc⟩ := exists_chart L hL hv hw
    exact mem_iUnion.mpr ⟨c, hc⟩
  obtain ⟨C, hC, hcover⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
    (fun c : Coordinates V W E F ↦ (domain c : Set (V →L[ℝ] W)))
    (fun c ↦ (domain c).isOpen) hcov
  refine ⟨C, hC, ?_⟩
  intro L hL
  obtain ⟨c, hc⟩ := mem_iUnion.mp (hcover hL)
  obtain ⟨hcC, hcL⟩ := mem_iUnion.mp hc
  exact ⟨c, hcC, hcL⟩

end NoExoticSixSphere.CorankOneCoordinates

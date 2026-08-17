import ErdosProblems.Erdos565.FiniteAnalysis
import ErdosProblems.Erdos565.Janson

/-!
# Pulling Janson weights back through finite projections

The projection of a hypergraph along a vertex map is `Hypergraph.map`.  Different source edges
can have the same projected edge, so pulling a weight back by plain composition would multiply
its mass.  We instead divide the weight of a projected edge equally among all source edges in
its fibre.

When the projection is injective on every source edge, weighted degrees split fibrewise.  The
sum of their squares can consequently only decrease.  This gives the deterministic pullback
principle for the Janson property used in the proof of Erdős Problem 565.
-/

open scoped BigOperators NNReal

namespace Erdos565
namespace Hypergraph

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- The source edges which project to `F`. -/
def edgeFiber (H : Hypergraph V) (π : V → W) (F : Finset W) : Hypergraph V :=
  H.filter fun E ↦ E.image π = F

@[simp] lemma mem_edgeFiber {H : Hypergraph V} {π : V → W} {F : Finset W}
    {E : Finset V} : E ∈ edgeFiber H π F ↔ E ∈ H ∧ E.image π = F := by
  simp [edgeFiber]

/-- All finite source sets which project to `K`. -/
def subsetFiber [Fintype V] (π : V → W) (K : Finset W) : Hypergraph V :=
  Finset.univ.powerset.filter fun L ↦ L.image π = K

@[simp] lemma mem_subsetFiber [Fintype V] {π : V → W} {K : Finset W}
    {L : Finset V} : L ∈ subsetFiber π K ↔ L.image π = K := by
  simp [subsetFiber]

/-- The canonical lift of `K` inside a source edge `E`. -/
def edgeLift (π : V → W) (E : Finset V) (K : Finset W) : Finset V :=
  E.filter fun v ↦ π v ∈ K

@[simp] lemma mem_edgeLift {π : V → W} {E : Finset V} {K : Finset W} {v : V} :
    v ∈ edgeLift π E K ↔ v ∈ E ∧ π v ∈ K := by
  simp [edgeLift]

lemma edgeLift_subset (π : V → W) (E : Finset V) (K : Finset W) :
    edgeLift π E K ⊆ E := by
  intro v hv
  exact (mem_edgeLift.mp hv).1

lemma image_edgeLift {π : V → W} {E : Finset V} {K : Finset W}
    (hK : K ⊆ E.image π) : (edgeLift π E K).image π = K := by
  ext w
  simp only [Finset.mem_image, mem_edgeLift]
  constructor
  · rintro ⟨v, ⟨_hvE, hvK⟩, rfl⟩
    exact hvK
  · intro hwK
    obtain ⟨v, hvE, hvEq⟩ := Finset.mem_image.mp (hK hwK)
    exact ⟨v, ⟨hvE, hvEq ▸ hwK⟩, hvEq⟩

lemma eq_edgeLift_of_subset_image_eq {π : V → W} {E L : Finset V} {K : Finset W}
    (hinj : Set.InjOn π E) (hLE : L ⊆ E) (himage : L.image π = K) :
    L = edgeLift π E K := by
  apply Finset.Subset.antisymm
  · intro v hvL
    exact mem_edgeLift.mpr ⟨hLE hvL, himage ▸ Finset.mem_image_of_mem π hvL⟩
  · intro v hvLift
    have hvE := (mem_edgeLift.mp hvLift).1
    have hvK := (mem_edgeLift.mp hvLift).2
    have hvImage : π v ∈ L.image π := himage.symm ▸ hvK
    obtain ⟨u, huL, huv⟩ := Finset.mem_image.mp hvImage
    have huE := hLE huL
    have huvEq : u = v := hinj huE hvE huv
    exact huvEq ▸ huL

/-- Inside an edge on which `π` is injective, a projected set has either one lift or none. -/
lemma subsetFiber_filter_subset [Fintype V] {π : V → W} {E : Finset V}
    {K : Finset W} (hinj : Set.InjOn π E) :
    (subsetFiber π K).filter (fun L ↦ L ⊆ E) =
      if K ⊆ E.image π then {edgeLift π E K} else ∅ := by
  by_cases hK : K ⊆ E.image π
  · rw [if_pos hK]
    ext L
    simp only [Finset.mem_filter, mem_subsetFiber, Finset.mem_singleton]
    constructor
    · rintro ⟨himage, hLE⟩
      exact eq_edgeLift_of_subset_image_eq hinj hLE himage
    · rintro rfl
      exact ⟨image_edgeLift hK, edgeLift_subset π E K⟩
  · rw [if_neg hK]
    ext L
    simp only [Finset.mem_filter, mem_subsetFiber]
    constructor
    · rintro ⟨himage, hLE⟩
      exact (hK (himage ▸ Finset.image_mono π hLE)).elim
    · intro hEmpty
      exact (Finset.notMem_empty L hEmpty).elim

/-- A projection is edgewise faithful when it is injective on every hyperedge. -/
def EdgewiseInjective (H : Hypergraph V) (π : V → W) : Prop :=
  ∀ E ∈ H, Set.InjOn π E

lemma edgewiseInjective_iff_card_image (H : Hypergraph V) (π : V → W) :
    EdgewiseInjective H π ↔ ∀ E ∈ H, (E.image π).card = E.card := by
  simp only [EdgewiseInjective, Finset.card_image_iff]

/-- The fibre-averaged pullback of a nonnegative edge weight.  Values off `H` are irrelevant. -/
noncomputable def averagePullback (H : Hypergraph V) (π : V → W)
    (μ : EdgeWeight (H.map π)) : EdgeWeight H :=
  fun E ↦ μ (E.image π) / (edgeFiber H π (E.image π)).card

lemma edgeFiber_card_pos {H : Hypergraph V} {π : V → W} {F : Finset W}
    (hF : F ∈ H.map π) : 0 < (edgeFiber H π F).card := by
  rw [Finset.card_pos]
  obtain ⟨E, hE, hEq⟩ := mem_map.mp hF
  exact ⟨E, mem_edgeFiber.mpr ⟨hE, hEq⟩⟩

/-- The averaged weights in one edge fibre add up to the original projected weight. -/
lemma sum_averagePullback_edgeFiber {H : Hypergraph V} {π : V → W}
    (μ : EdgeWeight (H.map π)) {F : Finset W} (hF : F ∈ H.map π) :
    ∑ E ∈ edgeFiber H π F, (averagePullback H π μ E : ℝ) = (μ F : ℝ) := by
  have hcard : (edgeFiber H π F).card ≠ 0 := Nat.ne_of_gt (edgeFiber_card_pos hF)
  have himage : ∀ E ∈ edgeFiber H π F, E.image π = F :=
    fun E hE ↦ (mem_edgeFiber.mp hE).2
  calc
    ∑ E ∈ edgeFiber H π F, (averagePullback H π μ E : ℝ) =
        ∑ _E ∈ edgeFiber H π F,
          ((μ F / ((edgeFiber H π F).card : ℝ≥0) : ℝ≥0) : ℝ) := by
            apply Finset.sum_congr rfl
            intro E hE
            simp only [averagePullback]
            rw [himage E hE]
    _ = (μ F : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, NNReal.coe_natCast, NNReal.coe_div]
      exact mul_div_cancel₀ (μ F : ℝ) (Nat.cast_ne_zero.mpr hcard)

/-- Fibre averaging preserves any sum selected by a predicate on projected edges. -/
lemma sum_averagePullback_image_filter {H : Hypergraph V} {π : V → W}
    (μ : EdgeWeight (H.map π)) (P : Finset W → Prop) [DecidablePred P] :
    ∑ E ∈ H with P (E.image π), (averagePullback H π μ E : ℝ) =
      ∑ F ∈ H.map π with P F, (μ F : ℝ) := by
  let s : Hypergraph V := H.filter fun E ↦ P (E.image π)
  let t : Hypergraph W := (H.map π).filter P
  have hmaps : ∀ E ∈ s, E.image π ∈ t := by
    intro E hE
    have hs := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr ⟨mem_map.mpr ⟨E, hs.1, rfl⟩, hs.2⟩
  have hsum := Finset.sum_fiberwise_of_maps_to hmaps
    (fun E ↦ (averagePullback H π μ E : ℝ))
  change (∑ E ∈ s, (averagePullback H π μ E : ℝ)) = ∑ F ∈ t, (μ F : ℝ)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro F hF
  have hFmap : F ∈ H.map π := (Finset.mem_filter.mp hF).1
  have hPF : P F := (Finset.mem_filter.mp hF).2
  have hfiber : s.filter (fun E ↦ E.image π = F) = edgeFiber H π F := by
    ext E
    simp only [s, edgeFiber, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hEH, _⟩, hEq⟩
      exact ⟨hEH, hEq⟩
    · rintro ⟨hEH, hEq⟩
      exact ⟨⟨hEH, hEq ▸ hPF⟩, hEq⟩
  rw [hfiber]
  exact sum_averagePullback_edgeFiber μ hFmap

/-- Fibre averaging preserves total mass. -/
lemma mass_averagePullback {H : Hypergraph V} {π : V → W}
    (μ : EdgeWeight (H.map π)) :
    mass H (averagePullback H π μ) = mass (H.map π) μ := by
  simpa [mass] using
    (sum_averagePullback_image_filter (H := H) (π := π) μ (fun _ ↦ True))

/-- A constant summed over the lifts of `K` inside an edge contributes exactly once when the
edge contains `K` after projection, and not at all otherwise. -/
lemma sum_subsetFiber_indicator [Fintype V] {π : V → W} {E : Finset V}
    {K : Finset W} (hinj : Set.InjOn π E) (a : ℝ) :
    ∑ L ∈ subsetFiber π K, (if L ⊆ E then a else 0) =
      if K ⊆ E.image π then a else 0 := by
  rw [← Finset.sum_filter, subsetFiber_filter_subset hinj]
  by_cases hK : K ⊆ E.image π <;> simp [hK]

/-- Weighted degrees split exactly over all source subsets in a projection fibre. -/
lemma weightedDegree_averagePullback_fiber [Fintype V] {H : Hypergraph V} {π : V → W}
    (hinj : EdgewiseInjective H π) (μ : EdgeWeight (H.map π)) (K : Finset W) :
    ∑ L ∈ subsetFiber π K, weightedDegree H (averagePullback H π μ) L =
      weightedDegree (H.map π) μ K := by
  calc
    ∑ L ∈ subsetFiber π K, weightedDegree H (averagePullback H π μ) L =
        ∑ L ∈ subsetFiber π K, ∑ E ∈ H,
          if L ⊆ E then (averagePullback H π μ E : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro L _hL
      rw [weightedDegree, Finset.sum_filter]
    _ = ∑ E ∈ H, ∑ L ∈ subsetFiber π K,
          if L ⊆ E then (averagePullback H π μ E : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ E ∈ H,
          if K ⊆ E.image π then (averagePullback H π μ E : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro E hE
      exact sum_subsetFiber_indicator (hinj E hE) _
    _ = ∑ E ∈ H with K ⊆ E.image π, (averagePullback H π μ E : ℝ) := by
      rw [Finset.sum_filter]
    _ = ∑ F ∈ H.map π with K ⊆ F, (μ F : ℝ) :=
      sum_averagePullback_image_filter μ (fun F ↦ K ⊆ F)
    _ = weightedDegree (H.map π) μ K := by
      rfl

/-- A source set on which `π` is not injective cannot be contained in an edge on which `π` is
injective, so its weighted degree is zero. -/
lemma weightedDegree_eq_zero_of_not_injOn {H : Hypergraph V} {π : V → W}
    (hinj : EdgewiseInjective H π) (ν : EdgeWeight H) {L : Finset V}
    (hL : ¬Set.InjOn π L) : weightedDegree H ν L = 0 := by
  rw [weightedDegree]
  apply Finset.sum_eq_zero
  intro E hE
  have hEf := Finset.mem_filter.mp hE
  exact (hL ((hinj E hEf.1).mono hEf.2)).elim

/-- Janson sets on which the vertex projection is injective.  All other Janson sets have degree
zero under an edgewise-injective projection. -/
noncomputable def faithfulJansonSets [Fintype V] (π : V → W) : Hypergraph V :=
  jansonSets.filter fun L ↦ Set.InjOn π L

@[simp] lemma mem_faithfulJansonSets [Fintype V] {π : V → W} {L : Finset V} :
    L ∈ faithfulJansonSets π ↔ L ∈ jansonSets ∧ Set.InjOn π L := by
  classical
  simp [faithfulJansonSets]

/-- Fibre averaging cannot increase the Janson energy. -/
lemma Lambda_averagePullback_le [Fintype V] [Fintype W] {H : Hypergraph V}
    {π : V → W} (hinj : EdgewiseInjective H π) (μ : EdgeWeight (H.map π))
    {p : ℝ} (hp : 0 < p) :
    Lambda H p (averagePullback H π μ) ≤ Lambda (H.map π) p μ := by
  classical
  let good : Hypergraph V := faithfulJansonSets π
  let term : Finset V → ℝ := fun L ↦
    weightedDegree H (averagePullback H π μ) L ^ 2 / p ^ L.card
  have hgood : good ⊆ jansonSets := by
    intro L hL
    exact (mem_faithfulJansonSets.mp hL).1
  have hzero : ∀ L ∈ jansonSets, L ∉ good → term L = 0 := by
    intro L hLj hLgood
    have hnot : ¬Set.InjOn π L := by
      intro hLi
      exact hLgood (mem_faithfulJansonSets.mpr ⟨hLj, hLi⟩)
    unfold term
    rw [weightedDegree_eq_zero_of_not_injOn hinj _ hnot]
    norm_num
  have hmaps : ∀ L ∈ good, L.image π ∈ (jansonSets : Hypergraph W) := by
    intro L hL
    have hparts := mem_faithfulJansonSets.mp hL
    have hcard : (L.image π).card = L.card := Finset.card_image_iff.mpr hparts.2
    simpa [jansonSets, hcard] using hparts.1
  rw [Lambda, Lambda]
  change (∑ L ∈ jansonSets, term L) ≤ _
  rw [← Finset.sum_subset hgood hzero]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps term]
  apply Finset.sum_le_sum
  intro K hK
  let gf : Hypergraph V := good.filter fun L ↦ L.image π = K
  have hgf_subset : gf ⊆ subsetFiber π K := by
    intro L hL
    exact mem_subsetFiber.mpr (Finset.mem_filter.mp hL).2
  have hsq :
      (∑ L ∈ gf, weightedDegree H (averagePullback H π μ) L ^ 2) ≤
        weightedDegree (H.map π) μ K ^ 2 := by
    calc
      (∑ L ∈ gf, weightedDegree H (averagePullback H π μ) L ^ 2) ≤
          ∑ L ∈ subsetFiber π K,
            weightedDegree H (averagePullback H π μ) L ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hgf_subset
          (fun _L _hL _hLgf ↦ sq_nonneg _)
      _ ≤ (∑ L ∈ subsetFiber π K,
            weightedDegree H (averagePullback H π μ) L) ^ 2 := by
        exact FiniteAnalysis.sum_sq_le_sq_sum_of_nonneg _ _
          (fun L _hL ↦ weightedDegree_nonneg H _ L)
      _ = weightedDegree (H.map π) μ K ^ 2 := by
        rw [weightedDegree_averagePullback_fiber hinj μ K]
  calc
    (∑ L ∈ good with L.image π = K, term L) =
        (∑ L ∈ gf, weightedDegree H (averagePullback H π μ) L ^ 2) /
          p ^ K.card := by
      simp only [term, div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro L hL
      have hLgood : L ∈ good := (Finset.mem_filter.mp hL).1
      have hLimage : L.image π = K := (Finset.mem_filter.mp hL).2
      have hLi : Set.InjOn π L := (mem_faithfulJansonSets.mp hLgood).2
      have hcard : K.card = L.card := by
        rw [← hLimage, Finset.card_image_iff.mpr hLi]
      rw [hcard]
    _ ≤ weightedDegree (H.map π) μ K ^ 2 / p ^ K.card :=
      div_le_div_of_nonneg_right hsq (pow_nonneg hp.le _)

namespace IsJanson

/-- Jansonness pulls back through a map which is injective on every hyperedge. -/
lemma pullback [Fintype V] [Fintype W] {H : Hypergraph V} {π : V → W}
    (hinj : EdgewiseInjective H π) {p R : ℝ} (hp : 0 < p)
    (h : (H.map π).IsJanson p R) : H.IsJanson p R := by
  rcases h with hR | ⟨μ, hμ⟩
  · exact Or.inl hR
  · right
    refine ⟨averagePullback H π μ, ?_⟩
    calc
      Lambda H p (averagePullback H π μ) ≤ Lambda (H.map π) p μ :=
        Lambda_averagePullback_le hinj μ hp
      _ < mass (H.map π) μ ^ 2 / R := hμ
      _ = mass H (averagePullback H π μ) ^ 2 / R := by
        rw [mass_averagePullback]

/-- Source-facing version of `pullback`, stated with preservation of edge cardinalities. -/
lemma pullback_of_card_image_eq [Fintype V] [Fintype W] {H : Hypergraph V}
    {π : V → W} (hcard : ∀ E ∈ H, (E.image π).card = E.card)
    {p R : ℝ} (hp : 0 < p) (h : (H.map π).IsJanson p R) : H.IsJanson p R := by
  exact pullback ((edgewiseInjective_iff_card_image H π).mpr hcard) hp h

end IsJanson

end Hypergraph
end Erdos565

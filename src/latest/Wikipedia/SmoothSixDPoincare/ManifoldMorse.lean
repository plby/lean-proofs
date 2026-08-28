import Wikipedia.SmoothSixDPoincare.MorseOpenDomain
import Wikipedia.SmoothSixDPoincare.ManifoldPerturbation

/-!
# Morse points on the original smooth manifold

The predicate below uses genuine maximal-atlas charts and the actual first
and second derivatives of the function in those charts. It includes regular
points as well as nondegenerate critical points. No Morse-function existence
or decomposition principle is an assumption.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable (E : Type*) {M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- A regular or nondegenerate critical point in an actual smooth coordinate chart. -/
def IsMorseAt (f : M → ℝ) (x : M) : Prop :=
  ∃ e : OpenPartialHomeomorph M E, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
    x ∈ e.source ∧ (fderiv ℝ (f ∘ e.symm) (e x) ≠ 0 ∨
      Function.Bijective (fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e x)))

/-- Every point in the prescribed set is regular or a nondegenerate critical point. -/
def IsMorseOn (f : M → ℝ) (K : Set M) : Prop := ∀ x ∈ K, IsMorseAt E f x

/-- A function has no degenerate critical points anywhere on the manifold. -/
def IsMorse (f : M → ℝ) : Prop := ∀ x, IsMorseAt E f x

variable {E}

omit [FiniteDimensional ℝ E] in
theorem IsMorseOn.mono {f : M → ℝ} {K L : Set M} (h : IsMorseOn E f K)
    (hLK : L ⊆ K) : IsMorseOn E f L := fun x hx => h x (hLK hx)

omit [FiniteDimensional ℝ E] in
theorem IsMorseOn.union {f : M → ℝ} {K L : Set M}
    (hK : IsMorseOn E f K) (hL : IsMorseOn E f L) : IsMorseOn E f (K ∪ L) := by
  intro x hx
  rcases hx with hx | hx
  · exact hK x hx
  · exact hL x hx

omit [FiniteDimensional ℝ E] in
/-- A smooth manifold function is smooth on the actual target of any smooth chart. -/
theorem contDiffOn_chartExpression {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContDiffOn ℝ ∞ (f ∘ e.symm) e.target :=
  (hf.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn

omit [FiniteDimensional ℝ E] in
/-- Transfer the actual Morse condition through equality of coordinate expressions near a point. -/
theorem isMorseAt_of_chart_eventuallyEq {f : M → ℝ} {g : E → ℝ} {x : M}
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hx : x ∈ e.source) (hg : MorsePerturbation.IsMorse g)
    (heq : f ∘ e.symm =ᶠ[𝓝 (e x)] g) : IsMorseAt E f x := by
  refine ⟨e, he, hx, ?_⟩
  by_cases hc : fderiv ℝ (f ∘ e.symm) (e x) = 0
  · right
    rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq]
    exact hg (e x) ((heq.fderiv_eq (𝕜 := ℝ)).symm.trans hc)
  · exact Or.inl hc

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [FiniteDimensional ℝ E] in
/-- Express a native smooth family in any fixed maximal-atlas chart. -/
theorem contDiffOn_inChart {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContDiffOn ℝ ∞ (fun q : P × E => f q.1 (e.symm q.2))
      {q : P × E | q.2 ∈ e.target} := by
  intro q hq
  have hi := contMDiffAt_symm_of_mem_maximalAtlas he hq
  have hmap : ContMDiffAt 𝓘(ℝ, P × E) (𝓘(ℝ, P).prod 𝓘(ℝ, E)) ∞
      (fun r : P × E => (r.1, e.symm r.2)) q :=
    contDiffAt_fst.contMDiffAt.prodMk (hi.comp q contDiffAt_snd.contMDiffAt)
  exact (hf.contMDiffAt.comp q hmap).contDiffAt.contDiffWithinAt

/-- The good-point condition in one fixed smooth chart is open in parameter and point. -/
theorem isOpen_morseInChart {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    IsOpen {q : P × M | q.2 ∈ e.source ∧
      (fderiv ℝ (f q.1 ∘ e.symm) (e q.2) ≠ 0 ∨
        Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1 ∘ e.symm)) (e q.2)))} := by
  have hg := MorsePerturbation.isOpen_goodJetOn (f := fun a y => f a (e.symm y))
    (e.open_target.preimage (continuous_snd : Continuous (Prod.snd : P × E → E)))
    (contDiffOn_inChart hf he)
  let S : Set (P × M) := {q | q.2 ∈ e.source}
  have hS : IsOpen S := e.open_source.preimage continuous_snd
  have hm : ContinuousOn (fun q : P × M => (q.1, e q.2)) S :=
    continuous_fst.continuousOn.prodMk
      (e.continuousOn.comp continuous_snd.continuousOn (fun _ hq => hq))
  convert hm.isOpen_inter_preimage hS hg using 1
  ext q
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, S]
  constructor
  · rintro ⟨hq, hg⟩
    exact ⟨hq, e.map_source hq, hg⟩
  · rintro ⟨hq, -, hg⟩
    exact ⟨hq, hg⟩

/-- Being a Morse point is open for a native jointly smooth family. -/
theorem isOpen_isMorseAt {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) :
    IsOpen {q : P × M | IsMorseAt E (f q.1) q.2} := by
  have heq : {q : P × M | IsMorseAt E (f q.1) q.2} =
      ⋃ (e : OpenPartialHomeomorph M E) (_ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M),
        {q : P × M | q.2 ∈ e.source ∧
          (fderiv ℝ (f q.1 ∘ e.symm) (e q.2) ≠ 0 ∨
            Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1 ∘ e.symm)) (e q.2)))} := by
    ext q
    simp only [mem_ofPred_eq, IsMorseAt, mem_iUnion, exists_prop]
  rw [heq]
  exact isOpen_iUnion fun e => isOpen_iUnion fun he => isOpen_morseInChart hf he

/-- Previously Morse compact regions remain Morse for all sufficiently nearby parameters. -/
theorem isOpen_isMorseOn {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {K : Set M} (hK : IsCompact K) :
    IsOpen {p : P | IsMorseOn E (f p) K} :=
  MorsePerturbation.isOpen_forall_mem_compact hK (isOpen_isMorseAt hf)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse

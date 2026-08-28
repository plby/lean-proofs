import Wikipedia.NoExoticSixSphere.SupportedHomeomorph
import Wikipedia.NoExoticSixSphere.SupportedNeighborhoodHomology

/-!
# Transport of the actual point-evaluation isomorphisms

The commuting evaluation squares show that bijectivity of evaluation is
preserved by homeomorphisms of supports and by open-neighborhood excision.
Combining these operations transports it through an actual partial chart.
-/

noncomputable section

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original evaluation is bijective on one side of a homeomorphism exactly
when it is bijective on the other side. -/
theorem evaluate_bijective_iff_homeomorph (A : ModuleCat.{0} ℤ) (h : X ≃ₜ Y)
    {K : Set X} {L : Set Y} (hK : ∀ x, x ∈ K ↔ h x ∈ L) (x : X) (hx : x ∈ K) (n : ℕ) :
    Function.Bijective (evaluate A L (h x) ((hK x).mp hx) n) ↔
      Function.Bijective (evaluate A K x hx n) := by
  let F := homeomorphEquiv A h hK n
  let G := RelativeCoefficients.localHomeomorphEquiv A h x n
  let f := evaluate A K x hx n
  let g := evaluate A L (h x) ((hK x).mp hx) n
  have he : g.comp F.toLinearMap = G.toLinearMap.comp f :=
    evaluate_homeomorphEquiv A h hK x hx n
  have hf : Function.Bijective (g.comp F.toLinearMap) ↔ Function.Bijective g :=
    Function.Bijective.of_comp_iff g F.bijective
  have hg : Function.Bijective (G.toLinearMap.comp f) ↔ Function.Bijective f :=
    Function.Bijective.of_comp_iff' G.bijective f
  rw [he] at hf
  exact hf.symm.trans hg

variable [T1Space X]

/-- Excision of an actual open neighborhood preserves bijectivity of point evaluation. -/
theorem evaluate_bijective_iff_inclusion (p : ℕ) (hp : p ≠ 0) (U K : Set X)
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (x : U) (hx : (x : X) ∈ K) (n : ℕ) :
    Function.Bijective (evaluate (ModuleCat.of ℤ (ZMod p)) K (x : X) hx n) ↔
      Function.Bijective (evaluate (ModuleCat.of ℤ (ZMod p)) (supportIn U K) x hx n) := by
  let F := inclusionEquiv p hp U K hU hK hKU n
  let G := RelativeCoefficients.modNeighborhoodEquiv p hp U hU x n
  let f := evaluate (ModuleCat.of ℤ (ZMod p)) (supportIn U K) x hx n
  let g := evaluate (ModuleCat.of ℤ (ZMod p)) K (x : X) hx n
  have he : g.comp F.toLinearMap = G.toLinearMap.comp f := evaluate_inclusion p U K x hx n
  have hf : Function.Bijective (g.comp F.toLinearMap) ↔ Function.Bijective g :=
    Function.Bijective.of_comp_iff g F.bijective
  have hg : Function.Bijective (G.toLinearMap.comp f) ↔ Function.Bijective f :=
    Function.Bijective.of_comp_iff' G.bijective f
  rw [he] at hf
  exact hf.symm.trans hg

variable [T1Space Y]

/-- Actual relative groups of closed supports correspond under a partial homeomorphism. -/
def partialHomeomorphEquiv (p : ℕ) (hp : p ≠ 0) (e : OpenPartialHomeomorph X Y)
    {K : Set X} {L : Set Y} (hK : IsClosed K) (hL : IsClosed L)
    (hKs : K ⊆ e.source) (hLt : L ⊆ e.target)
    (hKL : ∀ x ∈ e.source, x ∈ K ↔ e x ∈ L) (n : ℕ) :
    Homology (ModuleCat.of ℤ (ZMod p)) K n ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ (ZMod p)) L n :=
  ((inclusionEquiv p hp e.source K e.open_source hK hKs n).symm.trans
    (homeomorphEquiv (ModuleCat.of ℤ (ZMod p)) e.toHomeomorphSourceTarget
      (K := supportIn e.source K) (L := supportIn e.target L)
      (fun x => hKL x x.property) n)).trans
    (inclusionEquiv p hp e.target L e.open_target hL hLt n)

/-- The original evaluations on both sides of a partial chart are simultaneously bijective. -/
theorem evaluate_bijective_iff_partialHomeomorph (p : ℕ) (hp : p ≠ 0)
    (e : OpenPartialHomeomorph X Y) {K : Set X} {L : Set Y}
    (hK : IsClosed K) (hL : IsClosed L) (hKs : K ⊆ e.source) (hLt : L ⊆ e.target)
    (hKL : ∀ x ∈ e.source, x ∈ K ↔ e x ∈ L) (x : X) (hx : x ∈ K) (n : ℕ) :
    Function.Bijective (evaluate (ModuleCat.of ℤ (ZMod p)) K x hx n) ↔
      Function.Bijective
        (evaluate (ModuleCat.of ℤ (ZMod p)) L (e x) ((hKL x (hKs hx)).mp hx) n) := by
  let u : e.source := ⟨x, hKs hx⟩
  let v := e.toHomeomorphSourceTarget u
  have h₁ := evaluate_bijective_iff_inclusion p hp e.source K e.open_source hK hKs u hx n
  have h₂ := evaluate_bijective_iff_homeomorph (ModuleCat.of ℤ (ZMod p))
    e.toHomeomorphSourceTarget (K := supportIn e.source K) (L := supportIn e.target L)
    (fun z => hKL z z.property) u hx n
  have h₃ := evaluate_bijective_iff_inclusion p hp e.target L e.open_target hL hLt v
    ((hKL x (hKs hx)).mp hx) n
  exact h₁.trans (h₂.symm.trans h₃.symm)

end NoExoticSixSphere.SupportedRelativeHomology

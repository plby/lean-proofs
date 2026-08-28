import Wikipedia.NoExoticSixSphere.SupportedEvaluationTransport

/-!
# Original evaluation maps under a partial homeomorphism

The support and local homology equivalences are composed from source
excision, the actual source-target homeomorphism, and target inclusion.
Their evaluation square commutes by the three corresponding original
squares, including the inverse source-excision map.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual bijection of support points induced by the partial homeomorphism. -/
def partialSupportPoints (e : OpenPartialHomeomorph X Y) {K : Set X} {L : Set Y}
    (hKs : K ⊆ e.source) (hLt : L ⊆ e.target)
    (hKL : ∀ x ∈ e.source, x ∈ K ↔ e x ∈ L) : K ≃ L where
  toFun x := ⟨e x, (hKL x (hKs x.property)).mp x.property⟩
  invFun y := ⟨e.symm y, (hKL (e.symm y) (e.map_target (hLt y.property))).mpr
    (by simpa only [e.right_inv (hLt y.property)] using y.property)⟩
  left_inv x := Subtype.ext (e.left_inv (hKs x.property))
  right_inv y := Subtype.ext (e.right_inv (hLt y.property))

variable [T1Space X] [T1Space Y]

/-- The original local homology equivalence through the actual source-target homeomorphism. -/
def localPartialHomeomorphEquiv (p : ℕ) (hp : p ≠ 0) (e : OpenPartialHomeomorph X Y)
    (x : X) (hx : x ∈ e.source) (n : ℕ) :
    RelativeCoefficients.ModHomology p ({x}ᶜ : Set X) n ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology p ({e x}ᶜ : Set Y) n :=
  ((RelativeCoefficients.modNeighborhoodEquiv p hp e.source e.open_source ⟨x, hx⟩ n).symm.trans
    (RelativeCoefficients.localHomeomorphEquiv (ModuleCat.of ℤ (ZMod p))
      e.toHomeomorphSourceTarget ⟨x, hx⟩ n)).trans
    (RelativeCoefficients.modNeighborhoodEquiv p hp e.target e.open_target
      (e.toHomeomorphSourceTarget ⟨x, hx⟩) n)

/-- The actual relative equivalence through a partial chart commutes with point evaluation. -/
theorem evaluate_partialHomeomorphEquiv (p : ℕ) (hp : p ≠ 0)
    (e : OpenPartialHomeomorph X Y) {K : Set X} {L : Set Y}
    (hK : IsClosed K) (hL : IsClosed L) (hKs : K ⊆ e.source) (hLt : L ⊆ e.target)
    (hKL : ∀ x ∈ e.source, x ∈ K ↔ e x ∈ L) (x : X) (hx : x ∈ K) (n : ℕ)
    (a : Homology (ModuleCat.of ℤ (ZMod p)) K n) :
    evaluate (ModuleCat.of ℤ (ZMod p)) L (e x) ((hKL x (hKs hx)).mp hx) n
        (partialHomeomorphEquiv p hp e hK hL hKs hLt hKL n a) =
      localPartialHomeomorphEquiv p hp e x (hKs hx) n
        (evaluate (ModuleCat.of ℤ (ZMod p)) K x hx n a) := by
  let A := ModuleCat.of ℤ (ZMod p)
  let u : e.source := ⟨x, hKs hx⟩
  let v := e.toHomeomorphSourceTarget u
  let F := inclusionEquiv p hp e.source K e.open_source hK hKs n
  let H := homeomorphEquiv A e.toHomeomorphSourceTarget
    (K := supportIn e.source K) (L := supportIn e.target L) (fun z => hKL z z.property) n
  let J := inclusionEquiv p hp e.target L e.open_target hL hLt n
  let G := RelativeCoefficients.modNeighborhoodEquiv p hp e.source e.open_source u n
  let I := RelativeCoefficients.localHomeomorphEquiv A e.toHomeomorphSourceTarget u n
  let T := RelativeCoefficients.modNeighborhoodEquiv p hp e.target e.open_target v n
  have hsource : evaluate A K x hx n (F (F.symm a)) =
      G (evaluate A (supportIn e.source K) u hx n (F.symm a)) :=
    LinearMap.congr_fun (evaluate_inclusion p e.source K u hx n) (F.symm a)
  rw [LinearEquiv.apply_symm_apply] at hsource
  have hs : evaluate A (supportIn e.source K) u hx n (F.symm a) =
      G.symm (evaluate A K x hx n a) := by
    apply G.injective
    rw [LinearEquiv.apply_symm_apply]
    exact hsource.symm
  have hh : evaluate A (supportIn e.target L) v ((hKL x (hKs hx)).mp hx) n
      (H (F.symm a)) = I (evaluate A (supportIn e.source K) u hx n (F.symm a)) :=
    LinearMap.congr_fun (evaluate_homeomorphEquiv A e.toHomeomorphSourceTarget
      (K := supportIn e.source K) (L := supportIn e.target L)
      (fun z => hKL z z.property) u hx n) (F.symm a)
  have ht : evaluate A L (e x) ((hKL x (hKs hx)).mp hx) n (J (H (F.symm a))) =
      T (evaluate A (supportIn e.target L) v ((hKL x (hKs hx)).mp hx) n (H (F.symm a))) :=
    LinearMap.congr_fun (evaluate_inclusion p e.target L v ((hKL x (hKs hx)).mp hx) n)
      (H (F.symm a))
  exact ht.trans ((congrArg T hh).trans (congrArg (fun z => T (I z)) hs))

end NoExoticSixSphere.SupportedRelativeHomology

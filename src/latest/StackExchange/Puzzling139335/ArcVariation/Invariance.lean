import StackExchange.Puzzling139335.ArcVariation.Invariance.Reversal

/-!
# Invariance of concrete finite-resolution variation

Every equality of variations below is obtained by an equality of the sets of
finite-chain scores. In particular, these equalities do not assume boundedness
of the scores, continuity of a parametrization, or positivity of the resolution.
-/

open Set

namespace Puzzling139335.ArcVariation

noncomputable section

variable {α β X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- Mapping the parameter list is the same as composing its evaluation map. -/
theorem chainScore_map (ε : ℝ) (f : β → X) (g : α → β) (xs : List α) :
    chainScore ε f (xs.map g) = chainScore ε (f ∘ g) xs := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b xs ih₁ ih₂ =>
      simp only [List.map_cons, chainScore, Function.comp_apply]
      exact congrArg (fun r => chord ε (f (g a)) (f (g b)) + r) (ih₂ b)

/-- Only the values at the actual finite chain matter to its score. -/
theorem chainScore_congr {ε : ℝ} {f g : α → X} {xs : List α}
    (hfg : ∀ t ∈ xs, f t = g t) : chainScore ε f xs = chainScore ε g xs := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b xs ih₁ ih₂ =>
      have ha : f a = g a := hfg a (by simp)
      have hb : f b = g b := hfg b (by simp)
      have htail : ∀ t ∈ b :: xs, f t = g t := by
        intro t ht
        exact hfg t (List.mem_cons_of_mem a ht)
      simp only [chainScore, ha, hb, ih₂ b htail]

/-- A codomain isometry preserves every truncated chord. -/
@[simp] theorem chord_comp_isometry {g : X → Y} (hg : Isometry g)
    (ε : ℝ) (x y : X) : chord ε (g x) (g y) = chord ε x y := by
  simp only [chord, hg.dist_eq]

/-- A codomain isometry preserves every finite-chain score. -/
theorem chainScore_comp_isometry {g : X → Y} (hg : Isometry g)
    (ε : ℝ) (f : α → X) (xs : List α) :
    chainScore ε (g ∘ f) xs = chainScore ε f xs := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b xs ih₁ ih₂ =>
      simp only [chainScore, Function.comp_apply, chord_comp_isometry hg, ih₂ b]

/-- A codomain isometry preserves the entire set of finite-chain scores. -/
theorem scoresOn_comp_isometry [LE α] {g : X → Y} (hg : Isometry g)
    (ε : ℝ) (f : α → X) (s : Set α) :
    scoresOn ε (g ∘ f) s = scoresOn ε f s := by
  ext r
  simp only [scoresOn, mem_ofPred_eq, chainScore_comp_isometry hg]

/-- Codomain isometries preserve truncated variation, with no finiteness premise. -/
theorem variationOn_comp_isometry [LE α] {g : X → Y} (hg : Isometry g)
    (ε : ℝ) (f : α → X) (s : Set α) :
    variationOn ε (g ∘ f) s = variationOn ε f s := by
  unfold variationOn
  rw [scoresOn_comp_isometry hg]

/-- Maps that agree on the parameter set have the same attainable scores. -/
theorem scoresOn_congr [LE α] {ε : ℝ} {f g : α → X} {s : Set α}
    (hfg : EqOn f g s) : scoresOn ε f s = scoresOn ε g s := by
  ext r
  constructor
  · rintro ⟨xs, hxs, rfl⟩
    exact ⟨xs, hxs, chainScore_congr (fun t ht => hfg (hxs.2 t ht))⟩
  · rintro ⟨xs, hxs, rfl⟩
    exact ⟨xs, hxs, chainScore_congr (fun t ht => (hfg (hxs.2 t ht)).symm)⟩

theorem variationOn_congr [LE α] {ε : ℝ} {f g : α → X} {s : Set α}
    (hfg : EqOn f g s) : variationOn ε f s = variationOn ε g s := by
  unfold variationOn
  rw [scoresOn_congr hfg]

/-- A monotone map sends a concrete chain to a concrete chain. -/
theorem IsChainOn.map [Preorder α] [Preorder β] {s : Set α} {t : Set β} {xs : List α}
    (hxs : IsChainOn s xs) {g : α → β} (hg : MonotoneOn g s)
    (hmaps : MapsTo g s t) : IsChainOn t (xs.map g) := by
  constructor
  · apply List.pairwise_map.mpr
    exact hxs.1.imp_of_mem (fun ha hb hab => hg (hxs.2 _ ha) (hxs.2 _ hb) hab)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hmaps (hxs.2 x hx)

/-- A monotone parameter map realizes each source score as a target score. -/
theorem scoresOn_comp_subset [Preorder α] [Preorder β] (ε : ℝ) (f : β → X)
    {g : α → β} {s : Set α} {t : Set β} (hg : MonotoneOn g s)
    (hmaps : MapsTo g s t) : scoresOn ε (f ∘ g) s ⊆ scoresOn ε f t := by
  rintro r ⟨xs, hxs, rfl⟩
  exact ⟨xs.map g, hxs.map hg hmaps, (chainScore_map ε f g xs).symm⟩

/-- A monotone parameter map with a monotone right inverse on the target set
preserves exactly the attainable scores. No global bijectivity is required. -/
theorem scoresOn_comp_eq_of_rightInvOn [Preorder α] [Preorder β] (ε : ℝ) (f : β → X)
    {g : α → β} {h : β → α} {s : Set α} {t : Set β}
    (hg : MonotoneOn g s) (hh : MonotoneOn h t)
    (hg_maps : MapsTo g s t) (hh_maps : MapsTo h t s)
    (hgh : RightInvOn h g t) : scoresOn ε (f ∘ g) s = scoresOn ε f t := by
  apply Set.Subset.antisymm (scoresOn_comp_subset ε f hg hg_maps)
  rintro r ⟨xs, hxs, rfl⟩
  refine ⟨xs.map h, hxs.map hh hh_maps, ?_⟩
  rw [chainScore_map]
  apply chainScore_congr
  intro u hu
  simp only [Function.comp_apply, hgh (hxs.2 u hu)]

/-- Variation is invariant under monotone parameter changes with a monotone
right inverse on the parameter sets. -/
theorem variationOn_comp_eq_of_rightInvOn [Preorder α] [Preorder β] (ε : ℝ) (f : β → X)
    {g : α → β} {h : β → α} {s : Set α} {t : Set β}
    (hg : MonotoneOn g s) (hh : MonotoneOn h t)
    (hg_maps : MapsTo g s t) (hh_maps : MapsTo h t s)
    (hgh : RightInvOn h g t) : variationOn ε (f ∘ g) s = variationOn ε f t := by
  unfold variationOn
  rw [scoresOn_comp_eq_of_rightInvOn ε f hg hh hg_maps hh_maps hgh]

/-- On a linear order, a monotone surjection admits a monotone choice of
preimages. Mapping chains by that right inverse proves equality of score sets. -/
theorem scoresOn_comp_eq_of_monotoneOn_surjOn [LinearOrder α] [PartialOrder β]
    [Nonempty α] (ε : ℝ) (f : β → X) {g : α → β} {s : Set α} {t : Set β}
    (hg : MonotoneOn g s) (hmaps : MapsTo g s t) (hsurj : SurjOn g s t) :
    scoresOn ε (f ∘ g) s = scoresOn ε f t := by
  let h : β → α := Function.invFunOn g s
  have hh_maps : MapsTo h t s := hsurj.mapsTo_invFunOn
  have hgh : RightInvOn h g t := hsurj.rightInvOn_invFunOn
  have hh : MonotoneOn h t := by
    intro a ha b hb hab
    by_cases heq : a = b
    · subst b
      exact le_rfl
    · apply le_of_not_gt
      intro hba
      have hba' := hg (hh_maps hb) (hh_maps ha) hba.le
      rw [hgh hb, hgh ha] at hba'
      exact heq (le_antisymm hab hba')
  exact scoresOn_comp_eq_of_rightInvOn ε f hg hh hmaps hh_maps hgh

theorem variationOn_comp_eq_of_monotoneOn_surjOn [LinearOrder α] [PartialOrder β]
    [Nonempty α] (ε : ℝ) (f : β → X) {g : α → β} {s : Set α} {t : Set β}
    (hg : MonotoneOn g s) (hmaps : MapsTo g s t) (hsurj : SurjOn g s t) :
    variationOn ε (f ∘ g) s = variationOn ε f t := by
  unfold variationOn
  rw [scoresOn_comp_eq_of_monotoneOn_surjOn ε f hg hmaps hsurj]

/-- An order isomorphism transports exactly the concrete chains in a set. -/
theorem scoresOn_comp_orderIso [Preorder α] [Preorder β]
    (ε : ℝ) (f : β → X) (e : α ≃o β) (s : Set α) :
    scoresOn ε (f ∘ e) s = scoresOn ε f (e '' s) := by
  apply scoresOn_comp_eq_of_rightInvOn ε f (h := e.symm) (e.monotone.monotoneOn s)
    (e.symm.monotone.monotoneOn (e '' s)) (mapsTo_image e s)
  · rintro y ⟨x, hx, rfl⟩
    simpa only [e.symm_apply_apply] using hx
  · intro y hy
    exact e.apply_symm_apply y

theorem variationOn_comp_orderIso [Preorder α] [Preorder β]
    (ε : ℝ) (f : β → X) (e : α ≃o β) (s : Set α) :
    variationOn ε (f ∘ e) s = variationOn ε f (e '' s) := by
  unfold variationOn
  rw [scoresOn_comp_orderIso]

end

end Puzzling139335.ArcVariation

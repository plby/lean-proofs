import StackExchange.Puzzling139335.LoopVariation.Defs
import Mathlib.Data.List.Rotate

/-!
# Algebraic invariance of cyclic finite-resolution scores

The concrete cyclic score is preserved by changing its starting vertex,
reversing its list, or applying an isometry to the values. Monotone and
antitone parameter maps transport the actual admissible finite lists; when
they are surjective they give equality of the attainable score sets.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

variable {α β X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

private theorem chainScore_append_pair (ε : ℝ) (f : α → X)
    (xs : List α) (a b : α) :
    chainScore ε f (xs ++ [a, b]) =
      chainScore ε f (xs ++ [a]) + chord ε (f a) (f b) := by
  induction xs using List.twoStepInduction with
  | nil => simp [chainScore]
  | singleton c => simp [chainScore]
  | cons_cons c d xs ih₁ ih₂ =>
      simpa [chainScore, add_assoc] using
        congrArg (fun r => chord ε (f c) (f d) + r) (ih₂ d)

/-- Moving the starting vertex to the end leaves the cycle unchanged. -/
theorem cycleScore_cons_rotate (ε : ℝ) (f : α → X) (x : α) (xs : List α) :
    cycleScore ε f (x :: xs) = cycleScore ε f (xs ++ [x]) := by
  cases xs with
  | nil => rfl
  | cons y ys =>
      simpa only [cycleScore, List.cons_append, List.nil_append, List.append_assoc,
        chainScore, add_comm] using (chainScore_append_pair ε f (y :: ys) x y).symm

/-- Starting a cyclic list at another block does not change its score. -/
theorem cycleScore_append_comm (ε : ℝ) (f : α → X) (xs ys : List α) :
    cycleScore ε f (xs ++ ys) = cycleScore ε f (ys ++ xs) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
      calc
        cycleScore ε f ((x :: xs) ++ ys) =
            cycleScore ε f ((xs ++ ys) ++ [x]) := by
          simpa only [List.cons_append] using cycleScore_cons_rotate ε f x (xs ++ ys)
        _ = cycleScore ε f (xs ++ (ys ++ [x])) := by rw [List.append_assoc]
        _ = cycleScore ε f ((ys ++ [x]) ++ xs) := ih (ys ++ [x])
        _ = cycleScore ε f (ys ++ (x :: xs)) := by
          simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Reversing the orientation of a cyclic list preserves each unoriented chord. -/
theorem cycleScore_reverse (ε : ℝ) (f : α → X) (xs : List α) :
    cycleScore ε f xs.reverse = cycleScore ε f xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      rw [List.reverse_cons, ← cycleScore_cons_rotate]
      simp only [cycleScore]
      simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.cons_append, List.nil_append] using
        chainScore_reverse ε f ((x :: xs) ++ [x])

/-- Every cyclic rotation of a list has the same cyclic score. -/
theorem cycleScore_rotate (ε : ℝ) (f : α → X) (xs : List α) (n : ℕ) :
    cycleScore ε f (xs.rotate n) = cycleScore ε f xs := by
  rw [List.rotate_eq_drop_append_take_mod, cycleScore_append_comm,
    List.take_append_drop]

/-- Mapping a cyclic parameter list composes its evaluation map. -/
theorem cycleScore_map (ε : ℝ) (f : β → X) (g : α → β) (xs : List α) :
    cycleScore ε f (xs.map g) = cycleScore ε (f ∘ g) xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      simpa only [List.map_cons, List.map_nil, List.map_append, cycleScore] using
        chainScore_map ε f g ((x :: xs) ++ [x])

/-- Only the values at vertices of the actual list determine a cyclic score. -/
theorem cycleScore_congr {ε : ℝ} {f g : α → X} {xs : List α}
    (hfg : ∀ t ∈ xs, f t = g t) : cycleScore ε f xs = cycleScore ε g xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      apply chainScore_congr
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hfg t ht
      · exact hfg t (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp ht)))

/-- Codomain isometries preserve every cyclic score, at every resolution. -/
theorem cycleScore_comp_isometry {g : X → Y} (hg : Isometry g)
    (ε : ℝ) (f : α → X) (xs : List α) :
    cycleScore ε (g ∘ f) xs = cycleScore ε f xs := by
  cases xs with
  | nil => rfl
  | cons x xs => exact chainScore_comp_isometry hg ε f ((x :: xs) ++ [x])

/-- A codomain isometry preserves the set of attainable cyclic scores. -/
theorem cycleScoresOn_comp_isometry [LE α] {g : X → Y} (hg : Isometry g)
    (ε : ℝ) (f : α → X) (s : Set α) :
    cycleScoresOn ε (g ∘ f) s = cycleScoresOn ε f s := by
  ext r
  simp only [cycleScoresOn, mem_ofPred_eq, cycleScore_comp_isometry hg]

/-- Codomain isometries preserve cyclic variation without a finiteness premise. -/
theorem loopVariationOn_comp_isometry [LE α] {g : X → Y} (hg : Isometry g)
    (ε : ℝ) (f : α → X) (s : Set α) :
    loopVariationOn ε (g ∘ f) s = loopVariationOn ε f s := by
  unfold loopVariationOn
  rw [cycleScoresOn_comp_isometry hg]

/-- Agreement on the parameter set gives equality of cyclic score sets. -/
theorem cycleScoresOn_congr [LE α] {ε : ℝ} {f g : α → X} {s : Set α}
    (hfg : EqOn f g s) : cycleScoresOn ε f s = cycleScoresOn ε g s := by
  ext r
  constructor
  · rintro ⟨xs, hxs, rfl⟩
    exact ⟨xs, hxs, cycleScore_congr (fun t ht => hfg (hxs.2 t ht))⟩
  · rintro ⟨xs, hxs, rfl⟩
    exact ⟨xs, hxs, cycleScore_congr (fun t ht => (hfg (hxs.2 t ht)).symm)⟩

theorem loopVariationOn_congr [LE α] {ε : ℝ} {f g : α → X} {s : Set α}
    (hfg : EqOn f g s) : loopVariationOn ε f s = loopVariationOn ε g s := by
  unfold loopVariationOn
  rw [cycleScoresOn_congr hfg]

/-- A monotone map transports every source cyclic score to a target score. -/
theorem cycleScoresOn_comp_subset [Preorder α] [Preorder β]
    (ε : ℝ) (f : β → X) {g : α → β} {s : Set α} {t : Set β}
    (hg : MonotoneOn g s) (hmaps : MapsTo g s t) :
    cycleScoresOn ε (f ∘ g) s ⊆ cycleScoresOn ε f t := by
  rintro r ⟨xs, hxs, rfl⟩
  exact ⟨xs.map g, hxs.map hg hmaps, (cycleScore_map ε f g xs).symm⟩

/-- A monotone right inverse recovers every target cyclic score. -/
theorem cycleScoresOn_comp_eq_of_rightInvOn [Preorder α] [Preorder β]
    (ε : ℝ) (f : β → X) {g : α → β} {h : β → α} {s : Set α} {t : Set β}
    (hg : MonotoneOn g s) (hh : MonotoneOn h t)
    (hg_maps : MapsTo g s t) (hh_maps : MapsTo h t s)
    (hgh : RightInvOn h g t) : cycleScoresOn ε (f ∘ g) s = cycleScoresOn ε f t := by
  apply Set.Subset.antisymm (cycleScoresOn_comp_subset ε f hg hg_maps)
  rintro r ⟨xs, hxs, rfl⟩
  refine ⟨xs.map h, hxs.map hh hh_maps, ?_⟩
  rw [cycleScore_map]
  apply cycleScore_congr
  intro u hu
  simp only [Function.comp_apply, hgh (hxs.2 u hu)]

theorem loopVariationOn_comp_eq_of_rightInvOn [Preorder α] [Preorder β]
    (ε : ℝ) (f : β → X) {g : α → β} {h : β → α} {s : Set α} {t : Set β}
    (hg : MonotoneOn g s) (hh : MonotoneOn h t)
    (hg_maps : MapsTo g s t) (hh_maps : MapsTo h t s)
    (hgh : RightInvOn h g t) : loopVariationOn ε (f ∘ g) s = loopVariationOn ε f t := by
  unfold loopVariationOn
  rw [cycleScoresOn_comp_eq_of_rightInvOn ε f hg hh hg_maps hh_maps hgh]

/-- A monotone surjection from a linear order has a monotone choice of preimages. -/
theorem cycleScoresOn_comp_eq_of_monotoneOn_surjOn [LinearOrder α] [PartialOrder β]
    [Nonempty α] (ε : ℝ) (f : β → X) {g : α → β} {s : Set α} {t : Set β}
    (hg : MonotoneOn g s) (hmaps : MapsTo g s t) (hsurj : SurjOn g s t) :
    cycleScoresOn ε (f ∘ g) s = cycleScoresOn ε f t := by
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
  exact cycleScoresOn_comp_eq_of_rightInvOn ε f hg hh hmaps hh_maps hgh

theorem loopVariationOn_comp_eq_of_monotoneOn_surjOn [LinearOrder α] [PartialOrder β]
    [Nonempty α] (ε : ℝ) (f : β → X) {g : α → β} {s : Set α} {t : Set β}
    (hg : MonotoneOn g s) (hmaps : MapsTo g s t) (hsurj : SurjOn g s t) :
    loopVariationOn ε (f ∘ g) s = loopVariationOn ε f t := by
  unfold loopVariationOn
  rw [cycleScoresOn_comp_eq_of_monotoneOn_surjOn ε f hg hmaps hsurj]

/-- Order isomorphisms preserve exactly the admissible cyclic scores. -/
theorem cycleScoresOn_comp_orderIso [Preorder α] [Preorder β]
    (ε : ℝ) (f : β → X) (e : α ≃o β) (s : Set α) :
    cycleScoresOn ε (f ∘ e) s = cycleScoresOn ε f (e '' s) := by
  apply cycleScoresOn_comp_eq_of_rightInvOn ε f (h := e.symm) (e.monotone.monotoneOn s)
    (e.symm.monotone.monotoneOn (e '' s)) (mapsTo_image e s)
  · rintro y ⟨x, hx, rfl⟩
    simpa only [e.symm_apply_apply] using hx
  · intro y hy
    exact e.apply_symm_apply y

theorem loopVariationOn_comp_orderIso [Preorder α] [Preorder β]
    (ε : ℝ) (f : β → X) (e : α ≃o β) (s : Set α) :
    loopVariationOn ε (f ∘ e) s = loopVariationOn ε f (e '' s) := by
  unfold loopVariationOn
  rw [cycleScoresOn_comp_orderIso]

/-- A decreasing parameter map gives an increasing chain after list reversal. -/
theorem isChainOn_map_reverse_of_antitoneOn [Preorder α] [Preorder β]
    {s : Set α} {t : Set β} {xs : List α} (hxs : IsChainOn s xs)
    {g : α → β} (hg : AntitoneOn g s) (hmaps : MapsTo g s t) :
    IsChainOn t (xs.map g).reverse := by
  constructor
  · rw [List.pairwise_reverse, List.pairwise_map]
    exact hxs.1.imp_of_mem (fun ha hb hab => hg (hxs.2 _ ha) (hxs.2 _ hb) hab)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hy)
    exact hmaps (hxs.2 x hx)

/-- Decreasing parameter maps also transport all concrete cyclic scores. -/
theorem cycleScoresOn_comp_subset_of_antitoneOn [Preorder α] [Preorder β]
    (ε : ℝ) (f : β → X) {g : α → β} {s : Set α} {t : Set β}
    (hg : AntitoneOn g s) (hmaps : MapsTo g s t) :
    cycleScoresOn ε (f ∘ g) s ⊆ cycleScoresOn ε f t := by
  rintro r ⟨xs, hxs, rfl⟩
  refine ⟨(xs.map g).reverse, isChainOn_map_reverse_of_antitoneOn hxs hg hmaps, ?_⟩
  rw [cycleScore_reverse, cycleScore_map]

/-- A decreasing parameter map with a decreasing right inverse preserves the
entire set of cyclic scores. -/
theorem cycleScoresOn_comp_eq_of_antitoneOn_rightInvOn [Preorder α] [Preorder β]
    (ε : ℝ) (f : β → X) {g : α → β} {h : β → α} {s : Set α} {t : Set β}
    (hg : AntitoneOn g s) (hh : AntitoneOn h t)
    (hg_maps : MapsTo g s t) (hh_maps : MapsTo h t s)
    (hgh : RightInvOn h g t) : cycleScoresOn ε (f ∘ g) s = cycleScoresOn ε f t := by
  apply Set.Subset.antisymm (cycleScoresOn_comp_subset_of_antitoneOn ε f hg hg_maps)
  rintro r ⟨xs, hxs, rfl⟩
  refine ⟨(xs.map h).reverse, isChainOn_map_reverse_of_antitoneOn hxs hh hh_maps, ?_⟩
  rw [cycleScore_reverse, cycleScore_map]
  apply cycleScore_congr
  intro u hu
  simp only [Function.comp_apply, hgh (hxs.2 u hu)]

theorem loopVariationOn_comp_eq_of_antitoneOn_rightInvOn [Preorder α] [Preorder β]
    (ε : ℝ) (f : β → X) {g : α → β} {h : β → α} {s : Set α} {t : Set β}
    (hg : AntitoneOn g s) (hh : AntitoneOn h t)
    (hg_maps : MapsTo g s t) (hh_maps : MapsTo h t s)
    (hgh : RightInvOn h g t) : loopVariationOn ε (f ∘ g) s = loopVariationOn ε f t := by
  unfold loopVariationOn
  rw [cycleScoresOn_comp_eq_of_antitoneOn_rightInvOn ε f hg hh hg_maps hh_maps hgh]

/-- A decreasing surjection from a linear order admits a decreasing choice of
preimages, giving equality of all cyclic score sets. -/
theorem cycleScoresOn_comp_eq_of_antitoneOn_surjOn [LinearOrder α] [PartialOrder β]
    [Nonempty α] (ε : ℝ) (f : β → X) {g : α → β} {s : Set α} {t : Set β}
    (hg : AntitoneOn g s) (hmaps : MapsTo g s t) (hsurj : SurjOn g s t) :
    cycleScoresOn ε (f ∘ g) s = cycleScoresOn ε f t := by
  let h : β → α := Function.invFunOn g s
  have hh_maps : MapsTo h t s := hsurj.mapsTo_invFunOn
  have hgh : RightInvOn h g t := hsurj.rightInvOn_invFunOn
  have hh : AntitoneOn h t := by
    intro a ha b hb hab
    by_cases heq : a = b
    · subst b
      exact le_rfl
    · apply le_of_not_gt
      intro hab'
      have hba := hg (hh_maps ha) (hh_maps hb) hab'.le
      rw [hgh ha, hgh hb] at hba
      exact heq (le_antisymm hab hba)
  exact cycleScoresOn_comp_eq_of_antitoneOn_rightInvOn ε f hg hh hmaps hh_maps hgh

theorem loopVariationOn_comp_eq_of_antitoneOn_surjOn [LinearOrder α] [PartialOrder β]
    [Nonempty α] (ε : ℝ) (f : β → X) {g : α → β} {s : Set α} {t : Set β}
    (hg : AntitoneOn g s) (hmaps : MapsTo g s t) (hsurj : SurjOn g s t) :
    loopVariationOn ε (f ∘ g) s = loopVariationOn ε f t := by
  unfold loopVariationOn
  rw [cycleScoresOn_comp_eq_of_antitoneOn_surjOn ε f hg hmaps hsurj]

/-- Reversing a real parameter interval preserves every attainable cyclic score. -/
theorem cycleScoresOn_reflect_Icc (ε : ℝ) (f : ℝ → X) (a b : ℝ) :
    cycleScoresOn ε (fun u => f (a + b - u)) (Icc a b) =
      cycleScoresOn ε f (Icc a b) := by
  have hmaps : MapsTo (fun u : ℝ => a + b - u) (Icc a b) (Icc a b) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hanti : AntitoneOn (fun u : ℝ => a + b - u) (Icc a b) := by
    intro u hu v hv huv
    linarith
  have hsurj : SurjOn (fun u : ℝ => a + b - u) (Icc a b) (Icc a b) := by
    intro u hu
    refine ⟨a + b - u, hmaps hu, ?_⟩
    dsimp
    ring
  exact cycleScoresOn_comp_eq_of_antitoneOn_surjOn ε f hanti hmaps hsurj

theorem loopVariationOn_reflect_Icc (ε : ℝ) (f : ℝ → X) (a b : ℝ) :
    loopVariationOn ε (fun u => f (a + b - u)) (Icc a b) =
      loopVariationOn ε f (Icc a b) := by
  unfold loopVariationOn
  rw [cycleScoresOn_reflect_Icc]

/-- A continuous injective real interval parameter map is monotone or antitone,
so a surjective such map preserves the actual cyclic score sets. -/
theorem cycleScoresOn_comp_eq_of_continuousOn_injOn_Icc (ε : ℝ) (f : ℝ → X)
    {g : ℝ → ℝ} {a b : ℝ} {t : Set ℝ}
    (hg_cont : ContinuousOn g (Icc a b)) (hg_inj : InjOn g (Icc a b))
    (hmaps : MapsTo g (Icc a b) t) (hsurj : SurjOn g (Icc a b) t) :
    cycleScoresOn ε (f ∘ g) (Icc a b) = cycleScoresOn ε f t := by
  by_cases hab : a ≤ b
  · rcases hg_cont.strictMonoOn_of_injOn_Icc' hab hg_inj with hmono | hanti
    · exact cycleScoresOn_comp_eq_of_monotoneOn_surjOn ε f hmono.monotoneOn hmaps hsurj
    · exact cycleScoresOn_comp_eq_of_antitoneOn_surjOn ε f hanti.antitoneOn hmaps hsurj
  · have hmono : MonotoneOn g (Icc a b) := by
      intro u hu v hv huv
      exact (hab (hu.1.trans hu.2)).elim
    exact cycleScoresOn_comp_eq_of_monotoneOn_surjOn ε f hmono hmaps hsurj

theorem loopVariationOn_comp_eq_of_continuousOn_injOn_Icc (ε : ℝ) (f : ℝ → X)
    {g : ℝ → ℝ} {a b : ℝ} {t : Set ℝ}
    (hg_cont : ContinuousOn g (Icc a b)) (hg_inj : InjOn g (Icc a b))
    (hmaps : MapsTo g (Icc a b) t) (hsurj : SurjOn g (Icc a b) t) :
    loopVariationOn ε (f ∘ g) (Icc a b) = loopVariationOn ε f t := by
  unfold loopVariationOn
  rw [cycleScoresOn_comp_eq_of_continuousOn_injOn_Icc ε f hg_cont hg_inj hmaps hsurj]

end

end Puzzling139335.LoopVariation

import Wikipedia.NoExoticSixSphere.AnnulusPerturbationCutoff

/-!
# The compact closure of the actual annulus double points

The closure is taken in the original Euclidean source product. It is
compact, and continuity on the closed annulus suffices for equality of
the two limiting images. Injectivity of the union of both protected
collars puts at least one coordinate in the closed middle core. Separation
of interior and boundary images then excludes both boundary spheres.
-/

open Set Function Metric

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization

def openDomain (p : ℕ) : Set (Vector (p + 1)) := {x | 1 < ‖x‖ ∧ ‖x‖ < 2}

theorem isOpen_openDomain (p : ℕ) : IsOpen (openDomain p) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem openDomain_subset_domain (p : ℕ) : openDomain p ⊆ domain p :=
  fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩

theorem boundary_of_not_mem_openDomain {p : ℕ} {x : Vector (p + 1)}
    (hx : x ∈ domain p) (hnot : x ∉ openDomain p) : ‖x‖ = 1 ∨ ‖x‖ = 2 := by
  rcases lt_or_eq_of_le hx.1 with hl | hl
  · exact Or.inr (le_antisymm hx.2 (le_of_not_gt (fun hr ↦ hnot ⟨hl, hr⟩)))
  · exact Or.inl hl.symm

end NoExoticSixSphere.SphereAnnulus

namespace NoExoticSixSphere.AnnulusDoublePoints

open GLOrthonormalization SphereAnnulus

variable {p : ℕ} {Y : Type*}

def points (g : Vector (p + 1) → Y) : Set (Vector (p + 1) × Vector (p + 1)) :=
  {v | v.1 ∈ openDomain p ∧ v.2 ∈ openDomain p ∧ v.1 ≠ v.2 ∧ g v.1 = g v.2}

theorem closure_subset_domain (g : Vector (p + 1) → Y) :
    closure (points g) ⊆ domain p ×ˢ domain p := by
  apply closure_minimal _ ((isClosed_domain p).prod (isClosed_domain p))
  intro v hv
  exact ⟨openDomain_subset_domain p hv.1, openDomain_subset_domain p hv.2.1⟩

theorem isCompact_closure (g : Vector (p + 1) → Y) : IsCompact (closure (points g)) :=
  ((isCompact_domain p).prod (isCompact_domain p)).of_isClosed_subset
    isClosed_closure (closure_subset_domain g)

theorem closure_subset_one_in_core (g : Vector (p + 1) → Y) (r₀ r₁ : ℝ)
    (hi : InjOn g {x | x ∈ domain p ∧ (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖)}) :
    closure (points g) ⊆ {v | v.1 ∈ closedCore p r₀ r₁ ∨ v.2 ∈ closedCore p r₀ r₁} := by
  have hc : IsClosed {v : Vector (p + 1) × Vector (p + 1) |
      v.1 ∈ closedCore p r₀ r₁ ∨ v.2 ∈ closedCore p r₀ r₁} :=
    ((isCompact_closedCore p r₀ r₁).isClosed.preimage continuous_fst).union
      ((isCompact_closedCore p r₀ r₁).isClosed.preimage continuous_snd)
  apply closure_minimal _ hc
  intro v hv
  by_contra hnot
  have hend (x : Vector (p + 1)) (hx : x ∉ closedCore p r₀ r₁) :
      ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ := by
    change ¬ (r₀ ≤ ‖x‖ ∧ ‖x‖ ≤ r₁) at hx
    exact (not_and_or.mp hx).imp (fun h ↦ (lt_of_not_ge h).le)
      (fun h ↦ (lt_of_not_ge h).le)
  exact hv.2.2.1 (hi
    ⟨openDomain_subset_domain p hv.1, hend v.1 (fun h ↦ hnot (Or.inl h))⟩
    ⟨openDomain_subset_domain p hv.2.1, hend v.2 (fun h ↦ hnot (Or.inr h))⟩ hv.2.2.2)

variable [TopologicalSpace Y] [T2Space Y]

theorem closure_equal_image (g : Vector (p + 1) → Y) (hg : ContinuousOn g (domain p))
    {v : Vector (p + 1) × Vector (p + 1)} (hv : v ∈ closure (points g)) :
    g v.1 = g v.2 := by
  have hleft : ContinuousOn (fun w : Vector (p + 1) × Vector (p + 1) ↦ g w.1)
      (domain p ×ˢ domain p) := hg.comp continuous_fst.continuousOn (fun _ hw ↦ hw.1)
  have hright : ContinuousOn (fun w : Vector (p + 1) × Vector (p + 1) ↦ g w.2)
      (domain p ×ˢ domain p) := hg.comp continuous_snd.continuousOn (fun _ hw ↦ hw.2)
  have hc : IsClosed ((domain p ×ˢ domain p) ∩
      {w : Vector (p + 1) × Vector (p + 1) | g w.1 = g w.2}) :=
    (hleft.prodMk hright).preimage_isClosed_of_isClosed
      ((isClosed_domain p).prod (isClosed_domain p))
      (isClosed_eq continuous_fst continuous_snd)
  have hs : points g ⊆ (domain p ×ˢ domain p) ∩
      {w : Vector (p + 1) × Vector (p + 1) | g w.1 = g w.2} := fun w hw ↦
    ⟨⟨openDomain_subset_domain p hw.1, openDomain_subset_domain p hw.2.1⟩, hw.2.2.2⟩
  exact (closure_minimal hs hc hv).2

theorem closure_subset_interior (g : Vector (p + 1) → Y) (hg : ContinuousOn g (domain p))
    (r₀ r₁ : ℝ) (hr₀ : 1 < r₀) (hr₁ : r₁ < 2)
    (hi : InjOn g {x | x ∈ domain p ∧ (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖)})
    (hsep : ∀ x ∈ openDomain p, ∀ y, ‖y‖ = 1 ∨ ‖y‖ = 2 → g x ≠ g y) :
    closure (points g) ⊆ openDomain p ×ˢ openDomain p := by
  intro v hv
  have hK := closure_subset_domain g hv
  have heq := closure_equal_image g hg hv
  have hcore := closure_subset_one_in_core g r₀ r₁ hi hv
  have hsub : closedCore p r₀ r₁ ⊆ openDomain p :=
    fun _ hx ↦ ⟨hr₀.trans_le hx.1, hx.2.trans_lt hr₁⟩
  constructor
  · by_contra hnot
    have hb := boundary_of_not_mem_openDomain hK.1 hnot
    rcases hcore with hx | hy
    · exact hnot (hsub hx)
    · exact hsep v.2 (hsub hy) v.1 hb heq.symm
  · by_contra hnot
    have hb := boundary_of_not_mem_openDomain hK.2 hnot
    rcases hcore with hx | hy
    · exact hsep v.1 (hsub hx) v.2 hb heq
    · exact hnot (hsub hy)

end NoExoticSixSphere.AnnulusDoublePoints

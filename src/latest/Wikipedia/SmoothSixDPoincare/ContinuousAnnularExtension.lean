import Wikipedia.SmoothSixDPoincare.AnnularRadialMaps

/-!
# A continuous annular extension fixed on the whole annulus

Disk extensions of the inner and outer boundary maps glue to the given
continuous annular map. The result is defined on the whole normed space,
agrees exactly throughout the annulus, and is constant outside radius `2*b`.
-/

noncomputable section

open Set Function Metric Topology

namespace Wikipedia.SmoothSixDPoincare.AnnularExtension

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]

theorem disk_extension_on_radius {a : ℝ} (ha : 0 < a) {g : E → M}
    (F : C(closedBall (0 : E) 1, M))
    (hF : ∀ v : sphere (0 : E) 1, F ⟨v, sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    {x : E} (hx : ‖x‖ = a) : F (innerDisk ha x) = g x := by
  let v : sphere (0 : E) 1 := ⟨unitClamp a x, by
    rw [mem_sphere_zero_iff_norm, norm_unitClamp ha, hx, max_self, div_self ha.ne']⟩
  have heq : innerDisk ha x = ⟨(v : E), sphere_subset_closedBall v.property⟩ := rfl
  rw [heq, hF]
  change g (clamp a x) = g x
  rw [clamp_of_norm_le ha hx.le]

theorem exterior_extension_on_radius {a : ℝ} (ha : 0 < a) {g : E → M}
    (F : C(closedBall (0 : E) 1, M))
    (hF : ∀ v : sphere (0 : E) 1, F ⟨v, sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    {x : E} (hx : ‖x‖ = a) : F (exteriorDisk ha x) = g x := by
  have heq : exteriorDisk ha x = innerDisk ha x :=
    Subtype.ext (exteriorVector_on_sphere ha hx)
  rw [heq]
  exact disk_extension_on_radius ha F hF hx

/-- Two actual disk extensions give a global annulus-preserving extension with constant exterior. -/
theorem exists_continuous_annular_extension {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {g : E → M} (hg : ContinuousOn g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b})
    (F₀ F₁ : C(closedBall (0 : E) 1, M))
    (hF₀ : ∀ v : sphere (0 : E) 1,
      F₀ ⟨v, sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    (hF₁ : ∀ v : sphere (0 : E) 1,
      F₁ ⟨v, sphere_subset_closedBall v.property⟩ = g (b • (v : E))) :
    ∃ G : C(E, M), EqOn G g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ∧
      ∀ x, 2 * b ≤ ‖x‖ → G x = F₁ ⟨0, mem_closedBall_self zero_le_one⟩ := by
  classical
  have hb : 0 < b := ha.trans hab
  let inner : C(E, M) := F₀.comp (innerDisk ha)
  let outer : C(E, M) := F₁.comp (exteriorDisk hb)
  let middle : E → M := g ∘ clamp b
  have houtside : closure (closedBall (0 : E) a)ᶜ ⊆ {x : E | a ≤ ‖x‖} := by
    apply closure_minimal
    · intro x hx
      have hn : ¬‖x‖ ≤ a := by simpa only [mem_compl_iff, mem_closedBall_zero_iff] using hx
      exact le_of_lt (lt_of_not_ge hn)
    · exact isClosed_le continuous_const continuous_norm
  have hmiddle : ContinuousOn middle (closure (closedBall (0 : E) a)ᶜ) :=
    hg.comp (continuous_clamp hb).continuousOn
      (fun _ hx => clamp_mem_annulus hb hab.le (houtside hx))
  have hjoin₀ : ∀ x ∈ frontier (closedBall (0 : E) a), inner x = middle x := by
    intro x hx
    rw [frontier_closedBall _ ha.ne'] at hx
    have hnorm : ‖x‖ = a := mem_sphere_zero_iff_norm.mp hx
    change F₀ (innerDisk ha x) = g (clamp b x)
    rw [disk_extension_on_radius ha F₀ hF₀ hnorm, clamp_of_norm_le hb (hnorm.le.trans hab.le)]
  let G₀ : E → M := (closedBall (0 : E) a).piecewise inner middle
  have hG₀ : Continuous G₀ := continuous_piecewise hjoin₀ inner.continuous.continuousOn hmiddle
  have hG₀eq : EqOn G₀ g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
    intro x hx
    by_cases hxa : x ∈ closedBall (0 : E) a
    · have hnorm : ‖x‖ = a := le_antisymm (mem_closedBall_zero_iff.mp hxa) hx.1
      change ((closedBall (0 : E) a).piecewise inner middle) x = g x
      rw [piecewise_eq_of_mem _ _ _ hxa]
      exact disk_extension_on_radius ha F₀ hF₀ hnorm
    · change ((closedBall (0 : E) a).piecewise inner middle) x = g x
      rw [piecewise_eq_of_notMem _ _ _ hxa]
      change g (clamp b x) = g x
      rw [clamp_of_norm_le hb hx.2]
  have hjoin₁ : ∀ x ∈ frontier (closedBall (0 : E) b), G₀ x = outer x := by
    intro x hx
    rw [frontier_closedBall _ hb.ne'] at hx
    have hnorm : ‖x‖ = b := mem_sphere_zero_iff_norm.mp hx
    rw [hG₀eq (show a ≤ ‖x‖ ∧ ‖x‖ ≤ b by rw [hnorm]; exact ⟨hab.le, le_rfl⟩)]
    exact (exterior_extension_on_radius hb F₁ hF₁ hnorm).symm
  let G : C(E, M) := ⟨(closedBall (0 : E) b).piecewise G₀ outer,
    hG₀.piecewise hjoin₁ outer.continuous⟩
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    change ((closedBall (0 : E) b).piecewise G₀ outer) x = g x
    rw [piecewise_eq_of_mem _ _ _ (mem_closedBall_zero_iff.mpr hx.2)]
    exact hG₀eq hx
  · intro x hx
    have hxb : x ∉ closedBall (0 : E) b := by
      rw [mem_closedBall_zero_iff]
      linarith
    change ((closedBall (0 : E) b).piecewise G₀ outer) x = _
    rw [piecewise_eq_of_notMem _ _ _ hxb]
    change F₁ (exteriorDisk hb x) = F₁ ⟨0, mem_closedBall_self zero_le_one⟩
    apply congrArg F₁
    exact Subtype.ext (exteriorVector_eq_zero hb hx)

end Wikipedia.SmoothSixDPoincare.AnnularExtension

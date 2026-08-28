import Wikipedia.HopfProblem.AnalyticRootCoverGerms
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The analytic square-root germ cover has two sheets

At a point of finite order, the germs of a local root and its negative are
distinct, including when both have value zero. Every root germ is one of
these two germs. This constructs an equivalence with `Bool` for the actual
presheaf stalk and identifies that stalk with the literal fibre of the
étale-space projection.
-/

noncomputable section

open CategoryTheory Filter Function Opposite Set TopologicalSpace
open scoped Topology

namespace Wikipedia.HopfProblem.AnalyticRootCover

variable {S : Opens ℂ} {F : ℂ → ℂ} {U : Opens S}

/-- Finite order separates the two signed germs, not only their point values. -/
theorem germ_ne_neg (s : RootSection S F U) (x : S) (hx : x ∈ U)
    (hfinite : analyticOrderAt F (x : ℂ) ≠ ⊤) :
    (rootPresheaf S F).germ U x hx s ≠ (rootPresheaf S F).germ U x hx s.neg := by
  intro he
  have hxA : (x : ℂ) ∈ ambientOpen S U := (coe_mem_ambientOpen S U x).mpr hx
  have hroot : ∀ᶠ z in 𝓝 (x : ℂ), extendSection S U s.1 z ^ 2 = F z :=
    eventually_of_mem ((ambientOpen S U).isOpen.mem_nhds hxA)
      (fun _ hz => RootSection.square_eq s hz)
  apply root_germ_ne_neg hfinite hroot
  have hsg := (germ_eq_iff_eventuallyEq S F x hx hx s s.neg).mp he
  filter_upwards [hsg, (ambientOpen S U).isOpen.mem_nhds hxA] with z hz hzU
  exact hz.trans (RootSection.extend_neg_eqOn s hzU)

/-- The two signed actual germs determined by a local root section. -/
def rootStalkSignMap (s : RootSection S F U) (x : S) (hx : x ∈ U) :
    Bool → (rootPresheaf S F).stalk x
  | false => (rootPresheaf S F).germ U x hx s
  | true => (rootPresheaf S F).germ U x hx s.neg

@[simp] theorem rootStalkSignMap_false (s : RootSection S F U) (x : S) (hx : x ∈ U) :
    rootStalkSignMap s x hx false = (rootPresheaf S F).germ U x hx s := rfl

@[simp] theorem rootStalkSignMap_true (s : RootSection S F U) (x : S) (hx : x ∈ U) :
    rootStalkSignMap s x hx true = (rootPresheaf S F).germ U x hx s.neg := rfl

theorem rootStalkSignMap_injective (s : RootSection S F U) (x : S) (hx : x ∈ U)
    (hfinite : analyticOrderAt F (x : ℂ) ≠ ⊤) :
    Injective (rootStalkSignMap s x hx) := by
  intro b c h
  cases b <;> cases c
  · rfl
  · exact (germ_ne_neg s x hx hfinite h).elim
  · exact (germ_ne_neg s x hx hfinite h.symm).elim
  · rfl

theorem rootStalkSignMap_surjective (s : RootSection S F U) (x : S) (hx : x ∈ U) :
    Surjective (rootStalkSignMap s x hx) := by
  intro g
  obtain ⟨V, hxV, t, ht⟩ := (rootPresheaf S F).exists_germ_eq g
  rcases germ_eq_or_neg x hx hxV s t with hpos | hneg
  · exact ⟨false, hpos.symm.trans ht⟩
  · exact ⟨true, hneg.symm.trans ht⟩

/-- A local choice of root labels the actual stalk by its two signs. -/
def rootStalkEquivBool (s : RootSection S F U) (x : S) (hx : x ∈ U)
    (hfinite : analyticOrderAt F (x : ℂ) ≠ ⊤) :
    (rootPresheaf S F).stalk x ≃ Bool :=
  (Equiv.ofBijective (rootStalkSignMap s x hx)
    ⟨rootStalkSignMap_injective s x hx hfinite, rootStalkSignMap_surjective s x hx⟩).symm

@[simp] theorem rootStalkEquivBool_symm_false (s : RootSection S F U)
    (x : S) (hx : x ∈ U) (hfinite : analyticOrderAt F (x : ℂ) ≠ ⊤) :
    (rootStalkEquivBool s x hx hfinite).symm false =
      (rootPresheaf S F).germ U x hx s := rfl

@[simp] theorem rootStalkEquivBool_symm_true (s : RootSection S F U)
    (x : S) (hx : x ∈ U) (hfinite : analyticOrderAt F (x : ℂ) ≠ ⊤) :
    (rootStalkEquivBool s x hx hfinite).symm true =
      (rootPresheaf S F).germ U x hx s.neg := rfl

/-- The stalk has exactly two elements whenever a local root is available
and the prescribed function has finite order at the point. -/
theorem rootStalk_card_of_section (s : RootSection S F U) (x : S) (hx : x ∈ U)
    (hfinite : analyticOrderAt F (x : ℂ) ≠ ⊤) :
    Nat.card ((rootPresheaf S F).stalk x) = 2 := by
  rw [Nat.card_congr (rootStalkEquivBool s x hx hfinite)]
  simp

/-- The literal fibre of the actual étale-space projection is its presheaf stalk. -/
def rootEtaleFiberEquivStalk (S : Opens ℂ) (F : ℂ → ℂ) (x : S) :
    (TopCat.Presheaf.EtaleSpace.base (F := rootPresheaf S F) ⁻¹' {x}) ≃
      (rootPresheaf S F).stalk x where
  toFun e := by
    have he : e.1.base = x := e.2
    exact he ▸ e.1.germ
  invFun g := ⟨⟨x, g⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨y, g⟩, h⟩
    change y = x at h
    subst y
    rfl
  right_inv _ := rfl

/-- Every stalk has cardinal two under the actual finite-even-order hypotheses. -/
theorem rootStalk_card (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) (x : S) :
    Nat.card ((rootPresheaf S F).stalk x) = 2 := by
  obtain ⟨U, hx, _, ⟨s⟩⟩ := exists_root_neighborhood S F hF horder x
  obtain ⟨n, hn⟩ := horder x x.2
  apply rootStalk_card_of_section s x hx
  rw [hn]
  exact ENat.natCast_ne_top (2 * n)

/-- Every literal fibre of the actual root étale space has cardinal two,
including fibres over zeros. -/
theorem rootEtale_fibre_card (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) (x : S) :
    Nat.card (TopCat.Presheaf.EtaleSpace.base (F := rootPresheaf S F) ⁻¹' {x}) = 2 := by
  rw [Nat.card_congr (rootEtaleFiberEquivStalk S F x)]
  exact rootStalk_card S F hF horder x

/-- The actual analytic-root germ projection is a two-sheeted covering. -/
theorem rootEtale_two_sheeted (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := rootPresheaf S F)) ∧
      ∀ x : S,
        Nat.card (TopCat.Presheaf.EtaleSpace.base (F := rootPresheaf S F) ⁻¹' {x}) = 2 :=
  ⟨rootEtale_isCoveringMap S F hF horder, rootEtale_fibre_card S F hF horder⟩

end Wikipedia.HopfProblem.AnalyticRootCover

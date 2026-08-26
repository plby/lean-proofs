import Mathlib
import ErdosProblems.Erdos336.LocalBohrFromSyndetic
import ErdosProblems.Erdos336.LocalBohrReassembly
import ErdosProblems.Erdos336.GeneralPatchTransference

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Automatic piecewise-Bohr patches from the normalized parent
-/

namespace Erdos336

open PiecewiseBohrTransfer

/-- The finite cyclic removal bound alone now suffices: the normalized parent
automatically creates the required piecewise patch, at exact cost `4h`.
Consequently the removed set has eventual exact order `M+5h`. -/
theorem eventuallyExactlyZ_of_cyclic_bound_auto_patch
    {D : Set ℤ} {c : ℤ} {h q M : ℕ}
    (hzero : 0 ∈ D)
    (hparent : EventuallyWithOneExtra D c h)
    (hexact : EventuallyExactlyZ D q)
    (hcyclic : CyclicRemovalBound (h + 1) M) :
    EventuallyExactlyZ D (M + 4 * h + h) := by
  classical
  have hsynd := exactPowerEventuallySyndetic_of_oneExtra hzero hparent
  let s : ℕ := h + 1
  let qB : ℕ := 4 * s ^ 2
  let d : ℕ := 16 * qB ^ 3
  have hdata : ∀ R : ℕ,
      ∃ θ : Fin d → AddCircle (1 : ℝ), ∃ center : ℤ,
      ∀ x : ℤ, x.natAbs ≤ R →
        (∀ j : Fin d,
          ‖((AddCircle.toCircle (x • θ j) : Circle) : ℂ) - 1‖ ≤
            (1 / 2 : ℝ)) →
        ZRepExactly D (4 * h) (center + x) := by
    simpa [s, qB, d] using
      exists_local_bohr_data_of_exactPowerEventuallySyndetic hsynd
  choose θseq center hθseq using hdata
  let G := Fin d → AddCircle (1 : ℝ)
  obtain ⟨θ, σ, hσmono, hσlim⟩ :=
    CompactSpace.tendsto_subseq (fun R : ℕ => θseq R)
  let ψ : ℤ →+ G := zmultiplesHom G θ
  let phaseNorm : G → Fin d → ℝ := fun a j =>
    ‖((AddCircle.toCircle (a j) : Circle) : ℂ) - 1‖
  let U : Set G := {a | ∀ j, phaseNorm a j < (1 / 4 : ℝ)}
  have hphase_cont (x : ℤ) (j : Fin d) :
      Continuous (fun a : G => phaseNorm (x • a) j) := by
    have hcoord : Continuous (fun a : G => x • a j) :=
      (continuous_apply j).zsmul x
    have hcircle : Continuous (fun a : G =>
        ((AddCircle.toCircle (x • a j) : Circle) : ℂ)) :=
      continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp hcoord)
    exact (hcircle.sub continuous_const).norm
  have hUopen : IsOpen U := by
    dsimp [U]
    rw [show {a : G | ∀ j, phaseNorm a j < (1 / 4 : ℝ)} =
        ⋂ j : Fin d, {a : G | phaseNorm a j < (1 / 4 : ℝ)} by
      ext a
      simp]
    apply isOpen_iInter_of_finite
    intro j
    have hcoord : Continuous (fun a : G =>
        ((AddCircle.toCircle (a j) : Circle) : ℂ)) :=
      continuous_subtype_val.comp
        (AddCircle.continuous_toCircle.comp (continuous_apply j))
    exact isOpen_lt ((hcoord.sub continuous_const).norm) continuous_const
  have hUzero : (0 : G) ∈ U := by
    intro j
    change ‖((AddCircle.toCircle (0 : AddCircle (1 : ℝ)) : Circle) : ℂ) - 1‖ <
      (1 / 4 : ℝ)
    rw [AddCircle.toCircle_zero]
    norm_num
  have hlocal : ∀ R : ℕ, ∃ z : ℤ, ∀ x : ℤ,
      x.natAbs ≤ R → ψ x ∈ U → x + z ∈ {n | ZRepExactly D (4 * h) n} := by
    intro R
    let I : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ I, ψ x ∈ U →
          ∀ j : Fin d,
            phaseNorm (x • θseq (σ n)) j < (1 / 2 : ℝ) := by
      rw [Finset.eventually_all]
      intro x hxI
      by_cases hxU : ψ x ∈ U
      · have hall : ∀ᶠ n : ℕ in Filter.atTop,
            ∀ j : Fin d,
              phaseNorm (x • θseq (σ n)) j < (1 / 2 : ℝ) := by
          rw [Filter.eventually_all]
          intro j
          have hlim : Filter.Tendsto
              (fun n : ℕ => phaseNorm (x • θseq (σ n)) j)
              Filter.atTop
              (nhds (phaseNorm (x • θ) j)) := by
            exact ((hphase_cont x j).tendsto θ).comp hσlim
          have hquarter : phaseNorm (x • θ) j < (1 / 4 : ℝ) := by
            have := hxU j
            simpa [ψ, zmultiplesHom_apply] using this
          exact hlim.eventually_lt_const (by linarith)
        filter_upwards [hall] with n hn
        intro _
        simpa [phaseNorm, Pi.smul_apply] using hn
      · exact Filter.Eventually.of_forall fun n h => (hxU h).elim
    obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hev)
    let n : ℕ := max N R
    have hnN : N ≤ n := le_max_left _ _
    have hRn : R ≤ n := le_max_right _ _
    have hnσ : n ≤ σ n := hσmono.le_apply
    have hRσ : R ≤ σ n := le_trans hRn hnσ
    refine ⟨center (σ n), ?_⟩
    intro x hxR hxU
    have hxabs : |x| ≤ (R : ℤ) := by
      calc
        |x| = (x.natAbs : ℤ) := (Int.natCast_natAbs x).symm
        _ ≤ (R : ℤ) := by exact_mod_cast hxR
    have hxI : x ∈ I := by
      rw [Finset.mem_Icc]
      exact (abs_le.mp hxabs)
    have happ := hN n hnN x hxI hxU
    have hphase : ∀ j : Fin d,
        ‖((AddCircle.toCircle (x • θseq (σ n) j) : Circle) : ℂ) - 1‖ ≤
          (1 / 2 : ℝ) := by
      intro j
      have := happ j
      dsimp [phaseNorm] at this
      exact le_of_lt (by simpa [Pi.smul_apply] using this)
    have hrep := hθseq (σ n) x (le_trans hxR hRσ) hphase
    simpa [add_comm] using hrep
  let Rψ : AddSubgroup G := ψ.range
  let H : AddSubgroup G := Rψ.topologicalClosure
  have hRH : Rψ ≤ H := AddSubgroup.le_topologicalClosure Rψ
  let φ : ℤ →+ H := (AddSubgroup.inclusion hRH).comp ψ.rangeRestrict
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (AddSubgroup.isClosed_topologicalClosure Rψ).isCompact
  have hφdense : DenseRange φ := by
    have hincl : DenseRange (Set.inclusion (show (Rψ : Set G) ⊆ (H : Set G) from hRH)) := by
      apply (denseRange_inclusion_iff hRH).2
      intro y hy
      change y ∈ closure (Rψ : Set G)
      simpa [H, AddSubgroup.topologicalClosure_coe] using hy
    have hrange : DenseRange ψ.rangeRestrict :=
      (AddMonoidHom.rangeRestrict_surjective ψ).denseRange
    have hcomp := hincl.comp hrange (continuous_inclusion hRH)
    have hfun : (φ : ℤ → H) =
        Set.inclusion (show (Rψ : Set G) ⊆ (H : Set G) from hRH) ∘
          ψ.rangeRestrict := by rfl
    rw [hfun]
    exact hcomp
  let UH : Set H := {y | (y : G) ∈ U}
  have hUHopen : IsOpen UH := by
    exact hUopen.preimage continuous_subtype_val
  have hUHne : UH.Nonempty := by
    exact ⟨0, hUzero⟩
  have hlocalH : ∀ R : ℕ, ∃ z : ℤ, ∀ x : ℤ,
      x.natAbs ≤ R → φ x ∈ UH →
        x + z ∈ {n | ZRepExactly D (4 * h) n} := by
    intro R
    obtain ⟨z, hz⟩ := hlocal R
    refine ⟨z, ?_⟩
    intro x hx hxU
    apply hz x hx
    have hval : ((φ x : H) : G) = ψ x := by rfl
    simpa [UH, hval] using hxU
  obtain ⟨W, Tset, hWopen, hWne, hTthick, hpatch⟩ :=
    piecewise_patch_of_local_orbit_patterns φ hUHopen hUHne hlocalH
  apply eventuallyExactlyZ_of_cyclic_bound_and_general_patch φ hφdense
    hWopen hWne hzero hparent hexact hTthick hpatch
  · intro p hp
    exact hp
  · exact hcyclic

end Erdos336

/-
  Erdős problem 501 — the ZFC core.

  This library formalizes the forcing-free "ZFC core" of the profile-certificate
  proof (rev10), i.e. the first line of the logical decomposition

      ZFC  ⊢  Prof(𝒜) → Free_ω(𝒜).

  Contents:
  * `Erdos501.pos_measure_Q`, `Erdos501.infinite_measure_preservation`
        — Lemmas 2.1 and 2.2 (σ-finite selection).
  * `Erdos501.Certificate`, `Erdos501.Prof`, `Erdos501.Free`
        — Definition 3.1.
  * `Erdos501.prof_imp_free`, `Erdos501.prof_imp_free'`
        — Theorem 3.2.

  Nothing here uses forcing or CH.

  Provenance: `erdos501-zfc-core.zip` (session 2026-08-16, root module
  `Erdos501.lean` of the standalone Lake project `erdos501core`), verified
  sorry-free at Lean v4.30.0-rc2 / Mathlib 83a5988 and re-verified here at the
  unified pin.  The forcing development contains a second, independent
  formalization of the same results (`Flypitch.Erdos501.ZFCCore`), wired to the
  forcing files; this one is the audited standalone version.
-/
import ErdosProblems.Erdos501.ZFCCore.Selection
import ErdosProblems.Erdos501.ZFCCore.Certificate

namespace Erdos501

/-- **Theorem 3.2**, packaged form:  `Prof(𝒜) → Free_ω(𝒜)`, a theorem of ZFC. -/
theorem prof_imp_free' {A : ℝ → Set ℝ} (h : Prof A) : Free A :=
  h.elim prof_imp_free

end Erdos501

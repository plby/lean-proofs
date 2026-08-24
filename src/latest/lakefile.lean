import Lake

open System Lake DSL

package «lean-proofs-latest» where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, 3⟩
  ]

require leancert from git "https://github.com/alerad/leancert.git" @ "v4.33.0"

require ComparatorChallenges from "ComparatorChallenges"

require erdos211Incidence from "ErdosProblems/Erdos211/Incidence"

require APAP from git "https://github.com/YaelDillies/apap.git" @ "v4.33.0"

require AINTLIB from git "https://github.com/CBirkbeck/AINTLIB.git" @
  "1c1c74664e40071c2c2165bc55ca2616a67ccd6b"

require BoundedGaps from git "https://github.com/frenzymath/FormalPantheon.git" @
  "ffbb65c21afc8a36ace67720f1b0df1c63d26bd1" / "BoundedGaps"

require Waring from git "https://github.com/frenzymath/FormalPantheon.git" @
  "ffbb65c21afc8a36ace67720f1b0df1c63d26bd1" / "Warning"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

@[default_target] lean_lib All

lean_lib Arxiv

lean_lib BorisBukh

lean_lib ErdosProblems

lean_lib HundredTheorems

lean_lib MathOverflow

lean_lib PrimeNumberTheoremAnd

lean_lib Util

lean_lib UnitFractions

lean_lib Wikipedia

private def runGitApply
    (directory patch : FilePath) (arguments : Array String) : IO IO.Process.Output :=
  IO.Process.output {
    cmd := "git"
    args := #["-C", directory.toString, "apply"] ++ arguments ++ #[patch.toString]
  }

post_update pkg do
  for (name, patchName) in #[
      ("BoundedGaps", "formalpantheon-v4.33.0.patch"),
      ("BoundedGaps", "formalpantheon-v4.33.0-s2.patch"),
      ("AINTLIB", "aintlib-v4.33.0.patch")] do
    let dependency := pkg.dir / ".lake" / "packages" / name
    let patch := pkg.dir / "patches" / patchName
    if !(← dependency.pathExists) then
      error s!"{name} package directory does not exist: {dependency}"
    if !(← patch.pathExists) then
      error s!"{name} compatibility patch does not exist: {patch}"
    let forwardCheck ← runGitApply dependency patch #["--check"]
    if forwardCheck.exitCode = 0 then
      let result ← runGitApply dependency patch #[]
      if result.exitCode != 0 then
        error s!"failed to apply {name} compatibility patch {patch}:\n{result.stderr}"
      IO.println s!"Applied {name} compatibility patch {patchName}."
    else
      let reverseCheck ← runGitApply dependency patch #["--reverse", "--check"]
      if reverseCheck.exitCode = 0 then
        IO.println s!"{name} compatibility patch {patchName} is already applied."
      else
        error s!"{name} checkout is incompatible with compatibility patch {patch}.\n\
          Forward check:\n{forwardCheck.stderr}\nReverse check:\n{reverseCheck.stderr}"

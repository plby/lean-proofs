# Schoenflies planar-topology modules

These modules are the minimal transitive source closure needed for
`Schoenflies.Graph.Redrawing` and `Schoenflies.FaceCyclesLand`, vendored from
[`alonamaloh/schoenflies-lean`](https://github.com/alonamaloh/schoenflies-lean)
at commit `05a43d29cde026618777db3d4e4316204ccca237`.

Copyright (c) 2026 Álvaro Begué. The sources are used under the Apache License
2.0, as recorded in each source header and in the repository's root license.

Local changes are limited to:

- rewriting module imports under `ErdosProblems.Erdos223.Schoenflies`;
- one Lean 4.33 elaboration adjustment in `Subarc.lean`;
- one prose-only wording change needed by the project's placeholder scan.

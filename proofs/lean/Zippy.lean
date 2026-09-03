/-
The package root.  Every module of the Lean development is imported here, so `lake build` (and
therefore `scripts/check_lean.sh`, and therefore `sbt check`) checks all of it and a module that
stops compiling cannot hide by having no importer.
-/
import Zippy.Core

/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Lake
open Lake DSL

package lacunaryLeanPalomar where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc4"

@[default_target]
lean_lib Lacunary where
  roots := #[`Paper4.Statement, `Paper4.Integration, `Challenge, `Solution]
  globs := #[.submodules `Paper4, .one `Challenge, .one `Solution]

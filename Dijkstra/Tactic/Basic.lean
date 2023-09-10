/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv

/-!

## `assert_change` conversion tactic

The conversion tactic `assert_change e₁` replaces an expression `e` with `e₁` producing a new goal `e = e₁`.

Example: 

```lean
variable (m n : Nat) (h : n = 1) (hmn : m = n)

example : 0 + m = 1 := by
  conv =>
    -- | 0 + m = 1
    lhs
    -- | 0 + m
    assert_change m
    -- | m  and  ⊢ 0 + m = m
    . rw [hmn]
    . tactic => rw [Nat.zero_add]
  -- ⊢ n = 1
  exact h
```

-/
syntax (name:=assert_change) "assert_change" term : conv

open Lean.Elab Tactic Conv in
/-- `assert_change e₁` replaces an expression `e` with `e₁` producing a new goal `e = e₁`. -/
@[tactic assert_change]
def convAssertChangeTactic : Tactic
| `(conv| assert_change $e) => withMainContext do
  let lhs ← getLhs
  let r ← elabTermEnsuringType e (← Lean.Meta.inferType lhs)
  let t ← Lean.Meta.mkAppM ``Eq #[lhs, r]
  let g ← Lean.Meta.mkFreshExprMVar t
  updateLhs r g
  appendGoals [g.mvarId!]
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Conv


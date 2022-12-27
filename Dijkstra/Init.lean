/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Basic definitions
-/

universe u v

inductive DEq {α : Type u} (β : α → Type v) : {a₁ a₂ : α} → β a₁ → β a₂ → Prop
| rfl {a : α} (b : β a) : DEq β b b


/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Basic definitions
-/

universe u v

inductive DEq {α : Type u} (β : α → Type v) : {a₁ a₂ : α} → β a₁ → β a₂ → Prop
| refl {a : α} (b : β a) : DEq β b b

namespace DEq

variable {α : Type u} {β : α → Type v}

theorem trans {a₁ a₂ a₃ : α} : ∀ {x₁ : β a₁} {x₂ : β a₂} {x₃ : β a₃}, DEq β x₁ x₂ → DEq β x₂ x₃ → DEq β x₁ x₃
| _, _, _, DEq.refl _, DEq.refl _ => DEq.refl _

instance instTransDEq (a₁ a₂ a₃ : α) : Trans (DEq β (a₁:=a₁) (a₂:=a₂)) (DEq β (a₁:=a₂) (a₂:=a₃)) (DEq β (a₁:=a₁) (a₂:=a₃)) where
  trans hxy hyz := DEq.trans hxy hyz

theorem symm : ∀ {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, DEq β b₁ b₂ → DEq β b₂ b₁
| _, _, _, _, DEq.refl _ => DEq.refl _

theorem subst_deq : ∀ {a₁ a₂ : α} {h : a₁ = a₂} {b : β a₁}, DEq β (h ▸ b) b
| _, _, Eq.refl _, _ => DEq.refl _

theorem eq_param : ∀ {a₁ a₂ : α} {x₁ : β a₁} {x₂ : β a₂}, DEq β x₁ x₂ → a₁ = a₂
| _, _, _, _, DEq.refl _ => rfl

theorem deq_of_eq : ∀ {a : α} {x₁ x₂ : β a}, x₁ = x₂ → DEq β x₁ x₂
| _, _, _, rfl => DEq.refl _

theorem eq_of_deq : ∀ {a : α} {x₁ x₂ : β a}, DEq β x₁ x₂ → x₁ = x₂
| _, _, _, DEq.refl _ => rfl

end DEq
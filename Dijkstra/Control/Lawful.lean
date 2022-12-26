/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

universe u v
variable {m : Type u → Type v}

theorem map_bind [Monad m] [LawfulMonad m] {α β γ : Type u} (f : α → β) (x : m α) (g : β → m γ) : (f <$> x) >>= g = x >>= (g ∘ f) := by
  rw [map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro a; rw [pure_bind]
  rfl

/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Dijkstra.Control.Monad.Hom

/-!

# Binary relation on monads

Since the category of monads has finite products, we can define the notion of ***relations*** between two monads.
Namely, given monads `m : Type u → Type v` and `n : Type u → Type w`, we define a relation `r` between `m` and `n` to be a submonad of the monad

```lean
def MonadPair (m : Type u → Type v) [Monad m] (n : Type u → Type v) [Monad n] : Type u → Type (max u v) := λ α ↦ m α × n α
```

Thus, as an endo-functor, `r` is identified with a characteristic map `r : {α : Type u} → m α → n α → Prop`.
In order for the resulting subfunctor to inherit the structure of a monad, it has to satisfy the following properties:

```lean
MonadRel.rel_pure {α : Type u} : ∀ (a : α), r (pure a) (pure a)
MonadRel.rel_bind {α β : Type u} {x : m α} {y : n α} {f : α → m β} {g : α → n β} : r x y → (∀ a, r (f a) (g a)) → r (x >>= f) (y >>= g)
```

We call such a relation a ***monadic relation***.
-/

universe u v v₁ v₂ v₃ w w₁ w₂

class MonadRel (m : Type u → Type v) [Monad m] (n : Type u → Type w) [Monad n] where
  rel {α : Type u} : m α → n α → Prop
  rel_pure {α : Type u} (a : α) : rel (pure a) (pure a)
  rel_bind {α β : Type u} {x : m α} {y : n α} {f : α → m β} {g : α → n β} : rel x y → (∀ a, rel (f a) (g a)) → rel (x >>= f) (y >>=g)


namespace MonadRel

/-- The equality; `MonadRel.Eq m` is associated with `m` itself via the diagonal morphism `m → m × m`. -/
protected
def Eq {m : Type u → Type v} [Monad m] : MonadRel m m where
  rel := Eq
  rel_pure _ := rfl
  rel_bind h hfg := h ▸ bind_congr hfg

/-- Invert the direction of a given relation. -/
def swap {m : Type u → Type v} [Monad m] {n : Type u → Type w} [Monad n] (r : MonadRel m n) : MonadRel n m where
  rel y x := r.rel x y
  rel_pure a := r.rel_pure a
  rel_bind hxy hfg := r.rel_bind hxy hfg

/-- @warning the composition of monadic relations requires `Classical.Choice`. -/
def comp {m₁ : Type u → Type v₁} [Monad m₁] {m₂ : Type u → Type v₂} [Monad m₂] {m₃ : Type u → Type v₃} [Monad m₃] (r₁ : MonadRel m₁ m₂) (r₂ : MonadRel m₂ m₃) : MonadRel m₁ m₃ where
  rel x z := ∃ y, r₁.rel x y ∧ r₂.rel y z
  rel_pure a := Exists.intro (Pure.pure a) ⟨r₁.rel_pure a, r₂.rel_pure a⟩
  rel_bind := by
    dsimp; intro α β x z f h hxz hfh
    cases hxz with | intro y hy =>
    cases Classical.axiomOfChoice hfh with | intro g hg =>
    exists y >>= g
    exact ⟨r₁.rel_bind hy.left (λ a => (hg a).left), r₂.rel_bind hy.right (λ a => (hg a).right)⟩

/-- Pullback of a relation with respect to the left variable. -/
def pullLeft {m₁ : Type u → Type v₁} [Monad m₁] {m₂ : Type u → Type v₂} [Monad m₂] {n : Type u → Type w} [Monad n] (F : MonadHom m₁ m₂) (r : MonadRel m₂ n) : MonadRel m₁ n where
  rel x y := r.rel (F.app x) y
  rel_pure a := by dsimp; rw [F.app_pure a]; exact r.rel_pure a
  rel_bind hxy hfg := by dsimp; rw [F.app_bind]; exact r.rel_bind hxy hfg

/-- pullback of a relation with respect to the right variable. -/
def pullRight {m : Type u → Type v} [Monad m] {n₁ : Type u → Type w₁} [Monad n₁] {n₂ : Type u → Type w₂} [Monad n₂] (F : MonadHom n₁ n₂) (r : MonadRel m n₂) : MonadRel m n₁ where
  rel x y := r.rel x (F.app y)
  rel_pure a := by dsimp; rw [F.app_pure a]; exact r.rel_pure a
  rel_bind hxy hfg := by dsimp; rw [F.app_bind]; exact r.rel_bind hxy hfg

end MonadRel

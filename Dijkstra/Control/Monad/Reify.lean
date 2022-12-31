/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Dijkstra.Tactic.Basic

import Dijkstra.Control.Monad.Hom
import Dijkstra.Control.Monad.Rel
import Dijkstra.Control.Monad.Dijkstra
import Dijkstra.Control.Monad.Spec

universe u v v₁ v₂ w w₁ w₂


/-!

# Reification of Dijkstra monads

Given a Dijkstra monad `M : (α : Type u) → W α → Type v` over a monad `W : Type u → Type w`, one sometimes wants to take the value of type `M α w` into computation of a monad `m : Type u → Type v`.
For example, suppose that `M := Graph r` is the Dijkstra monad associated with the monadic relation `r : MonadRel m W` on `m` with a specification monad `W`.
In this case, a relation between a computation `x : m α` and a "specification" `w : W α` can be represented by `X : M α w`.
Sometimes, the specification `X` assures that the computation result of `x` actually lies in the subtype `{a : α // p a}` rather than `α` for some predicate `p : α → Prop`.
In other words, `X` enables to pass the result of `x` to the next computation of the form `(a : α) → p a → m β`.
In particular, if the next computation is `pure`, one obtains a value of type `m (Subtype p)`, which we would call the ***reification*** of `X`.

The goal of this module is to develop a formal framework for the above.

-/


/-!

## The transformer `SubtypeT`

We first investigate the type `m (Subtype p)` of the reifications.
Notice that it is a type construction from a monad `m : Type u → Type v`, a type `α : Type u`, and a prediate `p : α → Prop`.
Since `p` is also considered as a value of the predicate monad `Pred`, 
From this viewpoint, we introduce the following:

```lean
SubtypeT m (α : Type u) (p : Pred α) ≡ m (Subtype p)
```

It turns out that `SubtypeT m` forms a Dijkstra monad over `Pred` provided `m` is a monad.
Hence, we may think of `SubtypeT` as a transformer of a monad into a Dijkstra monad.

For each monad `m`, the Dijkstra monad `SubtypeT m` comes equipped with the following two fundamental operations:

```lean
def pureMk {α: Type u} {p : Pred α} : (a : α) → (h : p a) → SubtypeT m α p :=
  λ a h => return (Subtype.mk a h)

def weaken {α :Type u} {p q : Pred α} : MonadRel.rel p q → SubtypeT m α p → SubtypeT m α q :=
  λ hpq x => x >>= λ a => return ⟨a.val, hpq a.val a.property⟩
```

-/

def SubtypeT (m : Type u → Type v) (α : Type u) (p : Pred α) : Type v := m (Subtype p)

namespace SubtypeT

variable {m : Type u → Type v} [Monad m]

instance instDijkstraMonadSubtypeT : DijkstraMonad Pred (SubtypeT m) where
  dpure a := pure ⟨a,rfl⟩
  dbind x f := x >>= λ a => f a.val >>= λ b => return ⟨b, ⟨a, a.property, b.property⟩⟩

def pureMk {α : Type u} {p : Pred α} (a : α) (h : p a) : SubtypeT m α p :=
  pure ⟨a,h⟩

def weaken {α : Type u} {p q : Pred α} (hpq : mrel p q) (x : SubtypeT m α p) : SubtypeT m α q :=
  x >>= λ a => return ⟨a.val, hpq a a.property⟩

theorem deq_of_iff [LawfulMonad m] {α : Type u} {p q : Pred α} (hpq : ∀ a, p a ↔ q a) : ∀ (x : SubtypeT m α p), DEq (SubtypeT m α) x (x.weaken λ a => (hpq a).mp) := by
  have : p = q := funext (λ a => propext (hpq a))
  cases this
  intro x; apply DEq.deq_of_eq
  conv =>
    rhs; dsimp [weaken]; congr
    . skip
    . ext a; change pure a
  rw [bind_pure]

instance instDijkstraMonadLawfulSubtypeT [LawfulMonad m] : DijkstraMonad.Lawful Pred (SubtypeT m) where
  dbind_dpure := by
    intro α p x
    dsimp [dbind, dpure]
    conv =>
      lhs; rhs; ext a; rw [pure_bind]; dsimp [pure]
    have : ∀ a, (p >>= pure) a ↔ p a := by
      rw [bind_pure (m:=Pred)]; intros; exact Iff.rfl
    apply DEq.trans (deq_of_iff (m:=m) (q:=p) this _)
    apply DEq.deq_of_eq
    conv =>
      lhs; dsimp [weaken]; rw [bind_assoc]
      rhs; ext x; rw [pure_bind]
    rw [bind_pure (m:=m)]
  dpure_dbind := by
    intro α β wf a f
    dsimp [dbind, dpure]
    conv => lhs; rw [pure_bind]; dsimp
    have : ∀ a₁, (pure a >>= wf) a₁ ↔ wf a a₁ := by
      rw [pure_bind (m:=Pred)]; intros; exact Iff.rfl
    apply DEq.trans (deq_of_iff (m:=m) this _)
    apply DEq.deq_of_eq
    conv =>
      lhs; dsimp [weaken]; rw [bind_assoc]
      rhs; ext x; rw [pure_bind]; change pure x
    rw [bind_pure]
  dbind_assoc := by
    intro α β γ wa wf wg x f g
    have : ∀ c, (wa >>= wf >>= wg) c ↔ (wa >>= λ a => wf a >>= wg) c := by
      rw [bind_assoc (m:=Pred)]; intros; exact Iff.rfl
    apply DEq.trans (deq_of_iff this _)
    apply DEq.deq_of_eq
    dsimp [weaken, dbind]
    conv =>
      lhs; rw [bind_assoc, bind_assoc]
      rhs; ext x; rw [bind_assoc]
      rhs; ext y; rw [pure_bind, bind_assoc]
      rhs; ext z; rw [pure_bind]
    apply bind_congr
    intro a
    conv =>
      rhs; rw [bind_assoc]
      rhs; ext b; rw [bind_assoc]
      rhs; ext x; rw [pure_bind]

end SubtypeT


/-!

## Dijkstra lift

As seen in the previous section, the type `m (Subtype p)` of the result of the reification form a Dijkstra monad over the specification `Pred`.
This implies that the reification is a transformation of Dijkstra monads with possibly different underlying monads.
This is why we introduce the notion of ***Dijkstra lift***, which is an analogue of `MonadLift`.

-/

/-- Dijkstra lift structure. Notice that the ingredients include `MonadRel W Z` instead of `MonadHom W Z`. -/
class DijkstraLift {W : Type u → Type v₁} [Monad W] {Z : Type u → Type v₂} [Monad Z] (r : MonadRel W Z) (M : (α : Type u) → W α → Type w₁) [DijkstraMonad W M] (N : (α : Type u) → Z α → Type w₂) [DijkstraMonad Z N] where
  dLift {α : Type u} {w : W α} {z : Z α} : r.rel w z → M α w → N α z

/-- Axioms for Dijkstra lifts -/
class DijkstraLift.Lawful {W : Type u → Type v₁} [Monad W] {Z : Type u → Type v₂} [Monad Z] (r : MonadRel W Z) (M : (α : Type u) → W α → Type w₁) [DijkstraMonad W M] (N : (α : Type u) → Z α → Type w₂) [DijkstraMonad Z N] [DijkstraLift r M N] where
  -- Compatibility with `DijkstraMonad.dpure`
  dLift_dpure {α : Type u} (a : α) : dLift (r.pure a) (dpure (M:=M) a) = dpure (M:=N) a
  -- Compatibility with `DijkstraMonad.dbind`
  dLift_dbind {α β : Type u} {wa : W α} {wf : α → W β} {za : Z α} {zf : α → Z β} {ha : r.rel wa za} {hf : ∀ a, r.rel (wf a) (zf a)} (x : M α wa) (f : (a : α) → M β (wf a)) : dLift (r.bind ha hf) (dbind (M:=M) x f) = dbind (M:=N) (dLift ha x) λ a => dLift (hf a) (f a)

export DijkstraLift.Lawful (dLift_dpure dLift_dbind)

/-- As an example, for every monad `m`, `SubtypeT m` has a canonical lift to itself along the implication relation `Pred.rel p q ≡ ∀ a, p a → q a`. -/
instance instDijkstraLiftSubtypeTweaken (m : Type u → Type v) [Monad m] : DijkstraLift Pred.rel (SubtypeT m) (SubtypeT  m) where
  dLift h x := SubtypeT.weaken h x

instance instDijkstraLiftLawfulSubtypeTweaken (m : Type u → Type v) [Monad m] [LawfulMonad m] : DijkstraLift.Lawful Pred.rel (SubtypeT m) (SubtypeT m) where
  dLift_dpure a := by
    dsimp [DijkstraLift.dLift, SubtypeT.weaken, dpure]
    rw [pure_bind]
  dLift_dbind x f := by
    dsimp [DijkstraLift.dLift, SubtypeT.weaken, dbind]
    rw [bind_assoc, bind_assoc]
    apply bind_congr; intro a
    rw [bind_assoc, pure_bind, bind_assoc]
    apply bind_congr; intro b
    rw [pure_bind, pure_bind]


/-!

## Reification

We now define the notion of reification.
Let `M : (α : Type u) → W α → Type v` be a Dijkstra monad over a (specification) monad `W` equipped with a specification monadic relation `r : SpecMonadRel W Pred`.
Then, a monad `m : Tye u → Type w` is called a ***reification of `M`*** with respect to `r` if there is a Dijkstra lift `reify : r w p → M α w → SubtypeT m p` which satisfies the follogin conditions.

```lean
reify_weaken {α : Type u} {p q : Pred α} (hpq : ∀ a, p a → q a): ∀ {wp : WPPure α} {x : M α wp} {h : wp p}, (reify p x h).weaken hpq = reify q x (wp.monotonic h)
```
-/

/-- Reification of a Dijkstra monad  -/
class Reification {W : Type u → Type w} [Monad W] [SpecMonad W] (r : SpecMonadRel W Pred) (M : (α : Type u) → W α → Type v) [DijkstraMonad W M] (m : Type u → Type v₁) [Monad m] extends DijkstraLift r.toMonadRel M (SubtypeT m)

def reify {W : Type u → Type w} [Monad W] [SpecMonad W] {r : SpecMonadRel W Pred} {M : (α : Type u) → W α → Type v} [DijkstraMonad W M] {m : Type u → Type v₁} [Monad m] [self : Reification r M m] {α : Type u} {w : W α} (p : Pred α) : r.rel w p → M α w → SubtypeT m α p :=
  self.dLift

/-- The axioms for reification -/
class Reification.Lawful {W : Type u → Type w} [Monad W] [SpecMonad W] (r : SpecMonadRel W Pred) (M : (α : Type u) → W α → Type v) [DijkstraMonad W M] (m : Type u → Type v₁) [Monad m] [Reification r M m] [DijkstraLift.Lawful r.toMonadRel M (SubtypeT m)] where
  --- `reify` and `weaken`
  reify_weaken {α : Type u} {wa : W α} {p q : Pred α} (hpq : mrel p q) : ∀ {x : M α wa} {h : r.rel wa p}, (reify (M:=M) (m:=m) p h x).weaken hpq = reify (M:=M) (m:=m) q (r.trans_right h hpq) x

export Reification.Lawful (reify_weaken)

section Reification

variable {W : Type u → Type w} [Monad W] [SpecMonad W] {r : SpecMonadRel W Pred} {M : (α :Type u) → W α → Type v} [DijkstraMonad W M] {m :Type u → Type v₁} [Monad m] [Reification r M m] [DijkstraLift.Lawful r.toMonadRel M (SubtypeT m)] [self : Reification.Lawful r M m]

@[simp]
theorem reify_dpure {α : Type u} (a : α) : reify (M:=M) (pure a) (r.pure a) (dpure a) = dpure (M:=SubtypeT m) a :=
  dLift_dpure a

@[simp]
theorem reify_dbind {α β : Type u} {wa : W α} {wf : α → W β} {pa : Pred α} {pf : α → Pred β} {ha : r.rel wa pa} {hf : ∀ a, r.rel (wf a) (pf a)} (x : M α wa) (f : (a : α) → M β (wf a)) : reify (M:=M) (pa >>= pf) (r.bind ha hf) (dbind x f) = dbind (M:=SubtypeT m) (reify (M:=M) pa ha x) (λ a => reify (M:=M) (pf a) (hf a) (f a)) :=
  dLift_dbind x f

end Reification



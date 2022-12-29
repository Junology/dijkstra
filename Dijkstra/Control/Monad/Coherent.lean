/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import Dijkstra.Control.Monad.Hom
import Dijkstra.Control.Monad.Rel
import Dijkstra.Control.Monad.Dijkstra
import Dijkstra.Control.Monad.Spec

universe u v w


/-!

# Coherent monads

Given a Dijkstra monad `M : (α : Type u) → WPPure α → Type v` over the specification monad `WPPure` (i.e. the weakest precondition transformer for pure computation), we say a monad `m : Type u → Type v` is ***coherent*** along `M` if one can transform a computation of `M` into that of `m` along with the associated predicate.
Recall that the specification monads `Pred` and `WPPure` are defined so that `Pred α ≡ α → Prop` and `WPPure α ⊂ (Pred α → Prop)`.

-/


/-!

## The transformer `SubtypeT`

In order to formalize the concept of coherent monads, we first assigns a Dijkstra monad over `Pred` to each monad `m : Type u → Type v`.
Namely, given a `m`, we define

```lean
SubtypeT m (α : Type u) (p : Pred α) ≡ m (Subtype p)
```

It turns out that `SubtypeT m` forms a Dijkstra monad over `Pred` provided `m` is a monad.
From this point of view, we may think of `SubtypeT` as a transformer of a monad into a Dijkstra monad.

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

def weaken {α : Type u} {p q : Pred α} (hpq : MonadRel.rel p q) (x : SubtypeT m α p) : SubtypeT m α q :=
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

## Coherent monads

We now define the notion of coherent monads.
For a Dijkstra monad `M : Type u → Type v` over the specification monad `WPPure`, a monad `m : Tye u → Type w` is called ***coherent with respect to `M`*** if it is equipped with a morphism

```lean
reify {α : Type u} (p : Pred α) : {wp : WPPure α} → M α wp → wp p → SubtypeT m α p
```

which respects the structure of the Dijkstra monads; namely,

```lean
reify_dpure {α : Type u} {p : Pred α} : ∀ (a : α) {h : p a}, reify p (dpure a) h = pureMk a h

reify_dbind {α β : Type u} {p : Pred α} {q : α → Pred β} : ∀ {wa : WPPure α} {wf : α → WPPure β} (x : M α wa) (f : (a : α) → M β (wf a)) {h : (wa >>= wf) (p >>= q)} {hp : wa p} {hq : ∀ a, (wf a) (q a)}, reify (p >>= q) (dbind x f) h = dbind (reify p x hp) λ a => reify (q a) (f a) (hq a)

reify_weaken {α : Type u} {p q : Pred α} (hpq : ∀ a, p a → q a): ∀ {wp : WPPure α} {x : M α wp} {h : wp p}, (reify p x h).weaken hpq = reify q x (wp.monotonic h)
```
-/

/-- The structure of coherent monads -/
class CoherentMonad (M : (α : Type u) → WPPure α → Type v) [DijkstraMonad WPPure M] (m : Type u → Type w) where
  reify {α : Type u} (p : Pred α) : {wp : WPPure α} → M α wp → wp.predT p → SubtypeT m α p

/-- The axioms for coherent monads -/
class CoherentMonad.Lawful (M : (α : Type u) → WPPure α → Type v) [DijkstraMonad WPPure M] (m : Type u → Type w) [Monad m] [CoherentMonad M m] where
  --- `reify` on `dpure`
  reify_dpure {α : Type u} {p : Pred α} : ∀ (a : α) {h : p a}, reify (M:=M) p (dpure a) h = SubtypeT.pureMk (m:=m) a h
  --- `reify` on `dbind`
  reify_dbind {α β : Type u} {p : Pred α} {q : α → Pred β} : ∀ {wa : WPPure α} {wf : α → WPPure β} (x : M α wa) (f : (a : α) → M β (wf a)) {h : (wa >>= wf).predT (p >>= q)} {hp : wa.predT p} {hq : ∀ a, (wf a).predT (q a)}, reify (M:=M) (m:=m) (p >>= q) (dbind x f) h = dbind (reify p x hp) λ a => reify (q a) (f a) (hq a)
  --- `reify` and `weaken`
  reify_weaken {α : Type u} {p q : Pred α} (hpq : MonadRel.rel p q): ∀ {wp : WPPure α} {x : M α wp} {h : wp.predT p}, (reify (M:=M) (m:=m) p x h).weaken hpq = reify (M:=M) (m:=m) q x (wp.monotonic hpq h)

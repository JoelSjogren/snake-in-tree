-- See also closed meanders, https://en.wikipedia.org/wiki/Meander_(mathematics).

{-# OPTIONS --cubical --type-in-type #-}
module Snake2 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

data List (A : Type) : Type where
  nil : List A
  cons : A → List A → List A

snoc : {A : Type} → List A → A → List A
snoc nil a = cons a nil
snoc (cons a' as) a = cons a' (snoc as a)

data Index {A : Type} : List A → Type where
  here : {a : A} {as : List A} → Index (cons a as)
  there : {a : A} {as : List A} → Index as → Index (cons a as)

split-at-index : {A : Type} {as : List A} → Index as → List A × A × List A
split-at-index {A} {cons a as} here = nil , a , as
split-at-index {A} {cons a as} (there i) =
  let as₀ , a' , as₁ = split-at-index i in cons a as₀ , a' , as₁

_[_] : {A : Type} → (as : List A) → Index as → A
cons a as [ here ] = a
cons a as [ there i ] = as [ i ]

record Tree (A : Type) : Type where
  inductive
  constructor node
  field
    label : A
    children : List (Tree A)
open Tree

data Node {A : Type} : Tree A → Type where
  root : {t : Tree A} → Node t
  child : {a : A} {ts : List (Tree A)} (i : Index ts) → Node (ts [ i ]) → Node (node a ts)

_++_ : {A : Type} → List A → List A → List A
nil ++ as = as
cons a as ++ as' = cons a (as ++ as')

data Concat {A : Type} : (as₀ as₁ as : List A) → Type where
  left-of : {as : List A} → Concat nil as as
  right-of : {a : A} {as₀ as₁ as : List A} → Concat as₀ as₁ as →
    Concat (cons a as₀) as₁ (cons a as)

record Cut' {A : Type} (as : List A) : Type where
  constructor cut'
  field
    as₀ : List A
    as₁ : List A
    iden : Concat as₀ as₁ as

nil-cut : {A : Type} {as : List A} → Cut' as
nil-cut {A} {as} = cut' nil as left-of

cons-cut : {A : Type} (a : A) {as : List A} (c : Cut' as) → Cut' (cons a as)
cons-cut a (cut' as₀ as₁ iden) = cut' (cons a as₀) as₁ (right-of iden)

append-cut : {A : Type} (as₀ : List A) {as₁ : List A} (c : Cut' as₁) → Cut' (as₀ ++ as₁)
append-cut nil c = c
append-cut (cons a as₀) c = cons-cut a (append-cut as₀ c)

end-cut : {A : Type} {as : List A} → Cut' as
end-cut {A} {nil} = nil-cut
end-cut {A} {cons a as} = cons-cut a end-cut

_%_ : {A : Type} (t : Tree A) → Node t → Tree A
t % root = t
node a ts % child i n = (ts [ i ]) % n

Wedge : {A : Type} (t : Tree A) → Node t → Type
Wedge t n = Cut' (children (t % n))

record Tree-Node-Wedge (A : Type) : Type where
  constructor ⟨_,_,_⟩
  field
    t : Tree A
    n : Node t
    w : Wedge t n

INIT : {A : Type} (a₀ a₁ : A) → Tree-Node-Wedge A  -- (a₀) root
INIT a₀ a₁ =                                       --  ↓
  record {                                         -- (a₁)< wedge
    t = (node a₀ (cons (node a₁ nil) nil));
    n = child here root;
    w = cut' nil nil left-of
  }

data Neighbour {A : Type} : (t : Tree A) → Node t → Type where
  parent : {t : Tree A} (i : Index (children t))
    → Neighbour t (child i root)
  child : {t : Tree A} (i : Index (children t))
    → Neighbour t root
  lift : {t : Tree A} (i : Index (children t)) (n : Node (children t [ i ]))
    → Neighbour (children t [ i ]) n
    → Neighbour t (child i n)

Neighbour' : {A : Type} → Tree-Node-Wedge A → Type
Neighbour' tnw = let ⟨ t , n , w ⟩ = tnw in Neighbour t n

SPLIT-downwards' : {A : Type}
  (a : A)
  (ts : List (Tree A))
  (i₁ : Index ts)
  (c₁ : Cut' ts)
  → Σ[ ts' ∈ List (Tree A) ] Σ[ i' ∈ Index ts' ] Cut' (children (ts' [ i' ]))
SPLIT-downwards' a _ i₁ (cut' nil ts left-of) with split-at-index i₁
... | ts₀ , node a* ts* , ts₁ =
  cons t' ts₁ , here , nil-cut
    where
      t' = node a* (cons (node a ts₀) ts₁)
SPLIT-downwards' a _ here (cut' (cons (node a* ts*) ts₀) ts₁ (right-of iden)) =
  cons t' ts₁ , here , end-cut
    where
      t' = node a* (snoc ts* (node a ts₀))
SPLIT-downwards' a (cons t ts) (there i) (cut' _ _ (right-of iden)) =
  let ts' , i' , c' = SPLIT-downwards' a ts i (cut' _ _ iden)
  in cons t ts' , there i' , c'

SPLIT-upwards' : {A : Type}
  (ts : List (Tree A))
  (i₀ : Index ts)
  (c₁ : Cut' (children (ts [ i₀ ])))
  → Σ[ ts' ∈ List (Tree A) ] Cut' ts'
SPLIT-upwards' (cons (node a₁ a₁ts) a₀ts) here (cut' tsL tsR iden) =
  cons tL (cons tR a₀ts) , cut' _ _ (right-of left-of)
    where
      tL = node a₁ tsL
      tR = node a₁ tsR
SPLIT-upwards' (cons a₀t a₀ts) (there i₀) c₁ =
  let ts , c = SPLIT-upwards' a₀ts i₀ c₁
  in cons a₀t ts , cons-cut a₀t c

modify-tnw : {A : Type} (ts : List (Tree A)) (i : Index ts)
   → Tree-Node-Wedge A → Σ[ ts ∈ List (Tree A) ] Σ[ i ∈ Index ts ]
   let t = ts [ i ] in Σ[ n ∈ Node t ] Wedge t n
modify-tnw (cons t ts) here ⟨ t₁ , n , w ⟩ = cons t₁ ts , here , n , w
modify-tnw (cons t ts) (there i) tnw =
  let ts^ , i^ , n^ , w^ = modify-tnw ts i tnw in cons t ts^ , there i^ , n^ , w^

SPLIT : {A : Type} (tnw : Tree-Node-Wedge A) → (o : Neighbour' tnw) → Tree-Node-Wedge A
SPLIT ⟨ node a ts , .(child i root) , w ⟩ (parent i) =
  let ts' , c' = SPLIT-upwards' ts i w
  in ⟨ node a ts' , root , c' ⟩
SPLIT ⟨ node a ts , .root , w ⟩ (child i) =
  let ts' , i' , c' = SPLIT-downwards' a ts i w
  in ⟨ node a ts' , child i' root , c' ⟩
SPLIT ⟨ node a ts , .(child i n) , w ⟩ (lift i n o) =
  let ⟨ t' , n' , w' ⟩ = SPLIT ⟨ ts [ i ] , n , w ⟩ o
      ts^ , i^ , n^ , w^ = modify-tnw ts i ⟨ t' , n' , w' ⟩
  in ⟨ node a ts^ , child i^ n^ , w^ ⟩

data Snake {A : Type} : (t : Tree A) (n : Node t) (w : Wedge t n) → Type where
  init : {a₀ a₁ : A} →
    let open Tree-Node-Wedge (INIT a₀ a₁) in Snake t n w
  split : (t' : Tree A) (n' : Node t') (w' : Wedge t' n') (o : Neighbour t' n') →
    Snake t' n' w' →
    let open Tree-Node-Wedge (SPLIT ⟨ t' , n' , w' ⟩ o) in Snake t n w

data Snake₀ {A : Type} : Type where
  snake : (t : Tree A) (w : Wedge t root) → Snake₀

data Snake-Data (L : Type) {A : Type} : (t : Tree A) (n : Node t) (w : Wedge t n) → Type
    where
  init : L → {a₀ a₁ : A} →
    let open Tree-Node-Wedge (INIT a₀ a₁) in Snake-Data L t n w
  split : L → (t' : Tree A) (n' : Node t') (w' : Wedge t' n') (o : Neighbour t' n') →
    Snake-Data L t' n' w' →
    let open Tree-Node-Wedge (SPLIT ⟨ t' , n' , w' ⟩ o) in Snake-Data L t n w

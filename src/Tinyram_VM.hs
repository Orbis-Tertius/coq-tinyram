{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Tinyram_VM where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r =
  eq_rect

xorb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
xorb b2 b3 =
  case b2 of {
   Prelude.True ->
    case b3 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True};
   Prelude.False -> b3}

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

nat_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rec =
  nat_rect

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

uncurry :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
uncurry f p =
  case p of {
   (,) x y -> f x y}

compOpp :: Prelude.Ordering -> Prelude.Ordering
compOpp r =
  case r of {
   Prelude.EQ -> Prelude.EQ;
   Prelude.LT -> Prelude.GT;
   Prelude.GT -> Prelude.LT}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

proj1_sig :: a1 -> a1
proj1_sig e =
  e

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\p -> succ (add p m))
    n

mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\p -> add m (mul p m))
    n

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> n)
    (\k ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> n)
      (\l -> sub k l)
      m)
    n

eqb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> eqb n' m')
      m)
    n

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.True)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> leb n' m')
      m)
    n

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb n m =
  leb (succ n) m

pow :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> succ 0)
    (\m0 -> mul n (pow n m0))
    m

divmod :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
          Prelude.Integer -> (,) Prelude.Integer Prelude.Integer
divmod x y q u =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (,) q u)
    (\x' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> divmod x' y (succ q) y)
      (\u' -> divmod x' y q u')
      u)
    x

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div x y =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> y)
    (\y' -> fst (divmod x y' 0 y'))
    y

modulo :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo x y =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> y)
    (\y' -> sub y' (snd (divmod x y' 0 y')))
    y

pred :: Prelude.Integer -> Prelude.Integer
pred n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> n)
    (\u -> u)
    n

add0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\p -> succ (add0 p m))
    n

mul0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\p -> add0 m (mul0 p m))
    n

sub0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> n)
    (\k ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> n)
      (\l -> sub0 k l)
      m)
    n

compare :: Prelude.Integer -> Prelude.Integer -> Prelude.Ordering
compare n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.EQ)
      (\_ -> Prelude.LT)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.GT)
      (\m' -> compare n' m')
      m)
    n

pow0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow0 n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> succ 0)
    (\m0 -> mul0 n (pow0 n m0))
    m

log2_iter :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
             Prelude.Integer -> Prelude.Integer
log2_iter k p q r =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> p)
    (\k' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> log2_iter k' (succ p) (succ q) q)
      (\r' -> log2_iter k' p (succ q) r')
      r)
    k

log2 :: Prelude.Integer -> Prelude.Integer
log2 n =
  log2_iter (pred n) 0 (succ 0) 0

log2_up :: Prelude.Integer -> Prelude.Integer
log2_up a =
  case compare (succ 0) a of {
   Prelude.LT -> succ (log2 (pred a));
   _ -> 0}

tail_plus :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
tail_plus n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\n0 -> tail_plus n0 (succ m))
    n

nth_error :: (([]) a1) -> Prelude.Integer -> Prelude.Maybe a1
nth_error l n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) x _ -> Prelude.Just x})
    (\n0 ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) _ l0 -> nth_error l0 n0})
    n

nsucc_double :: Prelude.Integer -> Prelude.Integer
nsucc_double x =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> GHC.Base.id 1)
    (\p -> GHC.Base.id (((1 Prelude.+) GHC.Base.. (2 Prelude.*)) p))
    x

ndouble :: Prelude.Integer -> Prelude.Integer
ndouble n =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> 0)
    (\p -> GHC.Base.id ((2 Prelude.*) p))
    n

succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p -> (2 Prelude.*) (succ p))
    (\p -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) p)
    (\_ -> (2 Prelude.*) 1)
    x

add1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add1 x y =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> (2 Prelude.*) (add_carry p q))
      (\q -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) (add1 p q))
      (\_ -> (2 Prelude.*) (succ p))
      y)
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) (add1 p q))
      (\q -> (2 Prelude.*) (add1 p q))
      (\_ -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) p)
      y)
    (\_ ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> (2 Prelude.*) (succ q))
      (\q -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) q)
      (\_ -> (2 Prelude.*) 1)
      y)
    x

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x y =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) (add_carry p q))
      (\q -> (2 Prelude.*) (add_carry p q))
      (\_ -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) (succ p))
      y)
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> (2 Prelude.*) (add_carry p q))
      (\q -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) (add1 p q))
      (\_ -> (2 Prelude.*) (succ p))
      y)
    (\_ ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) (succ q))
      (\q -> (2 Prelude.*) (succ q))
      (\_ -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) 1)
      y)
    x

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) ((2 Prelude.*) p))
    (\p -> ((1 Prelude.+) GHC.Base.. (2 Prelude.*)) (pred_double p))
    (\_ -> 1)
    x

data Mask =
   IsNul
 | IsPos Prelude.Integer
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos 1;
   IsPos p -> IsPos (((1 Prelude.+) GHC.Base.. (2 Prelude.*)) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos ((2 Prelude.*) p);
   x0 -> x0}

double_pred_mask :: Prelude.Integer -> Mask
double_pred_mask x =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p -> IsPos ((2 Prelude.*) ((2 Prelude.*) p)))
    (\p -> IsPos ((2 Prelude.*) (pred_double p)))
    (\_ -> IsNul)
    x

sub_mask :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask x y =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> double_mask (sub_mask p q))
      (\q -> succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((2 Prelude.*) p))
      y)
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\q -> double_mask (sub_mask p q))
      (\_ -> IsPos (pred_double p))
      y)
    (\_ ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\_ -> IsNeg)
      (\_ -> IsNeg)
      (\_ -> IsNul)
      y)
    x

sub_mask_carry :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask_carry x y =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\q -> double_mask (sub_mask p q))
      (\_ -> IsPos (pred_double p))
      y)
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> double_mask (sub_mask_carry p q))
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\_ -> double_pred_mask p)
      y)
    (\_ -> IsNeg)
    x

mul1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul1 x y =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p -> add1 y ((2 Prelude.*) (mul1 p y)))
    (\p -> (2 Prelude.*) (mul1 p y))
    (\_ -> y)
    x

iter :: (a1 -> a1) -> a1 -> Prelude.Integer -> a1
iter f x n =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\n' -> f (iter f (iter f x n') n'))
    (\n' -> iter f (iter f x n') n')
    (\_ -> f x)
    n

pow1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow1 x =
  iter (mul1 x) 1

compare_cont :: Prelude.Ordering -> Prelude.Integer -> Prelude.Integer ->
                Prelude.Ordering
compare_cont r x y =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> compare_cont r p q)
      (\q -> compare_cont Prelude.GT p q)
      (\_ -> Prelude.GT)
      y)
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> compare_cont Prelude.LT p q)
      (\q -> compare_cont r p q)
      (\_ -> Prelude.GT)
      y)
    (\_ ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\_ -> Prelude.LT)
      (\_ -> Prelude.LT)
      (\_ -> r)
      y)
    x

compare0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Ordering
compare0 =
  compare_cont Prelude.EQ

eqb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb0 p q =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p0 ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q0 -> eqb0 p0 q0)
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      q)
    (\p0 ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\_ -> Prelude.False)
      (\q0 -> eqb0 p0 q0)
      (\_ -> Prelude.False)
      q)
    (\_ ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      (\_ -> Prelude.True)
      q)
    p

iter_op :: (a1 -> a1 -> a1) -> Prelude.Integer -> a1 -> a1
iter_op op p a =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p0 -> op a (iter_op op p0 (op a a)))
    (\p0 -> iter_op op p0 (op a a))
    (\_ -> a)
    p

to_nat :: Prelude.Integer -> Prelude.Integer
to_nat x =
  iter_op add x (succ 0)

of_succ_nat :: Prelude.Integer -> Prelude.Integer
of_succ_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 1)
    (\x -> succ (of_succ_nat x))
    n

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> GHC.Base.id 1)
    (\p -> GHC.Base.id (((1 Prelude.+) GHC.Base.. (2 Prelude.*)) p))
    x

double :: Prelude.Integer -> Prelude.Integer
double n =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> 0)
    (\p -> GHC.Base.id ((2 Prelude.*) p))
    n

succ0 :: Prelude.Integer -> Prelude.Integer
succ0 n =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> GHC.Base.id 1)
    (\p -> GHC.Base.id (succ p))
    n

add2 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add2 n m =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> m)
    (\p ->
    (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
      (\_ -> n)
      (\q -> GHC.Base.id (add1 p q))
      m)
    n

sub1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub1 n m =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> 0)
    (\n' ->
    (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
      (\_ -> n)
      (\m' -> case sub_mask n' m' of {
               IsPos p -> GHC.Base.id p;
               _ -> 0})
      m)
    n

mul2 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul2 n m =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> 0)
    (\p ->
    (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
      (\_ -> 0)
      (\q -> GHC.Base.id (mul1 p q))
      m)
    n

compare1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Ordering
compare1 n m =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ ->
    (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
      (\_ -> Prelude.EQ)
      (\_ -> Prelude.LT)
      m)
    (\n' ->
    (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
      (\_ -> Prelude.GT)
      (\m' -> compare0 n' m')
      m)
    n

eqb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb1 n m =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ ->
    (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      m)
    (\p ->
    (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
      (\_ -> Prelude.False)
      (\q -> eqb0 p q)
      m)
    n

leb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb0 x y =
  case compare1 x y of {
   Prelude.GT -> Prelude.False;
   _ -> Prelude.True}

ltb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb0 x y =
  case compare1 x y of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

pow2 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow2 n p =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> GHC.Base.id 1)
    (\p0 ->
    (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
      (\_ -> 0)
      (\q -> GHC.Base.id (pow1 q p0))
      n)
    p

pos_div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
                Prelude.Integer
pos_div_eucl a b =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub1 r' b);
       Prelude.False -> (,) (double q) r'}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub1 r' b);
       Prelude.False -> (,) (double q) r'}})
    (\_ ->
    (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
      (\_ -> (,) 0 (GHC.Base.id 1))
      (\p ->
      (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
        (\_ -> (,) 0 (GHC.Base.id 1))
        (\_ -> (,) 0 (GHC.Base.id 1))
        (\_ -> (,) (GHC.Base.id 1) 0)
        p)
      b)
    a

div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
            Prelude.Integer
div_eucl a b =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> (,) 0 0)
    (\na ->
    (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
      (\_ -> (,) 0 a)
      (\_ -> pos_div_eucl na b)
      b)
    a

div0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div0 a b =
  fst (div_eucl a b)

modulo0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo0 a b =
  snd (div_eucl a b)

of_nat :: Prelude.Integer -> Prelude.Integer
of_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n' -> GHC.Base.id (of_succ_nat n'))
    n

abs_nat :: Prelude.Integer -> Prelude.Integer
abs_nat z =
  (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
    (\_ -> 0)
    (\p -> to_nat p)
    (\p -> to_nat p)
    z

to_nat0 :: Prelude.Integer -> Prelude.Integer
to_nat0 z =
  (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
    (\_ -> 0)
    (\p -> to_nat p)
    (\_ -> 0)
    z

double0 :: Prelude.Integer -> Prelude.Integer
double0 x =
  (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
    (\_ -> 0)
    (\p -> GHC.Base.id ((2 Prelude.*) p))
    (\p -> (0 Prelude.-) ((2 Prelude.*) p))
    x

succ_double0 :: Prelude.Integer -> Prelude.Integer
succ_double0 x =
  (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
    (\_ -> GHC.Base.id 1)
    (\p -> GHC.Base.id (((1 Prelude.+) GHC.Base.. (2 Prelude.*)) p))
    (\p -> (0 Prelude.-) (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
    (\_ -> (0 Prelude.-) 1)
    (\p -> GHC.Base.id (pred_double p))
    (\p -> (0 Prelude.-) (((1 Prelude.+) GHC.Base.. (2 Prelude.*)) p))
    x

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pos_sub x y =
  (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> double0 (pos_sub p q))
      (\q -> succ_double0 (pos_sub p q))
      (\_ -> GHC.Base.id ((2 Prelude.*) p))
      y)
    (\p ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> pred_double0 (pos_sub p q))
      (\q -> double0 (pos_sub p q))
      (\_ -> GHC.Base.id (pred_double p))
      y)
    (\_ ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\q -> (0 Prelude.-) ((2 Prelude.*) q))
      (\q -> (0 Prelude.-) (pred_double q))
      (\_ -> 0)
      y)
    x

add3 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add3 x y =
  (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
    (\_ -> y)
    (\x' ->
    (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
      (\_ -> x)
      (\y' -> GHC.Base.id (add1 x' y'))
      (\y' -> pos_sub x' y')
      y)
    (\x' ->
    (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
      (\_ -> x)
      (\y' -> pos_sub y' x')
      (\y' -> (0 Prelude.-) (add1 x' y'))
      y)
    x

opp :: Prelude.Integer -> Prelude.Integer
opp x =
  (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
    (\_ -> 0)
    (\x0 -> (0 Prelude.-) x0)
    (\x0 -> GHC.Base.id x0)
    x

sub2 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub2 m n =
  add3 m (opp n)

mul3 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul3 x y =
  (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
    (\_ -> 0)
    (\x' ->
    (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
      (\_ -> 0)
      (\y' -> GHC.Base.id (mul1 x' y'))
      (\y' -> (0 Prelude.-) (mul1 x' y'))
      y)
    (\x' ->
    (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
      (\_ -> 0)
      (\y' -> (0 Prelude.-) (mul1 x' y'))
      (\y' -> GHC.Base.id (mul1 x' y'))
      y)
    x

pow_pos :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow_pos z =
  iter (mul3 z) (GHC.Base.id 1)

pow3 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow3 x y =
  (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
    (\_ -> GHC.Base.id 1)
    (\p -> pow_pos x p)
    (\_ -> 0)
    y

compare2 :: Prelude.Integer -> Prelude.Integer -> Prelude.Ordering
compare2 x y =
  (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
    (\_ ->
    (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
      (\_ -> Prelude.EQ)
      (\_ -> Prelude.LT)
      (\_ -> Prelude.GT)
      y)
    (\x' ->
    (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
      (\_ -> Prelude.GT)
      (\y' -> compare0 x' y')
      (\_ -> Prelude.GT)
      y)
    (\x' ->
    (\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )
      (\_ -> Prelude.LT)
      (\_ -> Prelude.LT)
      (\y' -> compOpp (compare0 x' y'))
      y)
    x

leb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb1 x y =
  case compare2 x y of {
   Prelude.GT -> Prelude.False;
   _ -> Prelude.True}

ltb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb1 x y =
  case compare2 x y of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

of_nat0 :: Prelude.Integer -> Prelude.Integer
of_nat0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n0 -> GHC.Base.id (of_succ_nat n0))
    n

t_rect :: a2 -> (a1 -> Prelude.Integer -> (([]) a1) -> a2 -> a2) ->
          Prelude.Integer -> (([]) a1) -> a2
t_rect f f0 _ t =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> f)
    (\h n t0 -> f0 h n t0 (t_rect f f0 n t0))
    t

rectS :: (a1 -> a2) -> (a1 -> Prelude.Integer -> (([]) a1) -> a2 -> a2) ->
         Prelude.Integer -> (([]) a1) -> a2
rectS bas rect _ v =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> __)
    (\a n0 v0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
        (\_ -> bas a)
        (\_ _ _ -> __)
        v0)
      (\nn' -> rect a nn' v0 (rectS bas rect nn' v0))
      n0)
    v

case0 :: a2 -> (([]) a1) -> a2
case0 h v =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> h)
    (\_ _ _ -> __)
    v

caseS :: (a1 -> Prelude.Integer -> (([]) a1) -> a2) -> Prelude.Integer ->
         (([]) a1) -> a2
caseS h _ v =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> __)
    (\h0 n0 t -> h h0 n0 t)
    v

caseS' :: Prelude.Integer -> (([]) a1) -> (a1 -> (([]) a1) -> a2) -> a2
caseS' _ v h =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> __)
    (\h0 _ t -> h h0 t)
    v

rect2 :: a3 -> (Prelude.Integer -> (([]) a1) -> (([]) a2) -> a3 -> a1 -> a2
         -> a3) -> Prelude.Integer -> (([]) a1) -> (([]) a2) -> a3
rect2 bas rect _ v1 v2 =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> case0 bas v2)
    (\h1 n' t1 ->
    caseS' n' v2 (\h2 t2 -> rect n' t1 t2 (rect2 bas rect n' t1 t2) h1 h2))
    v1

hd :: Prelude.Integer -> (([]) a1) -> a1
hd =
  caseS (\h _ _ -> h)

last :: Prelude.Integer -> (([]) a1) -> a1
last =
  rectS (\a -> a) (\_ _ _ h -> h)

const :: a1 -> Prelude.Integer -> ([]) a1
const a =
  nat_rect [] (\n x -> (\x _ xs -> x : xs) a n x)

tl :: Prelude.Integer -> (([]) a1) -> ([]) a1
tl =
  caseS (\_ _ t -> t)

append :: Prelude.Integer -> Prelude.Integer -> (([]) a1) -> (([]) a1) ->
          ([]) a1
append _ p v w =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> w)
    (\a n0 v' -> (\x _ xs -> x : xs) a (add n0 p) (append n0 p v' w))
    v

splitat :: Prelude.Integer -> Prelude.Integer -> (([]) a1) -> (,) (([]) a1)
           (([]) a1)
splitat l r v =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (,) [] v)
    (\l' ->
    case splitat l' r
           (tl
             (let {
               add4 n m =
                 (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                   (\_ -> m)
                   (\p -> succ (add4 p m))
                   n}
              in add4 l' r) v) of {
     (,) v1 v2 -> (,) ((\x _ xs -> x : xs)
      (hd
        (let {
          add4 n m =
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ -> m)
              (\p -> succ (add4 p m))
              n}
         in add4 l' r) v) l' v1) v2})
    l

rev_append_tail :: Prelude.Integer -> Prelude.Integer -> (([]) a1) -> (([])
                   a1) -> ([]) a1
rev_append_tail _ p v w =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> w)
    (\a n0 v' -> rev_append_tail n0 (succ p) v' ((\x _ xs -> x : xs) a p w))
    v

rev_append :: Prelude.Integer -> Prelude.Integer -> (([]) a1) -> (([]) 
              a1) -> ([]) a1
rev_append n p v w =
  eq_rect_r (tail_plus n p) (rev_append_tail n p v w) (add n p)

rev :: Prelude.Integer -> (([]) a1) -> ([]) a1
rev n v =
  eq_rect_r (add n 0) (rev_append n 0 v []) n

map :: (a1 -> a2) -> Prelude.Integer -> (([]) a1) -> ([]) a2
map f _ v =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> [])
    (\a n0 v' -> (\x _ xs -> x : xs) (f a) n0 (map f n0 v'))
    v

map2 :: (a1 -> a2 -> a3) -> Prelude.Integer -> (([]) a1) -> (([]) a2) -> ([])
        a3
map2 g =
  rect2 [] (\n _ _ h a b -> (\x _ xs -> x : xs) (g a b) n h)

cast :: Prelude.Integer -> (([]) a1) -> Prelude.Integer -> ([]) a1
cast _ v n =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> [])
      (\_ -> false_rect)
      n)
    (\h n0 w ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> false_rect)
      (\n' -> (\x _ xs -> x : xs) h n' (cast n0 w n'))
      n)
    v

type Functor f =
  () -> () -> (Any -> Any) -> f -> f
  -- singleton inductive, whose constructor was Build_Functor
  
fmap :: (Functor a1) -> (a2 -> a3) -> a1 -> a1
fmap functor x x0 =
  unsafeCoerce functor __ __ x x0

data Monad m =
   Build_Monad (() -> Any -> m) (() -> () -> m -> (Any -> m) -> m)

ret :: (Monad a1) -> a2 -> a1
ret monad x =
  case monad of {
   Build_Monad ret0 _ -> unsafeCoerce ret0 __ x}

bind :: (Monad a1) -> a1 -> (a2 -> a1) -> a1
bind monad x x0 =
  case monad of {
   Build_Monad _ bind1 -> unsafeCoerce bind1 __ __ x x0}

type StateT s m a = s -> m

functor_stateT :: (Functor a1) -> Functor (StateT a2 a1 Any)
functor_stateT fm _ _ f run0 s =
  fmap fm (\sa -> (,) (fst sa) (f (snd sa))) (run0 s)

monad_stateT :: (Monad a1) -> Monad (StateT a2 a1 Any)
monad_stateT fm =
  Build_Monad (\_ a s -> ret fm ((,) s a)) (\_ _ t k s ->
    bind fm (t s) (\sa -> k (snd sa) (fst sa)))

type MonadIter m = () -> () -> (Any -> m) -> Any -> m

iter0 :: (MonadIter a1) -> (a3 -> a1) -> a3 -> a1
iter0 monadIter x x0 =
  unsafeCoerce monadIter __ __ x x0

monadIter_stateT0 :: (Monad a1) -> (MonadIter a1) -> (a4 -> StateT a2 
                     a1 (Prelude.Either a4 a3)) -> a4 -> StateT a2 a1 
                     a3
monadIter_stateT0 mM aM step i s =
  iter0 aM (\si ->
    let {s0 = fst si} in
    let {i0 = snd si} in
    bind mM (step i0 s0) (\si' ->
      ret mM
        (case snd si' of {
          Prelude.Left i' -> Prelude.Left ((,) (fst si') i');
          Prelude.Right r -> Prelude.Right ((,) (fst si') r)}))) ((,) s i)

type Id_ obj c = obj -> c

id_ :: (Id_ a1 a2) -> a1 -> a2
id_ id_1 =
  id_1

type Cat obj c = obj -> obj -> obj -> c -> c -> c

cat :: (Cat a1 a2) -> a1 -> a1 -> a1 -> a2 -> a2 -> a2
cat cat1 =
  cat1

type Bimap obj c = obj -> obj -> obj -> obj -> c -> c -> c

bimap :: (a1 -> a1 -> a1) -> (Bimap a1 a2) -> a1 -> a1 -> a1 -> a1 -> a2 ->
         a2 -> a2
bimap _ bimap0 =
  bimap0

type Case obj c = obj -> obj -> obj -> c -> c -> c

case_ :: (a1 -> a1 -> a1) -> (Case a1 a2) -> a1 -> a1 -> a1 -> a2 -> a2 -> a2
case_ _ case1 =
  case1

type Inl obj c = obj -> obj -> c

inl_ :: (a1 -> a1 -> a1) -> (Inl a1 a2) -> a1 -> a1 -> a2
inl_ _ inl =
  inl

type Inr obj c = obj -> obj -> c

inr_ :: (a1 -> a1 -> a1) -> (Inr a1 a2) -> a1 -> a1 -> a2
inr_ _ inr =
  inr

bimap_Coproduct :: (Cat a1 a2) -> (a1 -> a1 -> a1) -> (Case a1 a2) -> (Inl 
                   a1 a2) -> (Inr a1 a2) -> Bimap a1 a2
bimap_Coproduct cat_C sUM coprod_SUM inl_SUM inr_SUM a b c d f g =
  case_ sUM coprod_SUM a b (sUM c d)
    (cat cat_C a c (sUM c d) f (inl_ sUM inl_SUM c d))
    (cat cat_C b d (sUM c d) g (inr_ sUM inr_SUM c d))

type ReSum obj c = c

resum :: a1 -> a1 -> (ReSum a1 a2) -> a2
resum _ _ reSum =
  reSum

reSum_id :: (Id_ a1 a2) -> a1 -> ReSum a1 a2
reSum_id =
  id_

reSum_inl :: (a1 -> a1 -> a1) -> (Cat a1 a2) -> (Inl a1 a2) -> a1 -> a1 -> a1
             -> (ReSum a1 a2) -> ReSum a1 a2
reSum_inl bif h0 h2 a b c h4 =
  cat h0 a b (bif b c) (resum a b h4) (inl_ bif h2 b c)

reSum_inr :: (a1 -> a1 -> a1) -> (Cat a1 a2) -> (Inr a1 a2) -> a1 -> a1 -> a1
             -> (ReSum a1 a2) -> ReSum a1 a2
reSum_inr bif h0 h3 a b c h4 =
  cat h0 a b (bif c b) (resum a b h4) (inr_ bif h3 c b)

data ItreeF e r itree =
   RetF r
 | TauF itree
 | VisF e (Any -> itree)

data Itree e r =
   Go (ItreeF e r (Itree e r))

_observe :: (Itree a1 a2) -> ItreeF a1 a2 (Itree a1 a2)
_observe i =
  case i of {
   Go _observe0 -> _observe0}

observe :: (Itree a1 a2) -> ItreeF a1 a2 (Itree a1 a2)
observe =
  _observe

subst :: (a2 -> Itree a1 a3) -> (Itree a1 a2) -> Itree a1 a3
subst k u =
  case observe u of {
   RetF r -> k r;
   TauF t -> Go (TauF (subst k t));
   VisF e h -> Go (VisF e (\x -> subst k (h x)))}

bind0 :: (Itree a1 a2) -> (a2 -> Itree a1 a3) -> Itree a1 a3
bind0 u k =
  subst k u

iter1 :: (a3 -> Itree a1 (Prelude.Either a3 a2)) -> a3 -> Itree a1 a2
iter1 step i =
  bind0 (step i) (\lr ->
    case lr of {
     Prelude.Left l -> Go (TauF (iter1 step l));
     Prelude.Right r -> Go (RetF r)})

map0 :: (a2 -> a3) -> (Itree a1 a2) -> Itree a1 a3
map0 f t =
  bind0 t (\x -> Go (RetF (f x)))

trigger :: a1 -> Itree a1 a2
trigger e =
  Go (VisF e (\x -> Go (RetF (unsafeCoerce x))))

functor_itree :: Functor (Itree a1 Any)
functor_itree _ _ =
  map0

monad_itree :: Monad (Itree a1 Any)
monad_itree =
  Build_Monad (\_ x -> Go (RetF x)) (\_ _ -> bind0)

monadIter_itree :: (a3 -> Itree a1 (Prelude.Either a3 a2)) -> a3 -> Itree 
                   a1 a2
monadIter_itree =
  iter1

data Sum1 e1 e2 x =
   Inl1 e1
 | Inr1 e2

type IFun e f = () -> e -> f

id_IFun :: a1 -> a1
id_IFun e =
  e

cat_IFun :: (IFun a1 a2) -> (IFun a2 a3) -> a1 -> a3
cat_IFun f1 f2 e =
  f2 __ (f1 __ e)

case_sum1 :: (() -> a1 -> a3) -> (() -> a2 -> a3) -> (Sum1 a1 a2 a4) -> a3
case_sum1 f g ab =
  case ab of {
   Inl1 a -> f __ a;
   Inr1 b -> g __ b}

case_sum0 :: (IFun a1 a3) -> (IFun a2 a3) -> (Sum1 a1 a2 a4) -> a3
case_sum0 =
  case_sum1

inl_sum1 :: a1 -> Sum1 a1 a2 a3
inl_sum1 x =
  Inl1 x

inr_sum1 :: a2 -> Sum1 a1 a2 a3
inr_sum1 x =
  Inr1 x

subevent :: (IFun a1 a2) -> a1 -> a2
subevent h x =
  resum __ __ h __ x

type Embeddable u v = u -> v

embed :: (Embeddable a1 a2) -> a1 -> a2
embed embeddable =
  embeddable

embeddable_forall :: (a1 -> Embeddable a2 a3) -> Embeddable (a1 -> a2)
                     (a1 -> a3)
embeddable_forall h u a =
  embed (h a) (u a)

embeddable_itree :: (IFun a1 a2) -> Embeddable a1 (Itree a2 a3)
embeddable_itree h e =
  trigger (subevent h e)

interp :: (Functor a2) -> (Monad a2) -> (MonadIter a2) -> (() -> a1 -> a2) ->
          (Itree a1 a3) -> a2
interp fM mM iM h =
  iter0 iM (\t ->
    case observe t of {
     RetF r -> ret mM (Prelude.Right r);
     TauF t0 -> ret mM (Prelude.Left t0);
     VisF e k -> fmap fM (\x -> Prelude.Left (k x)) (h __ e)})

htrigger :: (() -> a1 -> a2) -> a1 -> Itree a2 a3
htrigger m e =
  trigger (m __ e)

id_0 :: a1 -> Itree a1 a2
id_0 =
  trigger

cat0 :: (() -> a1 -> Itree a2 Any) -> (() -> a2 -> Itree a3 Any) -> a1 ->
        Itree a3 a4
cat0 f g e =
  interp (unsafeCoerce functor_itree) (unsafeCoerce monad_itree)
    (unsafeCoerce (\_ _ -> monadIter_itree)) (unsafeCoerce g) (f __ e)

inl_0 :: a1 -> Itree (Sum1 a1 a2 Any) a3
inl_0 x =
  htrigger (unsafeCoerce (\_ x0 -> Inl1 x0)) x

inr_0 :: a2 -> Itree (Sum1 a1 a2 Any) a3
inr_0 x =
  htrigger (unsafeCoerce (\_ x0 -> Inr1 x0)) x

case_0 :: (() -> a1 -> Itree a3 Any) -> (() -> a2 -> Itree a3 Any) -> (Sum1
          a1 a2 a4) -> Itree a3 a4
case_0 f g ab =
  case ab of {
   Inl1 a -> unsafeCoerce f __ a;
   Inr1 b -> unsafeCoerce g __ b}

type Handler e f = () -> e -> Itree f Any

id_Handler :: a1 -> Itree a1 a2
id_Handler =
  id_0

cat_Handler :: (Handler a1 a2) -> (Handler a2 a3) -> a1 -> Itree a3 a4
cat_Handler =
  cat0

case_sum1_Handler :: (Handler a1 a3) -> (Handler a2 a3) -> (Sum1 a1 a2 
                     a4) -> Itree a3 a4
case_sum1_Handler =
  case_0

inl_sum1_Handler :: a1 -> Itree (Sum1 a1 a2 Any) a3
inl_sum1_Handler =
  inl_0

inr_sum1_Handler :: a2 -> Itree (Sum1 a1 a2 Any) a3
inr_sum1_Handler =
  inr_0

lt_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lt_sub n m =
  nat_rec (\_ _ -> Prelude.error "absurd case") (\m0 iHm n0 _ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> succ m0)
      (\n1 -> iHm n1 __)
      n0) m n __

le_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
le_sub n m =
  nat_rec (\_ _ -> 0) (\m0 iHm n0 _ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> succ m0)
      (\n1 -> iHm n1 __)
      n0) m n __

type Fin = Prelude.Integer

fin_add :: Prelude.Integer -> Prelude.Integer -> Fin -> Fin -> Fin
fin_add _ _ =
  add0

fin_cast :: Prelude.Integer -> Prelude.Integer -> Fin -> Fin
fin_cast _ _ x =
  x

fin_max :: Prelude.Integer -> Fin
fin_max n =
  n

interp_state :: (Functor a2) -> (Monad a2) -> (MonadIter a2) -> (() -> a1 ->
                StateT a3 a2 Any) -> (Itree a1 a4) -> StateT a3 a2 a4
interp_state fM mM iM h x x0 =
  interp (functor_stateT fM) (monad_stateT mM) (\_ _ ->
    monadIter_stateT0 mM iM) h x x0

data StateE s x =
   Get
 | Put s

get :: (IFun (StateE a1 Any) a2) -> Itree a2 a1
get h =
  embed (embeddable_itree h) Get

put :: (IFun (StateE a1 Any) a2) -> a1 -> Itree a2 ()
put h =
  embed (embeddable_forall (\_ -> embeddable_itree h)) (\x -> Put x)

h_state :: (StateE a1 a3) -> a1 -> Itree a2 ((,) a1 a3)
h_state e s =
  case e of {
   Get -> Go (RetF ((,) s (unsafeCoerce s)));
   Put s' -> Go (RetF ((,) s' (unsafeCoerce ())))}

pure_state :: a2 -> a1 -> Itree a2 ((,) a1 a3)
pure_state e s =
  Go (VisF e (\x -> Go (RetF ((,) s (unsafeCoerce x)))))

run_state :: (Itree (Sum1 (StateE a1 Any) a2 Any) a3) -> a1 -> Itree 
             a2 ((,) a1 a3)
run_state x x0 =
  interp_state (unsafeCoerce functor_itree) (unsafeCoerce monad_itree)
    (unsafeCoerce (\_ _ -> monadIter_itree))
    (case_ __ (unsafeCoerce (\_ _ _ x1 x2 _ -> case_sum0 x1 x2)) __ __ __
      (unsafeCoerce (\_ -> h_state)) (unsafeCoerce (\_ -> pure_state))) x x0

vector_cons_split :: Prelude.Integer -> (([]) a1) -> SigT a1 (([]) a1)
vector_cons_split n v =
  ExistT (hd n v) (tl n v)

replace :: Prelude.Integer -> (([]) a1) -> Fin -> a1 -> ([]) a1
replace n =
  nat_rect (\_ _ _ -> []) (\n0 iHn v p0 a ->
    let {s = vector_cons_split n0 v} in
    case s of {
     ExistT vhd s0 ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> (\x _ xs -> x : xs) a n0 s0)
        (\p -> (\x _ xs -> x : xs) vhd n0 (iHn s0 p a))
        p0}) n

nth :: Prelude.Integer -> (([]) a1) -> Fin -> a1
nth n =
  nat_rect (\_ _ -> Prelude.error "absurd case") (\n0 iHn v p0 ->
    let {s = vector_cons_split n0 v} in
    case s of {
     ExistT vhd s0 ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> vhd)
        (\p -> iHn s0 p)
        p0}) n

vector_concat :: Prelude.Integer -> Prelude.Integer -> (([]) (([]) a1)) ->
                 ([]) a1
vector_concat n m v =
  t_rect [] (\h n0 _ iHv -> append n (mul n0 n) h iHv) m v

vector_unconcat :: Prelude.Integer -> Prelude.Integer -> (([]) a1) -> ([])
                   (([]) a1)
vector_unconcat n m v =
  nat_rect (\_ -> []) (\m0 iHm v0 ->
    let {p = splitat n (mul m0 n) v0} in
    case p of {
     (,) vv1 vvtl -> (\x _ xs -> x : xs) vv1 m0 (iHm vvtl)}) m v

block_Lem :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
             Prelude.Either Prelude.Integer
             (SigT Prelude.Integer (SigT Prelude.Integer Prelude.Integer))
block_Lem idx blksz memsz =
  let {lm_ib = ltb memsz (add idx blksz)} in
  case lm_ib of {
   Prelude.True ->
    let {s = lt_sub memsz (add idx blksz)} in
    Prelude.Right (ExistT s
    (let {s0 = lt_sub idx memsz} in ExistT s0 (lt_sub s idx)));
   Prelude.False -> Prelude.Left (le_sub (add idx blksz) memsz)}

block_Load :: Prelude.Integer -> (([]) a1) -> Fin -> Fin -> ([]) a1
block_Load memsz m idx0 blksz0 =
  let {s = block_Lem idx0 blksz0 memsz} in
  case s of {
   Prelude.Left s0 ->
    let {m0 = eq_rect memsz m (add (add idx0 blksz0) s0)} in
    let {p = splitat (add idx0 blksz0) s0 m0} in
    case p of {
     (,) m' _ ->
      let {p0 = splitat idx0 blksz0 m'} in case p0 of {
                                            (,) _ m2 -> m2}};
   Prelude.Right s0 ->
    case s0 of {
     ExistT blk1 s1 ->
      case s1 of {
       ExistT blk2 s2 ->
        let {m0 = eq_rect memsz m (add (add blk1 s2) blk2)} in
        let {p = splitat (add blk1 s2) blk2 m0} in
        case p of {
         (,) m' m3 ->
          let {p0 = splitat blk1 s2 m'} in
          case p0 of {
           (,) m1 _ ->
            cast (add blk1 blk2)
              (eq_rect_r (add0 blk2 blk1) (append blk2 blk1 m3 m1)
                (add0 blk1 blk2)) blksz0}}}}}

block_Store :: Prelude.Integer -> (([]) a1) -> Fin -> Fin -> (([]) a1) ->
               ([]) a1
block_Store memsz m idx0 blksz0 block =
  let {s = block_Lem idx0 blksz0 memsz} in
  case s of {
   Prelude.Left s0 ->
    let {m0 = eq_rect memsz m (add (add idx0 blksz0) s0)} in
    let {p = splitat (add idx0 blksz0) s0 m0} in
    case p of {
     (,) m' m3 ->
      let {p0 = splitat idx0 blksz0 m'} in
      case p0 of {
       (,) m1 _ ->
        eq_rect_r (add (add idx0 blksz0) s0)
          (append (add idx0 (proj1_sig blksz0)) s0
            (append idx0 (proj1_sig blksz0) m1 block) m3) memsz}};
   Prelude.Right s0 ->
    case s0 of {
     ExistT blk2 s1 ->
      case s1 of {
       ExistT blk1 s2 ->
        let {m0 = eq_rect memsz m (add (add blk2 s2) blk1)} in
        let {p = splitat (add blk2 s2) blk1 m0} in
        case p of {
         (,) m' _ ->
          let {p0 = splitat blk2 s2 m'} in
          case p0 of {
           (,) _ m2 ->
            let {block0 = eq_rect_r blksz0 block (add blk2 blk1)} in
            let {block1 = eq_rect (add0 blk2 blk1) block0 (add0 blk1 blk2)}
            in
            let {p1 = splitat blk1 blk2 block1} in
            case p1 of {
             (,) block2 block3 ->
              eq_rect_r (add (add blk2 s2) blk1)
                (append (add blk2 s2) blk1 (append blk2 s2 block3 m2) block2)
                memsz}}}}}}

b1 :: Prelude.Bool
b1 =
  Prelude.True

b0 :: Prelude.Bool
b0 =
  Prelude.False

bitValN :: Prelude.Bool -> Prelude.Integer
bitValN b =
  case b of {
   Prelude.True -> succ 0;
   Prelude.False -> 0}

type Byte = ([]) Prelude.Bool

iffb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
iffb b2 v2 =
  case b2 of {
   Prelude.True -> v2;
   Prelude.False ->
    case v2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

bv_eq :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
         Prelude.Bool
bv_eq n =
  rect2 Prelude.True (\_ _ _ r x y -> (Prelude.&&) (iffb x y) r) n

bv_and :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
          ([]) Prelude.Bool
bv_and n v1 v2 =
  map2 (Prelude.&&) n v1 v2

bv_or :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
         ([]) Prelude.Bool
bv_or n v1 v2 =
  map2 (Prelude.||) n v1 v2

bv_xor :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
          ([]) Prelude.Bool
bv_xor n v1 v2 =
  map2 xorb n v1 v2

bv_not :: Prelude.Integer -> (([]) Prelude.Bool) -> ([]) Prelude.Bool
bv_not n b =
  map Prelude.not n b

bitvector_fin_big :: Prelude.Integer -> (([]) Prelude.Bool) -> Fin
bitvector_fin_big n v =
  t_rect 0 (\h n0 _ iHv ->
    case h of {
     Prelude.True ->
      let {f2 = fin_max (pow (succ (succ 0)) n0)} in
      fin_cast
        (sub (add (pow (succ (succ 0)) n0) (succ (pow (succ (succ 0)) n0)))
          (succ 0)) (pow (succ (succ 0)) (succ n0))
        (fin_add (pow (succ (succ 0)) n0) (succ (pow (succ (succ 0)) n0)) iHv
          f2);
     Prelude.False ->
      fin_cast (pow (succ (succ 0)) n0) (pow (succ (succ 0)) (succ n0)) iHv})
    n v

bitvector_nat_big :: Prelude.Integer -> (([]) Prelude.Bool) ->
                     Prelude.Integer
bitvector_nat_big n v =
  proj1_sig (bitvector_fin_big n v)

nat_bitvector_big :: Prelude.Integer -> Prelude.Integer -> ([]) Prelude.Bool
nat_bitvector_big n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> [])
    (\n0 -> (\x _ xs -> x : xs)
    (Prelude.not (eqb (div m (pow (succ (succ 0)) n0)) 0)) n0
    (nat_bitvector_big n0 (modulo m (pow (succ (succ 0)) n0))))
    n

fin_bitvector_big :: Prelude.Integer -> Fin -> ([]) Prelude.Bool
fin_bitvector_big =
  nat_bitvector_big

positive_bitvector_little :: Prelude.Integer -> Prelude.Integer -> ([])
                             Prelude.Bool
positive_bitvector_little n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> [])
    (\n0 ->
    (\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )
      (\p -> (\x _ xs -> x : xs) b1 n0
      (positive_bitvector_little n0 p))
      (\p -> (\x _ xs -> x : xs) b0 n0
      (positive_bitvector_little n0 p))
      (\_ -> (\x _ xs -> x : xs) b1 n0 (const b0 n0))
      m)
    n

n_bitvector_little :: Prelude.Integer -> Prelude.Integer -> ([]) Prelude.Bool
n_bitvector_little n m =
  (\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)
    (\_ -> const b0 n)
    (\p -> positive_bitvector_little n p)
    m

bitvector_N_little :: Prelude.Integer -> (([]) Prelude.Bool) ->
                      Prelude.Integer
bitvector_N_little _ v =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> 0)
    (\hd0 n0 tl0 ->
    case hd0 of {
     Prelude.True -> nsucc_double (bitvector_N_little n0 tl0);
     Prelude.False -> ndouble (bitvector_N_little n0 tl0)})
    v

n_bitvector_big :: Prelude.Integer -> Prelude.Integer -> ([]) Prelude.Bool
n_bitvector_big n m =
  rev n (n_bitvector_little n m)

bitvector_N_big :: Prelude.Integer -> (([]) Prelude.Bool) -> Prelude.Integer
bitvector_N_big n v =
  bitvector_N_little n (rev n v)

bv_add :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
          ([]) Prelude.Bool
bv_add n v1 v2 =
  n_bitvector_big (succ n)
    (add2 (bitvector_N_big n v1) (bitvector_N_big n v2))

bv_sub :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
          ([]) Prelude.Bool
bv_sub n v1 v2 =
  n_bitvector_big (succ n)
    (sub1
      (add2 (bitvector_N_big n v1)
        (pow2 (GHC.Base.id ((2 Prelude.*) 1)) (of_nat n)))
      (bitvector_N_big n v2))

bv_mul_flags :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool)
                -> (,)
                ((,) ((,) Prelude.Bool Prelude.Bool) (([]) Prelude.Bool))
                (([]) Prelude.Bool)
bv_mul_flags n v1 v2 =
  let {prod = mul2 (bitvector_N_big n v1) (bitvector_N_big n v2)} in
  case splitat n n (n_bitvector_big (add n n) prod) of {
   (,) pvH pvL -> (,) ((,) ((,)
    (leb0 (pow2 (GHC.Base.id ((2 Prelude.*) 1)) (of_nat n)) prod)
    (eqb1 prod 0)) pvH) pvL}

bv_mul :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
          ([]) Prelude.Bool
bv_mul n v1 v2 =
  let {x = bv_mul_flags n v1 v2} in append n n (snd (fst x)) (snd x)

bv_udiv_flag :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool)
                -> (,) Prelude.Bool (([]) Prelude.Bool)
bv_udiv_flag n v1 v2 =
  let {den = bitvector_N_big n v2} in
  (,) (eqb1 den 0) (n_bitvector_big n (div0 (bitvector_N_big n v1) den))

bv_udiv :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
           ([]) Prelude.Bool
bv_udiv n v1 v2 =
  snd (bv_udiv_flag n v1 v2)

bv_umod_flag :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool)
                -> (,) Prelude.Bool (([]) Prelude.Bool)
bv_umod_flag n v1 v2 =
  let {bas = bitvector_N_big n v2} in
  (,) (eqb1 bas 0) (n_bitvector_big n (modulo0 (bitvector_N_big n v1) bas))

bv_umod :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
           ([]) Prelude.Bool
bv_umod n v1 v2 =
  snd (bv_umod_flag n v1 v2)

bv_shl :: Prelude.Integer -> Prelude.Integer -> (([]) Prelude.Bool) -> ([])
          Prelude.Bool
bv_shl n m v =
  let {b = leb m n} in
  case b of {
   Prelude.True ->
    eq_rect (add0 (sub0 n m) m)
      (append (sub0 n m) m
        (snd (splitat m (sub0 n m) (eq_rec_r n v (add m (sub n m)))))
        (const b0 m)) n;
   Prelude.False -> const b0 n}

bv_shr :: Prelude.Integer -> Prelude.Integer -> (([]) Prelude.Bool) -> ([])
          Prelude.Bool
bv_shr n m v =
  let {b = leb m n} in
  case b of {
   Prelude.True ->
    eq_rect (add m (sub n m))
      (append m (sub n m) (const b0 m)
        (let {v0 = eq_rec_r n v (add m (sub n m))} in
         let {v1 = eq_rect (add0 m (sub n m)) v0 (add0 (sub n m) m)} in
         case splitat (sub n m) m v1 of {
          (,) x _ -> x})) n;
   Prelude.False -> const b0 n}

twos_complement' :: Prelude.Integer -> (([]) Prelude.Bool) -> Prelude.Integer
twos_complement' n v =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> 0)
    (\x n0 xs ->
    add (mul (bitValN x) (pow (succ (succ 0)) (sub n (succ 0))))
      (twos_complement' n0 xs))
    v

twos_complement :: Prelude.Integer -> (([]) Prelude.Bool) -> Prelude.Integer
twos_complement n v =
  (\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)
    (\_ -> __)
    (\x n0 xs ->
    sub2 (of_nat0 (twos_complement' n0 xs))
      (of_nat0 (mul (bitValN x) (pow (succ (succ 0)) n))))
    v

twos_complement_inv :: Prelude.Integer -> Prelude.Integer -> ([])
                       Prelude.Bool
twos_complement_inv n z =
  case ltb1 z 0 of {
   Prelude.True ->
    nat_bitvector_big (succ n)
      (to_nat0
        (add3 z (pow3 (GHC.Base.id ((2 Prelude.*) 1)) (of_nat0 (succ n)))));
   Prelude.False -> nat_bitvector_big (succ n) (to_nat0 z)}

bv_abs :: Prelude.Integer -> (([]) Prelude.Bool) -> ([]) Prelude.Bool
bv_abs n v =
  nat_bitvector_big n (abs_nat (twos_complement n v))

bv_lt :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
         Prelude.Bool
bv_lt n u v =
  ltb0 (bitvector_N_big n u) (bitvector_N_big n v)

bv_le :: Prelude.Integer -> (([]) Prelude.Bool) -> (([]) Prelude.Bool) ->
         Prelude.Bool
bv_le n u v =
  leb0 (bitvector_N_big n u) (bitvector_N_big n v)

bv_succ :: Prelude.Integer -> (([]) Prelude.Bool) -> ([]) Prelude.Bool
bv_succ n v =
  n_bitvector_big n
    (modulo0 (succ0 (bitvector_N_big n v))
      (pow2 (GHC.Base.id ((2 Prelude.*) 1)) (of_nat n)))

wordSizeEighth :: Prelude.Integer
wordSizeEighth =
  succ (succ 0)

registerCount :: Prelude.Integer
registerCount =
  succ (succ (succ (succ 0)))

wordSize :: Prelude.Integer
wordSize =
  mul0 wordSizeEighth (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))

wordSizeEighthFin :: Fin
wordSizeEighthFin =
  wordSizeEighth

pcIncrement :: Prelude.Integer
pcIncrement =
  mul0 (succ (succ 0)) wordSizeEighth

type RegId = Fin

type Word = ([]) Prelude.Bool

wcast :: Word -> ([]) Prelude.Bool
wcast v =
  cast wordSize v (succ (pred wordSize))

wuncast :: (([]) Prelude.Bool) -> ([]) Prelude.Bool
wuncast v =
  cast (succ (pred wordSize)) v wordSize

wbcast :: (([]) a1) -> ([]) a1
wbcast v =
  eq_rect wordSize v
    (add0
      (sub0 wordSize (succ (succ (succ (succ (succ (succ (succ (succ
        0))))))))) (succ (succ (succ (succ (succ (succ (succ (succ 0)))))))))

wbuncast :: (([]) a1) -> ([]) a1
wbuncast v =
  eq_rect_r
    (add0
      (sub0 wordSize (succ (succ (succ (succ (succ (succ (succ (succ
        0))))))))) (succ (succ (succ (succ (succ (succ (succ (succ 0)))))))))
    v wordSize

wordBytes :: Word -> ([]) Byte
wordBytes r =
  vector_unconcat (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))
    wordSizeEighth r

bytesWord :: (([]) Byte) -> Word
bytesWord v =
  vector_concat (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))
    wordSizeEighth v

type Address = Fin

type Register = Fin

type Program = ([]) ((,) Word Word)

type Tape = ([]) Word

type Registers = ([]) Word

paddingSize :: Prelude.Integer
paddingSize =
  sub (sub wordSize (succ (succ (succ (succ (succ (succ 0)))))))
    (mul (succ (succ 0)) (log2_up registerCount))

interpSplit :: Word -> (,)
               ((,)
               ((,) ((,) (([]) Prelude.Bool) Prelude.Bool)
               (([]) Prelude.Bool)) (([]) Prelude.Bool)) (([]) Prelude.Bool)
interpSplit w =
  let {
   w0 = eq_rect wordSize w
          (add
            (add
              (add (add (succ (succ (succ (succ (succ 0))))) (succ 0))
                (log2_up registerCount)) (log2_up registerCount))
            paddingSize)}
  in
  let {
   w1 = splitat
          (add
            (add (add (succ (succ (succ (succ (succ 0))))) (succ 0))
              (log2_up registerCount)) (log2_up registerCount)) paddingSize
          w0}
  in
  case w1 of {
   (,) w2 f5 -> (,)
    (let {
      w3 = splitat
             (add (add (succ (succ (succ (succ (succ 0))))) (succ 0))
               (log2_up registerCount)) (log2_up registerCount) w2}
     in
     case w3 of {
      (,) w4 f4 -> (,)
       (let {
         w5 = splitat (add (succ (succ (succ (succ (succ 0))))) (succ 0))
                (log2_up registerCount) w4}
        in
        case w5 of {
         (,) w6 f3 -> (,)
          (let {
            w7 = splitat (succ (succ (succ (succ (succ 0))))) (succ 0) w6}
           in
           case w7 of {
            (,) f1 f2 -> (,) f1
             (let {s = vector_cons_split 0 f2} in
              case s of {
               ExistT b _ -> b})}) f3}) f4}) f5}

data InstructionI =
   AndI RegId RegId
 | OrI RegId RegId
 | XorI RegId RegId
 | NotI RegId
 | AddI RegId RegId
 | SubI RegId RegId
 | MullI RegId RegId
 | UmulhI RegId RegId
 | SmulhI RegId RegId
 | UdivI RegId RegId
 | UmodI RegId RegId
 | ShlI RegId RegId
 | ShrI RegId RegId
 | CmpeI RegId
 | CmpaI RegId
 | CmpaeI RegId
 | CmpgI RegId
 | CmpgeI RegId
 | MovI RegId
 | CmovI RegId
 | JmpI
 | CjmpI
 | CnjmpI
 | Store_bI RegId
 | Load_bI RegId
 | Store_wI RegId
 | Load_wI RegId
 | ReadI RegId
 | AnswerI

type Operand = Prelude.Either Word RegId

type Instruction = (,) InstructionI Operand

ijTr :: (RegId -> RegId -> InstructionI) -> RegId -> RegId -> Operand ->
        Instruction
ijTr con ri rj a =
  (,) (con ri rj) a

iTr :: (RegId -> InstructionI) -> RegId -> Operand -> Instruction
iTr con ri a =
  (,) (con ri) a

tr :: InstructionI -> Operand -> Instruction
tr con a =
  (,) con a

oreg :: Prelude.Integer -> (([]) Prelude.Bool) -> Prelude.Maybe RegId
oreg n v =
  let {f = bitvector_fin_big n v} in
  let {b = ltb f registerCount} in
  case b of {
   Prelude.True -> Prelude.Just f;
   Prelude.False -> Prelude.Nothing}

reg2pow :: (([]) Prelude.Bool) -> RegId
reg2pow v =
  bitvector_fin_big (log2_up registerCount) v

regFit :: Prelude.Integer -> (([]) Prelude.Bool) -> RegId
regFit n v =
  proj1_sig (bitvector_fin_big n v)

answer1 :: Instruction
answer1 =
  (,) AnswerI (Prelude.Left (fin_bitvector_big wordSize (succ 0)))

instructionDecodeA :: (Operand -> Instruction) -> Prelude.Bool -> Word ->
                      (Prelude.Maybe RegId) -> Instruction
instructionDecodeA code isReg w2 w2reg =
  case isReg of {
   Prelude.True -> code (Prelude.Left w2);
   Prelude.False ->
    case w2reg of {
     Prelude.Just w2reg0 -> code (Prelude.Right w2reg0);
     Prelude.Nothing -> answer1}}

instructionDecodeRiA :: (RegId -> Operand -> Instruction) -> Prelude.Bool ->
                        (Prelude.Maybe RegId) -> Word -> (Prelude.Maybe
                        RegId) -> Instruction
instructionDecodeRiA code isReg ri w2 w2reg =
  case ri of {
   Prelude.Just ri0 ->
    case isReg of {
     Prelude.True -> code ri0 (Prelude.Left w2);
     Prelude.False ->
      case w2reg of {
       Prelude.Just w2reg0 -> code ri0 (Prelude.Right w2reg0);
       Prelude.Nothing -> answer1}};
   Prelude.Nothing -> answer1}

instructionDecodeRiRjA :: (RegId -> RegId -> Operand -> Instruction) ->
                          Prelude.Bool -> (Prelude.Maybe RegId) ->
                          (Prelude.Maybe RegId) -> Word -> (Prelude.Maybe
                          RegId) -> Instruction
instructionDecodeRiRjA code isReg ri rj w2 w2reg =
  case ri of {
   Prelude.Just ri0 ->
    case rj of {
     Prelude.Just rj0 ->
      case isReg of {
       Prelude.True -> code ri0 rj0 (Prelude.Left w2);
       Prelude.False ->
        case w2reg of {
         Prelude.Just w2reg0 -> code ri0 rj0 (Prelude.Right w2reg0);
         Prelude.Nothing -> answer1}};
     Prelude.Nothing -> answer1};
   Prelude.Nothing -> answer1}

instructionDecode :: Word -> Word -> Instruction
instructionDecode w1 w2 =
  case interpSplit w1 of {
   (,) p _ ->
    case p of {
     (,) p0 prj ->
      case p0 of {
       (,) p1 pri ->
        case p1 of {
         (,) op isReg ->
          let {ri = oreg (log2_up registerCount) pri} in
          let {rj = oreg (log2_up registerCount) prj} in
          let {ow = oreg wordSize w2} in
          (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
            (\_ ->
            instructionDecodeRiRjA (ijTr (\x x0 -> AndI x x0)) isReg ri rj w2
              ow)
            (\n ->
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              instructionDecodeRiRjA (ijTr (\x x0 -> OrI x x0)) isReg ri rj
                w2 ow)
              (\n0 ->
              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                (\_ ->
                instructionDecodeRiRjA (ijTr (\x x0 -> XorI x x0)) isReg ri
                  rj w2 ow)
                (\n1 ->
                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                  (\_ ->
                  instructionDecodeRiA (iTr (\x -> NotI x)) isReg ri w2 ow)
                  (\n2 ->
                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                    (\_ ->
                    instructionDecodeRiRjA (ijTr (\x x0 -> AddI x x0)) isReg
                      ri rj w2 ow)
                    (\n3 ->
                    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                      (\_ ->
                      instructionDecodeRiRjA (ijTr (\x x0 -> SubI x x0))
                        isReg ri rj w2 ow)
                      (\n4 ->
                      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                        (\_ ->
                        instructionDecodeRiRjA (ijTr (\x x0 -> MullI x x0))
                          isReg ri rj w2 ow)
                        (\n5 ->
                        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                          (\_ ->
                          instructionDecodeRiRjA
                            (ijTr (\x x0 -> UmulhI x x0)) isReg ri rj w2 ow)
                          (\n6 ->
                          (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                            (\_ ->
                            instructionDecodeRiRjA
                              (ijTr (\x x0 -> SmulhI x x0)) isReg ri rj w2 ow)
                            (\n7 ->
                            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                              (\_ ->
                              instructionDecodeRiRjA
                                (ijTr (\x x0 -> UdivI x x0)) isReg ri rj w2
                                ow)
                              (\n8 ->
                              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                (\_ ->
                                instructionDecodeRiRjA
                                  (ijTr (\x x0 -> UmodI x x0)) isReg ri rj w2
                                  ow)
                                (\n9 ->
                                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                  (\_ ->
                                  instructionDecodeRiRjA
                                    (ijTr (\x x0 -> ShlI x x0)) isReg ri rj
                                    w2 ow)
                                  (\n10 ->
                                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                    (\_ ->
                                    instructionDecodeRiRjA
                                      (ijTr (\x x0 -> ShrI x x0)) isReg ri rj
                                      w2 ow)
                                    (\n11 ->
                                    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                      (\_ ->
                                      instructionDecodeRiA
                                        (iTr (\x -> CmpeI x)) isReg rj w2 ow)
                                      (\n12 ->
                                      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                        (\_ ->
                                        instructionDecodeRiA
                                          (iTr (\x -> CmpaI x)) isReg rj w2
                                          ow)
                                        (\n13 ->
                                        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                          (\_ ->
                                          instructionDecodeRiA
                                            (iTr (\x -> CmpaeI x)) isReg rj
                                            w2 ow)
                                          (\n14 ->
                                          (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                            (\_ ->
                                            instructionDecodeRiA
                                              (iTr (\x -> CmpgI x)) isReg rj
                                              w2 ow)
                                            (\n15 ->
                                            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                              (\_ ->
                                              instructionDecodeRiA
                                                (iTr (\x -> CmpgeI x)) isReg
                                                rj w2 ow)
                                              (\n16 ->
                                              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                (\_ ->
                                                instructionDecodeRiA
                                                  (iTr (\x -> MovI x)) isReg
                                                  ri w2 ow)
                                                (\n17 ->
                                                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                  (\_ ->
                                                  instructionDecodeRiA
                                                    (iTr (\x -> CmovI x))
                                                    isReg ri w2 ow)
                                                  (\n18 ->
                                                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                    (\_ ->
                                                    instructionDecodeA
                                                      (tr JmpI) isReg w2 ow)
                                                    (\n19 ->
                                                    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                      (\_ ->
                                                      instructionDecodeA
                                                        (tr CjmpI) isReg w2
                                                        ow)
                                                      (\n20 ->
                                                      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                        (\_ ->
                                                        instructionDecodeA
                                                          (tr CnjmpI) isReg
                                                          w2 ow)
                                                        (\n21 ->
                                                        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                          (\_ ->
                                                          answer1)
                                                          (\n22 ->
                                                          (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                            (\_ ->
                                                            answer1)
                                                            (\n23 ->
                                                            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                              (\_ ->
                                                              answer1)
                                                              (\n24 ->
                                                              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                                (\_ ->
                                                                instructionDecodeRiA
                                                                  (iTr (\x ->
                                                                    Store_bI
                                                                    x)) isReg
                                                                  ri w2 ow)
                                                                (\n25 ->
                                                                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                                  (\_ ->
                                                                  instructionDecodeRiA
                                                                    (iTr
                                                                    (\x ->
                                                                    Load_bI
                                                                    x)) isReg
                                                                    ri w2 ow)
                                                                  (\n26 ->
                                                                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                                    (\_ ->
                                                                    instructionDecodeRiA
                                                                    (iTr
                                                                    (\x ->
                                                                    Store_wI
                                                                    x)) isReg
                                                                    ri w2 ow)
                                                                    (\n27 ->
                                                                    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                                    (\_ ->
                                                                    instructionDecodeRiA
                                                                    (iTr
                                                                    (\x ->
                                                                    Load_wI
                                                                    x)) isReg
                                                                    ri w2 ow)
                                                                    (\n28 ->
                                                                    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                                    (\_ ->
                                                                    instructionDecodeRiA
                                                                    (iTr
                                                                    (\x ->
                                                                    ReadI x))
                                                                    isReg ri
                                                                    w2 ow)
                                                                    (\n29 ->
                                                                    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                                                    (\_ ->
                                                                    instructionDecodeA
                                                                    (tr
                                                                    AnswerI)
                                                                    isReg w2
                                                                    ow)
                                                                    (\_ ->
                                                                    answer1)
                                                                    n29)
                                                                    n28)
                                                                    n27)
                                                                    n26)
                                                                  n25)
                                                                n24)
                                                              n23)
                                                            n22)
                                                          n21)
                                                        n20)
                                                      n19)
                                                    n18)
                                                  n17)
                                                n16)
                                              n15)
                                            n14)
                                          n13)
                                        n12)
                                      n11)
                                    n10)
                                  n9)
                                n8)
                              n7)
                            n6)
                          n5)
                        n4)
                      n3)
                    n2)
                  n1)
                n0)
              n)
            (proj1_sig
              (bitvector_fin_big (succ (succ (succ (succ (succ 0))))) op))}}}}

and_code :: ([]) Prelude.Bool
and_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

or_code :: ([]) Prelude.Bool
or_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

xor_code :: ([]) Prelude.Bool
xor_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

not_code :: ([]) Prelude.Bool
not_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

add_code :: ([]) Prelude.Bool
add_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

sub_code :: ([]) Prelude.Bool
sub_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

mull_code :: ([]) Prelude.Bool
mull_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

umulh_code :: ([]) Prelude.Bool
umulh_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

smulh_code :: ([]) Prelude.Bool
smulh_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

udiv_code :: ([]) Prelude.Bool
udiv_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

umod_code :: ([]) Prelude.Bool
umod_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

shl_code :: ([]) Prelude.Bool
shl_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

shr_code :: ([]) Prelude.Bool
shr_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

cmpe_code :: ([]) Prelude.Bool
cmpe_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

cmpa_code :: ([]) Prelude.Bool
cmpa_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

cmpae_code :: ([]) Prelude.Bool
cmpae_code =
  (\x _ xs -> x : xs) b0 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

cmpg_code :: ([]) Prelude.Bool
cmpg_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

cmpge_code :: ([]) Prelude.Bool
cmpge_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

mov_code :: ([]) Prelude.Bool
mov_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

cmov_code :: ([]) Prelude.Bool
cmov_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

jmp_code :: ([]) Prelude.Bool
jmp_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

cjmp_code :: ([]) Prelude.Bool
cjmp_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

cnjmp_code :: ([]) Prelude.Bool
cnjmp_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b0 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

store_b_code :: ([]) Prelude.Bool
store_b_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

load_b_code :: ([]) Prelude.Bool
load_b_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b0 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

store_w_code :: ([]) Prelude.Bool
store_w_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

load_w_code :: ([]) Prelude.Bool
load_w_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b0 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

read_code :: ([]) Prelude.Bool
read_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b0 0 []))))

answer_code :: ([]) Prelude.Bool
answer_code =
  (\x _ xs -> x : xs) b1 (succ (succ (succ (succ 0)))) ((\x _ xs -> x : xs)
    b1 (succ (succ (succ 0))) ((\x _ xs -> x : xs) b1 (succ (succ 0))
    ((\x _ xs -> x : xs) b1 (succ 0) ((\x _ xs -> x : xs) b1 0 []))))

option_word :: Operand -> Word
option_word x =
  case x of {
   Prelude.Left w -> w;
   Prelude.Right r -> fin_bitvector_big wordSize r}

option_bool :: Operand -> Prelude.Bool
option_bool o =
  case o of {
   Prelude.Left _ -> b1;
   Prelude.Right _ -> b0}

reg_vect :: RegId -> ([]) Prelude.Bool
reg_vect x =
  fin_bitvector_big (log2_up registerCount) x

instructionEncode :: Instruction -> (,) Word Word
instructionEncode o =
  case o of {
   (,) i op ->
    case i of {
     AndI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) and_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     OrI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) or_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     XorI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) xor_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     NotI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) not_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     AddI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) add_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     SubI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) sub_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     MullI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) mull_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     UmulhI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) umulh_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     SmulhI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) smulh_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     UdivI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) udiv_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     UmodI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) umod_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     ShlI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) shl_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     ShrI ri rj -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) shr_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize (reg_vect rj)
                (const b0 paddingSize))))) wordSize) (option_word op);
     CmpeI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) cmpe_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)
              (const b0 (log2_up registerCount))
              (append (log2_up registerCount) paddingSize (reg_vect ri)
                (const b0 paddingSize))))) wordSize) (option_word op);
     CmpaI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) cmpa_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)
              (const b0 (log2_up registerCount))
              (append (log2_up registerCount) paddingSize (reg_vect ri)
                (const b0 paddingSize))))) wordSize) (option_word op);
     CmpaeI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) cmpae_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)
              (const b0 (log2_up registerCount))
              (append (log2_up registerCount) paddingSize (reg_vect ri)
                (const b0 paddingSize))))) wordSize) (option_word op);
     CmpgI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) cmpg_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)
              (const b0 (log2_up registerCount))
              (append (log2_up registerCount) paddingSize (reg_vect ri)
                (const b0 paddingSize))))) wordSize) (option_word op);
     CmpgeI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) cmpge_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)
              (const b0 (log2_up registerCount))
              (append (log2_up registerCount) paddingSize (reg_vect ri)
                (const b0 paddingSize))))) wordSize) (option_word op);
     MovI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) mov_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     CmovI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) cmov_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     JmpI -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) jmp_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)
              (const b0 (log2_up registerCount))
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     CjmpI -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) cjmp_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)
              (const b0 (log2_up registerCount))
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     CnjmpI -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) cnjmp_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)
              (const b0 (log2_up registerCount))
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     Store_bI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) store_b_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     Load_bI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) load_b_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     Store_wI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) store_w_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     Load_wI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) load_w_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     ReadI ri -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) read_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize) (reg_vect ri)
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op);
     AnswerI -> (,)
      (cast
        (add (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))))
        (append (succ (succ (succ (succ (succ 0)))))
          (add (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize))) answer_code
          (append (succ 0)
            (add (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)) ((\x _ xs -> x : xs)
            (option_bool op) 0 [])
            (append (log2_up registerCount)
              (add (log2_up registerCount) paddingSize)
              (const b0 (log2_up registerCount))
              (append (log2_up registerCount) paddingSize
                (const b0 (log2_up registerCount)) (const b0 paddingSize)))))
        wordSize) (option_word op)}}

type Memory = ([]) Byte

memory_Block_Load :: Memory -> Fin -> Fin -> ([]) Byte
memory_Block_Load m idx blksz =
  rev (proj1_sig blksz)
    (block_Load (pow0 (succ (succ 0)) wordSize) m idx blksz)

memory_Block_Store :: Memory -> Fin -> Fin -> (([]) Byte) -> Memory
memory_Block_Store m idx blksz block =
  block_Store (pow0 (succ (succ 0)) wordSize) m idx blksz
    (rev (proj1_sig blksz) block)

memory_Word_Load :: Memory -> Fin -> Word
memory_Word_Load m idx =
  vector_concat (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))
    wordSizeEighth (memory_Block_Load m idx wordSizeEighthFin)

memory_Word_Store :: Memory -> Fin -> Word -> Memory
memory_Word_Store m idx reg =
  memory_Block_Store m idx wordSizeEighthFin
    (vector_unconcat (succ (succ (succ (succ (succ (succ (succ (succ
      0)))))))) (proj1_sig wordSizeEighthFin) reg)

register_Index :: Word -> Fin
register_Index w =
  bitvector_fin_big wordSize w

memory_Word_Load_from_Reg :: Memory -> Word -> Word
memory_Word_Load_from_Reg m idx =
  memory_Word_Load m (register_Index idx)

memory_Word_Store_from_Reg :: Memory -> Word -> Word -> Memory
memory_Word_Store_from_Reg m idx reg =
  memory_Word_Store m (register_Index idx) reg

traverse_ :: (Monad a2) -> (a1 -> a2) -> (([]) a1) -> a2
traverse_ h f l =
  case l of {
   ([]) -> ret h ();
   (:) a l0 -> bind h (f a) (\_ -> traverse_ h f l0)}

data RegisterE x =
   GetReg Register
 | SetReg Register Word

data MemoryE x =
   LoadByte Address
 | StoreByte Address Byte
 | LoadWord Address
 | StoreWord Address Word

data ProgramCounterE x =
   SetPC Word
 | IncPC
 | GetPC

type InstructionE x =
  Prelude.Integer
  -- singleton inductive, whose constructor was ReadInst
  
data FlagE x =
   GetFlag
 | SetFlag Prelude.Bool

data ReadE x =
   ReadMain
 | ReadAux

denote_operand :: (IFun (RegisterE Any) a1) -> Operand -> Itree a1 Word
denote_operand hasRegister o =
  case o of {
   Prelude.Left v -> Go (RetF v);
   Prelude.Right v -> trigger (subevent hasRegister (GetReg v))}

denote_instruction :: (IFun (RegisterE Any) a1) -> (IFun (FlagE Any) 
                      a1) -> (IFun (ProgramCounterE Any) a1) -> (IFun
                      (MemoryE Any) a1) -> (IFun (ReadE Any) a1) ->
                      Instruction -> Itree a1 ()
denote_instruction hasRegister hasFlag hasProgramCounter hasMemory hasRead o =
  case o of {
   (,) o0 op ->
    bind0 (denote_operand hasRegister op) (\a ->
      case o0 of {
       AndI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {res = bv_and wordSize regj a} in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri res))) (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag
                  (bv_eq wordSize res (const b0 wordSize))))) (\_ ->
              trigger (subevent hasProgramCounter IncPC))));
       OrI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {res = bv_or wordSize regj a} in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri res))) (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag
                  (bv_eq wordSize res (const b0 wordSize))))) (\_ ->
              trigger (subevent hasProgramCounter IncPC))));
       XorI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {res = bv_xor wordSize regj a} in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri res))) (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag
                  (bv_eq wordSize res (const b0 wordSize))))) (\_ ->
              trigger (subevent hasProgramCounter IncPC))));
       NotI ri ->
        let {res = bv_not wordSize a} in
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (SetReg ri res))) (\_ ->
          bind (unsafeCoerce monad_itree)
            (trigger
              (subevent hasFlag (SetFlag
                (bv_eq wordSize res (const b0 wordSize))))) (\_ ->
            trigger (subevent hasProgramCounter IncPC)));
       AddI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {res = bv_add wordSize regj a} in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri (tl wordSize res))))
            (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger (subevent hasFlag (SetFlag (hd wordSize res)))) (\_ ->
              trigger (subevent hasProgramCounter IncPC))));
       SubI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {res = bv_sub wordSize regj a} in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri (tl wordSize res))))
            (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag (Prelude.not (hd wordSize res)))))
              (\_ -> trigger (subevent hasProgramCounter IncPC))));
       MullI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {res = splitat wordSize wordSize (bv_mul wordSize regj a)} in
          let {resh = fst res} in
          let {resl = snd res} in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri resl))) (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag
                  (bv_eq wordSize resh (const b0 wordSize))))) (\_ ->
              trigger (subevent hasProgramCounter IncPC))));
       UmulhI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {
           resh = fst (splitat wordSize wordSize (bv_mul wordSize regj a))}
          in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri resh))) (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag
                  (bv_eq wordSize resh (const b0 wordSize))))) (\_ ->
              trigger (subevent hasProgramCounter IncPC))));
       SmulhI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {wA = wcast a} in
          let {wrej = wcast regj} in
          let {
           mjA = mul3 (twos_complement (pred wordSize) wrej)
                   (twos_complement (pred wordSize) wA)}
          in
          let {
           sres = twos_complement_inv (add0 (pred wordSize) (pred wordSize))
                    mjA}
          in
          let {sign = hd (add0 (pred wordSize) (pred wordSize)) sres} in
          let {
           resh = fst
                    (splitat (pred wordSize) (pred wordSize)
                      (bv_abs (add0 (pred wordSize) (pred wordSize)) sres))}
          in
          bind (unsafeCoerce monad_itree)
            (trigger
              (subevent hasRegister (SetReg ri
                (wuncast ((\x _ xs -> x : xs) sign (pred wordSize) resh)))))
            (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag
                  ((Prelude.&&)
                    (leb1
                      (opp
                        (pow3 (GHC.Base.id ((2 Prelude.*) 1))
                          (sub2 (of_nat0 wordSize) (GHC.Base.id 1)))) mjA)
                    (ltb1 mjA
                      (pow3 (GHC.Base.id ((2 Prelude.*) 1))
                        (sub2 (of_nat0 wordSize) (GHC.Base.id 1))))))))
              (\_ -> trigger (subevent hasProgramCounter IncPC))));
       UdivI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {res = bv_udiv wordSize regj a} in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri res))) (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag
                  (bv_eq wordSize a (const b0 wordSize))))) (\_ ->
              trigger (subevent hasProgramCounter IncPC))));
       UmodI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {res = bv_umod wordSize regj a} in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri res))) (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag
                  (bv_eq wordSize a (const b0 wordSize))))) (\_ ->
              trigger (subevent hasProgramCounter IncPC))));
       ShlI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {res = bv_shl wordSize (bitvector_nat_big wordSize a) regj} in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri res))) (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag
                  (hd (pred wordSize) (wcast regj))))) (\_ ->
              trigger (subevent hasProgramCounter IncPC))));
       ShrI ri rj ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg rj))) (\regj ->
          let {res = bv_shr wordSize (bitvector_nat_big wordSize a) regj} in
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri res))) (\_ ->
            bind (unsafeCoerce monad_itree)
              (trigger
                (subevent hasFlag (SetFlag
                  (last (pred wordSize) (wcast regj))))) (\_ ->
              trigger (subevent hasProgramCounter IncPC))));
       CmpeI ri ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg ri))) (\regi ->
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasFlag (SetFlag (bv_eq wordSize regi a))))
            (\_ -> trigger (subevent hasProgramCounter IncPC)));
       CmpaI ri ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg ri))) (\regi ->
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasFlag (SetFlag (bv_lt wordSize a regi))))
            (\_ -> trigger (subevent hasProgramCounter IncPC)));
       CmpaeI ri ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg ri))) (\regi ->
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasFlag (SetFlag (bv_le wordSize a regi))))
            (\_ -> trigger (subevent hasProgramCounter IncPC)));
       CmpgI ri ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg ri))) (\regi ->
          bind (unsafeCoerce monad_itree)
            (trigger
              (subevent hasFlag (SetFlag
                (ltb1 (twos_complement (pred wordSize) (wcast a))
                  (twos_complement (pred wordSize) (wcast regi)))))) (\_ ->
            trigger (subevent hasProgramCounter IncPC)));
       CmpgeI ri ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg ri))) (\regi ->
          bind (unsafeCoerce monad_itree)
            (trigger
              (subevent hasFlag (SetFlag
                (leb1 (twos_complement (pred wordSize) (wcast a))
                  (twos_complement (pred wordSize) (wcast regi)))))) (\_ ->
            trigger (subevent hasProgramCounter IncPC)));
       MovI ri ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg ri))) (\_ ->
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri a))) (\_ ->
            trigger (subevent hasProgramCounter IncPC)));
       CmovI ri ->
        bind (unsafeCoerce monad_itree) (trigger (subevent hasFlag GetFlag))
          (\flag0 ->
          bind (unsafeCoerce monad_itree)
            (case flag0 of {
              Prelude.True ->
               bind (unsafeCoerce monad_itree)
                 (trigger (subevent hasRegister (GetReg ri))) (\_ ->
                 trigger (subevent hasRegister (SetReg ri a)));
              Prelude.False -> ret (unsafeCoerce monad_itree) ()}) (\_ ->
            trigger (subevent hasProgramCounter IncPC)));
       JmpI -> trigger (subevent hasProgramCounter (SetPC a));
       CjmpI ->
        bind (unsafeCoerce monad_itree) (trigger (subevent hasFlag GetFlag))
          (\flag0 ->
          case flag0 of {
           Prelude.True -> trigger (subevent hasProgramCounter (SetPC a));
           Prelude.False -> trigger (subevent hasProgramCounter IncPC)});
       CnjmpI ->
        bind (unsafeCoerce monad_itree) (trigger (subevent hasFlag GetFlag))
          (\flag0 ->
          case flag0 of {
           Prelude.True -> trigger (subevent hasProgramCounter IncPC);
           Prelude.False -> trigger (subevent hasProgramCounter (SetPC a))});
       Store_bI ri ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg ri))) (\regi ->
          bind (unsafeCoerce monad_itree)
            (trigger
              (subevent hasMemory (StoreByte (bitvector_fin_big wordSize a)
                (snd
                  (splitat
                    (sub0 wordSize (succ (succ (succ (succ (succ (succ (succ
                      (succ 0))))))))) (succ (succ (succ (succ (succ (succ
                    (succ (succ 0)))))))) (wbcast regi)))))) (\_ ->
            trigger (subevent hasProgramCounter IncPC)));
       Load_bI ri ->
        bind (unsafeCoerce monad_itree)
          (trigger
            (subevent hasMemory (LoadByte (bitvector_fin_big wordSize a))))
          (\abyte ->
          bind (unsafeCoerce monad_itree)
            (trigger
              (subevent hasRegister (SetReg ri
                (wbuncast
                  (append
                    (sub0 wordSize (succ (succ (succ (succ (succ (succ (succ
                      (succ 0))))))))) (succ (succ (succ (succ (succ (succ
                    (succ (succ 0))))))))
                    (const b0
                      (sub0 wordSize (succ (succ (succ (succ (succ (succ
                        (succ (succ 0)))))))))) abyte))))) (\_ ->
            trigger (subevent hasProgramCounter IncPC)));
       Store_wI ri ->
        bind (unsafeCoerce monad_itree)
          (trigger (subevent hasRegister (GetReg ri))) (\regi ->
          bind (unsafeCoerce monad_itree)
            (trigger
              (subevent hasMemory (StoreWord (bitvector_fin_big wordSize a)
                regi))) (\_ -> trigger (subevent hasProgramCounter IncPC)));
       Load_wI ri ->
        bind (unsafeCoerce monad_itree)
          (trigger
            (subevent hasMemory (LoadWord (bitvector_fin_big wordSize a))))
          (\aword ->
          bind (unsafeCoerce monad_itree)
            (trigger (subevent hasRegister (SetReg ri aword))) (\_ ->
            trigger (subevent hasProgramCounter IncPC)));
       ReadI ri ->
        bind (unsafeCoerce monad_itree)
          ((\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
             (\_ ->
             bind (unsafeCoerce monad_itree)
               (trigger (subevent hasRead ReadMain)) (\mtWord ->
               case mtWord of {
                Prelude.Just w ->
                 bind (unsafeCoerce monad_itree)
                   (trigger (subevent hasRegister (SetReg ri w))) (\_ ->
                   trigger (subevent hasFlag (SetFlag b0)));
                Prelude.Nothing ->
                 bind (unsafeCoerce monad_itree)
                   (trigger
                     (subevent hasRegister (SetReg ri (const b0 wordSize))))
                   (\_ -> trigger (subevent hasFlag (SetFlag b1)))}))
             (\n ->
             (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
               (\_ ->
               bind (unsafeCoerce monad_itree)
                 (trigger (subevent hasRead ReadAux)) (\mtWord ->
                 case mtWord of {
                  Prelude.Just w ->
                   bind (unsafeCoerce monad_itree)
                     (trigger (subevent hasRegister (SetReg ri w))) (\_ ->
                     trigger (subevent hasFlag (SetFlag b0)));
                  Prelude.Nothing ->
                   bind (unsafeCoerce monad_itree)
                     (trigger
                       (subevent hasRegister (SetReg ri (const b0 wordSize))))
                     (\_ -> trigger (subevent hasFlag (SetFlag b1)))}))
               (\_ ->
               bind (unsafeCoerce monad_itree)
                 (trigger
                   (subevent hasRegister (SetReg ri (const b0 wordSize))))
                 (\_ -> trigger (subevent hasFlag (SetFlag b1))))
               n)
             (bitvector_nat_big wordSize a)) (\_ ->
          trigger (subevent hasProgramCounter IncPC));
       AnswerI -> ret (unsafeCoerce monad_itree) ()})}

run_step :: (IFun (RegisterE Any) a1) -> (IFun (FlagE Any) a1) -> (IFun
            (ProgramCounterE Any) a1) -> (IFun (MemoryE Any) a1) -> (IFun
            (ReadE Any) a1) -> (IFun (InstructionE Any) a1) -> Itree 
            a1 (Prelude.Either () Word)
run_step hasRegister hasFlag hasProgramCounter hasMemory hasRead hasInstruction =
  bind0 (trigger (subevent hasProgramCounter GetPC)) (\a ->
    bind (unsafeCoerce monad_itree)
      (trigger (subevent hasInstruction (bitvector_nat_big wordSize a)))
      (\w2code ->
      let {instr = uncurry instructionDecode w2code} in
      case instr of {
       (,) i0 op ->
        case i0 of {
         AnswerI ->
          map0 (\x -> Prelude.Right x) (denote_operand hasRegister op);
         _ ->
          map0 (\x -> Prelude.Left x)
            (denote_instruction hasRegister hasFlag hasProgramCounter
              hasMemory hasRead instr)}}))

run :: (IFun (RegisterE Any) a1) -> (IFun (FlagE Any) a1) -> (IFun
       (ProgramCounterE Any) a1) -> (IFun (MemoryE Any) a1) -> (IFun
       (ReadE Any) a1) -> (IFun (InstructionE Any) a1) -> Itree a1 Word
run hasRegister hasFlag hasProgramCounter hasMemory hasRead hasInstruction =
  iter1 (\_ ->
    run_step hasRegister hasFlag hasProgramCounter hasMemory hasRead
      hasInstruction) ()

denote_program :: (IFun (RegisterE Any) a1) -> (IFun (FlagE Any) a1) -> (IFun
                  (ProgramCounterE Any) a1) -> (IFun (MemoryE Any) a1) ->
                  (IFun (ReadE Any) a1) -> (([]) Instruction) -> Itree 
                  a1 ()
denote_program hasRegister hasFlag hasProgramCounter hasMemory hasRead =
  traverse_ (unsafeCoerce monad_itree)
    (denote_instruction hasRegister hasFlag hasProgramCounter hasMemory
      hasRead)

data MachineState =
   MkMachineState Word Registers Prelude.Bool Memory Tape Tape Program

programCounter :: MachineState -> Word
programCounter m =
  case m of {
   MkMachineState programCounter0 _ _ _ _ _ _ -> programCounter0}

registers :: MachineState -> Registers
registers m =
  case m of {
   MkMachineState _ registers0 _ _ _ _ _ -> registers0}

flag :: MachineState -> Prelude.Bool
flag m =
  case m of {
   MkMachineState _ _ flag0 _ _ _ _ -> flag0}

memory :: MachineState -> Memory
memory m =
  case m of {
   MkMachineState _ _ _ memory0 _ _ _ -> memory0}

tapeMain :: MachineState -> Tape
tapeMain m =
  case m of {
   MkMachineState _ _ _ _ tapeMain0 _ _ -> tapeMain0}

tapeAux :: MachineState -> Tape
tapeAux m =
  case m of {
   MkMachineState _ _ _ _ _ tapeAux0 _ -> tapeAux0}

program :: MachineState -> Program
program m =
  case m of {
   MkMachineState _ _ _ _ _ _ program0 -> program0}

updtPC :: Word -> MachineState -> MachineState
updtPC n m =
  case m of {
   MkMachineState _ r0 f0 m0 t0 t1 p0 -> MkMachineState n r0 f0 m0 t0 t1 p0}

updtReg :: Registers -> MachineState -> MachineState
updtReg n m =
  case m of {
   MkMachineState pc0 _ f0 m0 t0 t1 p0 -> MkMachineState pc0 n f0 m0 t0 t1 p0}

updtFlag :: Prelude.Bool -> MachineState -> MachineState
updtFlag n m =
  case m of {
   MkMachineState pc0 r0 _ m0 t0 t1 p0 -> MkMachineState pc0 r0 n m0 t0 t1 p0}

updtMem :: Memory -> MachineState -> MachineState
updtMem n m =
  case m of {
   MkMachineState pc0 r0 f0 _ t0 t1 p0 -> MkMachineState pc0 r0 f0 n t0 t1 p0}

updtMTape :: Tape -> MachineState -> MachineState
updtMTape n m =
  case m of {
   MkMachineState pc0 r0 f0 m0 _ t1 p0 -> MkMachineState pc0 r0 f0 m0 n t1 p0}

updtATape :: Tape -> MachineState -> MachineState
updtATape n m =
  case m of {
   MkMachineState pc0 r0 f0 m0 t0 _ p0 -> MkMachineState pc0 r0 f0 m0 t0 n p0}

handle_registers :: (IFun (StateE MachineState Any) a1) -> (RegisterE 
                    a2) -> Itree a1 a2
handle_registers h e =
  bind (unsafeCoerce monad_itree) (get (unsafeCoerce h)) (\s ->
    let {reg = registers s} in
    case e of {
     GetReg x -> ret (unsafeCoerce monad_itree) (nth registerCount reg x);
     SetReg x v ->
      unsafeCoerce put h (updtReg (replace registerCount reg x v) s)})

handle_memory :: (IFun (StateE MachineState Any) a1) -> (MemoryE a2) -> Itree
                 a1 a2
handle_memory h e =
  bind (unsafeCoerce monad_itree) (get (unsafeCoerce h)) (\s ->
    let {m = memory s} in
    case e of {
     LoadByte x ->
      ret (unsafeCoerce monad_itree)
        (nth (pow0 (succ (succ 0)) wordSize) m x);
     StoreByte x v ->
      unsafeCoerce put h
        (updtMem (replace (pow0 (succ (succ 0)) wordSize) m x v) s);
     LoadWord x -> ret (unsafeCoerce monad_itree) (memory_Word_Load m x);
     StoreWord x v ->
      unsafeCoerce put h (updtMem (memory_Word_Store m x v) s)})

handle_programCounter :: (IFun (StateE MachineState Any) a1) ->
                         (ProgramCounterE a2) -> Itree a1 a2
handle_programCounter h e =
  bind (unsafeCoerce monad_itree) (get (unsafeCoerce h)) (\s ->
    let {pc = programCounter s} in
    case e of {
     SetPC v -> unsafeCoerce put h (updtPC v s);
     IncPC -> unsafeCoerce put h (updtPC (bv_succ wordSize pc) s);
     GetPC -> ret (unsafeCoerce monad_itree) pc})

handle_flag :: (IFun (StateE MachineState Any) a1) -> (FlagE a2) -> Itree 
               a1 a2
handle_flag h e =
  bind (unsafeCoerce monad_itree) (get (unsafeCoerce h)) (\s ->
    let {fl = flag s} in
    case e of {
     GetFlag -> ret (unsafeCoerce monad_itree) fl;
     SetFlag b -> unsafeCoerce put h (updtFlag b s)})

handle_read :: (IFun (StateE MachineState Any) a1) -> (ReadE a2) -> Itree 
               a1 a2
handle_read h e =
  bind (unsafeCoerce monad_itree) (get (unsafeCoerce h)) (\s ->
    let {main = tapeMain s} in
    let {aux = tapeAux s} in
    case e of {
     ReadMain ->
      case main of {
       ([]) -> ret (unsafeCoerce monad_itree) Prelude.Nothing;
       (:) x xs ->
        bind (unsafeCoerce monad_itree) (unsafeCoerce put h (updtMTape xs s))
          (\_ -> ret (unsafeCoerce monad_itree) (Prelude.Just x))};
     ReadAux ->
      case aux of {
       ([]) -> ret (unsafeCoerce monad_itree) Prelude.Nothing;
       (:) x xs ->
        bind (unsafeCoerce monad_itree) (unsafeCoerce put h (updtATape xs s))
          (\_ -> ret (unsafeCoerce monad_itree) (Prelude.Just x))}})

handle_instruction :: (IFun (StateE MachineState Any) a1) -> (InstructionE
                      a2) -> Itree a1 a2
handle_instruction h e =
  bind (unsafeCoerce monad_itree) (get (unsafeCoerce h)) (\s ->
    let {prog = program s} in
    case nth_error prog e of {
     Prelude.Just x -> ret (unsafeCoerce monad_itree) x;
     Prelude.Nothing ->
      ret (unsafeCoerce monad_itree) (instructionEncode answer1)})

type MachineE x =
  Sum1 (InstructionE Any)
  (Sum1 (ReadE Any)
  (Sum1 (FlagE Any)
  (Sum1 (ProgramCounterE Any) (Sum1 (MemoryE Any) (RegisterE Any) Any) Any)
  Any) Any) x

handle_machine :: (IFun (StateE MachineState Any) a1) -> (MachineE a2) ->
                  Itree a1 a2
handle_machine h x =
  case_ __ (unsafeCoerce (\_ _ _ x0 x1 _ -> case_sum1_Handler x0 x1)) __ __
    __ (unsafeCoerce (\_ -> handle_instruction h))
    (case_ __ (unsafeCoerce (\_ _ _ x0 x1 _ -> case_sum1_Handler x0 x1)) __
      __ __ (unsafeCoerce (\_ -> handle_read h))
      (case_ __ (unsafeCoerce (\_ _ _ x0 x1 _ -> case_sum1_Handler x0 x1)) __
        __ __ (unsafeCoerce (\_ -> handle_flag h))
        (case_ __ (unsafeCoerce (\_ _ _ x0 x1 _ -> case_sum1_Handler x0 x1))
          __ __ __ (unsafeCoerce (\_ -> handle_programCounter h))
          (case_ __
            (unsafeCoerce (\_ _ _ x0 x1 _ -> case_sum1_Handler x0 x1)) __ __
            __ (unsafeCoerce (\_ -> handle_memory h))
            (unsafeCoerce (\_ -> handle_registers h)))))) __ x

machine_h :: (Sum1 (MachineE Any) a1 a2) -> MachineState -> Itree a1
             ((,) MachineState a2)
machine_h x x0 =
  cat (unsafeCoerce (\_ _ _ x1 x2 _ -> cat_IFun x1 x2)) __ __ __
    (bimap __
      (bimap_Coproduct (unsafeCoerce (\_ _ _ x1 x2 _ -> cat_Handler x1 x2))
        __ (unsafeCoerce (\_ _ _ x1 x2 _ -> case_sum1_Handler x1 x2))
        (unsafeCoerce (\_ _ _ -> inl_sum1_Handler))
        (unsafeCoerce (\_ _ _ -> inr_sum1_Handler))) __ __ __ __
      (unsafeCoerce (\_ -> handle_machine (reSum_id (\_ _ -> id_IFun) __)))
      (id_ (unsafeCoerce (\_ _ -> id_Handler)) __)) (\_ ->
    unsafeCoerce run_state) __ x x0

interp_machine :: (Itree (Sum1 (MachineE Any) a1 Any) a2) -> MachineState ->
                  Itree a1 ((,) MachineState a2)
interp_machine t =
  interp_state (unsafeCoerce functor_itree) (unsafeCoerce monad_itree)
    (unsafeCoerce (\_ _ -> monadIter_itree)) (unsafeCoerce (\_ -> machine_h))
    t

initialState :: Program -> Tape -> Tape -> MachineState
initialState s t0 t1 =
  MkMachineState (const b0 wordSize)
    (const (const b0 wordSize) registerCount) b0
    (const
      (const b0 (succ (succ (succ (succ (succ (succ (succ (succ 0)))))))))
      (pow0 (succ (succ 0)) wordSize)) t0 t1 s

interp_program :: Program -> Tape -> Tape -> Itree a1 Word
interp_program s t0 t1 =
  map0 snd
    (interp_machine
      (run
        (reSum_inl __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
          (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
          (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
            (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
            (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
              (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
              (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
                (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
                (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
                  (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
                  (reSum_inr __
                    (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
                    (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
                    (reSum_id (unsafeCoerce (\_ _ -> id_IFun)) __)))))))
        (reSum_inl __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
          (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
          (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
            (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
            (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
              (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
              (reSum_inl __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
                (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
                (reSum_id (unsafeCoerce (\_ _ -> id_IFun)) __)))))
        (reSum_inl __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
          (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
          (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
            (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
            (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
              (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
              (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
                (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
                (reSum_inl __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
                  (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
                  (reSum_id (unsafeCoerce (\_ _ -> id_IFun)) __))))))
        (reSum_inl __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
          (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
          (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
            (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
            (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
              (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
              (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
                (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
                (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
                  (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
                  (reSum_inl __
                    (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
                    (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
                    (reSum_id (unsafeCoerce (\_ _ -> id_IFun)) __)))))))
        (reSum_inl __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
          (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
          (reSum_inr __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
            (unsafeCoerce (\_ _ _ -> inr_sum1)) __ __ __
            (reSum_inl __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
              (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
              (reSum_id (unsafeCoerce (\_ _ -> id_IFun)) __))))
        (reSum_inl __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
          (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
          (reSum_inl __ (unsafeCoerce (\_ _ _ x x0 _ -> cat_IFun x x0))
            (unsafeCoerce (\_ _ _ -> inl_sum1)) __ __ __
            (reSum_id (unsafeCoerce (\_ _ -> id_IFun)) __))))
      (initialState s t0 t1))


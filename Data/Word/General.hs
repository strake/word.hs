module Data.Word.General (Word) where

import Prelude hiding (Word, reverse, (!!))
import Control.Applicative
import Control.Monad.Trans.State
import Data.Bits (Bits (..))
import Data.Bool (bool)
import Data.Fin
import Data.Fin.List hiding (swap)
import Data.Function (on)
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Reverse (Reverse (..))
import Data.Maybe (fromMaybe, fromJust)
import Data.Natural.Class
import Data.Semigroup (Endo (..), Semigroup (..))
import Data.Tuple (swap)
import qualified Numeric.Natural as N

newtype Word n = Word { bits :: List n Bool }
  deriving (Eq)

instance Ord (Word n) where
    compare = compare `on` reverse . bits

instance Natural n => Num (Word n) where
    Word as + Word bs = Word (go False as bs)
      where
        go :: ∀ n . Natural n => Bool -> List n Bool -> List n Bool -> List n Bool
        go c = unOp₂ $ natural (Op₂ $ \ Nil Nil -> Nil) $ Op₂ $ \ (a:.as) (b:.bs) ->
            let (z, c') = ((a /= b) /= c, a && b && c) in z:.go c' as bs

    a * b = fromInteger . fromIntegral $ toNatural a * toNatural b

    negate = (+1) . complement

    abs = id

    signum = fromInteger . fromIntegral . signum . toNatural

    fromInteger n = case compare n 0 of
        LT -> negate $ fromInteger (abs n)
        EQ -> zeroBits
        GT -> fromInteger (n-1) + bit 0

toNatural :: Word n -> N.Natural
toNatural = foldl (\ n b -> bool id (+1) b $ n `shiftL` 1) 0 . bits

instance Natural n => Bits (Word n) where
    Word as .&. Word bs = Word (liftA2 (&&) as bs)
    Word as .|. Word bs = Word (liftA2 (||) as bs)
    Word as `xor` Word bs = Word (liftA2 (/=) as bs)
    complement (Word as) = Word (not <$> as)
    shiftL (Word as) k = Word $ stimes k (Endo go) `appEndo` as
      where go as = flip evalState False $ traverse (state . curry swap) as
    shiftR (Word as) k = Word $ stimes k (Endo go) `appEndo` as
      where go as = getReverse . flip evalState False $ traverse (state . curry swap) (Reverse as)
    rotateL (Word as) k = Word $ stimes k (Endo go) `appEndo` as
      where go as = let (bs, c) = flip runState c $ traverse (state . curry swap) as in bs
    rotateR (Word as) k = Word $ stimes k (Endo go) `appEndo` as
      where go as = let (Reverse bs, c) = flip runState c $ traverse (state . curry swap) (Reverse as) in bs
    bitSize = fromJust . bitSizeMaybe
    bitSizeMaybe _ = Just . fromIntegral . getConst $ (reify :: Const Peano n)
    isSigned _ = False
    testBit (Word as) = fromMaybe False . fmap (as !!) . toFinMay
    bit n = Word $ maybe id (\ n -> runIdentity . at n ((pure . pure) True)) (toFinMay n) $ pure False
    popCount = foldr (bool id (+1)) 0 . bits

newtype Op₂ a b n = Op₂ { unOp₂ :: List n a -> List n a -> List n b }

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Data.DiffUtils.Diff3 where

import Data.Proxy
import Data.Type.Equality
import Data.TypeList.DList
import Data.DiffUtils.Diff
import Data.DiffUtils.Diff3.Core
import Data.DiffUtils.Diff3.TypeCheck

-- User friendly entry point
-- TODO what kind of interface is better? ES3 or Either
-- TODO maybe even more friendly expecting directly raw types instead of DList ?
diff3 :: (Family f, Metric f, a :<: f, b :<: f) 
      => b -> a -> b -> Either [Conflict f] (ES f '[ a ] '[ b ])
diff3 = diff3' Proxy

diff3' :: (Family f, Metric f, a :<: f, b :<: f) 
      => Proxy f -> b -> a -> b -> Either [Conflict f] (ES f '[ a ] '[ b ])
diff3' _ x o y = 
  let (ox, oy) = (gdiff o x, gdiff o y) in
  case typeCheck (merge3 ox oy) of
    Left errs -> Left errs
    Right (WES ty e) ->
      case tysEq Proxy ty (TCons (proxyOf x) TNil) of
        Just Refl -> Right e
        Nothing -> Left [TConf tyErr]
          where tyErr = TyErr (ET (TCons (proxyOf x) TNil)) (toInferredType ty)


proxyOf :: a -> Proxy a
proxyOf _ = Proxy
